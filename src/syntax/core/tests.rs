use super::*;

fn parse(src: &str) -> RcTerm {
    RcTerm::from_concrete(&src.parse().unwrap())
}

mod alpha_eq {
    use super::*;

    #[test]
    fn var() {
        assert_eq!(parse(r"x"), parse(r"x"));
    }

    #[test]
    #[should_panic]
    fn var_diff() {
        assert_eq!(parse(r"x"), parse(r"y"));
    }

    #[test]
    fn ty() {
        assert_eq!(parse(r"Type"), parse(r"Type"));
    }

    #[test]
    fn lam() {
        assert_eq!(parse(r"\x : Type => x"), parse(r"\a : Type => a"));
    }

    #[test]
    fn pi() {
        assert_eq!(parse(r"(x : Type) -> x"), parse(r"(a : Type) -> a"));
    }

    #[test]
    fn lam_app() {
        assert_eq!(
            parse(r"\x : Type -> Type => x Type"),
            parse(r"\a : Type -> Type => a Type")
        );
    }

    #[test]
    fn pi_app() {
        assert_eq!(
            parse(r"(x : Type -> Type) -> x Type"),
            parse(r"(a : Type -> Type) -> a Type")
        );
    }

    #[test]
    fn lam_lam_app() {
        assert_eq!(
            parse(r"\x : Type -> Type => \y : Type => x y"),
            parse(r"\a : Type -> Type => \b : Type => a b"),
        );
    }

    #[test]
    fn pi_pi_app() {
        assert_eq!(
            parse(r"(x : Type -> Type) -> (y : Type) -> x y"),
            parse(r"(a : Type -> Type) -> (b : Type) -> a b"),
        );
    }
}

mod from_concrete {
    use super::*;

    #[test]
    fn parse_prelude() {
        Module::from_concrete(&include_str!("../../../prelude.lp").parse().unwrap());
    }

    #[test]
    fn var() {
        assert_eq!(parse(r"x"), Term::Var(Var::Free(Name::user("x"))).into());
    }

    #[test]
    fn var_kebab_case() {
        assert_eq!(
            parse(r"or-elim"),
            Term::Var(Var::Free(Name::user("or-elim"))).into(),
        );
    }

    #[test]
    fn ty() {
        assert_eq!(parse(r"Type"), RcTerm::universe());
    }

    #[test]
    fn ann() {
        assert_eq!(
            parse(r"Type : Type"),
            Term::Ann(RcTerm::universe(), RcTerm::universe()).into(),
        );
    }

    #[test]
    fn ann_ann_left() {
        assert_eq!(
            parse(r"Type : Type : Type"),
            Term::Ann(
                Term::Ann(RcTerm::universe(), RcTerm::universe()).into(),
                RcTerm::universe(),
            ).into(),
        );
    }

    #[test]
    fn ann_ann_right() {
        assert_eq!(
            parse(r"Type : (Type : Type)"),
            Term::Ann(
                RcTerm::universe(),
                Term::Ann(RcTerm::universe(), RcTerm::universe()).into(),
            ).into(),
        );
    }

    #[test]
    fn ann_ann_ann() {
        assert_eq!(
            parse(r"(Type : Type) : (Type : Type)"),
            Term::Ann(
                Term::Ann(RcTerm::universe(), RcTerm::universe()).into(),
                Term::Ann(RcTerm::universe(), RcTerm::universe()).into(),
            ).into(),
        );
    }

    #[test]
    fn lam_ann() {
        let x = Name::user("x");

        assert_eq!(
            parse(r"\x : Type -> Type => x"),
            Term::Lam(TermLam::bind(
                Named(
                    x.clone(),
                    Some(
                        Term::Pi(TermPi::bind(
                            Named(Name::Abstract, RcTerm::universe()),
                            RcTerm::universe(),
                        )).into()
                    ),
                ),
                Term::Var(Var::Free(x)).into(),
            )).into(),
        );
    }

    #[test]
    fn lam() {
        let x = Name::user("x");
        let y = Name::user("y");

        assert_eq!(
            parse(r"\x : (\y => y) => x"),
            Term::Lam(TermLam::bind(
                Named(
                    x.clone(),
                    Some(
                        Term::Lam(TermLam::bind(
                            Named(y.clone(), None),
                            Term::Var(Var::Free(y)).into(),
                        )).into()
                    ),
                ),
                Term::Var(Var::Free(x)).into(),
            )).into(),
        );
    }

    #[test]
    fn lam_lam_ann() {
        let x = Name::user("x");
        let y = Name::user("y");

        assert_eq!(
            parse(r"\x : Type => \y : Type => x"),
            Term::Lam(TermLam::bind(
                Named(x.clone(), Some(RcTerm::universe())),
                Term::Lam(TermLam::bind(
                    Named(y, Some(RcTerm::universe())),
                    Term::Var(Var::Free(x)).into(),
                )).into(),
            )).into(),
        );
    }

    #[test]
    fn arrow() {
        assert_eq!(
            parse(r"Type -> Type"),
            Term::Pi(TermPi::bind(
                Named(Name::Abstract, RcTerm::universe()),
                RcTerm::universe(),
            )).into(),
        );
    }

    #[test]
    fn pi() {
        let x = Name::user("x");

        assert_eq!(
            parse(r"(x : Type -> Type) -> x"),
            Term::Pi(TermPi::bind(
                Named(
                    x.clone(),
                    Term::Pi(TermPi::bind(
                        Named(Name::Abstract, RcTerm::universe()),
                        RcTerm::universe(),
                    )).into(),
                ),
                Term::Var(Var::Free(x)).into(),
            )).into(),
        );
    }

    #[test]
    fn pi_pi() {
        let x = Name::user("x");
        let y = Name::user("y");

        assert_eq!(
            parse(r"(x : Type) -> (y : Type) -> x"),
            Term::Pi(TermPi::bind(
                Named(x.clone(), RcTerm::universe()),
                Term::Pi(TermPi::bind(
                    Named(y, RcTerm::universe()),
                    Term::Var(Var::Free(x)).into(),
                )).into(),
            )).into(),
        );
    }

    #[test]
    fn pi_arrow() {
        let x = Name::user("x");

        assert_eq!(
            parse(r"(x : Type) -> x -> x"),
            Term::Pi(TermPi::bind(
                Named(x.clone(), RcTerm::universe()),
                Term::Pi(TermPi::bind(
                    Named(Name::Abstract, Term::Var(Var::Free(x.clone())).into(),),
                    Term::Var(Var::Free(x)).into(),
                )).into(),
            )).into(),
        );
    }

    #[test]
    fn lam_app() {
        let x = Name::user("x");
        let y = Name::user("y");

        assert_eq!(
            parse(r"\x : (Type -> Type) => \y : Type => x y"),
            Term::Lam(TermLam::bind(
                Named(
                    x.clone(),
                    Some(
                        Term::Pi(TermPi::bind(
                            Named(Name::Abstract, RcTerm::universe()),
                            RcTerm::universe(),
                        )).into(),
                    ),
                ),
                Term::Lam(TermLam::bind(
                    Named(y.clone(), Some(RcTerm::universe())),
                    Term::App(
                        Term::Var(Var::Free(x)).into(),
                        Term::Var(Var::Free(y)).into(),
                    ).into(),
                )).into(),
            )).into(),
        );
    }

    #[test]
    fn id() {
        let x = Name::user("x");
        let a = Name::user("a");

        assert_eq!(
            parse(r"\a : Type => \x : a => x"),
            Term::Lam(TermLam::bind(
                Named(a.clone(), Some(RcTerm::universe())),
                Term::Lam(TermLam::bind(
                    Named(x.clone(), Some(Term::Var(Var::Free(a)).into()),),
                    Term::Var(Var::Free(x)).into(),
                )).into(),
            )).into(),
        );
    }

    #[test]
    fn id_ty() {
        let a = Name::user("a");

        assert_eq!(
            parse(r"(a : Type) -> a -> a"),
            Term::Pi(TermPi::bind(
                Named(a.clone(), RcTerm::universe()),
                Term::Pi(TermPi::bind(
                    Named(Name::Abstract, Term::Var(Var::Free(a.clone())).into(),),
                    Term::Var(Var::Free(a)).into(),
                )).into(),
            )).into(),
        );
    }

    mod sugar {
        use super::*;

        #[test]
        fn lam_args() {
            assert_eq!(
                parse(r"\y (x : Type) z => x"),
                parse(r"\y => \x : Type => \z => x"),
            );
        }

        #[test]
        fn pi_args() {
            assert_eq!(
                parse(r"(a : Type) -> (x y z : a) -> x"),
                parse(r"(a : Type) -> (x : a) -> (y : a) -> (z : a) -> x"),
            );
        }

        #[test]
        fn arrow() {
            assert_eq!(
                parse(r"(a : Type) -> a -> a"),
                parse(r"(a : Type) -> (x : a) -> a"),
            )
        }
    }
}
