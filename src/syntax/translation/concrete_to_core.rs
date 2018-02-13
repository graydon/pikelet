use source::pos::Span;

use syntax::concrete;
use syntax::core;
use syntax::var::{Debruijn, Named, Var};

use super::FromConcrete;

fn lam_from_concrete(
    params: &[(Vec<(Span, String)>, Option<Box<concrete::Term>>)],
    body: &concrete::Term,
) -> core::RcTerm {
    let mut term = core::RcTerm::from_concrete(body);

    for &(ref names, ref ann) in params.iter().rev() {
        for &(span, ref name) in names.iter().rev() {
            let name = core::Name::User(name.clone());
            term = match *ann {
                None => {
                    let lam = core::TermLam::bind(Named::new(name, None), term);
                    core::Term::Lam(span.lo(), lam).into()
                },
                Some(ref ann) => {
                    let ann = core::RcTerm::from_concrete(ann);
                    let lam = core::TermLam::bind(Named::new(name, Some(ann)), term);
                    core::Term::Lam(span.lo(), lam).into()
                },
            };
        }
    }

    term
}

fn pi_from_concrete(
    param_names: &[(Span, String)],
    ann: &concrete::Term,
    body: &concrete::Term,
) -> core::RcTerm {
    let ann = core::RcTerm::from_concrete(ann);
    let mut term = core::RcTerm::from_concrete(body);

    for &(span, ref name) in param_names.iter().rev() {
        // This could be wrong... :/
        let param = Named::new(core::Name::User(name.clone()), ann.clone());
        let pi = core::TermPi::bind(param, term);
        term = core::Term::Pi(span.lo(), pi).into();
    }

    term
}

impl<'a> FromConcrete<&'a concrete::Module> for core::Module {
    /// Convert the module in the concrete syntax to a module in the core syntax
    fn from_concrete(module: &'a concrete::Module) -> core::Module {
        use std::collections::BTreeMap;
        use std::collections::btree_map::Entry;

        // The type claims that we have encountered so far! We'll use these when
        // we encounter their corresponding definitions later as type annotations
        let mut claims = BTreeMap::new();
        // The definitions, desugared from the concrete syntax
        let mut definitions = Vec::<core::Definition>::new();

        for declaration in &module.declarations {
            match *declaration {
                concrete::Declaration::Import { .. } => unimplemented!("import declarations"),
                // We've enountered a claim! Let's try to add it to the claims
                // that we've seen so far...
                concrete::Declaration::Claim {
                    name: (_, ref name),
                    ref ann,
                    ..
                } => {
                    match claims.entry(name) {
                        // Oh no! We've already seen a claim for this name!
                        Entry::Occupied(_) => panic!(), // FIXME: Better error
                        // This name does not yet have a claim associated with it
                        Entry::Vacant(mut entry) => {
                            let mut ann = core::RcTerm::from_concrete(ann);

                            for (level, definition) in definitions.iter().rev().enumerate() {
                                let name = core::Name::user(definition.name.clone());
                                ann.close_at(Debruijn(level as u32), &name);
                            }

                            entry.insert(ann)
                        },
                    };
                },
                // We've encountered a definition. Let's desugar it!
                concrete::Declaration::Definition {
                    name: (_, ref name),
                    ref params,
                    ref body,
                    ..
                } => {
                    let name = name.clone();
                    let mut term = lam_from_concrete(params, body);
                    let ann = claims.remove(&name);

                    for (level, definition) in definitions.iter().rev().enumerate() {
                        let name = core::Name::user(definition.name.clone());
                        term.close_at(Debruijn(level as u32), &name);
                    }

                    definitions.push(core::Definition { name, term, ann });
                },
            }
        }

        // FIXME: Better error
        assert!(claims.is_empty());

        core::Module {
            name: module.name.1.clone(),
            definitions,
        }
    }
}

impl<'a> FromConcrete<&'a concrete::Term> for core::RcTerm {
    /// Convert a term in the concrete syntax into a core term
    fn from_concrete(term: &'a concrete::Term) -> core::RcTerm {
        match *term {
            concrete::Term::Parens(_, ref term) => core::RcTerm::from_concrete(term),
            concrete::Term::Ann(ref expr, ref ty) => {
                let expr = core::RcTerm::from_concrete(expr).into();
                let ty = core::RcTerm::from_concrete(ty).into();

                core::Term::Ann(expr, ty).into()
            },
            concrete::Term::Universe(span, level) => {
                core::Term::Universe(span, level.map_or(core::Level::ZERO, core::Level)).into()
            },
            concrete::Term::Var(span, ref x) => {
                let var = Var::Free(core::Name::User(x.clone()));

                core::Term::Var(span, var).into()
            },
            concrete::Term::Lam(_, ref params, ref body) => lam_from_concrete(params, body),
            concrete::Term::Pi(_, (ref names, ref ann), ref body) => {
                pi_from_concrete(names, ann, body)
            },
            concrete::Term::Arrow(ref ann, ref body) => {
                let start = ann.span().hi();
                let name = core::Name::fresh(None::<&str>);
                let ann = core::RcTerm::from_concrete(ann);
                let body = core::RcTerm::from_concrete(body);

                core::Term::Pi(start, core::TermPi::bind(Named::new(name, ann), body)).into()
            },
            concrete::Term::App(ref fn_expr, ref arg) => {
                let fn_expr = core::RcTerm::from_concrete(fn_expr);
                let arg = core::RcTerm::from_concrete(arg);

                core::Term::App(fn_expr, arg).into()
            },
        }
    }
}

#[cfg(test)]
mod from_concrete {
    use source::pos::BytePos;

    use super::*;

    fn parse(src: &str) -> core::RcTerm {
        core::RcTerm::from_concrete(&src.parse().unwrap())
    }

    mod module {
        use super::*;

        use syntax::core::Module;

        #[test]
        fn parse_prelude() {
            Module::from_concrete(&include_str!("../../../prelude.lp").parse().unwrap());
        }
    }

    mod term {
        use super::*;

        use syntax::core::{Level, Name, Term, TermLam, TermPi};

        #[test]
        fn var() {
            assert_eq!(
                parse(r"x"),
                Term::Var(Span::start(), Var::Free(Name::user("x"))).into()
            );
        }

        #[test]
        fn var_kebab_case() {
            assert_eq!(
                parse(r"or-elim"),
                Term::Var(Span::start(), Var::Free(Name::user("or-elim"))).into(),
            );
        }

        #[test]
        fn ty() {
            assert_eq!(
                parse(r"Type"),
                Term::Universe(Span::start(), Level::ZERO).into()
            );
        }

        #[test]
        fn ty_level() {
            assert_eq!(
                parse(r"Type 2"),
                Term::Universe(Span::start(), Level::ZERO.succ().succ()).into()
            );
        }

        #[test]
        fn ann() {
            assert_eq!(
                parse(r"Type : Type"),
                Term::Ann(
                    Term::Universe(Span::start(), Level::ZERO).into(),
                    Term::Universe(Span::start(), Level::ZERO).into()
                ).into(),
            );
        }

        #[test]
        fn ann_ann_left() {
            assert_eq!(
                parse(r"Type : Type : Type"),
                Term::Ann(
                    Term::Universe(Span::start(), Level::ZERO).into(),
                    Term::Ann(
                        Term::Universe(Span::start(), Level::ZERO).into(),
                        Term::Universe(Span::start(), Level::ZERO).into()
                    ).into(),
                ).into(),
            );
        }

        #[test]
        fn ann_ann_right() {
            assert_eq!(
                parse(r"Type : (Type : Type)"),
                Term::Ann(
                    Term::Universe(Span::start(), Level::ZERO).into(),
                    Term::Ann(
                        Term::Universe(Span::start(), Level::ZERO).into(),
                        Term::Universe(Span::start(), Level::ZERO).into()
                    ).into(),
                ).into(),
            );
        }

        #[test]
        fn ann_ann_ann() {
            assert_eq!(
                parse(r"(Type : Type) : (Type : Type)"),
                Term::Ann(
                    Term::Ann(
                        Term::Universe(Span::start(), Level::ZERO).into(),
                        Term::Universe(Span::start(), Level::ZERO).into()
                    ).into(),
                    Term::Ann(
                        Term::Universe(Span::start(), Level::ZERO).into(),
                        Term::Universe(Span::start(), Level::ZERO).into()
                    ).into(),
                ).into(),
            );
        }

        #[test]
        fn lam_ann() {
            let x = Name::user("x");

            assert_eq!(
                parse(r"\x : Type -> Type => x"),
                Term::Lam(
                    BytePos(0),
                    TermLam::bind(
                        Named::new(
                            x.clone(),
                            Some(
                                Term::Pi(
                                    BytePos(0),
                                    TermPi::bind(
                                        Named::new(
                                            Name::user("_"),
                                            Term::Universe(Span::start(), Level::ZERO).into()
                                        ),
                                        Term::Universe(Span::start(), Level::ZERO).into(),
                                    )
                                ).into()
                            ),
                        ),
                        Term::Var(Span::start(), Var::Free(x)).into(),
                    )
                ).into(),
            );
        }

        #[test]
        fn lam() {
            let x = Name::user("x");
            let y = Name::user("y");

            assert_eq!(
                parse(r"\x : (\y => y) => x"),
                Term::Lam(
                    BytePos(0),
                    TermLam::bind(
                        Named::new(
                            x.clone(),
                            Some(
                                Term::Lam(
                                    BytePos(0),
                                    TermLam::bind(
                                        Named::new(y.clone(), None),
                                        Term::Var(Span::start(), Var::Free(y)).into(),
                                    )
                                ).into()
                            ),
                        ),
                        Term::Var(Span::start(), Var::Free(x)).into(),
                    )
                ).into(),
            );
        }

        #[test]
        fn lam_lam_ann() {
            let x = Name::user("x");
            let y = Name::user("y");

            assert_eq!(
                parse(r"\(x y : Type) => x"),
                Term::Lam(
                    BytePos(0),
                    TermLam::bind(
                        Named::new(
                            x.clone(),
                            Some(Term::Universe(Span::start(), Level::ZERO).into())
                        ),
                        Term::Lam(
                            BytePos(0),
                            TermLam::bind(
                                Named::new(
                                    y,
                                    Some(Term::Universe(Span::start(), Level::ZERO).into())
                                ),
                                Term::Var(Span::start(), Var::Free(x)).into(),
                            )
                        ).into(),
                    )
                ).into(),
            );
        }

        #[test]
        fn arrow() {
            assert_eq!(
                parse(r"Type -> Type"),
                Term::Pi(
                    BytePos(0),
                    TermPi::bind(
                        Named::new(
                            Name::user("_"),
                            Term::Universe(Span::start(), Level::ZERO).into()
                        ),
                        Term::Universe(Span::start(), Level::ZERO).into(),
                    )
                ).into(),
            );
        }

        #[test]
        fn pi() {
            let x = Name::user("x");

            assert_eq!(
                parse(r"(x : Type -> Type) -> x"),
                Term::Pi(
                    BytePos(0),
                    TermPi::bind(
                        Named::new(
                            x.clone(),
                            Term::Pi(
                                BytePos(0),
                                TermPi::bind(
                                    Named::new(
                                        Name::user("_"),
                                        Term::Universe(Span::start(), Level::ZERO).into()
                                    ),
                                    Term::Universe(Span::start(), Level::ZERO).into(),
                                )
                            ).into(),
                        ),
                        Term::Var(Span::start(), Var::Free(x)).into(),
                    )
                ).into(),
            );
        }

        #[test]
        fn pi_pi() {
            let x = Name::user("x");
            let y = Name::user("y");

            assert_eq!(
                parse(r"(x y : Type) -> x"),
                Term::Pi(
                    BytePos(0),
                    TermPi::bind(
                        Named::new(x.clone(), Term::Universe(Span::start(), Level::ZERO).into()),
                        Term::Pi(
                            BytePos(0),
                            TermPi::bind(
                                Named::new(y, Term::Universe(Span::start(), Level::ZERO).into()),
                                Term::Var(Span::start(), Var::Free(x)).into(),
                            )
                        ).into(),
                    )
                ).into(),
            );
        }

        #[test]
        fn pi_arrow() {
            let x = Name::user("x");

            assert_eq!(
                parse(r"(x : Type) -> x -> x"),
                Term::Pi(
                    BytePos(0),
                    TermPi::bind(
                        Named::new(x.clone(), Term::Universe(Span::start(), Level::ZERO).into()),
                        Term::Pi(
                            BytePos(0),
                            TermPi::bind(
                                Named::new(
                                    Name::user("_"),
                                    Term::Var(Span::start(), Var::Free(x.clone())).into(),
                                ),
                                Term::Var(Span::start(), Var::Free(x)).into(),
                            )
                        ).into(),
                    )
                ).into(),
            );
        }

        #[test]
        fn lam_app() {
            let x = Name::user("x");
            let y = Name::user("y");

            assert_eq!(
                parse(r"\(x : Type -> Type) (y : Type) => x y"),
                Term::Lam(
                    BytePos(0),
                    TermLam::bind(
                        Named::new(
                            x.clone(),
                            Some(
                                Term::Pi(
                                    BytePos(0),
                                    TermPi::bind(
                                        Named::new(
                                            Name::user("_"),
                                            Term::Universe(Span::start(), Level::ZERO).into()
                                        ),
                                        Term::Universe(Span::start(), Level::ZERO).into(),
                                    )
                                ).into(),
                            ),
                        ),
                        Term::Lam(
                            BytePos(0),
                            TermLam::bind(
                                Named::new(
                                    y.clone(),
                                    Some(Term::Universe(Span::start(), Level::ZERO).into())
                                ),
                                Term::App(
                                    Term::Var(Span::start(), Var::Free(x)).into(),
                                    Term::Var(Span::start(), Var::Free(y)).into(),
                                ).into(),
                            )
                        ).into(),
                    )
                ).into(),
            );
        }

        #[test]
        fn id() {
            let x = Name::user("x");
            let a = Name::user("a");

            assert_eq!(
                parse(r"\(a : Type) (x : a) => x"),
                Term::Lam(
                    BytePos(0),
                    TermLam::bind(
                        Named::new(
                            a.clone(),
                            Some(Term::Universe(Span::start(), Level::ZERO).into())
                        ),
                        Term::Lam(
                            BytePos(0),
                            TermLam::bind(
                                Named::new(
                                    x.clone(),
                                    Some(Term::Var(Span::start(), Var::Free(a)).into()),
                                ),
                                Term::Var(Span::start(), Var::Free(x)).into(),
                            )
                        ).into(),
                    )
                ).into(),
            );
        }

        #[test]
        fn id_ty() {
            let a = Name::user("a");

            assert_eq!(
                parse(r"(a : Type) -> a -> a"),
                Term::Pi(
                    BytePos(0),
                    TermPi::bind(
                        Named::new(a.clone(), Term::Universe(Span::start(), Level::ZERO).into()),
                        Term::Pi(
                            BytePos(0),
                            TermPi::bind(
                                Named::new(
                                    Name::user("_"),
                                    Term::Var(Span::start(), Var::Free(a.clone())).into(),
                                ),
                                Term::Var(Span::start(), Var::Free(a)).into(),
                            )
                        ).into(),
                    )
                ).into(),
            );
        }

        mod sugar {
            use super::*;

            #[test]
            fn lam_args() {
                assert_eq!(
                    parse(r"\x (y : Type) z => x"),
                    parse(r"\x => \y : Type => \z => x"),
                );
            }

            #[test]
            fn lam_args_multi() {
                assert_eq!(
                    parse(r"\(x : Type) (y : Type) z => x"),
                    parse(r"\(x y : Type) z => x"),
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
}
