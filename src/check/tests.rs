use super::*;

fn parse(src: &str) -> RcTerm {
    RcTerm::from_parse(&src.parse().unwrap())
}

mod normalize {
    use super::*;

    #[test]
    fn var() {
        let context = Context::new();

        let x = Name::user("x");

        let result = context.normalize(&parse(r"x")).unwrap();
        println!("{}", result);

        assert_eq!(result.value, Value::Var(Var::Free(x)).into(),);
    }

    #[test]
    fn ty() {
        let context = Context::new();

        let ty: RcValue = Value::Type.into();

        assert_eq!(context.normalize(&parse(r"Type")).unwrap().value, ty);
    }

    #[test]
    fn lam() {
        let context = Context::new();

        let x = Name::user("x");
        let ty: RcValue = Value::Type.into();

        let result = context.normalize(&parse(r"\x : Type => x")).unwrap();
        println!("{}", result);

        assert_eq!(
            result.value,
            Value::Lam(
                Named(x.clone(), Some(ty)),
                Value::Var(Var::Bound(Named(x, Debruijn(0)))).into(),
            ).into(),
        );
    }

    #[test]
    fn pi() {
        let context = Context::new();

        let x = Name::user("x");
        let ty: RcValue = Value::Type.into();

        let result = context.normalize(&parse(r"(x : Type) -> x")).unwrap();
        println!("{}", result);

        assert_eq!(
            result.value,
            Value::Pi(
                Named(x.clone(), ty),
                Value::Var(Var::Bound(Named(x, Debruijn(0)))).into(),
            ).into(),
        );
    }

    #[test]
    fn lam_app() {
        let context = Context::new();

        let x = Name::user("x");
        let y = Name::user("y");
        let ty: RcValue = Value::Type.into();
        let ty_arr: RcValue = Value::Pi(Named(Name::Abstract, ty.clone()), ty.clone()).into();

        let result = context
            .normalize(&parse(r"\x : Type -> Type => \y : Type => x y"))
            .unwrap();
        println!("{}", result);

        assert_eq!(
            result.value,
            Value::Lam(
                Named(x.clone(), Some(ty_arr)),
                Value::Lam(
                    Named(y.clone(), Some(ty)),
                    Value::App(
                        Value::Var(Var::Bound(Named(x, Debruijn(1)))).into(),
                        Value::Var(Var::Bound(Named(y, Debruijn(0)))).into(),
                    ).into(),
                ).into(),
            ).into(),
        );
    }

    #[test]
    fn pi_app() {
        let context = Context::new();

        let x = Name::user("x");
        let y = Name::user("y");
        let ty: RcValue = Value::Type.into();
        let ty_arr: RcValue = Value::Pi(Named(Name::Abstract, ty.clone()), ty.clone()).into();

        let result = context
            .normalize(&parse(r"(x : Type -> Type) -> \y : Type => x y"))
            .unwrap();
        println!("{}", result);

        assert_eq!(
            result.value,
            Value::Pi(
                Named(x.clone(), ty_arr),
                Value::Lam(
                    Named(y.clone(), Some(ty)),
                    Value::App(
                        Value::Var(Var::Bound(Named(x, Debruijn(1)))).into(),
                        Value::Var(Var::Bound(Named(y, Debruijn(0)))).into(),
                    ).into(),
                ).into(),
            ).into(),
        );
    }

    // Passing the id function to itself should yield the id function
    #[test]
    fn id_app_id() {
        let context = Context::new();

        let given_expr = r"
            (\a : Type => \x : a => x)
                ((a : Type) -> a -> a)
                (\a : Type => \x : a => x)
        ";
        let expected_expr = r"\a : Type => \x : a => x";

        let result = context.normalize(&parse(given_expr)).unwrap();
        println!("{}", result);

        assert_eq!(
            result.value,
            context.normalize(&parse(expected_expr)).unwrap().value,
        );
    }

    // Passing the id function to the 'const' combinator should yeild a
    // function that always returns the id function
    #[test]
    fn const_app_id_ty() {
        let context = Context::new();

        let given_expr = r"
            (\a : Type => \b : Type => \x : a => \y : b => x)
                ((a : Type) -> a -> a)
                Type
                (\a : Type => \x : a => x)
                Type
        ";
        let expected_expr = r"\a : Type => \x : a => x";

        let result = context.normalize(&parse(given_expr)).unwrap();
        println!("{}", result);

        assert_eq!(
            result.value,
            context.normalize(&parse(expected_expr)).unwrap().value,
        );
    }
}

mod infer {
    use super::*;

    #[test]
    fn free() {
        let context = Context::new();

        let given_expr = r"x";
        let x = Name::user("x");

        assert_eq!(
            context.infer(&parse(given_expr)),
            Err(TypeError::UnboundVariable(x)),
        );
    }

    #[test]
    fn ty() {
        let context = Context::new();

        let given_expr = r"Type";
        let expected_ty = r"Type";

        let result = context.infer(&parse(given_expr)).unwrap();
        println!("{}", result);

        assert_eq!(
            result.inferred,
            context.normalize(&parse(expected_ty)).unwrap().value,
        );
    }

    #[test]
    fn ann_ty_id() {
        let context = Context::new();

        let given_expr = r"(\a => a) : Type -> Type";
        let expected_ty = r"Type -> Type";

        let result = context.infer(&parse(given_expr)).unwrap();
        println!("{}", result);

        assert_eq!(
            result.inferred,
            context.normalize(&parse(expected_ty)).unwrap().value,
        );
    }

    #[test]
    fn ann_arrow_ty_id() {
        let context = Context::new();

        let given_expr = r"(\a => a) : (Type -> Type) -> (Type -> Type)";
        let expected_ty = r"(Type -> Type) -> (Type -> Type)";

        let result = context.infer(&parse(given_expr)).unwrap();
        println!("{}", result);

        assert_eq!(
            result.inferred,
            context.normalize(&parse(expected_ty)).unwrap().value,
        );
    }

    #[test]
    fn ann_id_as_ty() {
        let context = Context::new();

        let given_expr = r"(\a => a) : Type";

        match context.infer(&parse(given_expr)) {
            Err(TypeError::ExpectedFunction { .. }) => {},
            other => panic!("unexpected result: {:#?}", other),
        }
    }

    #[test]
    fn app() {
        let context = Context::new();

        let given_expr = r"(\a : Type => a) Type";
        let expected_ty = r"Type";

        let result = context.infer(&parse(given_expr)).unwrap();
        println!("{}", result);

        assert_eq!(
            result.inferred,
            context.normalize(&parse(expected_ty)).unwrap().value,
        );
    }

    #[test]
    fn app_ty() {
        let context = Context::new();

        let given_expr = r"Type Type";

        assert_eq!(
            context.infer(&parse(given_expr)),
            Err(TypeError::IllegalApplication),
        )
    }

    #[test]
    fn lam() {
        let context = Context::new();

        let given_expr = r"\a : Type => a";
        let expected_ty = r"(a : Type) -> Type";

        let result = context.infer(&parse(given_expr)).unwrap();
        println!("{}", result);

        assert_eq!(
            result.inferred,
            context.normalize(&parse(expected_ty)).unwrap().value,
        );
    }

    #[test]
    fn pi() {
        let context = Context::new();

        let given_expr = r"(a : Type) -> a";
        let expected_ty = r"Type";

        let result = context.infer(&parse(given_expr)).unwrap();
        println!("{}", result);

        assert_eq!(
            result.inferred,
            context.normalize(&parse(expected_ty)).unwrap().value,
        );
    }

    #[test]
    fn id() {
        let context = Context::new();

        let given_expr = r"\a : Type => \x : a => x";
        let expected_ty = r"(a : Type) -> a -> a";

        let result = context.infer(&parse(given_expr)).unwrap();
        println!("{}", result);

        assert_eq!(
            result.inferred,
            context.normalize(&parse(expected_ty)).unwrap().value,
        );
    }

    #[test]
    fn id_ann() {
        let context = Context::new();

        let given_expr = r"(\a => \x : a => x) : (A : Type) -> A -> A";
        let expected_ty = r"(a : Type) -> a -> a";

        let result = context.infer(&parse(given_expr)).unwrap();
        println!("{}", result);

        assert_eq!(
            result.inferred,
            context.normalize(&parse(expected_ty)).unwrap().value,
        );
    }

    #[test]
    fn id_app_ty_arr_ty() {
        let context = Context::new();

        let given_expr = r"(\a : Type => \x : a => x) Type (Type -> Type)";
        let expected_ty = r"Type -> Type";

        let result = context.infer(&parse(given_expr)).unwrap();
        println!("{}", result);

        assert_eq!(
            result.inferred,
            context.normalize(&parse(expected_ty)).unwrap().value,
        );
    }

    #[test]
    fn id_app_arr_pi_ty() {
        let context = Context::new();

        let given_expr = r"(\a : Type => \x : a => x) (Type -> Type) (\x : Type => Type)";
        let expected_ty = r"\x : Type => Type";

        let result = context.infer(&parse(given_expr)).unwrap();
        println!("{}", result);

        assert_eq!(
            result.inferred,
            context.normalize(&parse(expected_ty)).unwrap().value,
        );
    }

    #[test]
    fn apply() {
        let context = Context::new();

        let given_expr = r"
            \a : Type => \b : Type =>
                \f : (a -> b) => \x : a => f x
        ";
        let expected_ty = r"
            (a : Type) -> (b : Type) ->
                (a -> b) -> a -> b
        ";

        let result = context.infer(&parse(given_expr)).unwrap();
        println!("{}", result);

        assert_eq!(
            result.inferred,
            context.normalize(&parse(expected_ty)).unwrap().value,
        );
    }

    #[test]
    fn const_() {
        let context = Context::new();

        let given_expr = r"\a : Type => \b : Type => \x : a => \y : b => x";
        let expected_ty = r"(a : Type) -> (b : Type) -> a -> b -> a";

        let result = context.infer(&parse(given_expr)).unwrap();
        println!("{}", result);

        assert_eq!(
            result.inferred,
            context.normalize(&parse(expected_ty)).unwrap().value,
        );
    }

    #[test]
    fn const_flipped() {
        let context = Context::new();

        let given_expr = r"\a : Type => \b : Type => \x : a => \y : b => y";
        let expected_ty = r"(a : Type) -> (b : Type) -> a -> b -> b";

        let result = context.infer(&parse(given_expr)).unwrap();
        println!("{}", result);

        assert_eq!(
            result.inferred,
            context.normalize(&parse(expected_ty)).unwrap().value,
        );
    }

    #[test]
    fn flip() {
        let context = Context::new();

        let given_expr = r"
            \(a : Type) (b : Type) (c : Type) =>
                \(f : a -> b -> c) (x : a) (y : b) => f y x
        ";
        let expected_ty = r"
            (a : Type) -> (b : Type) -> (c : Type) -> (a -> b -> c) -> (b -> a -> c)
        ";

        let result = context.infer(&parse(given_expr)).unwrap();
        println!("{}", result);

        assert_eq!(
            result.inferred,
            context.normalize(&parse(expected_ty)).unwrap().value,
        );
    }

    #[test]
    fn compose() {
        let context = Context::new();

        let given_expr = r"
            \a : Type => \b : Type => \c : Type =>
                \f : (b -> c) => \g : (a -> b) => \x : a =>
                    f (g x)
        ";
        let expected_ty = r"
            (a : Type) -> (b : Type) -> (c : Type) ->
                (b -> c) -> (a -> b) -> (a -> c)
        ";

        let result = context.infer(&parse(given_expr)).unwrap();
        println!("{}", result);

        assert_eq!(
            result.inferred,
            context.normalize(&parse(expected_ty)).unwrap().value,
        );
    }

    mod church_encodings {
        use super::*;

        #[test]
        fn and() {
            let context = Context::new();

            let given_expr = r"\p : Type => \q : Type => (c : Type) -> (p -> q -> c) -> c";
            let expected_ty = r"Type -> Type -> Type";

            assert_eq!(
                context.infer(&parse(given_expr)).unwrap().inferred,
                context.normalize(&parse(expected_ty)).unwrap().value,
            );
        }

        #[test]
        fn and_intro() {
            let context = Context::new();

            let given_expr = r"
                \p : Type => \q : Type => \x : p => \y : q =>
                    \c : Type => \f : (p -> q -> c) => f x y
            ";
            let expected_ty = r"
                (p : Type) -> (q : Type) -> p -> q ->
                    ((c : Type) -> (p -> q -> c) -> c)
            ";

            assert_eq!(
                context.infer(&parse(given_expr)).unwrap().inferred,
                context.normalize(&parse(expected_ty)).unwrap().value,
            );
        }

        #[test]
        fn and_proj_left() {
            let context = Context::new();

            let given_expr = r"
                \p : Type => \q : Type => \pq : (c : Type) -> (p -> q -> c) -> c =>
                    pq p (\x => \y => x)
            ";
            let expected_ty = r"
                (p : Type) -> (q : Type) ->
                    ((c : Type) -> (p -> q -> c) -> c) -> p
            ";

            assert_eq!(
                context.infer(&parse(given_expr)).unwrap().inferred,
                context.normalize(&parse(expected_ty)).unwrap().value,
            );
        }

        #[test]
        fn and_proj_right() {
            let context = Context::new();

            let given_expr = r"
                \p : Type => \q : Type => \pq : (c : Type) -> (p -> q -> c) -> c =>
                    pq q (\x => \y => y)
            ";
            let expected_ty = r"
                (p : Type) -> (q : Type) ->
                    ((c : Type) -> (p -> q -> c) -> c) -> q
            ";

            assert_eq!(
                context.infer(&parse(given_expr)).unwrap().inferred,
                context.normalize(&parse(expected_ty)).unwrap().value,
            );
        }
    }
}

mod check_module {
    use super::*;

    #[test]
    fn check_prelude() {
        let module = Module::from_parse(&include_str!("../../prelude.lp").parse().unwrap());

        check_module(&module).unwrap();
    }
}
