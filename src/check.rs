//! Contexts and type checking

use std::fmt;
use std::rc::Rc;

use Derivation;
use core::{CTerm, EvalError, ITerm, Type, Value};
use var::{Debruijn, Name, Named, Var};

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum TypeError {
    Eval(EvalError),
    IllegalApplication,
    ExpectedFunction {
        lam_expr: Rc<CTerm>,
        expected: Rc<Type>,
    },
    Mismatch {
        expr: Rc<ITerm>,
        found: Rc<Type>,
        expected: Rc<Type>,
    },
    UnboundVariable(Name),
}

impl From<EvalError> for TypeError {
    fn from(src: EvalError) -> TypeError {
        TypeError::Eval(src)
    }
}

pub enum Context<'a> {
    Nil,
    Cons(&'a Context<'a>, Rc<Value>),
}

impl Default for Context<'static> {
    fn default() -> Context<'static> {
        Context::Nil
    }
}

impl<'a> fmt::Display for Context<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Context::Nil => write!(f, "∅"),
            Context::Cons(ref parent, ref term) => {
                fmt::Display::fmt(parent, f)?;
                write!(f, ", (")?;
                fmt::Display::fmt(term, f)?;
                write!(f, ")")
            }
        }
    }
}

impl<'a> Context<'a> {
    pub fn extend(&'a self, value: Rc<Value>) -> Context<'a> {
        Context::Cons(self, value)
    }

    pub fn lookup(&'a self, x: Debruijn) -> Option<&'a Rc<Value>> {
        match (self, x) {
            (&Context::Nil, _) => None,
            (&Context::Cons(_, ref value), Debruijn(0)) => Some(value),
            (&Context::Cons(parent, _), Debruijn(x)) => parent.lookup(Debruijn(x - 1)),
        }
    }

    /// Check that the type of an expression is compatible with the expected type
    pub fn check(&self, expr: &CTerm, expected_ty: &Type) -> Result<Derivation, TypeError> {
        let (rule, premises) = match *expr {
            CTerm::Inf(ref inf_expr) => {
                let (inf_ty, premise) = self.infer(inf_expr)?;

                if &*inf_ty == expected_ty {
                    ("INF", vec![premise])
                } else {
                    return Err(TypeError::Mismatch {
                        expr: inf_expr.clone(),
                        found: inf_ty,
                        expected: Rc::new(expected_ty.clone()),
                    });
                }
            }
            CTerm::Lam(_, ref body_expr) => match *expected_ty {
                Value::Pi(Named(_, ref param_ty), ref ret_ty) => {
                    let premise = self.extend(param_ty.clone()).check(body_expr, ret_ty)?;
                    ("LAM", vec![premise])
                }
                _ => {
                    return Err(TypeError::ExpectedFunction {
                        lam_expr: Rc::new(expr.clone()),
                        expected: Rc::new(expected_ty.clone()),
                    })
                }
            },
        };

        Ok(Derivation {
            judgement: "CHECK",
            rule,
            conclusion: format!(
                "{:#}  ├─  ({:#})  :↓  ({:#})",
                self, expr, expected_ty
            ),
            premises,
        })
    }

    pub fn infer(&self, expr: &ITerm) -> Result<(Rc<Type>, Derivation), TypeError> {
        let (rule, premises, out_ty) = match *expr {
            ITerm::Ann(ref expr, ref ty) => {
                // Check that the type is actually at the type level
                let ty_premise = self.check(ty, &Value::Type)?;
                // Simplify the type
                let (simp_ty, simp_ty_premise) = ty.eval()?;
                // Ensure that the type of the expression is compatible with the
                // simplified annotation
                let expr_premise = self.check(expr, &simp_ty)?;

                (
                    "ANN",
                    vec![ty_premise, expr_premise, simp_ty_premise],
                    simp_ty,
                )
            }
            ITerm::Type => ("TYPE", vec![], Rc::new(Value::Type)),
            ITerm::Lam(Named(ref param_name, ref param_ty), ref body_expr) => {
                // Check that the parameter type is at the type level
                let param_premise = self.check(param_ty, &Value::Type)?;
                // Simplify the parameter type
                let (simp_param_ty, simp_param_ty_premise) = param_ty.eval()?;
                // Infer the body of the lambda
                let (body_ty, body_premise) = self.extend(simp_param_ty.clone()).infer(body_expr)?;

                (
                    "LAM",
                    vec![param_premise, simp_param_ty_premise, body_premise],
                    Rc::new(Value::Pi(
                        Named(param_name.clone(), simp_param_ty),
                        body_ty, // shift??
                    )),
                )
            }
            ITerm::Pi(Named(_, ref param_ty), ref body_ty) => {
                // Check that the parameter type is at the type level
                let param_premise = self.check(param_ty, &Value::Type)?;
                // Simplify the parameter type
                let (simp_param_ty, simp_param_ty_premise) = param_ty.eval()?;
                // Ensure that the body of the pi type is also a type when the
                // parameter is added to the context
                let body_premise = self.extend(simp_param_ty).check(body_ty, &Value::Type)?;

                // If this is true, the type of the pi type is also a type
                (
                    "PI",
                    vec![param_premise, simp_param_ty_premise, body_premise],
                    Rc::new(Value::Type),
                )
            }
            ITerm::Var(ref var) => match *var {
                Var::Bound(Named(_, b)) => (
                    "VAR",
                    vec![
                        Derivation {
                            judgement: "CONTEXT",
                            rule: "CONS",
                            premises: vec![],
                            conclusion: format!("{:#} ∈ {:#}", var, self),
                        },
                    ],
                    self.lookup(b).expect("ICE: index out of bounds").clone(),
                ),
                Var::Free(ref name) => return Err(TypeError::UnboundVariable(name.clone())),
            },
            ITerm::App(ref fn_expr, ref arg_expr) => {
                let (fn_type, fn_premise) = self.infer(fn_expr)?;
                match *fn_type {
                    Value::Pi(Named(_, ref param_ty), ref ret_ty) => {
                        // Check that the type of the argument matches the
                        // expected type of the parameter
                        let pi_premise = self.check(arg_expr, param_ty)?;
                        // Simplify the argument
                        let (simp_arg_expr, simp_arg_expr_premise) = arg_expr.eval()?;
                        // Apply the argument to the body of the pi type
                        (
                            "APP",
                            vec![fn_premise, pi_premise, simp_arg_expr_premise],
                            Value::instantiate0(ret_ty, &simp_arg_expr)?,
                        )
                    }
                    // TODO: More error info
                    _ => {
                        return Err(TypeError::IllegalApplication);
                    }
                }
            }
        };

        let derivation = Derivation {
            judgement: "INFER",
            rule,
            conclusion: format!("{:#}  ├─  ({:#})  :↑  ({:#})", self, expr, out_ty),
            premises,
        };

        Ok((out_ty, derivation))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::SValue;

    fn parse(src: &str) -> ITerm {
        use parse::Term;

        Term::to_core(&src.parse().unwrap()).unwrap()
    }

    #[test]
    fn extend_lookup() {
        let x = Rc::new(Value::from(SValue::Var(Var::Free(Name(String::from("x"))))));
        let y = Rc::new(Value::from(SValue::Var(Var::Free(Name(String::from("y"))))));

        let context0 = Context::Nil;

        assert_eq!(context0.lookup(Debruijn(0)), None);

        let context1 = context0.extend(x.clone());

        assert_eq!(context1.lookup(Debruijn(0)), Some(&x));
        assert_eq!(context1.lookup(Debruijn(1)), None);

        let context2 = context1.extend(y.clone());

        assert_eq!(context2.lookup(Debruijn(0)), Some(&y));
        assert_eq!(context2.lookup(Debruijn(1)), Some(&x));
        assert_eq!(context2.lookup(Debruijn(2)), None);
    }

    mod infer {
        use super::*;

        #[test]
        fn free() {
            let ctx = Context::default();
            let given_expr = r"x";
            let x = Name(String::from("x"));

            assert_eq!(
                ctx.infer(&parse(given_expr)).unwrap_err(),
                TypeError::UnboundVariable(x),
            );
        }

        #[test]
        fn ty() {
            let ctx = Context::default();
            let given_expr = r"Type";
            let expected_ty = r"Type";

            let (inferred, derivation) = ctx.infer(&parse(given_expr)).unwrap();
            let (expected, _) = parse(expected_ty).eval().unwrap();

            println!("\n{}", derivation);

            assert_eq!(inferred, expected);
        }

        #[test]
        fn ann_ty_id() {
            let ctx = Context::default();
            let given_expr = r"(\a, a) : Type -> Type";
            let expected_ty = r"Type -> Type";

            let (inferred, derivation) = ctx.infer(&parse(given_expr)).unwrap();
            let (expected, _) = parse(expected_ty).eval().unwrap();

            println!("\n{}", derivation);

            assert_eq!(inferred, expected);
        }

        #[test]
        fn ann_arrow_ty_id() {
            let ctx = Context::default();
            let given_expr = r"(\a, a) : (Type -> Type) -> (Type -> Type)";
            let expected_ty = r"(Type -> Type) -> (Type -> Type)";

            let (inferred, derivation) = ctx.infer(&parse(given_expr)).unwrap();
            let (expected, _) = parse(expected_ty).eval().unwrap();

            println!("\n{}", derivation);

            assert_eq!(inferred, expected);
        }

        #[test]
        fn ann_id_as_ty() {
            let ctx = Context::default();
            let given_expr = r"(\a, a) : Type";

            match ctx.infer(&parse(given_expr)) {
                Err(TypeError::ExpectedFunction { .. }) => {}
                other => panic!("unexpected result: {:#?}", other),
            }
        }

        #[test]
        fn app() {
            let ctx = Context::default();
            let given_expr = r"(\a : Type, a) Type";
            let expected_ty = r"Type";

            let (inferred, derivation) = ctx.infer(&parse(given_expr)).unwrap();
            let (expected, _) = parse(expected_ty).eval().unwrap();

            println!("\n{}", derivation);

            assert_eq!(inferred, expected);
        }

        #[test]
        fn app_ty() {
            let ctx = Context::default();
            let given_expr = r"Type Type";

            assert_eq!(
                ctx.infer(&parse(given_expr)).unwrap_err(),
                TypeError::IllegalApplication,
            )
        }

        #[test]
        fn lam() {
            let ctx = Context::default();
            let given_expr = r"\a : Type, a";
            let expected_ty = r"[a : Type] -> Type";

            let (inferred, derivation) = ctx.infer(&parse(given_expr)).unwrap();
            let (expected, _) = parse(expected_ty).eval().unwrap();

            println!("\n{}", derivation);

            assert_eq!(inferred, expected);
        }

        #[test]
        fn pi() {
            let ctx = Context::default();
            let given_expr = r"[a : Type] -> a";
            let expected_ty = r"Type";

            let (inferred, derivation) = ctx.infer(&parse(given_expr)).unwrap();
            let (expected, _) = parse(expected_ty).eval().unwrap();

            println!("\n{}", derivation);

            assert_eq!(inferred, expected);
        }

        #[test]
        fn id() {
            let ctx = Context::default();
            let given_expr = r"\a : Type, \x : a, x";
            let expected_ty = r"[a : Type] -> a -> a";

            let (inferred, derivation) = ctx.infer(&parse(given_expr)).unwrap();
            let (expected, _) = parse(expected_ty).eval().unwrap();

            println!("\n{}", derivation);

            assert_eq!(inferred, expected);
        }

        #[test]
        fn id_ann() {
            let ctx = Context::default();
            let given_expr = r"(\a, \x : a, x) : [A : Type] -> A -> A";
            let expected_ty = r"[a : Type] -> a -> a";

            let (inferred, derivation) = ctx.infer(&parse(given_expr)).unwrap();
            let (expected, _) = parse(expected_ty).eval().unwrap();

            println!("\n{}", derivation);

            assert_eq!(inferred, expected);
        }

        #[test]
        fn id_app_ty_arr_ty() {
            let ctx = Context::default();
            let given_expr = r"(\a : Type, \x : a, x) Type (Type -> Type)";
            let expected_ty = r"Type -> Type";

            let (inferred, derivation) = ctx.infer(&parse(given_expr)).unwrap();
            let (expected, _) = parse(expected_ty).eval().unwrap();

            println!("\n{}", derivation);

            assert_eq!(inferred, expected);
        }

        #[test]
        fn id_app_arr_pi_ty() {
            let ctx = Context::default();
            let given_expr = r"(\a : Type, \x : a, x) (Type -> Type) (\x : Type, Type)";
            let expected_ty = r"\x : Type, Type";

            let (inferred, derivation) = ctx.infer(&parse(given_expr)).unwrap();
            let (expected, _) = parse(expected_ty).eval().unwrap();

            println!("\n{}", derivation);

            assert_eq!(inferred, expected);
        }

        #[test]
        fn apply() {
            let ctx = Context::default();
            let given_expr = r"
                \a : Type, \b : Type,
                    \f : (a -> b), \x : a, f x
            ";
            let expected_ty = r"
                [a : Type] -> [b : Type] ->
                    (a -> b) -> a -> b
            ";

            let (inferred, derivation) = ctx.infer(&parse(given_expr)).unwrap();
            let (expected, _) = parse(expected_ty).eval().unwrap();

            println!("\n{}", derivation);

            assert_eq!(inferred, expected);
        }

        #[test]
        fn constant() {
            let ctx = Context::default();
            let given_expr = r"
                \a : Type, \b : Type,
                    \f : (a -> b), \x : a, \y : b, x
            ";
            let expected_ty = r"
                [a : Type] -> [b : Type] ->
                    (a -> b) -> a -> b -> a
            ";

            let (inferred, derivation) = ctx.infer(&parse(given_expr)).unwrap();
            let (expected, _) = parse(expected_ty).eval().unwrap();

            println!("\n{}", derivation);

            assert_eq!(inferred, expected);
        }

        #[test]
        fn compose() {
            let ctx = Context::default();
            let given_expr = r"
                \a : Type, \b : Type, \c : Type,
                    \f : (b -> c), \g : (a -> b), \x : a,
                        f (g x)
            ";
            let expected_ty = r"
                [a : Type] -> [b : Type] -> [c : Type] ->
                    (b -> c) -> (a -> b) -> (a -> c)
            ";

            let (inferred, derivation) = ctx.infer(&parse(given_expr)).unwrap();
            let (expected, _) = parse(expected_ty).eval().unwrap();

            println!("\n{}", derivation);

            assert_eq!(inferred, expected);
        }
    }
}
