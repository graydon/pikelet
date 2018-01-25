use std::fmt;
use std::rc::Rc;

use parse::Term as ParseTerm;
use pretty::{self, ToDoc};
use var::{Debruijn, LocallyNameless, Name, Named, Scope, Var};

/// Checkable terms
///
/// These terms do not contain full type information within them, so in order to
/// check them we need to supply a type to the checking algorithm
#[derive(Debug, Clone, PartialEq)]
pub enum CTerm {
    /// Inferrable terms
    Inf(RcITerm),
    /// Lambdas without an explicit type annotation
    ///
    /// ```text
    /// \x => t
    /// ```
    Lam(Scope<Named<()>, RcCTerm>),
}

impl From<ITerm> for CTerm {
    fn from(src: ITerm) -> CTerm {
        CTerm::Inf(src.into())
    }
}

impl From<Var> for CTerm {
    fn from(src: Var) -> CTerm {
        CTerm::from(ITerm::from(src))
    }
}

impl fmt::Display for CTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.to_doc(pretty::Context::default())
            .group()
            .render_fmt(f.width().unwrap_or(80), f)
    }
}

/// Inferrable terms
///
/// These terms can be fully inferred without needing to resort to type
/// inference
#[derive(Debug, Clone, PartialEq)]
pub enum ITerm {
    /// A term annotated with a type
    ///
    /// ```text
    /// e : t
    /// ```
    Ann(RcCTerm, RcCTerm),
    /// Type of types
    Type,
    /// A variable
    Var(Var),
    /// Fully annotated lambda abstractions
    ///
    /// Note that the body of the lambda must have a type that can be inferred
    /// from context
    ///
    /// ```text
    /// \x : t => t
    /// ```
    Lam(Scope<Named<RcCTerm>, RcITerm>),
    /// Dependent function type
    ///
    /// ```text
    /// (x : t) -> t
    /// ```
    Pi(Scope<Named<RcCTerm>, RcCTerm>),
    /// Term application
    ///
    /// ```text
    /// f x
    /// ```
    App(RcITerm, RcCTerm),
}

impl From<Var> for ITerm {
    fn from(src: Var) -> ITerm {
        ITerm::Var(src)
    }
}

impl fmt::Display for ITerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.to_doc(pretty::Context::default())
            .group()
            .render_fmt(f.width().unwrap_or(80), f)
    }
}

/// Normal forms
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    /// The type of types
    Type,
    /// A partially evaluated lambda
    Lam(Scope<Named<Option<RcValue>>, RcValue>),
    /// A pi type
    Pi(Scope<Named<RcValue>, RcValue>),
    /// Variables
    Var(Var),
    /// Application of normal forms to neutral forms
    App(RcValue, RcValue),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.to_doc(pretty::Context::default())
            .group()
            .render_fmt(f.width().unwrap_or(80), f)
    }
}

// Wrapper types

macro_rules! make_wrapper {
    ($name:ident, $inner:ty) => {
        #[derive(Clone, PartialEq)]
        pub struct $name {
            pub inner: Rc<$inner>,
        }

        impl From<$inner> for $name {
            fn from(src: $inner) -> $name {
                $name {
                    inner: Rc::new(src),
                }
            }
        }

        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                fmt::Debug::fmt(&self.inner, f)
            }
        }
    };
}

make_wrapper!(RcCTerm, CTerm);
make_wrapper!(RcITerm, ITerm);
make_wrapper!(RcValue, Value);

/// Types are at the term level, so this is just an alias
pub type Type = Value;

/// Types are at the term level, so this is just an alias
pub type RcType = RcValue;

// Abstraction and instantiation

impl LocallyNameless for RcCTerm {
    fn close(&mut self, on_free: &Fn(&Name) -> Option<Debruijn>) {
        match *Rc::make_mut(&mut self.inner) {
            CTerm::Inf(ref mut i) => i.close(on_free),
            CTerm::Lam(ref mut scope) => scope.close(on_free),
        }
    }
}

impl LocallyNameless for RcITerm {
    fn close(&mut self, on_free: &Fn(&Name) -> Option<Debruijn>) {
        match *Rc::make_mut(&mut self.inner) {
            ITerm::Ann(ref mut expr, ref mut ty) => {
                expr.close(on_free);
                ty.close(on_free);
            }
            ITerm::Lam(ref mut scope) => scope.close(on_free),
            ITerm::Pi(ref mut scope) => scope.close(on_free),
            ITerm::Var(ref mut var) => var.close(on_free),
            ITerm::Type => {}
            ITerm::App(ref mut f, ref mut x) => {
                f.close(on_free);
                x.close(on_free);
            }
        }
    }
}

impl LocallyNameless for RcValue {
    fn close(&mut self, on_free: &Fn(&Name) -> Option<Debruijn>) {
        match *Rc::make_mut(&mut self.inner) {
            Value::Type => {}
            Value::Lam(ref mut scope) => scope.close(on_free),
            Value::Pi(ref mut scope) => scope.close(on_free),
            Value::Var(ref mut var) => var.close(on_free),
            Value::App(ref mut fn_expr, ref mut arg_expr) => {
                fn_expr.close(on_free);
                arg_expr.close(on_free);
            }
        }
    }
}

impl RcValue {
    pub fn open0(val: &RcValue, x: &RcValue) -> RcValue {
        RcValue::open(val, Debruijn::ZERO, &x)
    }

    pub fn open(val: &RcValue, level: Debruijn, x: &RcValue) -> RcValue {
        match *val.inner {
            Value::Type => val.clone(),
            Value::Lam(ref scope) => {
                let param_ty = match scope.unsafe_param.1.as_ref() {
                    None => None,
                    Some(ref param_ty) => Some(RcValue::open(param_ty, level, x)),
                };
                let body = RcValue::open(&scope.unsafe_body, level.succ(), x);

                Value::Lam(Scope {
                    unsafe_param: Named(scope.unsafe_param.0.clone(), param_ty),
                    unsafe_body: body,
                }).into()
            }
            Value::Pi(ref scope) => {
                let param_ty = RcValue::open(&scope.unsafe_param.1, level, x);
                let body = RcValue::open(&scope.unsafe_body, level.succ(), x);

                Value::Pi(Scope {
                    unsafe_param: Named(scope.unsafe_param.0.clone(), param_ty),
                    unsafe_body: body,
                }).into()
            }
            Value::Var(ref var) => match var.open(level) {
                true => x.clone(),
                false => val.clone(),
            },
            Value::App(ref fn_expr, ref arg_expr) => {
                let fn_expr = RcValue::open(fn_expr, level, x);
                let arg = RcValue::open(arg_expr, level, x);

                Value::App(fn_expr.clone(), arg).into() // FIXME: eval?
            }
        }
    }
}

// Conversions from the parse tree

// FIXME: use a proper error type
#[derive(Debug, Clone, PartialEq)]
pub struct FromParseError;

impl RcCTerm {
    /// Convert a parsed term into a checkable term
    fn from_parse(term: &ParseTerm) -> Result<RcCTerm, FromParseError> {
        match *term {
            ParseTerm::Lam(ref name, None, ref body) => Ok(
                CTerm::Lam(Scope::bind(
                    Named(Name::User(name.clone()), ()),
                    RcCTerm::from_parse(body)?,
                )).into(),
            ),
            _ => Ok(CTerm::Inf(RcITerm::from_parse(term)?).into()),
        }
    }
}

impl RcITerm {
    /// Convert a parsed term into an inferrable term
    pub fn from_parse(term: &ParseTerm) -> Result<RcITerm, FromParseError> {
        match *term {
            ParseTerm::Var(ref x) => Ok(ITerm::Var(Var::Free(Name::User(x.clone()))).into()),
            ParseTerm::Type => Ok(ITerm::Type.into()),
            ParseTerm::Ann(ref e, ref t) => Ok(
                ITerm::Ann(
                    RcCTerm::from_parse(e)?.into(),
                    RcCTerm::from_parse(t)?.into(),
                ).into(),
            ),
            ParseTerm::Lam(ref name, Some(ref ann), ref body) => Ok(
                ITerm::Lam(Scope::bind(
                    Named(Name::User(name.clone()), RcCTerm::from_parse(ann)?.into()),
                    RcITerm::from_parse(body)?,
                )).into(),
            ),
            // Type annotations needed!
            ParseTerm::Lam(_, None, _) => Err(FromParseError),
            ParseTerm::Pi(ref name, ref ann, ref body) => Ok(
                ITerm::Pi(Scope::bind(
                    Named(Name::User(name.clone()), RcCTerm::from_parse(ann)?.into()),
                    RcCTerm::from_parse(body)?,
                )).into(),
            ),
            ParseTerm::Arrow(ref ann, ref body) => Ok(
                ITerm::Pi(Scope::bind(
                    Named(Name::Abstract, RcCTerm::from_parse(ann)?.into()),
                    RcCTerm::from_parse(body)?,
                )).into(),
            ),
            ParseTerm::App(ref f, ref arg) => {
                Ok(ITerm::App(RcITerm::from_parse(f)?, RcCTerm::from_parse(arg)?).into())
            }
        }
    }
}

// Evaluation

impl RcCTerm {
    pub fn eval(&self) -> RcValue {
        // e ⇓ v
        match *self.inner {
            CTerm::Inf(ref inf) => inf.eval(),

            //  1. e ⇓ v
            // ───────────────── (EVAL/LAM)
            //     λx.e ⇓ λx→v
            CTerm::Lam(ref scope) => {
                let body_expr = scope.unsafe_body.eval(); // 1.

                Value::Lam(Scope {
                    unsafe_param: Named(scope.unsafe_param.0.clone(), None),
                    unsafe_body: body_expr,
                }).into()
            }
        }
    }
}

impl RcITerm {
    pub fn eval(&self) -> RcValue {
        // e ⇓ v
        match *self.inner {
            //  1.  e ⇓ v
            // ────────────────── (EVAL/ANN)
            //      e : ρ ⇓ v
            ITerm::Ann(ref expr, _) => {
                expr.eval() // 1.
            }

            // ───────────── (EVAL/TYPE)
            //  Type ⇓ Type
            ITerm::Type => Value::Type.into(),

            // ─────── (EVAL/Var)
            //  x ⇓ x
            ITerm::Var(ref var) => Value::Var(var.clone()).into(),

            //  1.  ρ ⇓ τ
            //  2.  e ⇓ v
            // ──────────────────────── (EVAL/LAM-ANN)
            //      λx:ρ→e ⇓ λx:τ→v
            ITerm::Lam(ref scope) => {
                let param_ty = scope.unsafe_param.1.eval(); // 1.
                let body_expr = scope.unsafe_body.eval(); // 2.

                Value::Lam(Scope {
                    unsafe_param: Named(scope.unsafe_param.0.clone(), Some(param_ty)),
                    unsafe_body: body_expr,
                }).into()
            }

            //  1.  ρ₁ ⇓ τ₁
            //  2.  ρ₂ ⇓ τ₂
            // ─────────────────────────── (EVAL/PI-ANN)
            //      (x:ρ₁)→ρ₂ ⇓ (x:τ₁)→τ₂
            ITerm::Pi(ref scope) => {
                let param_ty = scope.unsafe_param.1.eval(); // 1.
                let body_ty = scope.unsafe_body.eval(); // 2.

                Value::Pi(Scope {
                    unsafe_param: Named(scope.unsafe_param.0.clone(), param_ty),
                    unsafe_body: body_ty,
                }).into()
            }

            //  1.  e₁ ⇓ λx→v₁
            //  2.  v₁[x↦e₂] ⇓ v₂
            // ───────────────────── (EVAL/APP)
            //      e₁ e₂ ⇓ v₂
            ITerm::App(ref fn_expr, ref arg) => {
                let fn_expr = fn_expr.eval(); // 1.
                let arg = arg.eval(); // 2.

                match *fn_expr.inner {
                    Value::Lam(ref scope) => RcValue::open0(&scope.unsafe_body, &arg),
                    _ => Value::App(fn_expr.clone(), arg).into(),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(src: &str) -> RcITerm {
        RcITerm::from_parse(&src.parse().unwrap()).unwrap()
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

    mod eval {
        use super::*;

        #[test]
        fn var() {
            let x = Name::user("x");

            assert_eq!(parse(r"x").eval(), Value::Var(Var::Free(x)).into(),);
        }

        #[test]
        fn ty() {
            let ty: RcValue = Value::Type.into();

            assert_eq!(parse(r"Type").eval(), ty);
        }

        #[test]
        fn lam() {
            let x = Name::user("x");
            let ty: RcValue = Value::Type.into();

            assert_eq!(
                parse(r"\x : Type => x").eval(),
                Value::Lam(Scope::bind(
                    Named(x.clone(), Some(ty)),
                    Value::Var(Var::Free(x)).into(),
                )).into(),
            );
        }

        #[test]
        fn pi() {
            let x = Name::user("x");
            let ty: RcValue = Value::Type.into();

            assert_eq!(
                parse(r"(x : Type) -> x").eval(),
                Value::Pi(Scope::bind(
                    Named(x.clone(), ty),
                    Value::Var(Var::Free(x)).into(),
                )).into(),
            );
        }

        #[test]
        fn lam_app() {
            let x = Name::user("x");
            let y = Name::user("y");
            let ty: RcValue = Value::Type.into();
            let ty_arr: RcValue =
                Value::Pi(Scope::bind(Named(Name::Abstract, ty.clone()), ty.clone())).into();

            assert_eq!(
                parse(r"\x : Type -> Type => \y : Type => x y").eval(),
                Value::Lam(Scope::bind(
                    Named(x.clone(), Some(ty_arr)),
                    Value::Lam(Scope::bind(
                        Named(y.clone(), Some(ty)),
                        Value::App(
                            Value::Var(Var::Free(x)).into(),
                            Value::Var(Var::Free(y)).into(),
                        ).into(),
                    )).into(),
                )).into(),
            );
        }

        #[test]
        fn pi_app() {
            let x = Name::user("x");
            let y = Name::user("y");
            let ty: RcValue = Value::Type.into();
            let ty_arr: RcValue =
                Value::Pi(Scope::bind(Named(Name::Abstract, ty.clone()), ty.clone())).into();

            assert_eq!(
                parse(r"(x : Type -> Type) -> \y : Type => x y").eval(),
                Value::Pi(Scope::bind(
                    Named(x.clone(), ty_arr),
                    Value::Lam(Scope::bind(
                        Named(y.clone(), Some(ty)),
                        Value::App(
                            Value::Var(Var::Free(x)).into(),
                            Value::Var(Var::Free(y)).into(),
                        ).into(),
                    )).into(),
                )).into(),
            );
        }
    }
}
