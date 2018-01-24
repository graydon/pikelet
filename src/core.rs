use std::fmt;
use std::rc::Rc;

use parse::Term as ParseTerm;
use pretty::{self, ToDoc};
use var::{Debruijn, LocallyNameless, Name, Named, Var};

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
    Lam(Named<()>, RcCTerm),
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
    Lam(Named<RcCTerm>, RcITerm),
    /// Dependent function type
    ///
    /// ```text
    /// (x : t) -> t
    /// ```
    Pi(Named<RcCTerm>, RcCTerm),
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
    Lam(Named<Option<RcValue>>, RcValue),
    /// A pi type
    Pi(Named<RcValue>, RcValue),
    /// Neutral values
    Neutral(RcNeutral),
}

impl From<RcNeutral> for Value {
    fn from(src: RcNeutral) -> Value {
        Value::Neutral(src)
    }
}

impl From<Neutral> for Value {
    fn from(src: Neutral) -> Value {
        Value::from(RcNeutral::from(src))
    }
}

impl From<Var> for Value {
    fn from(src: Var) -> Value {
        Value::from(Neutral::from(src))
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.to_doc(pretty::Context::default())
            .group()
            .render_fmt(f.width().unwrap_or(80), f)
    }
}

/// Neutral forms
///
/// https://cs.stackexchange.com/questions/69434/intuitive-explanation-of-neutral-normal-form-in-lambda-calculus
#[derive(Debug, Clone, PartialEq)]
pub enum Neutral {
    /// Variabls
    Var(Var),
    /// Application of normal forms to neutral forms
    App(RcNeutral, RcValue),
}

impl From<Var> for Neutral {
    fn from(src: Var) -> Neutral {
        Neutral::Var(src)
    }
}

impl fmt::Display for Neutral {
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
make_wrapper!(RcNeutral, Neutral);

/// Types are at the term level, so this is just an alias
pub type Type = Value;

/// Types are at the term level, so this is just an alias
pub type RcType = RcValue;

// Abstraction and instantiation

impl LocallyNameless for RcCTerm {
    fn close(&mut self, on_free: &Fn(&Name) -> Option<Debruijn>) {
        match *Rc::make_mut(&mut self.inner) {
            CTerm::Inf(ref mut i) => i.close(on_free),
            CTerm::Lam(ref mut param, ref mut body) => {
                param.close(on_free);
                body.close(&|name| on_free(name).map(Debruijn::succ));
            }
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
            ITerm::Lam(ref mut param, ref mut body) => {
                param.close(on_free);
                body.close(&|name| on_free(name).map(Debruijn::succ));
            }
            ITerm::Pi(ref mut param, ref mut body) => {
                param.close(on_free);
                body.close(&|name| on_free(name).map(Debruijn::succ));
            }
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
            Value::Lam(ref mut param, ref mut body) => {
                param.close(on_free);
                body.close(on_free);
            }
            Value::Pi(ref mut param, ref mut body) => {
                param.close(on_free);
                body.close(on_free);
            }
            Value::Neutral(ref mut stuck) => stuck.close(on_free),
        }
    }
}

impl LocallyNameless for RcNeutral {
    fn close(&mut self, on_free: &Fn(&Name) -> Option<Debruijn>) {
        match *Rc::make_mut(&mut self.inner) {
            Neutral::Var(ref mut var) => var.close(on_free),
            Neutral::App(ref mut fn_expr, ref mut arg_expr) => {
                fn_expr.close(on_free);
                arg_expr.close(on_free);
            }
        }
    }
}

impl RcValue {
    pub fn eval_app(fn_expr: RcValue, arg: RcValue) -> Result<RcValue, EvalError> {
        match *fn_expr.inner {
            Value::Lam(_, ref body) => RcValue::open0(body, &arg),
            Value::Neutral(ref stuck) => Ok(Value::from(Neutral::App(stuck.clone(), arg)).into()),
            _ => Err(EvalError::ArgAppliedToNonFunction {
                expr: fn_expr.clone(),
                arg: arg,
            }),
        }
    }

    pub fn open0(val: &RcValue, x: &RcValue) -> Result<RcValue, EvalError> {
        RcValue::open(val, Debruijn::ZERO, &x)
    }

    pub fn open(
        val: &RcValue,
        level: Debruijn,
        x: &RcValue,
    ) -> Result<RcValue, EvalError> {
        match *val.inner {
            Value::Type => Ok(val.clone()),
            Value::Lam(Named(ref name, ref param_ty), ref body) => {
                let param_ty = match param_ty.as_ref() {
                    None => None,
                    Some(ref param_ty) => Some(RcValue::open(param_ty, level, x)?),
                };
                let body = RcValue::open(body, level.succ(), x)?;

                Ok(Value::Lam(Named(name.clone(), param_ty), body).into())
            }
            Value::Pi(Named(ref name, ref param_ty), ref body) => {
                let param_ty = RcValue::open(param_ty, level, x)?;
                let body = RcValue::open(body, level.succ(), x)?;

                Ok(Value::Pi(Named(name.clone(), param_ty), body).into())
            }
            Value::Neutral(ref stuck) => RcNeutral::open(stuck, level, x),
        }
    }
}

impl RcNeutral {
    pub fn open0(val: &RcNeutral, x: &RcValue) -> Result<RcValue, EvalError> {
        RcNeutral::open(val, Debruijn::ZERO, &x)
    }

    pub fn open(
        val: &RcNeutral,
        level: Debruijn,
        x: &RcValue,
    ) -> Result<RcValue, EvalError> {
        match *val.inner {
            Neutral::Var(ref var) => match var.open(level) {
                true => Ok(x.clone()),
                false => Ok(Value::from(val.clone()).into()),
            },
            Neutral::App(ref fn_expr, ref arg_expr) => {
                let fn_expr = RcNeutral::open(fn_expr, level, x)?;
                let arg = RcValue::open(arg_expr, level, x)?;

                RcValue::eval_app(fn_expr, arg)
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
            ParseTerm::Lam(ref name, None, ref body) => {
                let name = Name::User(name.clone());
                let mut body = RcCTerm::from_parse(body)?;
                body.close0(&name);

                Ok(CTerm::Lam(Named(name, ()), body.into()).into())
            }
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
            ParseTerm::Ann(ref e, ref t) => {
                Ok(ITerm::Ann(RcCTerm::from_parse(e)?.into(), RcCTerm::from_parse(t)?.into()).into())
            }
            ParseTerm::Lam(ref name, Some(ref ann), ref body) => {
                let name = Name::User(name.clone());
                let mut body = RcITerm::from_parse(body)?;
                body.close0(&name);

                Ok(ITerm::Lam(Named(name, RcCTerm::from_parse(ann)?.into()), body).into())
            }
            // Type annotations needed!
            ParseTerm::Lam(_, None, _) => Err(FromParseError),
            ParseTerm::Pi(ref name, ref ann, ref body) => {
                let name = Name::User(name.clone());
                let mut body = RcCTerm::from_parse(body)?;
                body.close0(&name);

                Ok(ITerm::Pi(Named(name, RcCTerm::from_parse(ann)?.into()), body).into())
            }
            ParseTerm::Arrow(ref ann, ref body) => {
                let name = Name::Abstract;
                let mut body = RcCTerm::from_parse(body)?;
                body.close0(&name);

                Ok(ITerm::Pi(Named(name, RcCTerm::from_parse(ann)?.into()), body).into())
            }
            ParseTerm::App(ref f, ref arg) => {
                Ok(ITerm::App(RcITerm::from_parse(f)?, RcCTerm::from_parse(arg)?).into())
            },
        }
    }
}

// Evaluation

#[derive(Debug, Clone, PartialEq)]
pub enum EvalError {
    /// Attempted to apply an argument to a term that is not a function
    ArgAppliedToNonFunction { arg: RcValue, expr: RcValue },
}

impl RcCTerm {
    pub fn eval(&self) -> Result<RcValue, EvalError> {
        // e ⇓ v
        match *self.inner {
            CTerm::Inf(ref inf) => inf.eval(),

            //  1. e ⇓ v
            // ───────────────── (EVAL/LAM)
            //     λx.e ⇓ λx→v
            CTerm::Lam(Named(ref name, ()), ref body_expr) => {
                let body_expr = body_expr.eval()?; // 1.

                Ok(Value::Lam(Named(name.clone(), None), body_expr).into())
            }
        }
    }
}

impl RcITerm {
    pub fn eval(&self) -> Result<RcValue, EvalError> {
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
            ITerm::Type => Ok(Value::Type.into()),

            // ─────── (EVAL/Var)
            //  x ⇓ x
            ITerm::Var(ref var) => Ok(Value::from(var.clone()).into()),

            //  1.  ρ ⇓ τ
            //  2.  e ⇓ v
            // ──────────────────────── (EVAL/LAM-ANN)
            //      λx:ρ→e ⇓ λx:τ→v
            ITerm::Lam(Named(ref name, ref param_ty), ref body_expr) => {
                let param_ty = param_ty.eval()?; // 1.
                let body_expr = body_expr.eval()?; // 2.

                Ok(Value::Lam(Named(name.clone(), Some(param_ty)), body_expr).into())
            }

            //  1.  ρ₁ ⇓ τ₁
            //  2.  ρ₂ ⇓ τ₂
            // ─────────────────────────── (EVAL/PI-ANN)
            //      (x:ρ₁)→ρ₂ ⇓ (x:τ₁)→τ₂
            ITerm::Pi(Named(ref name, ref param_ty), ref body_expr) => {
                let param_ty = param_ty.eval()?; // 1.
                let body_expr = body_expr.eval()?; // 2.

                Ok(Value::Pi(Named(name.clone(), param_ty), body_expr).into())
            }

            //  1.  e₁ ⇓ λx→v₁
            //  2.  v₁[x↦e₂] ⇓ v₂
            // ───────────────────── (EVAL/APP)
            //      e₁ e₂ ⇓ v₂
            ITerm::App(ref fn_expr, ref arg) => {
                let fn_expr = fn_expr.eval()?; // 1.
                let arg = arg.eval()?; // 2.

                RcValue::eval_app(fn_expr, arg)
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

            assert_eq!(
                parse(r"x").eval().unwrap(),
                Value::from(Var::Free(x)).into(),
            );
        }

        #[test]
        fn ty() {
            let ty: RcValue = Value::Type.into();

            assert_eq!(parse(r"Type").eval().unwrap(), ty);
        }

        #[test]
        fn lam() {
            let x = Name::user("x");
            let ty: RcValue = Value::Type.into();

            assert_eq!(
                parse(r"\x : Type => x").eval().unwrap(),
                Value::Lam(
                    Named(x.clone(), Some(ty)),
                    Value::from(Var::Bound(Named(x, Debruijn(0)))).into(),
                ).into(),
            );
        }

        #[test]
        fn pi() {
            let x = Name::user("x");
            let ty: RcValue = Value::Type.into();

            assert_eq!(
                parse(r"(x : Type) -> x").eval().unwrap(),
                Value::Pi(
                    Named(x.clone(), ty),
                    Value::from(Var::Bound(Named(x, Debruijn(0)))).into(),
                ).into(),
            );
        }

        #[test]
        fn lam_app() {
            let x = Name::user("x");
            let y = Name::user("y");
            let ty: RcValue = Value::Type.into();
            let ty_arr: RcValue = Value::Pi(Named(Name::Abstract, ty.clone()), ty.clone()).into();

            assert_eq!(
                parse(r"\x : Type -> Type => \y : Type => x y")
                    .eval()
                    .unwrap(),
                Value::Lam(
                    Named(x.clone(), Some(ty_arr)),
                    Value::Lam(
                        Named(y.clone(), Some(ty)),
                        Value::from(Neutral::App(
                            Neutral::from(Var::Bound(Named(x, Debruijn(1)))).into(),
                            Value::from(Var::Bound(Named(y, Debruijn(0)))).into(),
                        )).into(),
                    ).into(),
                ).into(),
            );
        }

        #[test]
        fn pi_app() {
            let x = Name::user("x");
            let y = Name::user("y");
            let ty: RcValue = Value::Type.into();
            let ty_arr: RcValue = Value::Pi(Named(Name::Abstract, ty.clone()), ty.clone()).into();

            assert_eq!(
                parse(r"(x : Type -> Type) -> \y : Type => x y")
                    .eval()
                    .unwrap(),
                Value::Pi(
                    Named(x.clone(), ty_arr),
                    Value::Lam(
                        Named(y.clone(), Some(ty)),
                        Value::from(Neutral::App(
                            Neutral::from(Var::Bound(Named(x, Debruijn(1)))).into(),
                            Value::from(Var::Bound(Named(y, Debruijn(0)))).into(),
                        )).into(),
                    ).into(),
                ).into(),
            );
        }
    }
}
