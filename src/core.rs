use std::rc::Rc;
use std::fmt;

use Derivation;
use var::{Debruijn, Name, Named, Var};

/// Checkable terms
///
/// These terms do not contain full type information within them, so in order to
/// check them we need to supply a type to the checking algorithm
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum CTerm {
    /// Inferrable terms
    Inf(Rc<ITerm>),
    /// Lambdas without an explicit type annotation
    ///
    /// ```text
    /// \x, t
    /// ```
    Lam(Named<()>, Rc<CTerm>),
}

impl From<ITerm> for CTerm {
    fn from(src: ITerm) -> CTerm {
        CTerm::Inf(Rc::new(src))
    }
}

impl From<Var> for CTerm {
    fn from(src: Var) -> CTerm {
        CTerm::from(ITerm::from(src))
    }
}

impl fmt::Display for CTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            CTerm::Inf(ref iterm) => fmt::Display::fmt(iterm, f),
            CTerm::Lam(Named(ref name, ()), ref body) => {
                write!(f, "\\{} => ", name)?;
                fmt::Display::fmt(body, f)
            }
        }
    }
}

/// Inferrable terms
///
/// These terms can be fully inferred without needing to resort to type
/// inference
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum ITerm {
    /// A term annotated with a type
    ///
    /// ```text
    /// e : t
    /// ```
    Ann(Rc<CTerm>, Rc<CTerm>),
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
    /// \x : t, t
    /// ```
    Lam(Named<Rc<CTerm>>, Rc<ITerm>),
    /// Fully annotated pi types
    ///
    /// ```text
    /// [x : t] -> t
    /// ```
    Pi(Named<Rc<CTerm>>, Rc<CTerm>),
    /// Term application
    ///
    /// ```text
    /// f x
    /// ```
    App(Rc<ITerm>, Rc<CTerm>),
}

impl From<Var> for ITerm {
    fn from(src: Var) -> ITerm {
        ITerm::Var(src)
    }
}

impl fmt::Display for ITerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ITerm::Ann(ref expr, ref ty) => {
                fmt::Display::fmt(expr, f)?;
                write!(f, " : ")?;
                fmt::Display::fmt(ty, f)
            }
            ITerm::Type => write!(f, "Type"),
            ITerm::Var(ref var) => fmt::Display::fmt(var, f),
            ITerm::Lam(Named(ref name, ref ann), ref body) => {
                write!(f, "\\{} : ", name)?;
                fmt::Display::fmt(ann, f)?;
                write!(f, " => ")?;
                fmt::Display::fmt(body, f)
            }
            ITerm::Pi(Named(ref name, ref ann), ref body) => {
                write!(f, "[{} : ", name)?;
                fmt::Display::fmt(ann, f)?;
                write!(f, "] -> ")?;
                fmt::Display::fmt(body, f)
            }
            ITerm::App(ref fn_term, ref arg_term) => {
                fmt::Display::fmt(fn_term, f)?;
                write!(f, " ")?;
                fmt::Display::fmt(arg_term, f)
            }
        }
    }
}

/// Fully evaluated or stuck values
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Value {
    /// The type of types
    Type,
    /// A partially evaluated lambda
    Lam(Named<Option<Rc<Value>>>, Rc<Value>),
    /// A pi type
    Pi(Named<Rc<Value>>, Rc<Value>),
    /// Stuck values
    Stuck(Rc<SValue>),
}

impl From<Rc<SValue>> for Value {
    fn from(src: Rc<SValue>) -> Value {
        Value::Stuck(src)
    }
}

impl From<SValue> for Value {
    fn from(src: SValue) -> Value {
        Value::from(Rc::new(src))
    }
}

impl From<Var> for Value {
    fn from(src: Var) -> Value {
        Value::from(SValue::from(src))
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Value::Type => write!(f, "Type"),
            Value::Lam(Named(ref name, ref ann), ref body) => {
                write!(f, "\\{}", name)?;
                if let Some(ann) = ann.as_ref() {
                    write!(f, " : ")?;
                    fmt::Display::fmt(ann, f)?;
                }
                write!(f, " => ")?;
                fmt::Display::fmt(body, f)
            }
            Value::Pi(Named(ref name, ref ann), ref body) => {
                write!(f, "[{} : ", name)?;
                fmt::Display::fmt(ann, f)?;
                write!(f, "] -> ")?;
                fmt::Display::fmt(body, f)
            }
            Value::Stuck(ref svalue) => fmt::Display::fmt(svalue, f),
        }
    }
}

/// 'Stuck' values that cannot be reduced further
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum SValue {
    /// Attempted to evaluate a variable
    Var(Var),
    /// Tried to apply a value to a stuck term
    App(Rc<SValue>, Rc<Value>),
}

impl From<Var> for SValue {
    fn from(src: Var) -> SValue {
        SValue::Var(src)
    }
}

impl fmt::Display for SValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            SValue::Var(ref var) => fmt::Display::fmt(var, f),
            SValue::App(ref fn_term, ref arg_term) => {
                fmt::Display::fmt(fn_term, f)?;
                write!(f, " ")?;
                fmt::Display::fmt(arg_term, f)
            }
        }
    }
}

/// Types are at the term level, so this is just an alias
pub type Type = Value;

// Abstraction and instantiation

impl CTerm {
    pub fn abstract0(&mut self, name: &Name) {
        self.abstract_at(Debruijn::zero(), name);
    }

    pub fn abstract_at(&mut self, level: Debruijn, name: &Name) {
        match *self {
            CTerm::Inf(ref mut i) => Rc::make_mut(i).abstract_at(level, name),
            CTerm::Lam(_, ref mut body) => Rc::make_mut(body).abstract_at(level.succ(), name),
        }
    }
}

impl ITerm {
    pub fn abstract0(&mut self, name: &Name) {
        self.abstract_at(Debruijn::zero(), name);
    }

    pub fn abstract_at(&mut self, level: Debruijn, name: &Name) {
        match *self {
            ITerm::Ann(ref mut expr, ref mut ty) => {
                Rc::make_mut(expr).abstract_at(level, name);
                Rc::make_mut(ty).abstract_at(level, name);
            }
            ITerm::Lam(Named(_, ref mut ty), ref mut body) => {
                Rc::make_mut(ty).abstract_at(level, name);
                Rc::make_mut(body).abstract_at(level.succ(), name);
            }
            ITerm::Pi(Named(_, ref mut ty), ref mut body) => {
                Rc::make_mut(ty).abstract_at(level, name);
                Rc::make_mut(body).abstract_at(level.succ(), name);
            }
            ITerm::Var(ref mut var) => var.abstract_at(level, name),
            ITerm::Type => {}
            ITerm::App(ref mut f, ref mut x) => {
                Rc::make_mut(f).abstract_at(level, name);
                Rc::make_mut(x).abstract_at(level, name);
            }
        }
    }
}

impl Value {
    pub fn app(fn_expr: Rc<Value>, arg: Rc<Value>) -> Result<Rc<Value>, EvalError> {
        match *fn_expr {
            Value::Lam(_, ref body) => Value::instantiate0(body, &arg),
            Value::Stuck(ref stuck) => Ok(Rc::new(Value::from(SValue::App(stuck.clone(), arg)))),
            _ => Err(EvalError::ArgAppliedToNonFunction {
                expr: fn_expr.clone(),
                arg: arg,
            }),
        }
    }

    pub fn instantiate0(val: &Rc<Value>, x: &Rc<Value>) -> Result<Rc<Value>, EvalError> {
        Value::instantiate_at(val, Debruijn::zero(), &x)
    }

    pub fn instantiate_at(
        val: &Rc<Value>,
        level: Debruijn,
        x: &Rc<Value>,
    ) -> Result<Rc<Value>, EvalError> {
        match **val {
            Value::Type => Ok(val.clone()),
            Value::Lam(Named(ref name, ref param_ty), ref body) => {
                let param_ty = match param_ty.as_ref() {
                    None => None,
                    Some(ref param_ty) => Some(Value::instantiate_at(param_ty, level, x)?),
                };
                let body = Value::instantiate_at(body, level.succ(), x)?;

                Ok(Rc::new(Value::Lam(Named(name.clone(), param_ty), body)))
            }
            Value::Pi(Named(ref name, ref param_ty), ref body) => {
                let param_ty = Value::instantiate_at(param_ty, level, x)?;
                let body = Value::instantiate_at(body, level.succ(), x)?;

                Ok(Rc::new(Value::Pi(Named(name.clone(), param_ty), body)))
            }
            Value::Stuck(ref stuck) => SValue::instantiate_at(stuck, level, x),
        }
    }
}

impl SValue {
    pub fn instantiate0(val: &Rc<SValue>, x: &Rc<Value>) -> Result<Rc<Value>, EvalError> {
        SValue::instantiate_at(val, Debruijn::zero(), &x)
    }

    pub fn instantiate_at(
        val: &Rc<SValue>,
        level: Debruijn,
        x: &Rc<Value>,
    ) -> Result<Rc<Value>, EvalError> {
        match **val {
            SValue::Var(ref var) => match var.instantiate_at(level) {
                true => Ok(x.clone()),
                false => Ok(Rc::new(Value::from(val.clone()))),
            },
            SValue::App(ref fn_expr, ref arg_expr) => {
                let fn_expr = SValue::instantiate_at(fn_expr, level, x)?;
                let arg = Value::instantiate_at(arg_expr, level, x)?;

                Value::app(fn_expr, arg)
            }
        }
    }
}

// Evaluation

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum EvalError {
    /// Attempted to apply an argument to a term that is not a function
    ArgAppliedToNonFunction { arg: Rc<Value>, expr: Rc<Value> },
}

impl CTerm {
    pub fn eval(&self) -> Result<(Rc<Value>, Derivation), EvalError> {
        let (rule, premises, result) = match *self {
            CTerm::Inf(ref inf) => {
                let (result, premise) = inf.eval()?;
                ("INF", vec![premise], result)
            }
            CTerm::Lam(Named(ref name, ()), ref body_expr) => {
                // Evalute the body before building the lambda
                let name = name.clone();
                let (body_expr, body_premise) = body_expr.eval()?;
                let result = Rc::new(Value::Lam(Named(name, None), body_expr));

                ("INF", vec![body_premise], result)
            }
        };

        let derivation = Derivation {
            judgement: "EVAL-CTERM",
            rule,
            conclusion: format!("{:#}  ⇓  {:#}", self, result),
            premises,
        };

        Ok((result, derivation))
    }
}

impl ITerm {
    pub fn eval(&self) -> Result<(Rc<Value>, Derivation), EvalError> {
        let (rule, premises, result) = match *self {
            ITerm::Ann(ref expr, _) => {
                let (result, premise) = expr.eval()?;
                ("ANN", vec![premise], result)
            }

            ITerm::Type => ("TYPE", vec![], Rc::new(Value::Type)),
            ITerm::Var(ref var) => ("VAR", vec![], Rc::new(Value::from(var.clone()))),

            ITerm::Lam(Named(ref name, ref param_ty), ref body_expr) => {
                let name = name.clone();
                let (param_ty, param_ty_premise) = param_ty.eval()?;
                let (body_expr, body_expr_premise) = body_expr.eval()?;

                let result = Rc::new(Value::Lam(Named(name, Some(param_ty)), body_expr));

                ("LAM", vec![param_ty_premise, body_expr_premise], result)
            }

            ITerm::Pi(Named(ref name, ref param_ty), ref body_expr) => {
                let name = name.clone();
                let (param_ty, param_ty_premise) = param_ty.eval()?;
                let (body_expr, body_expr_premise) = body_expr.eval()?;

                let result = Rc::new(Value::Pi(Named(name, param_ty), body_expr));

                ("PI", vec![param_ty_premise, body_expr_premise], result)
            }

            ITerm::App(ref fn_expr, ref arg) => {
                let (fn_expr, fn_expr_premise) = fn_expr.eval()?;
                let (arg, arg_premise) = arg.eval()?;

                let result = Value::app(fn_expr, arg)?;

                ("APP", vec![fn_expr_premise, arg_premise], result)
            }
        };

        let derivation = Derivation {
            judgement: "EVAL-ITERM",
            rule,
            conclusion: format!("{:#}  ⇓  {:#}", self, result),
            premises,
        };

        Ok((result, derivation))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(src: &str) -> ITerm {
        use parse::Term;

        Term::to_core(&src.parse().unwrap()).unwrap()
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
            assert_eq!(parse(r"\x : Type, x"), parse(r"\a : Type, a"));
        }

        #[test]
        fn pi() {
            assert_eq!(parse(r"[x : Type] -> x"), parse(r"[a : Type] -> a"));
        }

        #[test]
        fn lam_app() {
            assert_eq!(
                parse(r"\x : (Type -> Type), x Type"),
                parse(r"\a : (Type -> Type), a Type")
            );
        }

        #[test]
        fn pi_app() {
            assert_eq!(
                parse(r"[x : (Type -> Type)] -> x Type"),
                parse(r"[a : (Type -> Type)] -> a Type")
            );
        }

        #[test]
        fn lam_lam_app() {
            assert_eq!(
                parse(r"\x : (Type -> Type), \y : Type, x y"),
                parse(r"\a : (Type -> Type), \b : Type, a b"),
            );
        }

        #[test]
        fn pi_pi_app() {
            assert_eq!(
                parse(r"[x : (Type -> Type)] -> [y : Type] -> x y"),
                parse(r"[a : (Type -> Type)] -> [b : Type] -> a b"),
            );
        }
    }

    mod eval {
        use super::*;

        #[test]
        fn var() {
            let x = Name(String::from("x"));

            let (evaluated, derivation) = parse(r"x").eval().unwrap();

            println!("\n{}", derivation);

            assert_eq!(evaluated, Rc::new(Value::from(Var::Free(x))),);
        }

        #[test]
        fn ty() {
            let ty = Rc::new(Value::Type);

            let (evaluated, derivation) = parse(r"Type").eval().unwrap();

            println!("\n{}", derivation);

            assert_eq!(evaluated, ty);
        }

        #[test]
        fn lam() {
            let x = Name(String::from("x"));
            let ty = Rc::new(Value::Type);

            let (evaluated, derivation) = parse(r"\x : Type, x").eval().unwrap();

            println!("\n{}", derivation);

            assert_eq!(
                evaluated,
                Rc::new(Value::Lam(
                    Named(x.clone(), Some(ty)),
                    Rc::new(Value::from(Var::Bound(Named(x, Debruijn(0))))),
                )),
            );
        }

        #[test]
        fn pi() {
            let x = Name(String::from("x"));
            let ty = Rc::new(Value::Type);

            let (evaluated, derivation) = parse(r"[x : Type] -> x").eval().unwrap();

            println!("\n{}", derivation);

            assert_eq!(
                evaluated,
                Rc::new(Value::Pi(
                    Named(x.clone(), ty),
                    Rc::new(Value::from(Var::Bound(Named(x, Debruijn(0))))),
                )),
            );
        }

        #[test]
        fn lam_app() {
            let x = Name(String::from("x"));
            let y = Name(String::from("y"));
            let u = Name(String::from("_"));
            let ty = Rc::new(Value::Type);
            let ty_arr = Rc::new(Value::Pi(Named(u, ty.clone()), ty.clone()));

            let (evaluated, derivation) = parse(r"\x : (Type -> Type), \y : Type, x y")
                .eval()
                .unwrap();

            println!("\n{}", derivation);

            assert_eq!(
                evaluated,
                Rc::new(Value::Lam(
                    Named(x.clone(), Some(ty_arr)),
                    Rc::new(Value::Lam(
                        Named(y.clone(), Some(ty)),
                        Rc::new(Value::from(SValue::App(
                            Rc::new(SValue::from(Var::Bound(Named(x, Debruijn(1))))),
                            Rc::new(Value::from(Var::Bound(Named(y, Debruijn(0))))),
                        ))),
                    )),
                )),
            );
        }

        #[test]
        fn pi_app() {
            let x = Name(String::from("x"));
            let y = Name(String::from("y"));
            let u = Name(String::from("_"));
            let ty = Rc::new(Value::Type);
            let ty_arr = Rc::new(Value::Pi(Named(u, ty.clone()), ty.clone()));

            let (evaluated, derivation) = parse(r"[x : (Type -> Type)] -> \y : Type, x y")
                .eval()
                .unwrap();

            println!("\n{}", derivation);

            assert_eq!(
                evaluated,
                Rc::new(Value::Pi(
                    Named(x.clone(), ty_arr),
                    Rc::new(Value::Lam(
                        Named(y.clone(), Some(ty)),
                        Rc::new(Value::from(SValue::App(
                            Rc::new(SValue::from(Var::Bound(Named(x, Debruijn(1))))),
                            Rc::new(Value::from(Var::Bound(Named(y, Debruijn(0))))),
                        ))),
                    )),
                )),
            );
        }
    }
}
