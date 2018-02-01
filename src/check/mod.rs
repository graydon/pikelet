//! Contexts and type checking

use rpds::List;
use std::fmt;

use core::{Module, RcTerm, RcType, RcValue, Term, Value};
use pretty::{self, ToDoc};
use var::{Debruijn, Name, Named, Var};

#[cfg(test)]
mod tests;

/// A typechecked and elaborated module
pub struct CheckedModule {
    pub name: String,
    pub definitions: Vec<CheckedDefinition>,
}

/// A typechecked and elaborated definition
pub struct CheckedDefinition {
    pub name: String,
    pub term: RcValue,
    pub ann: RcType,
}

/// Typecheck and elaborate a module
pub fn check_module(module: &Module) -> Result<CheckedModule, TypeError> {
    let mut context = Context::new();
    let mut definitions = Vec::with_capacity(module.definitions.len());

    for definition in &module.definitions {
        let ann = match definition.ann {
            // We don't have a type annotation available to us! Instead we will attempt to infer it
            // based on the body of the definition
            None => context.infer(&definition.term)?.inferred,
            // We have a type annotation! Evaluate it to its normal form, then check that it matches
            // the body of the definition
            Some(ref ann) => {
                let ann = context.normalize(&ann)?;
                context.check(&definition.term, &ann.value)?;
                ann.value
            },
        };
        // Evaluate the body of the definition
        let term = context.normalize(&definition.term)?.value;
        let name = definition.name.clone();
        // Add the definition to the context
        context = context.extend(Binder::Let(term.clone(), ann.clone()));

        definitions.push(CheckedDefinition { name, term, ann })
    }

    Ok(CheckedModule {
        name: module.name.clone(),
        definitions,
    })
}

/// An internal error. These are bugs!
#[derive(Debug, Clone, PartialEq)]
pub enum InternalError {
    NormalizedUnboundVariable(Name),
    DeBruijnIndexOutOfScope { index: Debruijn, context: Context },
}

/// An error produced during typechecking
#[derive(Debug, Clone, PartialEq)]
pub enum TypeError {
    IllegalApplication,
    TypeAnnotationsNeeded,
    ExpectedFunction {
        lam_expr: RcTerm,
        expected: RcType,
    },
    Mismatch {
        expr: RcTerm,
        found: RcType,
        expected: RcType,
    },
    UnboundVariable(Name),
    Internal(InternalError),
}

impl From<InternalError> for TypeError {
    fn from(src: InternalError) -> TypeError {
        TypeError::Internal(src)
    }
}

/// A binder that introduces a variable into the context
//
// b ::= λx:τ           1. lambda abstraction
//     | Πx:τ           2. dependent function
//     | let x:τ = v    3. let binding
//
#[derive(Debug, Clone, PartialEq)]
pub enum Binder {
    /// A type introduced after entering a lambda abstraction
    Lam(Option<RcType>), // 1.
    /// A type introduced after entering a pi type
    Pi(RcType), // 2.
    /// A value and type binding that was introduced by passing over a let binding
    Let(RcValue, RcType), // 3.
}

impl Binder {
    /// Return the type associated with a binder
    pub fn ty(&self) -> Option<&RcType> {
        match *self {
            Binder::Lam(ref ty) => ty.as_ref(),
            Binder::Pi(ref ty) | Binder::Let(_, ref ty) => Some(ty),
        }
    }
}

impl fmt::Display for Binder {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.to_doc(pretty::Options::default().with_debug_indices(f.alternate()))
            .group()
            .render_fmt(f.width().unwrap_or(80), f)
    }
}

/// A list of binders that have been accumulated during typechecking
#[derive(Debug, Clone, PartialEq)]
pub struct Context {
    // Γ ::= ε           1. empty context
    //     | Γ,b         2. context extension
    pub binders: List<Binder>,
}

impl fmt::Display for Context {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.to_doc(pretty::Options::default().with_debug_indices(f.alternate()))
            .group()
            .render_fmt(f.width().unwrap_or(80), f)
    }
}

impl Context {
    /// Create a new, empty context
    pub fn new() -> Context {
        Context {
            binders: List::new(),
        }
    }

    /// Extend the context with a binder
    pub fn extend(&self, binder: Binder) -> Context {
        Context {
            binders: self.binders.push_front(binder),
        }
    }

    /// Look up a binder based on the given Debruijn index
    pub fn lookup_binder(&self, index: Debruijn) -> Result<&Binder, InternalError> {
        self.binders.iter().nth(index.0 as usize).ok_or_else(|| {
            InternalError::DeBruijnIndexOutOfScope {
                index,
                context: self.clone(),
            }
        })
    }

    /// Evaluates a core term to its normal form
    //
    // Γ ⊢ e ⇓ v
    //
    pub fn normalize(&self, term: &RcTerm) -> Result<NormalizeDerivation, InternalError> {
        match *term.inner {
            //  1.  Γ ⊢ e ⇓ v
            // ─────────────────────── (EVAL/ANN)
            //      Γ ⊢ e:ρ ⇓ v
            Term::Ann(ref expr, _) => {
                let nexpr = self.normalize(expr)?; // 1.

                Ok(NormalizeDerivation {
                    context: self.clone(),
                    term: term.clone(),
                    value: nexpr.value.clone(),
                    rule: NormalizeRule::Ann(nexpr.into()),
                })
            },

            // ─────────────────── (EVAL/TYPE)
            //  Γ ⊢ Type ⇓ Type
            Term::Type => Ok(NormalizeDerivation {
                rule: NormalizeRule::Type,
                context: self.clone(),
                term: term.clone(),
                value: Value::Type.into(),
            }),

            Term::Var(ref var) => match *var {
                Var::Free(ref name) => Err(InternalError::NormalizedUnboundVariable(name.clone())),
                Var::Bound(Named(_, index)) => match *self.lookup_binder(index)? {
                    // Can't reduce further - we are in a pi or let binding
                    //
                    //  1.  λx:τ ∈ Γ
                    // ───────────────────── (EVAL/VAR-LAM)
                    //      Γ ⊢ x ⇓ x
                    //
                    //  2.  Πx:τ ∈ Γ
                    // ───────────────────── (EVAL/VAR-PI)
                    //      Γ ⊢ x ⇓ x
                    Binder::Lam(_) => Ok(NormalizeDerivation {
                        context: self.clone(),
                        term: term.clone(),
                        value: Value::Var(var.clone()).into(),
                        rule: NormalizeRule::VarLam,
                    }),
                    Binder::Pi(_) => Ok(NormalizeDerivation {
                        rule: NormalizeRule::VarPi,
                        context: self.clone(),
                        term: term.clone(),
                        value: Value::Var(var.clone()).into(),
                    }),
                    // We have a value in scope, let's use that!
                    //
                    //  1.  let x:τ = v ∈ Γ
                    // ───────────────────── (EVAL/VAR-LET)
                    //      Γ ⊢ x ⇓ v
                    Binder::Let(_, ref value) => Ok(NormalizeDerivation {
                        rule: NormalizeRule::VarLet,
                        context: self.clone(),
                        term: term.clone(),
                        value: value.clone(),
                    }),
                },
            },

            //  1. Γ,λx ⊢ e ⇓ v
            // ───────────────────────── (EVAL/LAM)
            //     Γ ⊢ λx.e ⇓ λx.v
            Term::Lam(Named(ref name, None), ref body_expr) => {
                let binder = Binder::Lam(None);
                let nbody = self.extend(binder).normalize(body_expr)?; // 1.

                Ok(NormalizeDerivation {
                    context: self.clone(),
                    term: term.clone(),
                    value: Value::Lam(Named(name.clone(), None), nbody.value.clone()).into(),
                    rule: NormalizeRule::Lam(nbody.into()),
                })
            },

            //  1.  Γ ⊢ ρ ⇓ τ
            //  2.  Γ,λx:τ ⊢ e ⇓ v
            // ──────────────────────────────── (EVAL/LAM-ANN)
            //      Γ ⊢ λx:ρ.e ⇓ λx:τ.v
            Term::Lam(Named(ref name, Some(ref param_ty)), ref body_expr) => {
                let nparam_ty = self.normalize(param_ty)?; // 1.
                let binder = Binder::Lam(Some(nparam_ty.value.clone()));
                let nbody_expr = self.extend(binder).normalize(body_expr)?; // 2.

                Ok(NormalizeDerivation {
                    context: self.clone(),
                    term: term.clone(),
                    value: Value::Lam(
                        Named(name.clone(), Some(nparam_ty.value.clone())),
                        nbody_expr.value.clone(),
                    ).into(),
                    rule: NormalizeRule::LamAnn(nparam_ty.into(), nbody_expr.into()),
                })
            },

            //  1.  Γ ⊢ ρ₁ ⇓ τ₁
            //  2.  Γ,Πx:τ ⊢ ρ₂ ⇓ τ₂
            // ─────────────────────────────────── (EVAL/PI-ANN)
            //      Γ ⊢ Πx:ρ₁.ρ₂ ⇓ Πx:τ₁.τ₂
            Term::Pi(Named(ref name, ref param_ty), ref body_expr) => {
                let nparam_ty = self.normalize(param_ty)?; // 1.
                let binder = Binder::Pi(nparam_ty.value.clone());
                let nbody_expr = self.extend(binder).normalize(body_expr)?; // 2.

                Ok(NormalizeDerivation {
                    context: self.clone(),
                    term: term.clone(),
                    value: Value::Pi(
                        Named(name.clone(), nparam_ty.value.clone()),
                        nbody_expr.value.clone(),
                    ).into(),
                    rule: NormalizeRule::Pi(nparam_ty.into(), nbody_expr.into()),
                })
            },

            // Perform [β-reduction](https://en.wikipedia.org/wiki/Lambda_calculus#β-reduction),
            // ie. apply functions to their arguments
            //
            //  1.  Γ ⊢ e₁ ⇓ λx.v₁
            //  2.  Γ ⊢ v₁[x↦e₂] ⇓ v₂
            // ───────────────────────────── (EVAL/APP)
            //      Γ ⊢ e₁ e₂ ⇓ v₂
            Term::App(ref fn_expr, ref arg) => {
                let fn_expr = self.normalize(fn_expr)?; // 1.
                let arg = self.normalize(arg)?; // 2.

                match *fn_expr.value.clone().inner {
                    Value::Lam(_, ref body) => Ok(NormalizeDerivation {
                        context: self.clone(),
                        term: term.clone(),
                        value: body.open(&arg.value),
                        rule: NormalizeRule::AppLam(fn_expr.into(), arg.into()),
                    }),
                    _ => Ok(NormalizeDerivation {
                        context: self.clone(),
                        term: term.clone(),
                        value: Value::App(fn_expr.value.clone(), arg.value.clone()).into(),
                        rule: NormalizeRule::AppStuck(fn_expr.into(), arg.into()),
                    }),
                }
            },
        }
    }

    /// Check that the given term has the expected type
    //
    // Γ ⊢ e :↓ τ
    //
    pub fn check(&self, term: &RcTerm, expected: &RcType) -> Result<CheckDerivation, TypeError> {
        match *term.inner {
            //  1.  Γ,Πx:τ₁ ⊢ e :↓ τ₂
            // ─────────────────────────────── (CHECK/LAM)
            //      Γ ⊢ λx.e :↓ Πx:τ₁.τ₂
            Term::Lam(Named(_, None), ref body_expr) => match *expected.inner {
                Value::Pi(Named(_, ref param_ty), ref ret_ty) => {
                    let binder = Binder::Pi(param_ty.clone());
                    let body = self.extend(binder).check(body_expr, ret_ty)?; // 1.
                    Ok(CheckDerivation {
                        context: self.clone(),
                        term: term.clone(),
                        expected: expected.clone(),
                        rule: CheckRule::Lam(body.into()),
                    })
                },
                _ => Err(TypeError::ExpectedFunction {
                    lam_expr: term.clone(),
                    expected: expected.clone(),
                }),
            },

            //  1.  Γ ⊢ e :↑ τ
            // ─────────────────── (CHECK/INFER)
            //      Γ ⊢ e :↓ τ
            _ => {
                let inferred_ty = self.infer(term)?; // 1.
                match &inferred_ty.inferred == expected {
                    true => Ok(CheckDerivation {
                        context: self.clone(),
                        term: term.clone(),
                        expected: expected.clone(),
                        rule: CheckRule::Infer(inferred_ty.into()),
                    }),
                    false => Err(TypeError::Mismatch {
                        expr: term.clone(),
                        found: inferred_ty.inferred,
                        expected: expected.clone(),
                    }),
                }
            },
        }
    }

    /// Infer the type of the given term
    //
    // Γ ⊢ e :↑ τ
    //
    pub fn infer(&self, term: &RcTerm) -> Result<InferDerivation, TypeError> {
        match *term.inner {
            //  1.  Γ ⊢ ρ₁ :↓ Type
            //  2.  ρ ⇓ τ
            //  3.  Γ ⊢ e :↓ τ
            // ───────────────────────── (INFER/ANN)
            //      Γ ⊢ (e:ρ) :↑ τ
            Term::Ann(ref expr, ref ty) => {
                let ty = self.check(ty, &Value::Type.into())?; // 1.
                let simp_ty = self.normalize(&ty.term)?; // 2.
                let expr = self.check(expr, &simp_ty.value)?; // 3.
                Ok(InferDerivation {
                    context: self.clone(),
                    term: term.clone(),
                    inferred: simp_ty.value.clone(),
                    rule: InferRule::Ann(ty.into(), simp_ty.into(), expr.into()),
                })
            },

            // ─────────────────── (INFER/TYPE)
            //  Γ ⊢ TYPE :↑ Type
            Term::Type => Ok(InferDerivation {
                context: self.clone(),
                term: term.clone(),
                inferred: Value::Type.into(),
                rule: InferRule::Type,
            }),

            Term::Lam(Named(_, None), _) => {
                // TODO: More error info
                Err(TypeError::TypeAnnotationsNeeded)
            },

            //  1.  Γ ⊢ ρ :↓ Type
            //  2.  ρ ⇓ τ₁
            //  3.  Γ,λx:τ₁ ⊢ e :↑ τ₂
            // ─────────────────────────────── (INFER/LAM)
            //      Γ ⊢ λx:ρ.e :↑ Πx:τ₁.τ₂
            Term::Lam(Named(ref param_name, Some(ref param_ty)), ref body_expr) => {
                let param_ty = self.check(param_ty, &Value::Type.into())?; // 1.
                let simp_param_ty = self.normalize(&param_ty.term)?; // 2.
                let binder = Binder::Lam(Some(simp_param_ty.value.clone()));
                let body_ty = self.extend(binder).infer(body_expr)?; // 3.

                Ok(InferDerivation {
                    context: self.clone(),
                    term: term.clone(),
                    inferred: Value::Pi(
                        Named(param_name.clone(), simp_param_ty.value.clone()),
                        body_ty.inferred.clone(),
                    ).into(),
                    rule: InferRule::Lam(param_ty.into(), simp_param_ty.into(), body_ty.into()),
                })
            },

            //  1.  Γ ⊢ ρ₁ :↓ Type
            //  2.  ρ₁ ⇓ τ₁
            //  3.  Γ,Πx:τ₁ ⊢ ρ₂ :↓ Type
            // ────────────────────────────── (INFER/PI)
            //      Γ ⊢ Πx:ρ₁.ρ₂ :↑ Type
            Term::Pi(Named(_, ref param_ty), ref body_ty) => {
                let param_ty = self.check(param_ty, &Value::Type.into())?; // 1.
                let simp_param_ty = self.normalize(&param_ty.term)?; // 2.
                let binder = Binder::Pi(simp_param_ty.value.clone());
                let body_ty = self.extend(binder).check(body_ty, &Value::Type.into())?; // 3.
                Ok(InferDerivation {
                    context: self.clone(),
                    term: term.clone(),
                    inferred: Value::Type.into(),
                    rule: InferRule::Pi(param_ty.into(), simp_param_ty.into(), body_ty.into()),
                })
            },

            //  1.  x:τ ∈ Γ
            // ──────────────────── (INFER/VAR)
            //      Γ ⊢ x :↑ τ
            Term::Var(ref var) => match *var {
                Var::Free(ref name) => Err(TypeError::UnboundVariable(name.clone())),
                Var::Bound(Named(_, index)) => match self.lookup_binder(index)?.ty() {
                    Some(ty) => Ok(InferDerivation {
                        context: self.clone(),
                        term: term.clone(),
                        inferred: ty.clone(),
                        rule: InferRule::Var,
                    }), // 1.
                    None => Err(TypeError::TypeAnnotationsNeeded),
                },
            },

            //  1.  Γ ⊢ e₁ :↑ Πx:τ₁.τ₂
            //  2.  Γ ⊢ e₂ :↓ τ₁
            //  3.  τ₂[x↦e₂] ⇓ τ₃
            // ────────────────────────────── (INFER/APP)
            //      Γ ⊢ e₁ e₂ :↑ τ₃
            Term::App(ref fn_expr, ref arg_expr) => {
                let fn_type = self.infer(fn_expr)?; // 1.
                match *fn_type.inferred.clone().inner {
                    Value::Pi(Named(_, ref param_ty), ref ret_ty) => {
                        let arg_expr = self.check(arg_expr, param_ty)?; // 2.
                        let simp_arg = self.normalize(&arg_expr.term)?;
                        let body_ty = ret_ty.open(&simp_arg.value); // 3.
                        Ok(InferDerivation {
                            context: self.clone(),
                            term: term.clone(),
                            inferred: body_ty,
                            rule: InferRule::App(fn_type.into(), arg_expr.into(), simp_arg.into()),
                        })
                    },
                    // TODO: More error info
                    _ => Err(TypeError::IllegalApplication),
                }
            },
        }
    }
}

#[derive(Copy, Clone)]
struct Indent(usize);

impl Indent {
    fn nest(self) -> Indent {
        Indent(self.0 + 1)
    }
}

impl fmt::Display for Indent {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for _ in 0..self.0 {
            write!(f, "    ")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct NormalizeDerivation {
    context: Context,
    term: RcTerm,
    value: RcValue,
    rule: NormalizeRule,
}

fn pretty_normalize_derivation(
    indent: Indent,
    deriv: &NormalizeDerivation,
    f: &mut fmt::Formatter,
) -> fmt::Result {
    writeln!(f, "{}NormalizeDerivation", indent)?;
    writeln!(f, "{}  context: {:#}", indent, deriv.context)?;
    writeln!(f, "{}  term: {:#}", indent, deriv.term)?;
    writeln!(f, "{}  value: {:#}", indent, deriv.value)?;
    match deriv.rule {
        NormalizeRule::Ann(ref d1) => {
            writeln!(f, "{}  rule: Ann", indent)?;
            pretty_normalize_derivation(indent.nest(), d1, f)?;
        },
        NormalizeRule::Type => writeln!(f, "{}  rule: Type", indent)?,
        NormalizeRule::VarLam => writeln!(f, "{}  rule: VarLam", indent)?,
        NormalizeRule::VarPi => writeln!(f, "{}  rule: VarPi", indent)?,
        NormalizeRule::VarLet => writeln!(f, "{}  rule: VarLet", indent)?,
        NormalizeRule::Lam(ref d1) => {
            writeln!(f, "{}  rule: Lam", indent)?;
            pretty_normalize_derivation(indent.nest(), d1, f)?;
        },
        NormalizeRule::LamAnn(ref d1, ref d2) => {
            writeln!(f, "{}  rule: LamAnn", indent)?;
            pretty_normalize_derivation(indent.nest(), d1, f)?;
            pretty_normalize_derivation(indent.nest(), d2, f)?;
        },
        NormalizeRule::Pi(ref d1, ref d2) => {
            writeln!(f, "{}  rule: Pi", indent)?;
            pretty_normalize_derivation(indent.nest(), d1, f)?;
            pretty_normalize_derivation(indent.nest(), d2, f)?;
        },
        NormalizeRule::AppLam(ref d1, ref d2) => {
            writeln!(f, "{}  rule: AppLam", indent)?;
            pretty_normalize_derivation(indent.nest(), d1, f)?;
            pretty_normalize_derivation(indent.nest(), d2, f)?;
        },
        NormalizeRule::AppStuck(ref d1, ref d2) => {
            writeln!(f, "{}  rule: AppStuck", indent)?;
            pretty_normalize_derivation(indent.nest(), d1, f)?;
            pretty_normalize_derivation(indent.nest(), d2, f)?;
        },
    }
    Ok(())
}

impl fmt::Display for NormalizeDerivation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        pretty_normalize_derivation(Indent(0), self, f)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum NormalizeRule {
    Ann(Box<NormalizeDerivation>),
    Type,
    VarLam,
    VarPi,
    VarLet,
    Lam(Box<NormalizeDerivation>),
    LamAnn(Box<NormalizeDerivation>, Box<NormalizeDerivation>),
    Pi(Box<NormalizeDerivation>, Box<NormalizeDerivation>),
    AppLam(Box<NormalizeDerivation>, Box<NormalizeDerivation>),
    AppStuck(Box<NormalizeDerivation>, Box<NormalizeDerivation>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct CheckDerivation {
    context: Context,
    term: RcTerm,
    expected: RcType,
    rule: CheckRule,
}

fn pretty_check_derivation(
    indent: Indent,
    deriv: &CheckDerivation,
    f: &mut fmt::Formatter,
) -> fmt::Result {
    writeln!(f, "{}CheckDerivation", indent)?;
    writeln!(f, "{}  context: {:#}", indent, deriv.context)?;
    writeln!(f, "{}  term: {:#}", indent, deriv.term)?;
    writeln!(f, "{}  expected: {:#}", indent, deriv.expected)?;
    match deriv.rule {
        CheckRule::Lam(ref d1) => {
            writeln!(f, "{}  rule: Lam", indent)?;
            pretty_check_derivation(indent.nest(), d1, f)?;
        },
        CheckRule::Infer(ref d1) => {
            writeln!(f, "{}  rule: Infer", indent)?;
            pretty_infer_derivation(indent.nest(), d1, f)?;
        },
    }
    Ok(())
}

impl fmt::Display for CheckDerivation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        pretty_check_derivation(Indent(0), self, f)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum CheckRule {
    Lam(Box<CheckDerivation>),
    Infer(Box<InferDerivation>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct InferDerivation {
    context: Context,
    term: RcTerm,
    inferred: RcType,
    rule: InferRule,
}

fn pretty_infer_derivation(
    indent: Indent,
    deriv: &InferDerivation,
    f: &mut fmt::Formatter,
) -> fmt::Result {
    writeln!(f, "{}InferDerivation", indent)?;
    writeln!(f, "{}  context: {:#}", indent, deriv.context)?;
    writeln!(f, "{}  term: {:#}", indent, deriv.term)?;
    writeln!(f, "{}  inferred: {:#}", indent, deriv.inferred)?;
    match deriv.rule {
        InferRule::Ann(ref d1, ref d2, ref d3) => {
            writeln!(f, "{}  rule: Ann", indent)?;
            pretty_check_derivation(indent.nest(), d1, f)?;
            pretty_normalize_derivation(indent.nest(), d2, f)?;
            pretty_check_derivation(indent.nest(), d3, f)?;
        },
        InferRule::Type => writeln!(f, "{}  rule: Type", indent)?,
        InferRule::Var => writeln!(f, "{}  rule: Var", indent)?,
        InferRule::Lam(ref d1, ref d2, ref d3) => {
            writeln!(f, "{}  rule: Lam", indent)?;
            pretty_check_derivation(indent.nest(), d1, f)?;
            pretty_normalize_derivation(indent.nest(), d2, f)?;
            pretty_infer_derivation(indent.nest(), d3, f)?;
        },
        InferRule::Pi(ref d1, ref d2, ref d3) => {
            writeln!(f, "{}  rule: Pi", indent)?;
            pretty_check_derivation(indent.nest(), d1, f)?;
            pretty_normalize_derivation(indent.nest(), d2, f)?;
            pretty_check_derivation(indent.nest(), d3, f)?;
        },
        InferRule::App(ref d1, ref d2, ref d3) => {
            writeln!(f, "{}  rule: App", indent)?;
            pretty_infer_derivation(indent.nest(), d1, f)?;
            pretty_check_derivation(indent.nest(), d2, f)?;
            pretty_normalize_derivation(indent.nest(), d3, f)?;
        },
    }
    Ok(())
}

impl fmt::Display for InferDerivation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        pretty_infer_derivation(Indent(0), self, f)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum InferRule {
    Ann(
        Box<CheckDerivation>,
        Box<NormalizeDerivation>,
        Box<CheckDerivation>,
    ),
    Type,
    Lam(
        Box<CheckDerivation>,
        Box<NormalizeDerivation>,
        Box<InferDerivation>,
    ),
    Pi(
        Box<CheckDerivation>,
        Box<NormalizeDerivation>,
        Box<CheckDerivation>,
    ),
    Var,
    App(
        Box<InferDerivation>,
        Box<CheckDerivation>,
        Box<NormalizeDerivation>,
    ),
}
