//! The semantics of the language
//!
//! The key judgements we define in this module are:
//!
//! - normalization: `Γ ⊢ e ⇓ v`
//! - type checking: `Γ ⊢ e ⇐ τ ⤳ v`
//! - type inference: `Γ ⊢ e ⇒ τ ⤳ v`
//!
//! We take a bidirectional approach to type checking, splitting it into two
//! phases: type checking and type inference. This makes the flow of information
//! through the type checker clear and relatively easy to reason about.

use syntax::core::{Binder, Context, Module, RcTerm, RcType, RcValue, Term, Value};
use syntax::var::{Debruijn, Name, Named, Var};

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

fn lookup(context: &Context, index: Debruijn) -> Result<&Binder, InternalError> {
    match context.lookup_binder(index) {
        Some(&Named(_, ref binder)) => Ok(binder),
        None => Err(InternalError::DeBruijnIndexOutOfScope {
            index,
            context: context.clone(),
        }),
    }
}

/// Typecheck and elaborate a module
pub fn check_module(module: &Module) -> Result<CheckedModule, TypeError> {
    let mut context = Context::new();
    let mut definitions = Vec::with_capacity(module.definitions.len());

    for definition in &module.definitions {
        let name = definition.name.clone();
        let (term, ann) = match definition.ann {
            // We don't have a type annotation available to us! Instead we will attempt to infer it
            // based on the body of the definition
            None => infer(&context, &definition.term)?,
            // We have a type annotation! Evaluate it to its normal form, then check that it matches
            // the body of the definition
            Some(ref ann) => {
                let ann = normalize(&context, &ann)?;
                let elab_term = check(&context, &definition.term, &ann)?;
                (elab_term, ann)
            },
        };

        // Add the definition to the context
        context = context.extend(Named(
            Name::user(name.clone()),
            Binder::Let(term.clone(), ann.clone()),
        ));

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
    NormalizedHole,
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

/// Evaluate a term in a context
///
/// Normalizes (evaluates) a core term to its normal form under the assumptions
/// in the context.
///
/// ```text
/// Γ ⊢ e ⇓ v
/// ```
///
/// Here we diverge from the LambdaPi paper by requiring a context to be
/// supplied. This allows us to resolve previously defined terms during
/// normalization.
pub fn normalize(context: &Context, term: &RcTerm) -> Result<RcValue, InternalError> {
    match *term.inner {
        //  1.  Γ ⊢ e ⇓ v
        // ─────────────────────── (EVAL/ANN)
        //      Γ ⊢ e:ρ ⇓ v
        Term::Ann(ref expr, _) => {
            normalize(context, expr) // 1.
        },

        // ─────────────────── (EVAL/TYPE)
        //  Γ ⊢ Type ⇓ Type
        Term::Universe => Ok(RcValue::universe()),

        Term::Hole => Err(InternalError::NormalizedHole),

        Term::Var(ref var) => match *var {
            Var::Free(ref name) => Err(InternalError::NormalizedUnboundVariable(name.clone())),
            Var::Bound(Named(_, index)) => match *lookup(context, index)? {
                // Can't reduce further - we are in a pi or let binding
                //
                //  1.  λx:τ ∈ Γ
                // ───────────────────── (EVAL/VAR-LAM)
                //      Γ ⊢ x ⇓ x
                //
                //  2.  Πx:τ ∈ Γ
                // ───────────────────── (EVAL/VAR-PI)
                //      Γ ⊢ x ⇓ x
                Binder::Lam(_) | Binder::Pi(_) => Ok(Value::Var(var.clone()).into()),
                // We have a value in scope, let's use that!
                //
                //  1.  let x:τ = v ∈ Γ
                // ───────────────────── (EVAL/VAR-LET)
                //      Γ ⊢ x ⇓ v
                Binder::Let(_, ref value) => Ok(value.clone()),
            },
        },

        //  1.  Γ ⊢ ρ ⇓ τ
        //  2.  Γ,λx:τ ⊢ e ⇓ v
        // ──────────────────────────────── (EVAL/LAM)
        //      Γ ⊢ λx:ρ.e ⇓ λx:τ.v
        Term::Lam(Named(ref name, ref param_ty), ref body_expr) => {
            let param_ty = normalize(context, param_ty)?; // 1.
            let binder = Named(name.clone(), Binder::Lam(param_ty.clone()));
            let body_expr = normalize(&context.extend(binder), body_expr)?; // 2.

            Ok(Value::Lam(Named(name.clone(), param_ty), body_expr).into())
        },

        //  1.  Γ ⊢ ρ₁ ⇓ τ₁
        //  2.  Γ,Πx:τ ⊢ ρ₂ ⇓ τ₂
        // ─────────────────────────────────── (EVAL/PI-ANN)
        //      Γ ⊢ Πx:ρ₁.ρ₂ ⇓ Πx:τ₁.τ₂
        Term::Pi(Named(ref name, ref param_ty), ref body_expr) => {
            let param_ty = normalize(context, param_ty)?; // 1.
            let binder = Named(name.clone(), Binder::Pi(param_ty.clone()));
            let body_expr = normalize(&context.extend(binder), body_expr)?; // 2.

            Ok(Value::Pi(Named(name.clone(), param_ty), body_expr).into())
        },

        // Perform [β-reduction](https://en.wikipedia.org/wiki/Lambda_calculus#β-reduction),
        // ie. apply functions to their arguments
        //
        //  1.  Γ ⊢ e₁ ⇓ λx.v₁
        //  2.  Γ ⊢ v₁[x↦e₂] ⇓ v₂
        // ───────────────────────────── (EVAL/APP)
        //      Γ ⊢ e₁ e₂ ⇓ v₂
        Term::App(ref fn_expr, ref arg) => {
            let fn_expr = normalize(context, fn_expr)?; // 1.
            let arg = normalize(context, arg)?; // 2.

            match *fn_expr.inner {
                Value::Lam(_, ref body) => Ok(body.open(&arg)),
                _ => Ok(Value::App(fn_expr.clone(), arg).into()),
            }
        },
    }
}

/// Type checking of terms
///
/// Under the assumptions in the context, check that the given term has
/// the expected type and return its elaborated form.
///
/// ```text
/// Γ ⊢ e ⇐ τ ⤳ v
/// ```
pub fn check(context: &Context, term: &RcTerm, expected: &RcType) -> Result<RcValue, TypeError> {
    match *term.inner {
        //  1.  Γ,Πx:τ₁ ⊢ e ⇐ τ₂ ⤳ v
        // ────────────────────────────────────── (CHECK/LAM)
        //      Γ ⊢ λx.e ⇐ Πx:τ₁.τ₂ ⤳ λx:τ₁.v
        Term::Lam(Named(ref lam_name, ref ann), ref body) if *ann.inner == Term::Hole => {
            match *expected.inner {
                Value::Pi(Named(ref pi_name, ref param_ty), ref ret) => {
                    let binder = Named(pi_name.clone(), Binder::Pi(param_ty.clone()));
                    let elab_body = check(&context.extend(binder), body, ret)?; // 1.

                    Ok(Value::Lam(Named(lam_name.clone(), param_ty.clone()), elab_body).into())
                },
                _ => Err(TypeError::ExpectedFunction {
                    lam_expr: term.clone(),
                    expected: expected.clone(),
                }),
            }
        },

        //  1.  Γ ⊢ e ⇒ τ ⤳ v
        // ─────────────────────── (CHECK/INFER)
        //      Γ ⊢ e ⇐ τ ⤳ v
        _ => {
            let (elab_term, inferred_ty) = infer(context, term)?; // 1.
            match &inferred_ty == expected {
                true => Ok(elab_term),
                false => Err(TypeError::Mismatch {
                    expr: term.clone(),
                    found: inferred_ty,
                    expected: expected.clone(),
                }),
            }
        },
    }
}

/// Type inference of terms
///
/// Under the assumptions in the context, synthesize a type for the given term
/// and return its elaborated form.
///
/// ```text
/// Γ ⊢ e ⇒ τ ⤳ v
/// ```
pub fn infer(context: &Context, term: &RcTerm) -> Result<(RcValue, RcType), TypeError> {
    match *term.inner {
        //  1.  Γ ⊢ ρ ⇐ Type ⤳ τ
        //  2.  ρ ⇓ τ
        //  3.  Γ ⊢ e ⇐ τ ⤳ v
        // ───────────────────────────── (INFER/ANN)
        //      Γ ⊢ (e:ρ) ⇒ τ ⤳ v
        Term::Ann(ref expr, ref ty) => {
            check(context, ty, &RcValue::universe())?; // 1.
            let simp_ty = normalize(context, &ty)?; // 2.
            let elab_expr = check(context, expr, &simp_ty)?; // 3.
            Ok((elab_expr, simp_ty))
        },

        // ─────────────────────────── (INFER/TYPE)
        //  Γ ⊢ Type ⇒ Type ⤳ Type
        Term::Universe => Ok((RcValue::universe(), RcValue::universe())),

        // TODO: More error info
        Term::Hole => Err(TypeError::TypeAnnotationsNeeded),

        Term::Var(ref var) => match *var {
            Var::Free(ref name) => Err(TypeError::UnboundVariable(name.clone())),
            Var::Bound(Named(_, index)) => match *lookup(context, index)? {
                //  1.  λx:τ ∈ Γ
                // ─────────────────────── (INFER/VAR-LAM)
                //      Γ ⊢ x ⇒ τ ⤳ x
                //
                //  2.  Πx:τ ∈ Γ
                // ─────────────────────── (INFER/VAR-PI)
                //      Γ ⊢ x ⇒ τ ⤳ x
                Binder::Lam(ref ty) | Binder::Pi(ref ty) => {
                    Ok((Value::Var(var.clone()).into(), ty.clone()))
                },
                //  1.  let x:τ = v ∈ Γ
                // ─────────────────────── (INFER/VAR-LET)
                //      Γ ⊢ x ⇒ τ ⤳ v
                Binder::Let(ref ty, ref value) => Ok((ty.clone(), value.clone())),
            },
        },

        Term::Lam(Named(_, ref ann), _) if *ann.inner == Term::Hole => {
            // TODO: More error info
            Err(TypeError::TypeAnnotationsNeeded)
        },

        //  1.  Γ ⊢ ρ ⇐ Type ⤳ τ
        //  2.  ρ ⇓ τ₁
        //  3.  Γ,λx:τ₁ ⊢ e ⇒ τ₂ ⤳ v
        // ───────────────────────────────────────── (INFER/LAM)
        //      Γ ⊢ λx:ρ.e ⇒ Πx:τ₁.τ₂ ⤳ λx:τ.v
        Term::Lam(Named(ref name, ref ann), ref body_expr) => {
            let elab_ann = check(context, ann, &RcValue::universe())?; // 1.
            let simp_ann = normalize(context, &ann)?; // 2.
            let binder = Named(name.clone(), Binder::Lam(simp_ann.clone()));
            let (elab_body_expr, body_ty) = infer(&context.extend(binder), body_expr)?; // 3.

            Ok((
                Value::Lam(Named(name.clone(), elab_ann), elab_body_expr).into(),
                Value::Pi(Named(name.clone(), simp_ann), body_ty).into(),
            ))
        },

        //  1.  Γ ⊢ ρ₁ ⇐ Type ⤳ τ₁
        //  2.  ρ₁ ⇓ τ₁'
        //  3.  Γ,Πx:τ₁' ⊢ ρ₂ ⇐ Type ⤳ τ₂
        // ────────────────────────────────────────── (INFER/PI)
        //      Γ ⊢ Πx:ρ₁.ρ₂ ⇒ Type ⤳ Πx:τ₁.τ₂
        Term::Pi(Named(ref name, ref ann), ref body_ty) => {
            let elab_ann = check(context, ann, &RcValue::universe())?; // 1.
            let simp_ann = normalize(context, &ann)?; // 2.
            let binder = Named(name.clone(), Binder::Pi(simp_ann));
            let elab_body_ty = check(&context.extend(binder), body_ty, &RcValue::universe())?; // 3.

            Ok((
                Value::Pi(Named(name.clone(), elab_ann), elab_body_ty).into(),
                RcValue::universe(),
            ))
        },

        //  1.  Γ ⊢ e₁ ⇒ Πx:τ₁.τ₂ ⤳ v₁
        //  2.  Γ ⊢ e₂ ⇐ τ₁ ⤳ v₂
        //  3.  τ₂[x↦e₂] ⇓ τ₃
        // ───────────────────────────────── (INFER/APP)
        //      Γ ⊢ e₁ e₂ ⇒ τ₃ ⤳ v₁ v₂
        Term::App(ref fn_expr, ref arg_expr) => {
            let (elab_fn_expr, fn_type) = infer(context, fn_expr)?; // 1.
            match *fn_type.inner {
                Value::Pi(Named(_, ref ann), ref ret_ty) => {
                    let elab_arg_expr = check(context, arg_expr, ann)?; // 2.
                    let body_ty = ret_ty.open(&normalize(context, &arg_expr)?); // 3.
                    Ok((Value::App(elab_fn_expr, elab_arg_expr).into(), body_ty))
                },
                // TODO: More error info
                _ => Err(TypeError::IllegalApplication),
            }
        },
    }
}
