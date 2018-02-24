// TODO

use syntax::concrete;
use syntax::core;

use syntax::var::Var;

/// Translate something to the corresponding concrete representation
pub trait ToConcrete<T> {
    fn to_concrete(&self) -> T;
}

impl ToConcrete<concrete::Module> for core::Module {
    fn to_concrete(&self) -> concrete::Module {
        unimplemented!()
    }
}

impl ToConcrete<Option<u32>> for core::Level {
    fn to_concrete(&self) -> Option<u32> {
        match *self {
            core::Level(0) => None,
            core::Level(level) => Some(level),
        }
    }
}

impl ToConcrete<concrete::Term> for core::RcTerm {
    fn to_concrete(&self) -> concrete::Term {
        match *self.inner {
            core::Term::Ann(_, ref term, ref ty) => {
                concrete::Term::Ann(term.to_concrete().into(), ty.to_concrete().into())
            },
            core::Term::Universe(meta, level) => {
                concrete::Term::Universe(meta.span, level.to_concrete())
            },
            core::Term::Var(meta, Var::Free(core::Name::User(ref name))) => {
                concrete::Term::Var(meta.span, name.clone())
            },
            core::Term::Var(_, Var::Free(core::Name::Gen(ref _gen))) => {
                // TODO: use name if it is present, and not used in the current scope
                // otherwise create a pretty name
                unimplemented!()
            },
            core::Term::Var(_, Var::Bound(_)) => {
                // TODO: Better message
                panic!("Tried to convert a term that was not locally closed");
            },
            core::Term::Lam(_, ref lam) => {
                let (_param, _body) = lam.clone().unbind();
                // use name if it is present, and not used in the current scope
                // otherwise create a pretty name
                // add the used name to the environment
                // convert the body using the new environment
                unimplemented!()
            },
            core::Term::Pi(_, ref pi) => {
                let (param, body) = pi.clone().unbind();
                if body.free_vars().contains(&param.name) {
                    // use name if it is present, and not used in the current scope
                    // otherwise create a pretty name
                    // add the used name to the environment
                    // convert the body using the new environment
                    unimplemented!()
                } else {
                    // The body is not dependent on the parameter - so let's use an arrow instead!
                    concrete::Term::Arrow(
                        param.inner.to_concrete().into(),
                        body.to_concrete().into(),
                    )
                }
            },
            core::Term::App(_, ref fn_term, ref arg) => {
                concrete::Term::Ann(fn_term.to_concrete().into(), arg.to_concrete().into())
            },
        }
    }
}
