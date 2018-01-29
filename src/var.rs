//! Data types related to variable binding
//!
//! We use a locally nameless representation for variable binding.
//!
//! # References
//!
//! - [How I learned to stop worrying and love de Bruijn indices](http://disciple-devel.blogspot.com.au/2011/08/how-i-learned-to-stop-worrying-and-love.html)
//! - [The Locally Nameless Representation](https://www.chargueraud.org/research/2009/ln/main.pdf)
//! - [Locally nameless representation with cofinite quantification](http://www.chargueraud.org/softs/ln/)
//! - [A Locally-nameless Backend for Ott](http://www.di.ens.fr/~zappa/projects/ln_ott/)
//! - [Library STLC_Tutorial](https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/coqdoc/STLC_Tutorial.html)
//!
//! ## Libraries
//!
//! There are a number of libraries out there for other languages that abstract
//! away the error-prone tedium handling locally nameless representations, but
//! I've not yet figured out how to port them to Rust yet:
//!
//! - DBLib: Facilities for working with de Bruijn indices in Coq
//!     - [Blog Post](http://gallium.inria.fr/blog/announcing-dblib/)
//!     - [Github](https://github.com/coq-contribs/dblib)
//! - Unbound: Specify the binding structure of your data type with an
//!   expressive set of type combinators, and Unbound handles the rest!
//!   Automatically derives alpha-equivalence, free variable calculation,
//!   capture-avoiding substitution, and more.
//!     - [Github](https://github.com/sweirich/replib)
//!     - [Hackage](https://hackage.haskell.org/package/unbound)
//! - Unbound-Generics: an independent re-implementation of Unbound but using
//!   GHC.Generics instead of RepLib.
//!     - [Github](http://github.com/lambdageek/unbound-generics)
//!     - [Hackage](https://hackage.haskell.org/package/unbound-generics)
//! - Bound: Bruijn indices for Haskell
//!     - [Blog Post](https://www.schoolofhaskell.com/user/edwardk/bound)
//!     - [Github](https://github.com/ekmett/bound/)
//!     - [Hackage](https://hackage.haskell.org/package/bound)
//! - The Penn Locally Nameless Metatheory Library
//!     - [Github](https://github.com/plclub/metalib)

use std::fmt;

/// Locally nameless terms
pub trait LocallyNameless: Sized {
    /// Capture some free variables in the term
    fn close(&mut self, on_free: &Fn(&Name) -> Option<Debruijn>);

    fn open(&mut self, on_bound: &Fn(&Debruijn) -> Option<Name>);

    fn subst(&self);
}

impl LocallyNameless for () {
    fn close(&mut self, _: &Fn(&Name) -> Option<Debruijn>) {}
    fn open(&mut self, _: &Fn(&Debruijn) -> Option<Name>) {}
    fn subst(&self) {}
}

impl<T: LocallyNameless> LocallyNameless for Option<T> {
    fn close(&mut self, on_free: &Fn(&Name) -> Option<Debruijn>) {
        if let Some(ref mut x) = *self {
            x.close(on_free);
        }
    }

    fn open(&mut self, on_bound: &Fn(&Debruijn) -> Option<Name>) {
        if let Some(ref mut x) = *self {
            x.open(on_bound);
        }
    }

    fn subst(&self) {
        unimplemented!()
    }
}

/// Locally nameless patterns
pub trait Pattern: LocallyNameless {
    fn handle_free(&self, level: Debruijn, name: &Name) -> Option<Debruijn>;
    fn freshen(&mut self, gen: &mut FreshGen);
}

/// The name of a free variable
#[derive(Debug, Clone)]
pub enum Name {
    /// Names originating from user input
    User(String),
    /// A variable that was generated from a fresh name generator
    Gen(GenId),
    /// Abstract names, `_`
    ///
    /// These are generally used in non-dependent function types, ie:
    ///
    /// ```text
    /// t1 -> t2 -> t3
    /// ```
    ///
    /// will be stored as:
    ///
    /// ```text
    /// (_ : t1) -> (_ : t2) -> t3
    /// ```
    ///
    /// They should never actually appear as variables in terms.
    ///
    /// Comparing two abstract names will always return false because we cannot
    /// be sure what they actually refer to. For example, in the type
    /// shown above, `_` could refer to either `t1` or `t2`.
    Abstract,
}

impl Name {
    pub fn user<S: Into<String>>(name: S) -> Name {
        Name::User(name.into())
    }
}

impl PartialEq for Name {
    fn eq(&self, other: &Name) -> bool {
        match (self, other) {
            (&Name::User(ref lhs), &Name::User(ref rhs)) => lhs == rhs,
            (&Name::Abstract, &Name::Abstract) | (_, _) => false,
        }
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Name::User(ref name) => write!(f, "{}", name),
            Name::Gen(ref id) => write!(f, "{}", id),
            Name::Abstract => write!(f, "_"),
        }
    }
}

pub struct FreshGen {
    next_gen: u32,
}

impl FreshGen {
    pub fn new() -> FreshGen {
        FreshGen { next_gen: 0 }
    }

    pub fn next_gen(&mut self) -> GenId {
        let next_gen = self.next_gen;
        self.next_gen += 1;
        GenId(next_gen)
    }
}

/// A generated id
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct GenId(u32);

impl fmt::Display for GenId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "${}", self.0)
    }
}

/// A type annotated with a name for debugging purposes
///
/// The name is ignored for equality comparisons
#[derive(Debug, Clone)]
pub struct Named<T>(pub Name, pub T);

impl<T: PartialEq> PartialEq for Named<T> {
    fn eq(&self, other: &Named<T>) -> bool {
        &self.1 == &other.1
    }
}

impl<T: LocallyNameless> LocallyNameless for Named<T> {
    fn close(&mut self, on_free: &Fn(&Name) -> Option<Debruijn>) {
        self.1.close(on_free);
    }

    fn open(&mut self, on_bound: &Fn(&Debruijn) -> Option<Name>) {
        self.1.open(on_bound);
    }

    fn subst(&self) {
        unimplemented!()
    }
}

impl<T: LocallyNameless> Pattern for Named<T> {
    fn handle_free(&self, level: Debruijn, name: &Name) -> Option<Debruijn> {
        if &self.0 == name {
            Some(level)
        } else {
            None
        }
    }

    fn freshen(&mut self, gen: &mut FreshGen) {
        unimplemented!()
    }
}

/// The [debruijn index] of the binder that introduced the variable
///
/// For example:
///
/// ```text
/// λx.∀y.λz. x z (y z)
/// λ  ∀  λ   2 0 (1 0)
/// ```
///
/// [debruijn index]: https://en.wikipedia.org/wiki/De_Bruijn_index
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct Debruijn(pub u32);

impl Debruijn {
    /// The debruijn index of the current binder
    pub const ZERO: Debruijn = Debruijn(0);

    /// Move the current debruijn index into an inner binder
    pub fn succ(self) -> Debruijn {
        Debruijn(self.0 + 1)
    }

    pub fn pred(self) -> Option<Debruijn> {
        match self {
            Debruijn::ZERO => None,
            Debruijn(i) => Some(Debruijn(i - 1)),
        }
    }
}

impl fmt::Display for Debruijn {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A variable that can either be free or bound
#[derive(Debug, Clone, PartialEq)]
pub enum Var {
    /// A free variable
    Free(Name),
    /// A variable that is bound by a lambda or pi binder
    Bound(Named<Debruijn>),
}

impl LocallyNameless for Var {
    fn close(&mut self, on_free: &Fn(&Name) -> Option<Debruijn>) {
        *self = match *self {
            Var::Bound(_) => return,
            Var::Free(ref name) => match on_free(name) {
                None => return,
                Some(level) => Var::Bound(Named(name.clone(), level)),
            },
        };
    }

    fn open(&mut self, on_bound: &Fn(&Debruijn) -> Option<Name>) {
        *self = match *self {
            Var::Bound(ref bound) => match on_bound(&bound.1) {
                None => return,
                Some(name) => Var::Free(name),
            },
            Var::Free(_) => return,
        };
    }

    fn subst(&self) {
        unimplemented!()
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Var::Bound(Named(ref name, ref b)) if f.alternate() => write!(f, "{}#{}", name, b),
            Var::Bound(Named(ref name, _)) | Var::Free(ref name) => write!(f, "{}", name),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Scope<P, T> {
    pub unsafe_param: P,
    pub unsafe_body: T,
}

impl<P: Pattern, T: LocallyNameless> Scope<P, T> {
    pub fn bind(param: P, mut body: T) -> Scope<P, T> {
        body.close(&|found| param.handle_free(Debruijn::ZERO, found));
        Scope {
            unsafe_param: param,
            unsafe_body: body,
        }
    }

    pub fn unbind(self, gen: &mut FreshGen) -> (P, T) {
        let mut param = self.unsafe_param;
        let mut body = self.unsafe_body;

        param.freshen(gen);
        body.open(&|index| param.handle_bound(Debruijn::ZERO, index));

        (param, body)
    }
}

impl<P: Pattern, T: LocallyNameless> LocallyNameless for Scope<P, T> {
    fn close(&mut self, on_free: &Fn(&Name) -> Option<Debruijn>) {
        self.unsafe_param.close(on_free);
        self.unsafe_body
            .close(&|name| on_free(name).map(|var| var.succ()));
    }

    fn open(&mut self, on_bound: &Fn(&Debruijn) -> Option<Name>) {
        self.unsafe_param.open(on_bound);
        self.unsafe_body.open(&|var| on_bound(&var.succ()));
    }

    fn subst(&self) {
        unimplemented!()
    }
}
