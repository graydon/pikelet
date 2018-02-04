//! Parser utilities

use lalrpop_util::ParseError as LalrpopError;
use std::str::FromStr;

use syntax::concrete;

mod grammar {
    include!(concat!(env!("OUT_DIR"), "/syntax/parse/grammar.rs"));
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError(pub String);

impl FromStr for concrete::ReplCommand {
    type Err = ParseError;

    fn from_str(src: &str) -> Result<concrete::ReplCommand, ParseError> {
        grammar::parse_ReplCommand(src).map_err(|e| ParseError(format!("{}", e)))
    }
}

impl FromStr for concrete::Module {
    type Err = ParseError;

    fn from_str(src: &str) -> Result<concrete::Module, ParseError> {
        grammar::parse_Module(src).map_err(|e| ParseError(format!("{}", e)))
    }
}

impl FromStr for concrete::Declaration {
    type Err = ParseError;

    fn from_str(src: &str) -> Result<concrete::Declaration, ParseError> {
        grammar::parse_Declaration(src).map_err(|e| ParseError(format!("{}", e)))
    }
}

impl FromStr for concrete::Term {
    type Err = ParseError;

    fn from_str(src: &str) -> Result<concrete::Term, ParseError> {
        grammar::parse_Term(src).map_err(|e| ParseError(format!("{}", e)))
    }
}

fn build_pi_type<T>(
    binders: concrete::Term,
    body: concrete::Term,
) -> Result<concrete::Term, LalrpopError<usize, T, &'static str>> {
    use syntax::concrete::Term;

    match binders {
        // single binder
        Term::Parens(term) => {
            let term = *term; // HACK: see https://github.com/rust-lang/rust/issues/16223
            match term {
                Term::Ann(name, ann) => match *name {
                    Term::Var(name) => Ok(Term::Pi(vec![(vec![name], ann)], Box::new(body))),
                    Term::App(name, rest) => unimplemented!(),
                    _ => Err(LalrpopError::User {
                        error: "identifier expected in pi type", // TODO: better error!
                    }),
                },
                ann => Ok(Term::Arrow(
                    Box::new(Term::Parens(Box::new(ann))),
                    Box::new(body),
                )),
            }
        },
        Term::App(binders, arg) => {
            let binders = *binders;
            match binders {
                Term::Parens(term) => {
                    let term = *term; // HACK: see https://github.com/rust-lang/rust/issues/16223
                    match term {
                        Term::Ann(name, ann) => match *name {
                            Term::Var(name) => {
                                Ok(Term::Pi(vec![(vec![name], ann)], Box::new(body)))
                            },
                            Term::App(name, rest) => unimplemented!(),
                            _ => Err(LalrpopError::User {
                                error: "identifier expected in pi type", // TODO: better error!
                            }),
                        },
                        ann => Ok(Term::Arrow(
                            Box::new(Term::Parens(Box::new(ann))),
                            Box::new(body),
                        )),
                    }
                },
            }
        },
        ann => Ok(Term::Arrow(Box::new(ann), Box::new(body))),
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use super::*;

    #[test]
    fn pi_bad_ident() {
        let parse_result = concrete::Term::from_str("((x : Type) : Type) -> Type");

        assert_eq!(
            parse_result,
            Err(ParseError(String::from("identifier expected in pi type"))),
        );
    }
}
