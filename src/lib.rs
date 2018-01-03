extern crate lalrpop_util;
#[cfg(test)]
#[macro_use]
extern crate pretty_assertions;

use std::fmt;

pub mod core;
pub mod check;
pub mod parse;
pub mod var;

#[derive(Debug)]
pub struct Derivation {
    judgement: &'static str,
    rule: &'static str,
    conclusion: String,
    premises: Vec<Derivation>,
}

impl<'a> fmt::Display for Derivation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        #[derive(Copy, Clone)]
        struct Indent(usize);

        impl Indent {
            const WIDTH: usize = 4;

            fn bump(self) -> Indent {
                Indent(self.0 + 1)
            }
        }

        impl fmt::Display for Indent {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                for _ in 0..(self.0 * Indent::WIDTH) {
                    write!(f, " ")?;
                }
                Ok(())
            }
        }

        fn fmt_inner(indent: Indent, d: &Derivation, f: &mut fmt::Formatter) -> fmt::Result {
            let judgement_len = d.judgement.chars().count();
            let rule_len = d.rule.chars().count();
            let conclusion_len = d.conclusion.chars().count();

            let hr_width = std::cmp::max(judgement_len + rule_len + 1, conclusion_len) + 2;

            writeln!(f, "{} {}/{}", indent, d.judgement, d.rule)?;

            write!(f, "{}", indent)?;
            for _ in 0..hr_width {
                write!(f, "╶")?;
            }
            writeln!(f)?;

            writeln!(f, "{} {}", indent, d.conclusion)?;
            writeln!(f)?;

            for p in &d.premises {
                fmt_inner(indent.bump(), p, f)?;
            }

            Ok(())
        }

        fmt_inner(Indent(0), self, f)
    }
}
