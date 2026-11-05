use crate::context::Context;
use crate::error::Result;
use crate::lang::ProofStep;
use crate::lang::{Db, Display};
use crate::parser::{Parse, Parser};
use crate::tactics::Tactics;
use crate::tactics::TacticsResult;
use core::fmt::Formatter;

/// A tactics which leaves the goal for deciders to prove, by name: `{ decide ring-eval }`.
///
/// The goal is returned as an open goal tagged with the names, in both modes. A stepwise
/// request hands it back to the caller with its tags; a batch proof which contains one is
/// not complete, and fails as such.
#[derive(Debug)]
pub struct Decide {
    names: Vec<String>,
}

impl Parse for Decide {
    fn parse(parser: &mut Parser) -> Result<Self> {
        let mut names = Vec::new();
        while let Some(name) = parser.parse_optional_identifier()? {
            names.push(name);
        }
        Ok(Decide { names })
    }
}

impl Display for Decide {
    fn format(&self, fmt: &mut Formatter, _db: &Db) -> std::result::Result<(), std::fmt::Error> {
        fmt.write_str("{ decide")?;
        for name in &self.names {
            fmt.write_str(" ")?;
            fmt.write_str(name)?;
        }
        fmt.write_str(" }")
    }
}

impl Tactics for Decide {
    fn get_name(&self) -> String {
        "decide".to_string()
    }

    fn get_desc(&self) -> String {
        "Leaves the goal open, tagged with the names of the deciders which may prove it.".to_string()
    }

    fn execute(&self, context: &mut Context) -> TacticsResult {
        context.enter(&format!("Decide {}", self.names.join(" ")));
        context.exit("Left open");
        Ok(ProofStep::open(context.goal().clone(), Some(self.names.clone())))
    }
}
