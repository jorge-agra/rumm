use crate::error::Result;
use crate::lang::{Db, Display};
use crate::lang::{ProofDefinition, TacticsDefinition, TacticsDict};
use crate::parser::{Parse, Parser};
use crate::tactics::TacticsError;
use crate::context::DEFAULT_MAX_DEPTH;
use core::fmt::{Debug, Formatter};
use std::panic::{catch_unwind, AssertUnwindSafe};

pub struct Script {
    pub(crate) db: Db,
    pub(crate) tactics_definitions: TacticsDict,
    pub(crate) proof_definitions: Vec<ProofDefinition>,
    /// Limit on the nesting depth of tactics, see `Context::check_depth`.
    pub max_depth: usize,
}

impl Debug for Script {
    fn fmt(&self, fmt: &mut Formatter) -> std::result::Result<(), std::fmt::Error> {
        fmt.write_str("Script {")?;
        fmt.write_str("tactics_definitions: [")?;
        self.tactics_definitions.format(fmt, &self.db)?;
        fmt.write_str("]\n")?;
        fmt.write_str("proofs_definitions: [")?;
        for p in &self.proof_definitions {
            p.format(fmt, &self.db)?;
        }
        fmt.write_str("]\n")?;
        fmt.write_str("}\n")
    }
}

impl Parse for Script {
    fn parse(parser: &mut Parser) -> Result<Self> {
        parser.parse_script()
    }
}

impl Script {
    pub fn new(
        db: Db,
        tactics_list: Vec<TacticsDefinition>,
        proof_definitions: Vec<ProofDefinition>,
    ) -> Self {
        Script {
            db,
            tactics_definitions: TacticsDict::from(tactics_list),
            proof_definitions,
            max_depth: DEFAULT_MAX_DEPTH,
        }
    }

    pub fn from_str(filename: String, str: &str) -> Result<Self> {
        Script::parse(&mut Parser::from_str(filename, str))
    }

    pub fn execute(&mut self) -> Result {
        for proof_def in &self.proof_definitions {
            // A panic while proving or exporting one proof (e.g. an unbound work variable)
            // is reported as that proof's failure, and the next proofs still run.
            let outcome = catch_unwind(AssertUnwindSafe(|| {
                proof_def
                    .prove(self.db.clone(), self.tactics_definitions.clone(), self.max_depth)
                    .and_then(|step| {
                        // A proof with a metavariable left is not complete.
                        let unresolved = step.unresolved_metavariables(&self.db);
                        if !unresolved.is_empty() {
                            return Err(TacticsError::UnresolvedMetavariables(
                                unresolved.into_iter().collect::<Vec<_>>().join(" "),
                            ));
                        }
                        // The citations are checked again on the finished proof, whose
                        // substitutions are settled; this also gives the `$d` it needs.
                        let distinct = step.distinct_variables(&self.db, Some(proof_def.theorem()))?;
                        Ok((step, distinct))
                    })
                    .map(|(step, distinct)| {
                        let mut arr = step.as_proof_tree_array(self.db.clone());
                        arr.calc_indent();
                        let mut mmp = Vec::new();
                        self.db.export_mmp(proof_def.theorem(), &distinct, &arr, &mut mmp);
                        String::from_utf8_lossy(&mmp).into_owned()
                    })
            }));
            match outcome {
                Ok(Ok(mmp)) => {
                    println!("Success");
                    print!("{}", mmp);
                }
                Ok(Err(error)) => {
                    println!("Failure: {:?}", error);
                }
                Err(panic) => {
                    let reason = panic
                        .downcast_ref::<String>()
                        .map(|s| s.as_str())
                        .or_else(|| panic.downcast_ref::<&str>().copied())
                        .unwrap_or("unknown panic");
                    println!("Failure: panic: {}", reason);
                }
            }
        }
        Ok(())
    }
}
