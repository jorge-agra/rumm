use crate::error::Result;
use crate::lang::{Db, Display};
use crate::lang::{prove_theorem, TacticsExpression, ProofDefinition, TacticsDefinition, TacticsDict};
use crate::parser::{Parse, Parser};
use crate::tactics::TacticsError;
use crate::context::{DEFAULT_MAX_DEPTH, TraceSink};
use core::fmt::{Debug, Formatter};
use metamath_rs::Label;
use serde::Serialize;
use std::any::Any;
use std::collections::BTreeSet;
use std::sync::Arc;
use std::panic::{catch_unwind, AssertUnwindSafe};

pub struct Script {
    pub(crate) db: Db,
    pub(crate) tactics_definitions: TacticsDict,
    pub(crate) proof_definitions: Vec<ProofDefinition>,
    /// Limit on the nesting depth of tactics, see `Context::check_depth`.
    pub max_depth: usize,
    /// What the parser noticed without failing (e.g. a `load` it skipped).
    pub warnings: Vec<String>,
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
            warnings: Vec::new(),
        }
    }

    pub fn from_str(filename: String, str: &str) -> Result<Self> {
        Script::parse(&mut Parser::from_str(filename, str))
    }

    /// Proves each proof of the script, printing the trace, then `Success` and the proof as
    /// an `.mmp` worksheet or `Failure: ...`, on stdout (the batch command line).
    pub fn execute(&mut self) -> Result {
        let trace: TraceSink = Arc::new(|line: &str| println!("{}", line));
        for proof_def in &self.proof_definitions {
            match self.run_proof(proof_def.theorem(), proof_def.tactics(), Some(trace.clone()), self.max_depth) {
                Ok((mmp, _)) => {
                    println!("Success");
                    print!("{}", mmp);
                }
                Err(failure) => println!("Failure: {}", failure.message),
            }
        }
        Ok(())
    }

    /// The `tactics` expression of the first proof the script gives for `theorem`.
    pub fn proof_line(&self, theorem: Label) -> Option<&TacticsExpression> {
        self.proof_definitions.iter().find(|p| p.theorem() == theorem).map(|p| p.tactics())
    }

    /// The database of the script.
    pub fn db(&self) -> &Db {
        &self.db
    }

    /// Proves `theorem` with `tactics` (using this script's tactics definitions), and gives the
    /// proof as a structured result. Nothing is printed; the trace goes to `trace`.
    /// A panic while proving or exporting is reported as a failure.
    pub fn prove(&self, theorem: Label, tactics: &TacticsExpression, trace: Option<TraceSink>, max_depth: usize) -> std::result::Result<Proof, Failure> {
        let (mmp, distinct) = self.run_proof(theorem, tactics, trace, max_depth)?;
        Ok(Proof::from_mmp(self.db.label_name(theorem), &mmp, &distinct))
    }

    /// The `.mmp` text of a proof, with the `$d` it needs.
    fn run_proof(
        &self,
        theorem: Label,
        tactics: &TacticsExpression,
        trace: Option<TraceSink>,
        max_depth: usize,
    ) -> std::result::Result<(String, BTreeSet<(String, String)>), Failure> {
        // A panic while proving or exporting one proof (e.g. an unbound work variable)
        // is reported as that proof's failure, and the next proofs still run.
        let outcome = catch_unwind(AssertUnwindSafe(|| {
            prove_theorem(theorem, tactics, self.db.clone(), self.tactics_definitions.clone(), max_depth, trace)
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
                    let distinct = step.distinct_variables(&self.db, Some(theorem))?;
                    Ok((step, distinct))
                })
                .map(|(step, distinct)| {
                    let mut arr = step.as_proof_tree_array(self.db.clone());
                    arr.calc_indent();
                    let mut mmp = Vec::new();
                    self.db.export_mmp(theorem, &distinct, &arr, &mut mmp);
                    (String::from_utf8_lossy(&mmp).into_owned(), distinct)
                })
        }));
        match outcome {
            Ok(Ok(done)) => Ok(done),
            Ok(Err(error)) => Err(Failure::from_tactics_error(&error)),
            Err(panic) => Err(Failure::from_panic(panic)),
        }
    }
}

/// Why a request or a proof failed: a `kind` to branch on and a `message` to show.
#[derive(Debug, Clone, Serialize, PartialEq)]
pub struct Failure {
    pub kind: String,
    pub message: String,
}

impl Failure {
    pub fn new(kind: &str, message: impl Into<String>) -> Self {
        Failure { kind: kind.to_string(), message: message.into() }
    }

    /// The kind is the name of the `TacticsError` variant in kebab-case (`no-match-found`), the
    /// message its debug text.
    fn from_tactics_error(error: &TacticsError) -> Self {
        let message = format!("{:?}", error);
        let variant = message.split(|c| c == '(' || c == ' ').next().unwrap_or("");
        let mut kind = String::new();
        for (i, c) in variant.chars().enumerate() {
            if c.is_ascii_uppercase() {
                if i > 0 {
                    kind.push('-');
                }
                kind.push(c.to_ascii_lowercase());
            } else {
                kind.push(c);
            }
        }
        Failure { kind, message }
    }

    pub fn from_panic(panic: Box<dyn Any + Send>) -> Self {
        let reason = panic
            .downcast_ref::<String>()
            .map(|s| s.as_str())
            .or_else(|| panic.downcast_ref::<&str>().copied())
            .unwrap_or("unknown panic");
        Failure::new("panic", format!("panic: {}", reason))
    }
}

/// One step of a proof, as in an `.mmp` worksheet: `<label>:<hyps>:<ref> <expr>`.
#[derive(Debug, Clone, Serialize, PartialEq)]
pub struct ProofLine {
    /// `h1`, `h2`... for the hypotheses of the theorem, `s1`, `s2`... then `qed` for the others.
    pub label: String,
    /// The steps this one cites as hypotheses, in order: a derived step by its label (`s3`), a
    /// hypothesis step by its number (`3` for `h3`), as in mmj2 `.mmp` syntax.
    pub hyps: Vec<String>,
    /// The database statement the step cites: the `$e` label for a hypothesis step.
    #[serde(rename = "ref")]
    pub reference: String,
    /// The statement, with its typecode (`|- ...`).
    pub expr: String,
}

/// A complete proof: its steps (each after the steps it cites) and the `$d` it needs.
#[derive(Debug, Clone, Serialize, PartialEq)]
pub struct Proof {
    pub theorem: String,
    pub steps: Vec<ProofLine>,
    pub dv: Vec<(String, String)>,
}

impl Proof {
    /// Reads the steps of the `.mmp` worksheet `export_mmp` writes: the lines before the blank
    /// line, `<name>:<hyp numbers>:<label> <expr>`. Hypotheses keep the `h<n>` of the worksheet,
    /// the other steps `<n>` become `s<n>`, the conclusion stays `qed`.
    fn from_mmp(theorem: String, mmp: &str, distinct: &BTreeSet<(String, String)>) -> Proof {
        let mut steps = Vec::new();
        for line in mmp.lines().filter(|l| !l.starts_with("$d ")).take_while(|l| !l.trim().is_empty()) {
            let mut parts = line.splitn(3, ':');
            let (name, hyps, rest) = (parts.next().unwrap_or(""), parts.next().unwrap_or(""), parts.next().unwrap_or(""));
            let (reference, expr) = match rest.split_once(char::is_whitespace) {
                Some((reference, expr)) => (reference, expr.trim()),
                None => (rest, ""),
            };
            steps.push((name.to_string(), hyps.split(',').filter(|h| !h.is_empty()).map(str::to_string).collect::<Vec<_>>(), reference.to_string(), expr.to_string()));
        }
        // Numbers in the worksheet are shared between hypothesis steps (`h<n>`) and the others.
        let label_of = |number: &str, steps: &[(String, Vec<String>, String, String)]| -> String {
            steps
                .iter()
                .map(|(name, ..)| name)
                .find(|name| name.as_str() == number || name.as_str() == format!("h{}", number))
                // mmj2 syntax: a hypothesis step `h3` is cited by its number, `3`.
                .map(|name| if name.starts_with('h') { number.to_string() } else { Self::rename(name) })
                .unwrap_or_else(|| format!("s{}", number))
        };
        let snapshot = steps.clone();
        let steps = steps
            .into_iter()
            .map(|(name, hyps, reference, expr)| ProofLine {
                label: Self::rename(&name),
                hyps: hyps.iter().map(|h| label_of(h, &snapshot)).collect(),
                reference,
                expr,
            })
            .collect();
        Proof { theorem, steps, dv: distinct.iter().cloned().collect() }
    }

    fn rename(name: &str) -> String {
        if name == "qed" || name.starts_with('h') { name.to_string() } else { format!("s{}", name) }
    }
}
