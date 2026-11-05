//! A Metamath Proof Assistant: the library behind the `rumm` command.
//!
//! [`Engine`] holds a loaded database and proves theorems from tactics libraries, returning
//! structured results and printing nothing; the trace of the search goes to the
//! [`TraceSink`] the caller passes, if any. [`serve`] speaks the JSON-lines protocol of
//! `PROTOCOL.md` over any reader and writer.

pub mod context;
pub mod error;
pub mod lang;
pub mod parser;
pub mod script;
pub mod serve;
pub mod tactics;

pub use context::{TraceSink, DEFAULT_MAX_DEPTH};
pub use script::{Failure, Proof, ProofLine, Script};

use error::Result;
use lang::{Db, TacticsExpression};
use metamath_rs::Label;
use parser::{Parse, Parser};
use std::fs;
use std::panic::{catch_unwind, AssertUnwindSafe};

/// Stack size of the thread which proves. Tactics nest as deep as the depth budget allows,
/// and each level uses several Rust stack frames.
pub const STACK_SIZE: usize = 256 << 20;

/// The tactics library of a request: a file, or its text.
#[derive(Debug, Clone, PartialEq)]
pub enum Library {
    Path(String),
    Text(String),
}

/// A request to prove one theorem.
#[derive(Debug, Clone, PartialEq)]
pub struct ProveRequest {
    pub library: Library,
    /// The label of the theorem, without `~`.
    pub theorem: String,
    /// A tactics expression in `.rmm` syntax (`{ apply ~ax-mp ! ! }`); by default, the
    /// library's own proof line for the theorem.
    pub tactic: Option<String>,
    /// Overrides the engine's depth budget for this request.
    pub max_depth: Option<usize>,
}

/// What came of a [`ProveRequest`].
#[derive(Debug, Clone, PartialEq)]
pub struct ProveOutcome {
    pub proof: std::result::Result<Proof, Failure>,
    /// E.g. a `load` directive of the library which was ignored.
    pub warnings: Vec<String>,
}

/// A database, loaded once, which proves theorems. It keeps nothing else between calls.
pub struct Engine {
    db: Db,
    loads: usize,
    /// The depth budget of requests which don't set their own.
    pub max_depth: usize,
}

impl Engine {
    /// Loads the plain Metamath database `path` (silently).
    pub fn load(path: &str) -> Result<Engine> {
        let mut db = Db::default();
        db.set_verbose(false);
        db.parse(path)?;
        Ok(Engine { db, loads: 1, max_depth: DEFAULT_MAX_DEPTH })
    }

    /// How many times this engine loaded a database.
    pub fn loads(&self) -> usize {
        self.loads
    }

    /// Proves the theorem of the request. Never panics and never prints: a panic while
    /// proving is a failure of kind `panic`.
    pub fn prove(&mut self, request: &ProveRequest, trace: Option<TraceSink>) -> ProveOutcome {
        let mut warnings = Vec::new();
        let proof = catch_unwind(AssertUnwindSafe(|| self.try_prove(request, trace, &mut warnings)))
            .unwrap_or_else(|panic| Err(Failure::from_panic(panic)));
        ProveOutcome { proof, warnings }
    }

    fn try_prove(
        &mut self,
        request: &ProveRequest,
        trace: Option<TraceSink>,
        warnings: &mut Vec<String>,
    ) -> std::result::Result<Proof, Failure> {
        let (name, text) = match &request.library {
            Library::Path(path) => {
                let text = fs::read_to_string(path)
                    .map_err(|e| Failure::new("library-file", format!("Cannot read {}: {}", path, e)))?;
                (path.clone(), text)
            }
            Library::Text(text) => ("<library_text>".to_string(), text.clone()),
        };
        let mut parser = Parser::with_db(name, &text, self.db.clone(), true)
            .map_err(|e| Failure::new("library-parse", e.describe()))?;
        let script = Script::parse(&mut parser).map_err(|e| Failure::new("library-parse", e.describe()))?;
        warnings.extend(parser.warnings.iter().cloned());
        let theorem: Label = self
            .db
            .get_theorem_label(request.theorem.clone())
            .ok_or_else(|| Failure::new("unknown-theorem", format!("Unknown theorem {}", request.theorem)))?;
        let own;
        let tactics: &TacticsExpression = match &request.tactic {
            Some(tactic_text) => {
                let mut parser = Parser::with_db("<tactic>".to_string(), tactic_text, self.db.clone(), true)
                    .map_err(|e| Failure::new("tactic-parse", e.describe()))?;
                own = parser.parse_tactics().map_err(|e| Failure::new("tactic-parse", e.describe()))?;
                &own
            }
            None => script.proof_line(theorem).ok_or_else(|| {
                Failure::new("no-proof", format!("The library has no proof line for {}, and the request no tactic", request.theorem))
            })?,
        };
        script.prove(theorem, tactics, trace, request.max_depth.unwrap_or(self.max_depth))
    }
}
