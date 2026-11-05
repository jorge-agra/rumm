use crate::lang::TacticsExpression;
use crate::context::{Context, TraceSink};
use crate::error::Result;
use crate::lang::TacticsDict;
use crate::lang::{Db, Display};
use crate::parser::{Parse, Parser};
use crate::tactics::TacticsError;
use core::fmt::Formatter;
use std::collections::BTreeSet;
use metamath_rs::formula::Substitutions;
use metamath_rs::proof::ProofTreeArray;
use metamath_rs::Formula;
use metamath_rs::Label;

#[derive(Clone)]
/// One step in a proof
pub enum ProofStep {
	Apply {
	    apply: Label,
	    apply_on: Box<[ProofStep]>,
	    result: Formula,
	    substitutions: Box<Substitutions>,
	},
	Hyp {
		label: Label,
		result: Formula,
	},
}

impl ProofStep {
    pub fn apply(
        apply: Label,
        apply_on: Box<[ProofStep]>,
        result: Formula,
        substitutions: Box<Substitutions>,
    ) -> Self {
        ProofStep::Apply {
            apply,
            apply_on,
            result,
            substitutions,
        }
    }

    pub fn hyp(label: Label, result: Formula) -> Self {
    	ProofStep::Hyp { label, result }
    }

    pub fn result(&self) -> &Formula {
        match self {
            ProofStep::Apply { result: r, .. } => r,
            ProofStep::Hyp { result: r, .. } => r,
        }
    }

    fn add_to_proof_tree_array(
        &self,
        stack_buffer: &mut Vec<u8>,
        arr: &mut ProofTreeArray,
        db: Db,
    ) -> Option<usize> {
    	match self {
    		ProofStep::Apply { apply, apply_on, result, substitutions } => {
		        let hyps = apply_on
		            .iter()
		            .map(|step| step.add_to_proof_tree_array(stack_buffer, arr, db.clone()))
		            .flatten()
		            .collect();
		        db.build_proof_step(
		            *apply,
		            result.clone(),
		            hyps,
		            &substitutions,
		            stack_buffer,
		            arr,
		        )
    		},
    		ProofStep::Hyp { label, result } => {
                db.build_proof_hyp(
                    *label,
                    result.clone(),
                    stack_buffer,
                    arr,
                )
    		},
    	}
    }

    /// The metavariables left in the finished proof, in its conclusions and in the
    /// substitutions of its citations. A proof which has some is not complete.
    pub fn unresolved_metavariables(&self, db: &Db) -> BTreeSet<String> {
        let mut found = BTreeSet::new();
        self.collect_metavariables(db, &mut found);
        found
    }

    fn collect_metavariables(&self, db: &Db, found: &mut BTreeSet<String>) {
        db.metavariables_in(self.result(), found);
        if let ProofStep::Apply { apply_on, substitutions, .. } = self {
            for (_, formula) in substitutions.iter() {
                db.metavariables_in(formula, found);
            }
            for step in apply_on.iter() {
                step.collect_metavariables(db, found);
            }
        }
    }

    /// Checks the `$d` constraints of every citation of the proof against the frame of
    /// `theorem`, which the substitutions of the finished proof allow to settle, and returns
    /// the `$d` the proof needs, as pairs of variable names.
    pub fn distinct_variables(&self, db: &Db, theorem: Option<Label>) -> std::result::Result<BTreeSet<(String, String)>, TacticsError> {
        let mut needed = BTreeSet::new();
        self.collect_distinct_variables(db, theorem, &Substitutions::new(), &mut needed)?;
        Ok(needed)
    }

    fn collect_distinct_variables(
        &self,
        db: &Db,
        theorem: Option<Label>,
        bindings: &Substitutions,
        needed: &mut BTreeSet<(String, String)>,
    ) -> std::result::Result<(), TacticsError> {
        if let ProofStep::Apply { apply, apply_on, substitutions, .. } = self {
            db.check_distinct(theorem, *apply, substitutions, bindings, needed)?;
            for step in apply_on.iter() {
                step.collect_distinct_variables(db, theorem, bindings, needed)?;
            }
        }
        Ok(())
    }

    pub fn as_proof_tree_array(&self, db: Db) -> ProofTreeArray {
        let mut arr = ProofTreeArray::default();
        let mut stack_buffer = vec![];
        arr.qed = self
            .add_to_proof_tree_array(&mut stack_buffer, &mut arr, db)
            .unwrap();
        arr
    }
}

pub struct ProofDefinition {
    theorem: Label,
    tactics: TacticsExpression,
}

impl Display for ProofDefinition {
    fn format(&self, fmt: &mut Formatter, db: &Db) -> std::result::Result<(), std::fmt::Error> {
        fmt.write_str("proof ")?;
        self.theorem.format(fmt, db)?;
        self.tactics.format(fmt, db)
    }
}

impl Parse for ProofDefinition {
    fn parse(parser: &mut Parser) -> Result<Self> {
        let theorem = parser.parse_theorem_label()?;
        let tactics = parser.parse_tactics()?;
        Ok(ProofDefinition { theorem, tactics })
    }
}

impl ProofDefinition {
    pub fn prove(&self, db: Db, tactics_definitions: TacticsDict, max_depth: usize, trace: Option<TraceSink>) -> std::result::Result<ProofStep, TacticsError> {
        prove_theorem(self.theorem, &self.tactics, db, tactics_definitions, max_depth, trace)
    }

    pub fn theorem(&self) -> Label {
        self.theorem
    }

    pub fn tactics(&self) -> &TacticsExpression {
        &self.tactics
    }
}

/// Runs `tactics` on the statement of `theorem`, with its essential hypotheses.
pub fn prove_theorem(
    theorem: Label,
    tactics: &TacticsExpression,
    db: Db,
    tactics_definitions: TacticsDict,
    max_depth: usize,
    trace: Option<TraceSink>,
) -> std::result::Result<ProofStep, TacticsError> {
    let say = |text: String| {
        if let Some(trace) = &trace {
            trace(&text);
        }
    };
    if let Some((theorem_formula, essential_hypotheses)) = db.get_theorem_formulas(theorem) {
        say("====================================================\n\n".to_string());
        say(format!("Proof for {:?}:", theorem.to_string(&db)));
        let mut context =
            Context::new(db.clone(), theorem_formula, Some(theorem), essential_hypotheses, tactics_definitions, max_depth, trace.clone());
        tactics.execute(&mut context)
    } else {
        say(format!("Unknown theorem {:?}!", theorem));
        Err(TacticsError::UnknownLabel(theorem))
    }
}
