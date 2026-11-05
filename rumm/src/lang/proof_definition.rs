use crate::lang::TacticsExpression;
use crate::context::{Context, TraceSink};
use crate::error::Result;
use crate::lang::TacticsDict;
use crate::lang::{compose_bindings, Db, Display};
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
        /// The work variables the citation bound (stepwise mode; empty in batch).
        bindings: Box<Substitutions>,
    },
    Hyp {
        label: Label,
        result: Formula,
        /// The work variables matching the hypothesis bound (stepwise mode).
        bindings: Box<Substitutions>,
    },
    /// A goal left open (stepwise mode, or `decide`): nothing proves it yet. `deciders`
    /// are the names a `{ decide ... }` tagged it with.
    Open {
        result: Formula,
        deciders: Option<Vec<String>>,
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
            bindings: Box::new(Substitutions::new()),
        }
    }

    /// An application which also bound work variables.
    pub fn apply_binding(
        apply: Label,
        apply_on: Box<[ProofStep]>,
        result: Formula,
        substitutions: Box<Substitutions>,
        bindings: Substitutions,
    ) -> Self {
        ProofStep::Apply { apply, apply_on, result, substitutions, bindings: Box::new(bindings) }
    }

    pub fn hyp(label: Label, result: Formula) -> Self {
    	ProofStep::Hyp { label, result, bindings: Box::new(Substitutions::new()) }
    }

    /// A hypothesis matched by binding work variables.
    pub fn hyp_binding(label: Label, result: Formula, bindings: Substitutions) -> Self {
        ProofStep::Hyp { label, result, bindings: Box::new(bindings) }
    }

    /// A goal left open.
    pub fn open(result: Formula, deciders: Option<Vec<String>>) -> Self {
        ProofStep::Open { result, deciders }
    }

    pub fn result(&self) -> &Formula {
        match self {
            ProofStep::Apply { result: r, .. } => r,
            ProofStep::Hyp { result: r, .. } => r,
            ProofStep::Open { result: r, .. } => r,
        }
    }

    /// Whether some leaf of the proof is an open goal.
    pub fn has_open_goals(&self) -> bool {
        match self {
            ProofStep::Open { .. } => true,
            ProofStep::Apply { apply_on, .. } => apply_on.iter().any(|s| s.has_open_goals()),
            ProofStep::Hyp { .. } => false,
        }
    }

    /// The open goals of the proof, in order, with their deciders.
    pub fn open_goals(&self) -> Vec<(&Formula, &Option<Vec<String>>)> {
        match self {
            ProofStep::Open { result, deciders } => vec![(result, deciders)],
            ProofStep::Apply { apply_on, .. } => apply_on.iter().flat_map(|s| s.open_goals()).collect(),
            ProofStep::Hyp { .. } => vec![],
        }
    }

    /// The work variables bound anywhere in the proof, composed into one idempotent set.
    pub fn bindings(&self) -> Substitutions {
        let mut all = Substitutions::new();
        self.collect_bindings(&mut all);
        all
    }

    fn collect_bindings(&self, into: &mut Substitutions) {
        match self {
            ProofStep::Apply { apply_on, bindings, .. } => {
                compose_bindings(into, bindings);
                for step in apply_on.iter() {
                    step.collect_bindings(into);
                }
            }
            ProofStep::Hyp { bindings, .. } => compose_bindings(into, bindings),
            ProofStep::Open { .. } => {}
        }
    }

    /// The same proof with the work variables of `bindings` replaced everywhere.
    pub fn substitute_metavariables(&self, bindings: &Substitutions) -> ProofStep {
        match self {
            ProofStep::Apply { apply, apply_on, result, substitutions, bindings: own } => {
                let mut substituted = Substitutions::new();
                for (label, formula) in substitutions.iter() {
                    substituted.insert(*label, formula.substitute(bindings));
                }
                ProofStep::Apply {
                    apply: *apply,
                    apply_on: apply_on.iter().map(|s| s.substitute_metavariables(bindings)).collect(),
                    result: result.substitute(bindings),
                    substitutions: Box::new(substituted),
                    bindings: own.clone(),
                }
            }
            ProofStep::Hyp { label, result, bindings: own } => {
                ProofStep::Hyp { label: *label, result: result.substitute(bindings), bindings: own.clone() }
            }
            ProofStep::Open { result, deciders } => {
                ProofStep::Open { result: result.substitute(bindings), deciders: deciders.clone() }
            }
        }
    }

    fn add_to_proof_tree_array(
        &self,
        stack_buffer: &mut Vec<u8>,
        arr: &mut ProofTreeArray,
        db: Db,
    ) -> Option<usize> {
    	match self {
    		ProofStep::Apply { apply, apply_on, result, substitutions, .. } => {
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
    		ProofStep::Hyp { label, result, .. } => {
                db.build_proof_hyp(
                    *label,
                    result.clone(),
                    stack_buffer,
                    arr,
                )
    		},
    		// A proof with open goals is not exported (see `Script::run_proof`).
    		ProofStep::Open { .. } => None,
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
