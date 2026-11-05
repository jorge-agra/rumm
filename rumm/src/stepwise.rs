//! The stepwise request: apply a tactic to one goal of a proof state (see `PROTOCOL.md`).
//!
//! The caller owns the proof state. It hands rumm the whole state, one open goal and a
//! tactic; rumm returns the new state, and keeps nothing.

use crate::context::{Context, TraceSink};
use crate::lang::{scan_metavariables, Db, Hypotheses, ProofStep};
use crate::script::Failure;
use crate::tactics::TacticsError;
use crate::{Engine, Library};
use metamath_rs::formula::Substitutions;
use metamath_rs::{Formula, Label};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::panic::{catch_unwind, AssertUnwindSafe};

/// One step of a proof state: a proved step (`ref` is the statement it cites, `hyps` the steps
/// it cites as hypotheses), a hypothesis step (`h<n>`, `ref` its `$e` label), or an open goal
/// (`ref` is `null`).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct StateStep {
    pub label: String,
    /// The statement with its typecode (`|- ( ph -> &W1 )`); work variables are `&W1`, `&C1`...
    pub expr: String,
    #[serde(rename = "ref", default)]
    pub reference: Option<String>,
    /// A step cited by its label, a hypothesis step by its number (`"1"` for `h1`).
    #[serde(default)]
    pub hyps: Vec<String>,
    /// For an open goal left by `{ decide <names> }`: the names.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub deciders: Option<Vec<String>>,
}

/// A proof state: what MMX holds and passes in, and gets back.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct State {
    /// The theorem being proved, or `null` for a new theorem, which may cite any statement.
    #[serde(default)]
    pub theorem: Option<String>,
    pub steps: Vec<StateStep>,
    /// The `$d` the steps need (pairs of variable names), which rumm completes.
    #[serde(default)]
    pub dv: Vec<(String, String)>,
}

#[derive(Debug, Clone, Serialize, PartialEq)]
pub struct OpenGoal {
    pub label: String,
    pub expr: String,
    pub deciders: Option<Vec<String>>,
}

/// A request to apply a tactic to one open goal of a proof state.
#[derive(Debug, Clone, PartialEq)]
pub struct ApplyRequest {
    /// Where the tactics definitions come from (default: none).
    pub library: Library,
    pub state: State,
    /// The label of the open goal.
    pub goal: String,
    /// A tactics expression in `.rmm` syntax.
    pub tactic: String,
    pub max_depth: Option<usize>,
}

/// What an `apply` produced.
#[derive(Debug, Clone, Serialize, PartialEq)]
pub struct Applied {
    /// The labels of the steps the tactic added, in the order of the state.
    pub produced: Vec<String>,
    /// The labels of the steps which were already there and changed: the goal, and the steps
    /// where a work variable the tactic bound was replaced.
    pub updated: Vec<String>,
    /// The goal, when a hypothesis alone closed it: it is no step of the new state, and the
    /// steps which cited it cite the hypothesis.
    pub removed: Vec<String>,
    pub state: State,
    pub open: Vec<OpenGoal>,
    /// The state is complete: no open goal and no work variable left.
    pub proved: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ApplyOutcome {
    pub result: std::result::Result<Applied, Failure>,
    pub warnings: Vec<String>,
}

/// A step of a state, read.
struct Step {
    label: String,
    typecode: String,
    formula: Formula,
    reference: Option<String>,
    hyps: Vec<String>,
    deciders: Option<Vec<String>>,
}

impl Step {
    fn is_hypothesis(&self) -> bool {
        hypothesis_number(&self.label).is_some()
    }
}

/// `3` for `h3`.
fn hypothesis_number(label: &str) -> Option<&str> {
    let number = label.strip_prefix('h')?;
    if !number.is_empty() && number.bytes().all(|b| b.is_ascii_digit()) { Some(number) } else { None }
}

fn invalid(message: impl Into<String>) -> Failure {
    Failure::new("invalid-state", message)
}

fn pair(a: &str, b: &str) -> (String, String) {
    if a <= b { (a.to_string(), b.to_string()) } else { (b.to_string(), a.to_string()) }
}

fn expression(db: &Db, typecode: &str, formula: &Formula) -> String {
    let body = db.expression_body(formula);
    if body.is_empty() { typecode.to_string() } else { format!("{} {}", typecode, body) }
}

impl Engine {
    /// Applies the tactic of the request to its goal. Never panics and never prints. On a
    /// failure the state is unchanged (the caller keeps its own).
    pub fn apply(&mut self, request: &ApplyRequest, trace: Option<TraceSink>) -> ApplyOutcome {
        let mut warnings = Vec::new();
        let result = catch_unwind(AssertUnwindSafe(|| self.try_apply(request, trace, &mut warnings)))
            .unwrap_or_else(|panic| Err(Failure::from_panic(panic)));
        ApplyOutcome { result, warnings }
    }

    fn try_apply(
        &mut self,
        request: &ApplyRequest,
        trace: Option<TraceSink>,
        warnings: &mut Vec<String>,
    ) -> std::result::Result<Applied, Failure> {
        // Work variables of the state, the tactic and the library must be declared before
        // any of them is parsed; the fresh ones a tactic needs are numbered after them.
        let mut highest: BTreeMap<char, usize> = BTreeMap::new();
        let mut note = |text: &str| {
            for (letter, index) in scan_metavariables(text) {
                let slot = highest.entry(letter).or_insert(0);
                *slot = (*slot).max(index);
            }
        };
        for step in &request.state.steps {
            note(&step.expr);
        }
        note(&request.tactic);
        if let Library::Text(text) = &request.library {
            note(text);
        }
        self.db.ensure_metavariables(&highest).map_err(|e| Failure::new("metavariables", e.describe()))?;

        let script = self.load_script(&request.library, warnings)?;
        let tactics = self.parse_tactic(&request.tactic)?;
        let db = self.db.clone();

        let (theorem, steps) = read_state(&db, &request.state)?;
        let needed_before = settle(&db, theorem, &steps)?;
        let goal_index = steps
            .iter()
            .position(|s| s.label == request.goal)
            .ok_or_else(|| Failure::new("unknown-goal", format!("the state has no step {}", request.goal)))?;
        let goal = &steps[goal_index];
        if goal.reference.is_some() || goal.is_hypothesis() {
            return Err(Failure::new("goal-not-open", format!("step {} is not an open goal", goal.label)));
        }

        // The hypothesis steps are the hypotheses of the run. They are told apart by a label
        // of the database each (a new theorem has none of its own), mapped back to the step.
        let hypothesis_steps: Vec<&Step> = steps.iter().filter(|s| s.is_hypothesis()).collect();
        let placeholders = db.placeholder_labels(hypothesis_steps.len());
        let hypotheses: Hypotheses =
            placeholders.iter().zip(&hypothesis_steps).map(|(l, s)| (*l, s.formula.clone())).collect();
        let by_placeholder: HashMap<Label, String> =
            placeholders.iter().zip(&hypothesis_steps).map(|(l, s)| (*l, s.label.clone())).collect();

        let max_depth = request.max_depth.unwrap_or(self.max_depth);
        let mut context = Context::new(
            db.clone(),
            goal.formula.clone(),
            theorem,
            hypotheses,
            script.tactics_definitions.clone(),
            max_depth,
            trace,
        );
        context.set_stepwise(highest);
        let tree = tactics.execute(&mut context).map_err(|e| Failure::from_tactics_error(&e))?;

        // What the tactic bound is replaced everywhere: in what it built, and in the other
        // steps of the state.
        let bindings = tree.bindings();
        let tree = tree.substitute_metavariables(&bindings);
        if tree.result().substitute(&bindings) != goal.formula.substitute(&bindings) {
            return Err(Failure::new(
                "step-mismatch",
                format!("the tactic proved {} instead of the goal", expression(&db, &goal.typecode, tree.result())),
            ));
        }

        let mut labels: HashSet<String> = steps.iter().map(|s| s.label.clone()).collect();
        let mut builder = Builder {
            db: &db,
            labels: &mut labels,
            counter: 0,
            steps: Vec::new(),
            memo: HashMap::new(),
            by_placeholder: &by_placeholder,
        };
        let goal_label = goal.label.clone();
        // A goal closed by a hypothesis alone is not a step of its own: the steps citing it
        // cite the hypothesis instead, and the goal is gone.
        let alias = match &tree {
            ProofStep::Hyp { label, .. } => {
                let hypothesis = by_placeholder.get(label).cloned().unwrap_or_default();
                if !steps.iter().any(|s| s.hyps.contains(&goal_label)) {
                    return Err(Failure::new(
                        "goal-is-a-hypothesis",
                        "the tactic closes the conclusion by a hypothesis alone; a step can't just be one: apply a statement instead",
                    ));
                }
                Some(hypothesis_number(&hypothesis).unwrap_or(&hypothesis).to_string())
            }
            _ => None,
        };
        let (produced, goal_step) = match &alias {
            Some(_) => (Vec::new(), None),
            None => {
                builder.convert(&tree, &goal.typecode, Some(goal_label.clone()))?;
                let mut built = builder.steps;
                let goal_step = built.pop().expect("the goal's step is built last");
                (built, Some(goal_step))
            }
        };
        let produced_labels: Vec<String> = produced.iter().map(|s| s.label.clone()).collect();
        let mut produced = produced;

        let mut updated = vec![goal_label.clone()];
        let mut new_steps: Vec<StateStep> = Vec::new();
        for (index, step) in steps.iter().enumerate() {
            if index == goal_index {
                new_steps.append(&mut produced);
                new_steps.extend(goal_step.clone());
                continue;
            }
            let formula = step.formula.substitute(&bindings);
            let expr = expression(&db, &step.typecode, &formula);
            let mut hyps = step.hyps.clone();
            let mut changed = formula != step.formula;
            if let Some(number) = &alias {
                for hyp in hyps.iter_mut().filter(|h| **h == goal_label) {
                    *hyp = number.clone();
                    changed = true;
                }
            }
            if changed {
                updated.push(step.label.clone());
            }
            new_steps.push(StateStep {
                label: step.label.clone(),
                expr: if formula != step.formula { expr } else { request.state.steps[index].expr.clone() },
                reference: step.reference.clone(),
                hyps,
                deciders: step.deciders.clone(),
            });
        }
        let produced = produced_labels;
        let mut removed = Vec::new();
        if alias.is_some() {
            updated.retain(|l| *l != goal_label);
            removed.push(goal_label.clone());
        }

        // The new state is read and settled like the one passed in: every step must follow
        // from what it cites, and the `$d` it needs must be declared.
        let mut state = State { theorem: request.state.theorem.clone(), steps: new_steps, dv: Vec::new() };
        let (_, read) = read_state(&db, &state)?;
        let needed = settle(&db, theorem, &read).map_err(|f| {
            if f.kind == "invalid-state" { Failure::new("step-mismatch", f.message) } else { f }
        })?;
        let mut dv: BTreeSet<(String, String)> = BTreeSet::new();
        for (a, b) in &request.state.dv {
            dv.insert(pair(a, b));
        }
        dv.extend(needed_before);
        dv.extend(needed);
        state.dv = dv.into_iter().collect();

        let open: Vec<OpenGoal> = read
            .iter()
            .filter(|s| s.reference.is_none() && !s.is_hypothesis())
            .map(|s| OpenGoal {
                label: s.label.clone(),
                expr: expression(&db, &s.typecode, &s.formula),
                deciders: s.deciders.clone(),
            })
            .collect();
        if open.is_empty() {
            let mut left = BTreeSet::new();
            for step in &read {
                db.metavariables_in(&step.formula, &mut left);
            }
            if !left.is_empty() {
                return Err(Failure::from_tactics_error(&TacticsError::UnresolvedMetavariables(
                    left.into_iter().collect::<Vec<_>>().join(" "),
                )));
            }
        }
        let proved = open.is_empty();
        Ok(Applied { produced, updated, removed, state, open, proved })
    }
}

/// Turns the proof the tactic returned into steps of the state.
struct Builder<'a> {
    db: &'a Db,
    labels: &'a mut HashSet<String>,
    counter: usize,
    steps: Vec<StateStep>,
    /// An identical proved step is built once.
    memo: HashMap<(String, Vec<String>, String), String>,
    by_placeholder: &'a HashMap<Label, String>,
}

impl Builder<'_> {
    fn fresh_label(&mut self) -> String {
        loop {
            self.counter += 1;
            let label = format!("s{}", self.counter);
            if self.labels.insert(label.clone()) {
                return label;
            }
        }
    }

    /// Builds the steps of `step`, the last of them being `step` itself, and returns how a step
    /// citing it names it. `label` is the label `step` must have (the goal's).
    fn convert(&mut self, step: &ProofStep, typecode: &str, label: Option<String>) -> std::result::Result<String, Failure> {
        match step {
            ProofStep::Hyp { label: hypothesis, .. } => {
                if label.is_some() {
                    return Err(Failure::new(
                        "goal-is-a-hypothesis",
                        "the tactic closes the goal by a hypothesis alone; a step can't just be one: apply a statement instead",
                    ));
                }
                let step_label = self.by_placeholder.get(hypothesis).cloned().unwrap_or_default();
                Ok(hypothesis_number(&step_label).unwrap_or(&step_label).to_string())
            }
            ProofStep::Open { result, deciders } => {
                let label = label.unwrap_or_else(|| self.fresh_label());
                self.steps.push(StateStep {
                    label: label.clone(),
                    expr: expression(self.db, typecode, result),
                    reference: None,
                    hyps: Vec::new(),
                    deciders: deciders.clone(),
                });
                Ok(label)
            }
            ProofStep::Apply { apply, apply_on, result, .. } => {
                let hypotheses = self.db.get_theorem_formulas(*apply).map(|(_, hyps)| hyps).unwrap_or_default();
                let mut cites = Vec::new();
                for (index, child) in apply_on.iter().enumerate() {
                    let child_typecode = hypotheses
                        .get(index)
                        .map(|(_, formula)| self.db.typecode_name(formula))
                        .unwrap_or_else(|| typecode.to_string());
                    cites.push(self.convert(child, &child_typecode, None)?);
                }
                let reference = self.db.label_name(*apply);
                let expr = expression(self.db, typecode, result);
                let key = (reference.clone(), cites.clone(), expr.clone());
                if label.is_none() {
                    if let Some(existing) = self.memo.get(&key) {
                        return Ok(existing.clone());
                    }
                }
                let label = label.unwrap_or_else(|| self.fresh_label());
                self.memo.insert(key, label.clone());
                self.steps.push(StateStep { label: label.clone(), expr, reference: Some(reference), hyps: cites, deciders: None });
                Ok(label)
            }
        }
    }
}

/// Reads a state: the theorem, and each step's formula.
fn read_state(db: &Db, state: &State) -> std::result::Result<(Option<Label>, Vec<Step>), Failure> {
    let theorem = match &state.theorem {
        None => None,
        Some(name) => {
            let label = db
                .get_theorem_label(name.clone())
                .filter(|l| db.is_assertion(*l))
                .ok_or_else(|| Failure::new("unknown-theorem", format!("Unknown theorem {}", name)))?;
            Some(label)
        }
    };
    let mut seen = HashSet::new();
    let mut steps = Vec::new();
    for step in &state.steps {
        if !seen.insert(step.label.clone()) {
            return Err(invalid(format!("two steps are labelled {}", step.label)));
        }
        let (typecode, body) = step.expr.trim().split_once(char::is_whitespace).unwrap_or((step.expr.trim(), ""));
        if typecode.is_empty() || db.get_symbol(typecode.to_string()).is_none() {
            return Err(invalid(format!("step {}: the expression starts with no typecode: {}", step.label, step.expr)));
        }
        let formula = db
            .parse_expression(body)
            .map_err(|e| Failure::new("invalid-expression", format!("step {}: {}", step.label, e)))?;
        steps.push(Step {
            label: step.label.clone(),
            typecode: typecode.to_string(),
            formula,
            reference: step.reference.clone(),
            hyps: step.hyps.clone(),
            deciders: step.deciders.clone(),
        });
    }
    Ok((theorem, steps))
}

/// Checks that each step follows from the statement it cites and the steps it cites as
/// hypotheses, and gives the `$d` the citations need (as pairs of variable names, ordered).
/// A citation which violates a `$d`, or one the theorem doesn't declare, is a failure.
fn settle(db: &Db, theorem: Option<Label>, steps: &[Step]) -> std::result::Result<BTreeSet<(String, String)>, Failure> {
    let index: HashMap<&str, usize> = steps.iter().enumerate().map(|(i, s)| (s.label.as_str(), i)).collect();
    let cited_step = |name: &str| index.get(name).or_else(|| index.get(format!("h{}", name).as_str())).copied();
    let mut needed = BTreeSet::new();
    let frame_hyps = theorem.and_then(|t| db.get_theorem_formulas(t)).map(|(_, hyps)| hyps);
    for step in steps {
        if step.is_hypothesis() {
            if !step.hyps.is_empty() {
                return Err(invalid(format!("hypothesis step {} cites steps", step.label)));
            }
            // A hypothesis of a database theorem is one of its own.
            if let (Some(frame_hyps), Some(reference)) = (&frame_hyps, &step.reference) {
                let known = frame_hyps.iter().find(|(l, _)| db.label_name(*l) == *reference);
                match known {
                    Some((_, formula)) if *formula == step.formula => {}
                    Some(_) => return Err(invalid(format!("hypothesis step {} differs from {}", step.label, reference))),
                    None => return Err(invalid(format!("step {}: {} is not a hypothesis of the theorem", step.label, reference))),
                }
            }
            continue;
        }
        let Some(reference) = &step.reference else {
            if !step.hyps.is_empty() {
                return Err(invalid(format!("the open goal {} cites steps", step.label)));
            }
            continue;
        };
        let cited = db
            .get_theorem_label(reference.clone())
            .filter(|l| db.is_assertion(*l))
            .ok_or_else(|| {
                Failure::new(
                    "unknown-ref",
                    format!(
                        "step {} cites {}, which is not a statement of the database (local theorems are not supported)",
                        step.label, reference
                    ),
                )
            })?;
        if !db.precedes(cited, theorem) {
            return Err(Failure::from_tactics_error(&TacticsError::CitedAfterGoal(reference.clone())));
        }
        let (conclusion, hypotheses) = db.get_theorem_formulas(cited).expect("an assertion has a frame");
        if hypotheses.len() != step.hyps.len() {
            return Err(invalid(format!(
                "step {} cites {} as {} hypothesis step(s), and {} needs {}",
                step.label, reference, step.hyps.len(), reference, hypotheses.len()
            )));
        }
        let mismatch = || invalid(format!("step {} does not follow from {} and the steps it cites", step.label, reference));
        let mut subst = Substitutions::new();
        step.formula.unify(&conclusion, &mut subst).map_err(|_| mismatch())?;
        for ((_, hypothesis), name) in hypotheses.iter().zip(&step.hyps) {
            let child = cited_step(name).ok_or_else(|| invalid(format!("step {} cites {}, which is not a step", step.label, name)))?;
            steps[child].formula.unify(hypothesis, &mut subst).map_err(|_| mismatch())?;
        }
        db.check_distinct(theorem, cited, &subst, &Substitutions::new(), &mut needed)
            .map_err(|e| Failure::from_tactics_error(&e))?;
    }
    Ok(needed)
}
