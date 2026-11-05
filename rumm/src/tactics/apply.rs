use crate::lang::{compose_bindings, DisplayPair, Term};
use metamath_rs::Label;
use std::collections::HashMap;
use crate::lang::SubstitutionListExpression;
use metamath_rs::formula::Substitutions;
use crate::lang::TacticsExpression;
use crate::context::Context;
use crate::error::Result;
use crate::lang::ProofStep;
use crate::lang::{Db, Display};
use crate::lang::StatementExpression;
use crate::parser::{Parse, Parser, OptionalTactics};
use crate::tactics::Tactics;
use crate::tactics::TacticsError;
use crate::tactics::TacticsResult;
use core::fmt::Formatter;
use std::collections::BTreeSet;


/// A tactics which applies a given theorem to prove the goal.
///
pub struct Apply {
    theorem: StatementExpression,
    subtactics: Vec<TacticsExpression>,
    substitutions: SubstitutionListExpression,
}

impl Display for Apply {
    fn format(&self, fmt: &mut Formatter, db: &Db) -> std::result::Result<(), std::fmt::Error> {
        fmt.write_str("{ Apply \n")?;
        self.theorem.format(fmt, db)?;
        for t in &self.subtactics {
            t.format(fmt, db)?;
        }
        fmt.write_str("}\n")
    }
}

impl Parse for Apply {
    fn parse(parser: &mut Parser) -> Result<Self> {
        let theorem = StatementExpression::parse(parser)?;
        let mut subtactics = Vec::new();
        let mut substitutions = SubstitutionListExpression::default();
        loop {
            match parser.parse_optional_tactics()? {
                OptionalTactics::Some(t) => subtactics.push(t),
                OptionalTactics::None => break,
                OptionalTactics::With => {
                    substitutions = SubstitutionListExpression::parse(parser)?;
                    break;
                }
            }
        }
        
        Ok(Apply {
            theorem,
            subtactics,
            substitutions,
        })
    }
}

impl Tactics for Apply {
    fn get_name(&self) -> String {
        "apply".to_string()
    }

    fn get_desc(&self) -> String {
        "A tactics which applies a given theorem to prove the goal.".to_string()
    }

    fn execute(&self, context: &mut Context) -> TacticsResult {
        context.enter(&format!("Apply {}", DisplayPair(&self.theorem, &context.db)));
        // context.db.debug_formula(context.goal());
        // println!("  vars:{}", DisplayPair(context.variables(), &context.db));
        let mut my_subst = Substitutions::default();
        for (l,f) in self.substitutions.evaluate(context)?.iter() {
            context.message(format!("Subst: {} {}", DisplayPair(l, &context.db), DisplayPair(f, &context.db)).as_str());
            my_subst.insert(*l, f.substitute(context.variables()));
        }

        let theorem = self.theorem.evaluate(context)?;
        context.message(&format!(" Attempting apply {}", DisplayPair(&theorem, &context.db)));
        if !context.db.precedes(theorem, context.theorem()) {
            context.exit("Apply statement is not before the theorem");
            return Err(TacticsError::CitedAfterGoal(context.db.label_name(theorem)));
        }
        if context.stepwise() {
            return self.execute_stepwise(context, theorem, my_subst);
        }
        if let Some((theorem_formula, hyps)) = context.get_theorem_formulas(theorem) {
            let mut subst = Substitutions::new();
            if let Err(e) = context.goal().unify(&theorem_formula, &mut subst) {
                context.exit("Apply statement doesn't match");
                return Err(e.into());
            }
            subst.extend(&my_subst);
            if let Err(e) = context.db.check_distinct(context.theorem(), theorem, &subst, context.variables(), &mut BTreeSet::new()) {
                context.exit(&format!("Apply violates $d: {:?}", e));
                return Err(e);
            }
            // context.message(&format!("  subst:{}", DisplayPair(&subst, &context.db)));
            if hyps.len() == self.subtactics.len() {
                let mut substeps = vec![];
                // TODO check count!
                for ((_hyp_label, hyp_formula), tactics) in hyps.iter().zip(&self.subtactics) {
                    let sub_goal = hyp_formula.substitute(&subst);
                    let mut sub_context = context.with_goal(sub_goal);
                    substeps.push(tactics.execute(&mut sub_context)?);
                }
                context.exit("Apply Unification success");
                Ok(ProofStep::apply(
                    theorem,
                    substeps.into_boxed_slice(),
                    context.goal().clone(),
                    Box::new(subst),
                ))
            } else {
                context.exit("Apply Hyps don't match");
                Err(TacticsError::WrongHypCount(self.subtactics.len(), hyps.len()))
            }
        } else {
            context.exit("Unknown theorem label");
            Err(TacticsError::UnknownLabel(theorem))
        }
    }
}

impl Apply {
    /// The application of a stepwise run. The goal may hold work variables, which the
    /// statement can bind; the variables of the statement the goal doesn't determine become
    /// fresh work variables (the subgoals can't hold the statement's own variables, which
    /// would read as the theorem's); and the work variables bound while proving a subgoal are
    /// substituted in the subgoals after it. The bindings are kept in the returned step, so a
    /// branch which fails leaves none behind.
    fn execute_stepwise(&self, context: &mut Context, theorem: Label, my_subst: Substitutions) -> TacticsResult {
        let Some((theorem_formula, hyps)) = context.get_theorem_formulas(theorem) else {
            context.exit("Unknown theorem label");
            return Err(TacticsError::UnknownLabel(theorem));
        };
        if hyps.len() != self.subtactics.len() {
            context.exit("Apply Hyps don't match");
            return Err(TacticsError::WrongHypCount(self.subtactics.len(), hyps.len()));
        }
        let db = context.db.clone();
        let unified = match db.unify_terms(context.goal(), &theorem_formula, true) {
            Ok(unified) => unified,
            Err(e) => {
                context.exit("Apply statement doesn't match");
                return Err(e);
            }
        };
        // What the statement leaves undetermined gets a fresh work variable, one per variable.
        let mut fresh: HashMap<Label, Term> = HashMap::new();
        let mut residual = |variable: Label| -> TacticsResult<Term> {
            if let Some(term) = fresh.get(&variable) {
                return Ok(term.clone());
            }
            let typecode = db.label_typecode_name(variable);
            let formula = context.fresh_metavariable(&typecode)?;
            let term = db.term_of(&formula, false);
            fresh.insert(variable, term.clone());
            Ok(term)
        };
        let mut subst = Substitutions::new();
        for variable in db.floating_labels(theorem) {
            if let Some(given) = my_subst.get(variable) {
                subst.insert(variable, given.clone());
                continue;
            }
            let term = unified.model.get(&variable).cloned().unwrap_or(Term::Model(variable));
            subst.insert(variable, db.formula_of(&term.replace_model(&mut residual)?)?);
        }
        let mut bindings = Substitutions::new();
        for (meta, term) in unified.meta.iter() {
            bindings.insert(*meta, db.formula_of(&term.replace_model(&mut residual)?)?);
        }
        // The instance of the statement must be the goal, as bound.
        if theorem_formula.substitute(&subst).substitute(&bindings) != context.goal().substitute(&bindings) {
            context.exit("Apply substitution doesn't match the goal");
            return Err(TacticsError::UnificationFailed);
        }
        if let Err(e) = db.check_distinct(context.theorem(), theorem, &subst, context.variables(), &mut BTreeSet::new()) {
            context.exit(&format!("Apply violates $d: {:?}", e));
            return Err(e);
        }
        let mut known = bindings.clone();
        let mut substeps = vec![];
        for ((_hyp_label, hyp_formula), tactics) in hyps.iter().zip(&self.subtactics) {
            let sub_goal = hyp_formula.substitute(&subst).substitute(&known);
            let mut sub_context = context.with_goal(sub_goal);
            let step = tactics.execute(&mut sub_context)?;
            compose_bindings(&mut known, &step.bindings());
            substeps.push(step);
        }
        context.exit("Apply Unification success");
        Ok(ProofStep::apply_binding(
            theorem,
            substeps.into_boxed_slice(),
            context.goal().clone(),
            Box::new(subst),
            bindings,
        ))
    }
}
