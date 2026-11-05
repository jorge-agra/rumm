use crate::error::{Error, Result};
use crate::lang::Display;
use crate::tactics::{TacticsResult, TacticsError};

use colored::*;
use metamath_rs::grammar::FormulaToken;
use core::cell::RefCell;
use core::fmt::Formatter;
use metamath_rs::as_str;
use metamath_rs::database::DbOptions;
use metamath_rs::diag::StmtParseError;
use metamath_rs::formula::Substitutions;
use metamath_rs::proof::ProofTreeArray;
use metamath_rs::verify::ProofBuilder;
use metamath_rs::Database;
use metamath_rs::Formula;
use metamath_rs::Label;
use metamath_rs::StatementType;
use metamath_rs::Symbol;
use metamath_rs::scopeck::{FrameRef, Hyp};
use std::collections::{BTreeSet, HashMap};
use std::ops::Bound;
use std::ops::Deref;
use std::io::Write;
use std::sync::Arc;

/// A type for representing theorem essential hypotheses: a label and the corresponding formula.
pub type Hypotheses = Box<[(Label, Formula)]>;

#[derive(Clone)]
pub struct Db {
    intern: Arc<RefCell<Database>>,
}

impl Default for Db {
    fn default() -> Self {
        let options = DbOptions {
            incremental: true,
            autosplit: false,
            ..Default::default()
        };
        Db {
            intern: Arc::new(RefCell::new(Database::new(options))),
        }
    }
}

impl Db {
    pub fn parse(&mut self, filename: &str) -> Result {
        let mut database = self.intern.borrow_mut();

        print!("Loading \"{}\" ... ", filename);
        database.parse(filename.to_string(), Vec::new());
        let err = database.diag_notations();
        if !err.is_empty() {
            return Err(Error::DBError(filename.to_string(), err).into());
        }
        println!("{}", "ok".green());

        print!("Building \"{}\" grammar... ", filename);
        database.grammar_pass();
        let gerr = database.diag_notations();
        if !gerr.is_empty() {
            return Err(Error::DBError(filename.to_string(), gerr).into());
        }
        println!("{}", "ok".green());

        print!("Parsing \"{}\"... ", filename);
        database.stmt_parse_pass();
        let gerr = database.diag_notations();
        if !gerr.is_empty() {
            return Err(Error::DBError(filename.to_string(), gerr).into());
        }
        println!("{}", "ok".green());
        //let testx = self.get_theorem_label("testx".to_string()).unwrap();
        //let (_f, ..) = self.get_theorem_formulas(testx).unwrap();
        //println!("TESTX {}", f.debug(self.database.borrow_mut().name_result()));
        Ok(())
    }

    pub fn get_symbol(&self, name: String) -> Option<Symbol> {
        let database = self.intern.borrow();
        Some(database
            .name_result()
            .lookup_symbol(name.as_bytes())?
            .atom
        )
    }

    pub fn get_theorem_label(&self, name: String) -> Option<Label> {
        let database = self.intern.borrow();
        Some(database
            .name_result()
            .lookup_label(name.as_bytes())?.atom
        )
    }

    pub fn get_theorem_formulas(&self, label: Label) -> Option<(Formula, Hypotheses)> {
        let database = self.intern.borrow();
        let sref = database.statement_by_label(label)?;
        let formula = database.stmt_parse_result().get_formula(&sref)?.clone();
        let frame = database.get_frame(label)?;
        let hypotheses: Vec<(Label, Formula)> = frame.essentials().map(|(l,f)| { (l, f.clone()) }).collect();
        Some((formula, hypotheses.into_boxed_slice()))
    }

    pub fn parse_formula(&self, symbols: Vec<std::result::Result<FormulaToken, StmtParseError>>) -> std::result::Result<Formula, StmtParseError> {
        let database = self.intern.borrow();
        let grammar = database.grammar_result().clone();
        let nset = database.name_result();
        let convert_to_provable = false;
        grammar
            .parse_formula(&mut symbols.into_iter(), &grammar.typecodes(), convert_to_provable, nset)
    }

    pub fn ensure_type(&self, fmla: Formula, label: Label) -> TacticsResult<Formula> {
        let database = self.intern.borrow();
        let target_tc = database.label_typecode(label);
        let source_tc = fmla.get_typecode();
        if target_tc != source_tc {
            let grammar = database.grammar_result().clone();
            grammar.convert_typecode(fmla, target_tc).ok_or(TacticsError::WrongTypecode(source_tc, target_tc, label))
        } else {
            Ok(fmla)
        }
    }

    pub fn debug_formula<'a>(&'a self, f: &'a Formula) {
        let database = self.intern.borrow();
        println!("{:?}", f.as_ref(&database));
    }

    /// Whether the statement `cited` may be cited in the proof of `theorem`: it must come
    /// before it in the database. A goal with no database position (`theorem` is `None`,
    /// as for a new theorem) may cite every statement, as if it were appended at the end.
    pub fn precedes(&self, cited: Label, theorem: Option<Label>) -> bool {
        match theorem {
            None => true,
            Some(theorem) => {
                let database = self.intern.borrow();
                // An unknown label can't be placed; it is rejected where it is looked up.
                matches!(database.cmp_label(&cited, &theorem), Some(std::cmp::Ordering::Less) | None)
            }
        }
    }

    pub fn label_name(&self, label: Label) -> String {
        let database = self.intern.borrow();
        as_str(database.name_result().atom_name(label)).to_string()
    }

    /// The statements which may be cited in the proof of `theorem` (all of them if `None`,
    /// see `precedes`), in database order.
    pub fn statements(&self, theorem: Option<Label>, filter: impl Fn(bool, &[u8]) -> bool) -> impl Iterator<Item = (Label, Formula, Hypotheses)> + '_ {
        let database = self.intern.borrow();
        let nset = database.name_result().clone();
        let provable = database.grammar_result().provable_typecode();
        let end = match theorem.and_then(|t| nset.lookup_label(nset.atom_name(t))) {
            Some(lookup) => Bound::Excluded(lookup.address),
            None => Bound::Unbounded,
        };
        database.statements_range_address((Bound::Unbounded, end)).filter_map(move |sref| {
            match sref.statement_type() {
                StatementType::Axiom | StatementType::Provable => {
                    let is_axiom = sref.statement_type() == StatementType::Axiom;
                    let name = sref.label();
                    if nset.get_atom(&sref.math_at(0)) == provable && filter(is_axiom, name) {
                        let label = nset.lookup_label(name)?.atom;
                        let (formula, hyps) = self.get_theorem_formulas(label)?;
                        Some((label, formula, hyps))
                    } else { None }
                },
                _ => None,
            }
        }).collect::<Vec<_>>().into_iter()
    }

    /// Add a hypothesis step to a proof array
    pub fn build_proof_hyp(
        &self,
        label: Label,
        formula: Formula,
        stack_buffer: &mut Vec<u8>,
        arr: &mut ProofTreeArray,
    ) -> Option<usize> {
        let database = self.intern.borrow();
        let nset = database.name_result().clone();
        let token = nset.atom_name(label);
        let address = nset.lookup_label(token)?.address;
        let range = formula.as_ref(&database).append_to_stack_buffer(stack_buffer);
        Some(arr.build(address, Default::default(), stack_buffer, range))
    }

    /// Add a normal step to a proof array
    pub fn build_proof_step(
        &self,
        label: Label,
        formula: Formula,
        mand_hyps: Vec<usize>,
        substitutions: &Substitutions,
        stack_buffer: &mut Vec<u8>,
        arr: &mut ProofTreeArray,
    ) -> Option<usize> {
        let database = self.intern.borrow();
        let token = database.name_result().atom_name(label);
        let address = database.name_result().lookup_label(token)?.address;
        let range = formula.as_ref(&database).append_to_stack_buffer(stack_buffer);
        let frame = database.get_frame(label)?;
        let mut hyps = vec![];
        for label in frame.floating() {
            let formula = &substitutions.get(label).unwrap_or_else(|| {
                panic!("While building proof using {}: No substitution for {}", as_str(token), as_str(database.name_result().atom_name(label)));
            });
            let proof_tree_index = formula.as_ref(&database).build_syntax_proof::<usize, Vec<usize>>(
                stack_buffer,
                arr,
            );
            hyps.push(proof_tree_index);
        }
        hyps.extend(mand_hyps);
        Some(arr.build(address, hyps, stack_buffer, range))
    }

    /// The name of the variable of a `$f` hypothesis label.
    fn variable_name(database: &Database, label: Label) -> Option<String> {
        let sref = database.statement_by_label(label)?;
        Some(as_str(sref.math_at(1).slice).to_string())
    }

    /// The variables of a frame, by `$f` label, with their index in the frame.
    fn frame_variables(frame: &FrameRef<'_>) -> Vec<(Label, usize)> {
        let indices = frame.hypotheses.iter().filter_map(|hyp| match hyp {
            Hyp::Floating(_, index, _) => Some(*index),
            _ => None,
        });
        frame.floating().zip(indices).collect()
    }

    /// Checks the `$d` constraints of the statement `cited` for a citation instantiating it
    /// with `subst` (read through `bindings`, the metavariables bound so far).
    ///
    /// For each mandatory `$d x y` of `cited`, the expressions substituted for `x` and `y`
    /// may not share a variable, and every pair made of one variable of each must be declared
    /// disjoint in the frame of `theorem`. When `theorem` is `None` (a new theorem), any pair of
    /// distinct variables is accepted: the pairs are the `$d` the new theorem must declare.
    /// Pairs involving a metavariable (`&W1`...) can't be decided yet, and are skipped:
    /// the check is run again on the finished proof. So are `$d` whose variables are not bound.
    ///
    /// The goal variable pairs which the citation relies on are added to `needed`, by name.
    pub fn check_distinct(
        &self,
        theorem: Option<Label>,
        cited: Label,
        subst: &Substitutions,
        bindings: &Substitutions,
        needed: &mut BTreeSet<(String, String)>,
    ) -> TacticsResult<()> {
        let database = self.intern.borrow();
        let cited_frame = match database.get_frame(cited) {
            Some(frame) if !frame.mandatory_dv.is_empty() => frame,
            _ => return Ok(()),
        };
        let cited_vars: HashMap<usize, Label> = Self::frame_variables(&cited_frame)
            .into_iter()
            .map(|(label, index)| (index, label))
            .collect();
        let goal_frame = theorem.and_then(|t| database.get_frame(t));
        // The `$d` in scope of the theorem also cover variables which are only used in its
        // proof (dummy variables), so the frame's variables are looked up by name.
        let goal_vars: HashMap<String, usize> = goal_frame
            .as_ref()
            .map(|f| {
                f.var_list.iter().enumerate()
                    .map(|(index, atom)| (as_str(database.name_result().atom_name(*atom)).to_string(), index))
                    .collect()
            })
            .unwrap_or_default();
        let variables_of = |formula: &Formula| -> Vec<Label> {
            let mut vars = vec![];
            for (label, is_variable) in formula.substitute(bindings).labels_iter() {
                if is_variable && !vars.contains(&label) {
                    vars.push(label);
                }
            }
            vars
        };
        let name = |label: Label| Self::variable_name(&database, label).unwrap_or_default();
        let cited_name = as_str(database.name_result().atom_name(cited)).to_string();
        for &(i, j) in cited_frame.mandatory_dv.iter() {
            let (Some(li), Some(lj)) = (cited_vars.get(&i), cited_vars.get(&j)) else { continue };
            let (Some(ei), Some(ej)) = (subst.get(*li), subst.get(*lj)) else { continue };
            let (vars_i, vars_j) = (variables_of(ei), variables_of(ej));
            for &a in &vars_i {
                for &b in &vars_j {
                    let (na, nb) = (name(a), name(b));
                    if a == b {
                        return Err(TacticsError::DistinctVariable(format!(
                            "{} requires {} and {} to be disjoint, but both contain {}",
                            cited_name, name(*li), name(*lj), na
                        )));
                    }
                    if na.starts_with('&') || nb.starts_with('&') {
                        continue;
                    }
                    if let Some(goal_frame) = &goal_frame {
                        let declared = match (goal_vars.get(&na), goal_vars.get(&nb)) {
                            (Some(&ia), Some(&ib)) => goal_frame.optional_dv[ia].has_bit(ib),
                            _ => false,
                        };
                        if !declared {
                            return Err(TacticsError::DistinctVariable(format!(
                                "{} requires {} and {} to be disjoint, but the theorem doesn't declare $d {} {}",
                                cited_name, name(*li), name(*lj), na, nb
                            )));
                        }
                    }
                    needed.insert(if na <= nb { (na, nb) } else { (nb, na) });
                }
            }
        }
        Ok(())
    }

    /// Exports a proof as an mmp worksheet, starting with the `$d` lines it needs.
    pub fn export_mmp<W: Write>(&self, theorem: Label, distinct: &BTreeSet<(String, String)>, arr: &ProofTreeArray, out: &mut W) {
        for (a, b) in distinct {
            writeln!(out, "$d {} {}", a, b).unwrap();
        }
        let database = self.intern.borrow();
        let thm_label = database.name_result().atom_name(theorem);
        database.export_mmp_proof_tree(thm_label, arr, out).unwrap();
    }
}

impl Display for Symbol {
    fn format(&self, f: &mut Formatter, db: &Db) -> std::result::Result<(), std::fmt::Error> {
        let database = db.intern.borrow();
        f.write_str(as_str(
            database.name_result().atom_name(*self),
        ))
    }
}

// Label and Symbol are actually both synonyms for `Atom`, no need to duplicate definition.
//
// impl Display for Label {
// 	fn format(&self, f: &mut Formatter, db: &Db) -> std::result::Result<(), std::fmt::Error> {
// 		f.write_str(&db.label_str(self))
// 	}
// }

impl Display for Formula {
    fn format(&self, f: &mut Formatter, db: &Db) -> std::result::Result<(), std::fmt::Error> {
        let database = db.intern.borrow();
        std::fmt::Display::fmt(&self.as_ref(&database), f)
    }
}

impl Display for Substitutions {
    fn format(&self, f: &mut Formatter, db: &Db) -> std::result::Result<(), std::fmt::Error> {
        let database = db.intern.borrow();
        std::fmt::Debug::fmt(&self.as_ref(&database), f)
    }
}

// impl Display for Substitutions {
//     fn format(&self, f: &mut Formatter, db: &Db) -> std::result::Result<(), std::fmt::Error> {
//         for (l,fmla) in self.0.iter() {
//             f.write_str("\n    ")?;
//             l.format(f, db)?;
//             f.write_str(" => ")?;
//             fmla.format(f, db)?;
//         }
//         Ok(())
//     }
// }

impl Display for Box<Substitutions> {
    fn format(&self, f: &mut Formatter, db: &Db) -> std::result::Result<(), std::fmt::Error> {
        self.deref().format(f, db)
    }
}
#[cfg(test)]
mod tests {
    use super::*;

    fn dv_db() -> Db {
        let mut db = Db::default();
        db.parse(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/dv.mm")).unwrap();
        db
    }

    fn label(db: &Db, name: &str) -> Label {
        db.get_theorem_label(name.to_string()).unwrap()
    }

    fn cited(db: &Db, theorem: Option<Label>) -> Vec<String> {
        db.statements(theorem, |_, _| true).map(|(l, _, _)| db.label_name(l)).collect()
    }

    /// A goal with no database position (a new theorem) may cite every statement.
    #[test]
    fn goal_without_position_cites_every_statement() {
        let db = dv_db();
        let everything = cited(&db, None);
        assert!(everything.contains(&"later".to_string()));
        assert_eq!(everything.last().unwrap(), "later");
        assert!(db.precedes(label(&db, "later"), None));
        // A goal at a position cites only what is before it.
        let before_earlier = cited(&db, Some(label(&db, "earlier")));
        assert!(before_earlier.contains(&"ax-5".to_string()));
        assert!(!before_earlier.contains(&"earlier".to_string()));
        assert!(!before_earlier.contains(&"later".to_string()));
        assert!(db.precedes(label(&db, "ax-5"), Some(label(&db, "earlier"))));
        assert!(!db.precedes(label(&db, "earlier"), Some(label(&db, "earlier"))));
        assert!(!db.precedes(label(&db, "later"), Some(label(&db, "earlier"))));
    }

    /// Without a database theorem there is no frame declaring `$d`: distinct variables are
    /// accepted, and are the `$d` which the new theorem needs. Shared variables never are.
    #[test]
    fn goal_without_position_needs_the_distinct_variables() {
        let db = dv_db();
        let wff = db.get_symbol("wff".to_string()).unwrap();
        let setvar = db.get_symbol("setvar".to_string()).unwrap();
        let var = |name: &str, tc| Formula::from_float(label(&db, name), tc);
        let ax5 = label(&db, "ax-5");

        let mut subst = Substitutions::new();
        subst.insert(label(&db, "wph"), var("wps", wff));
        subst.insert(label(&db, "vx"), var("vx", setvar));
        let mut needed = BTreeSet::new();
        db.check_distinct(None, ax5, &subst, &Substitutions::new(), &mut needed).unwrap();
        assert_eq!(needed.into_iter().collect::<Vec<_>>(), vec![("ps".to_string(), "x".to_string())]);

        // Unbound variables, and metavariables, are deferred.
        let mut deferred = Substitutions::new();
        deferred.insert(label(&db, "wph"), var("ww1", wff));
        deferred.insert(label(&db, "vx"), var("vx", setvar));
        let mut needed = BTreeSet::new();
        db.check_distinct(None, ax5, &deferred, &Substitutions::new(), &mut needed).unwrap();
        db.check_distinct(None, ax5, &Substitutions::new(), &Substitutions::new(), &mut needed).unwrap();
        assert!(needed.is_empty());

        // The same variable on both sides: a violation whatever the goal.
        let mut shared = Substitutions::new();
        shared.insert(label(&db, "wph"), var("vx", wff));
        shared.insert(label(&db, "vx"), var("vx", setvar));
        assert!(db.check_distinct(None, ax5, &shared, &Substitutions::new(), &mut BTreeSet::new()).is_err());
    }
}
