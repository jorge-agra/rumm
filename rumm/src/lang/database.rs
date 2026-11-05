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
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::ops::Bound;
use std::ops::Deref;
use std::io::Write;
use std::sync::Arc;

/// A type for representing theorem essential hypotheses: a label and the corresponding formula.
pub type Hypotheses = Box<[(Label, Formula)]>;

/// The prefix of the labels of the `$f` hypotheses which type the metavariables. The labels
/// are not valid in a script, and a database which already uses the prefix is refused, so a
/// metavariable can't be mistaken for a statement of the database.
pub const METAVARIABLE_LABEL_PREFIX: &str = "rumm.mv.";

/// The name of the synthetic in-memory file which includes the database and declares the
/// metavariables. Nothing is written to disk.
const ROOT_FILE: &str = "rumm:root";

/// How many metavariables of each letter are declared beyond the ones the scripts use,
/// for the tactics which need fresh ones.
pub const METAVARIABLE_RESERVE: usize = 8;

/// The metavariables of a database: `&<letter><n>`, whose letter gives the typecode.
#[derive(Default)]
struct Metavariables {
    /// The database file the synthetic root includes.
    file: String,
    /// The typecode of each letter, see `Db::letter_typecodes`.
    letters: BTreeMap<char, String>,
    /// How many metavariables of each letter the synthetic segment declares.
    declared: BTreeMap<char, usize>,
    /// The highest index the scripts use, by letter.
    required: BTreeMap<char, usize>,
}

/// The highest index of each metavariable letter (`&W3`, `&C12`...) used in a text.
pub fn scan_metavariables(text: &str) -> BTreeMap<char, usize> {
    let mut used = BTreeMap::new();
    for token in text.split_whitespace() {
        let mut chars = token.chars();
        if chars.next() != Some('&') { continue; }
        let Some(letter) = chars.next().filter(char::is_ascii_uppercase) else { continue };
        let digits = chars.as_str();
        if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) { continue; }
        if let Ok(index) = digits.parse::<usize>() {
            let highest = used.entry(letter).or_insert(0);
            *highest = (*highest).max(index);
        }
    }
    used
}

#[derive(Clone)]
pub struct Db {
    intern: Arc<RefCell<Database>>,
    metavariables: Arc<RefCell<Metavariables>>,
    /// Whether loading prints its progress on stdout (the batch command line does).
    verbose: bool,
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
            metavariables: Arc::new(RefCell::new(Metavariables::default())),
            verbose: true,
        }
    }
}

impl Db {
    /// Chooses whether loading prints its progress on stdout (the default), or nothing.
    pub fn set_verbose(&mut self, verbose: bool) {
        self.verbose = verbose;
    }

    fn progress(&self, text: String) {
        if self.verbose {
            print!("{}", text);
        }
    }

    /// Loads the plain database `filename`, and declares the metavariables of the scripts.
    ///
    /// The database is loaded through a synthetic in-memory root file which includes it, then
    /// declares the metavariables as `$v` and `$f`, so that no `.mm` file has to. The root is
    /// first parsed with the include alone to learn the typecodes, then with the declarations;
    /// the second parse reuses the file already read.
    pub fn parse(&mut self, filename: &str) -> Result {
        self.progress(format!("Loading \"{}\" ... ", filename));
        {
            let mut meta = self.metavariables.borrow_mut();
            meta.file = filename.to_string();
            meta.declared.clear();
            meta.letters.clear();
        }
        if filename.contains(char::is_whitespace) || filename.contains('$') {
            return Err(Error::MetavariableError(format!("cannot include \"{}\": the path has spaces or `$`", filename)));
        }
        {
            let mut database = self.intern.borrow_mut();
            database.parse(ROOT_FILE.to_string(), vec![(ROOT_FILE.to_string(), Self::root_text(filename, &BTreeMap::new()))]);
            let (letters, collision) = Self::letter_typecodes(&database);
            if let Some(label) = collision {
                return Err(Error::MetavariableError(format!(
                    "the database uses the label \"{}\", whose prefix \"{}\" is reserved for metavariables", label, METAVARIABLE_LABEL_PREFIX)));
            }
            self.metavariables.borrow_mut().letters = letters;
        }
        self.declare_metavariables(false)?;
        self.check_diagnostics(filename)?;
        self.progress(format!("{}\n", "ok".green()));
        self.run_passes(filename)
    }

    /// Makes sure at least the given highest index of each letter (`'W' => 9` for `&W1`..`&W9`)
    /// can be used, with a reserve of fresh metavariables beyond it. When more must be declared,
    /// the synthetic segment is regenerated larger and the database reparsed incrementally.
    /// Formulas built before remain valid. Letters without a typecode are ignored.
    pub fn ensure_metavariables(&mut self, needs: &BTreeMap<char, usize>) -> Result {
        let grow = {
            let mut meta = self.metavariables.borrow_mut();
            let mut grow = false;
            for (&letter, &index) in needs {
                if !meta.letters.contains_key(&letter) { continue; }
                let required = meta.required.entry(letter).or_insert(0);
                *required = (*required).max(index);
                grow |= index > meta.declared.get(&letter).copied().unwrap_or(0);
            }
            grow
        };
        if !grow {
            return Ok(());
        }
        let file = self.metavariables.borrow().file.clone();
        self.declare_metavariables(true)?;
        self.check_diagnostics(&file)?;
        self.run_passes(&file)
    }

    /// Records the metavariables the scripts use (see `scan_metavariables`) for the next `parse`,
    /// or declares them at once if a database is loaded.
    pub fn require_metavariables(&mut self, needs: &BTreeMap<char, usize>) -> Result {
        let loaded = !self.metavariables.borrow().file.is_empty();
        if loaded {
            return self.ensure_metavariables(needs);
        }
        let mut meta = self.metavariables.borrow_mut();
        for (&letter, &index) in needs {
            let required = meta.required.entry(letter).or_insert(0);
            *required = (*required).max(index);
        }
        Ok(())
    }

    /// The typecode of each metavariable letter, in the way MMX derives its work variable tags:
    /// the typecodes with a `$f` in order of first `$f`, each taking the first letter of its
    /// uppercased name (A-Z only) not yet taken, else the first free letter (a typecode with no
    /// letter left has no metavariables). Also returns a label of the database which uses the
    /// reserved metavariable prefix, if any.
    fn letter_typecodes(database: &Database) -> (BTreeMap<char, String>, Option<String>) {
        let mut order: Vec<String> = vec![];
        let mut collision = None;
        for sref in database.statements() {
            if sref.statement_type() == StatementType::Floating {
                let typecode = as_str(sref.math_at(0).slice).to_string();
                if !order.contains(&typecode) {
                    order.push(typecode);
                }
            }
            if collision.is_none() && sref.label().starts_with(METAVARIABLE_LABEL_PREFIX.as_bytes()) {
                collision = Some(as_str(sref.label()).to_string());
            }
        }
        let mut letters: BTreeMap<char, String> = BTreeMap::new();
        for typecode in order {
            let own = typecode.to_uppercase().chars().filter(char::is_ascii_uppercase).find(|c| !letters.contains_key(c));
            if let Some(letter) = own.or_else(|| ('A'..='Z').find(|c| !letters.contains_key(c))) {
                letters.insert(letter, typecode);
            }
        }
        (letters, collision)
    }

    /// The text of the synthetic root: the include of the database and the declarations of
    /// `counts[letter]` metavariables of each letter.
    fn root_text(file: &str, declarations: &BTreeMap<char, (String, usize)>) -> Vec<u8> {
        let mut text = format!("$[ {} $]\n", file);
        for (letter, (_, count)) in declarations {
            for chunk in (1..=*count).collect::<Vec<_>>().chunks(20) {
                let names: Vec<String> = chunk.iter().map(|i| format!("&{}{}", letter, i)).collect();
                text.push_str(&format!("$v {} $.\n", names.join(" ")));
            }
        }
        for (letter, (typecode, count)) in declarations {
            for i in 1..=*count {
                text.push_str(&format!("{}{}{} $f {} &{}{} $.\n", METAVARIABLE_LABEL_PREFIX, letter, i, typecode, letter, i));
            }
        }
        text.into_bytes()
    }

    /// Parses the synthetic root with the declarations the scripts require (`growing`: at least
    /// what is declared already).
    fn declare_metavariables(&mut self, growing: bool) -> Result {
        let (file, declarations) = {
            let mut meta = self.metavariables.borrow_mut();
            let mut declarations = BTreeMap::new();
            for (&letter, typecode) in &meta.letters {
                let required = meta.required.get(&letter).copied().unwrap_or(0);
                let declared = meta.declared.get(&letter).copied().unwrap_or(0);
                let count = if growing && required <= declared { declared } else { required + METAVARIABLE_RESERVE };
                declarations.insert(letter, (typecode.clone(), count));
            }
            for (&letter, (_, count)) in &declarations {
                meta.declared.insert(letter, *count);
            }
            (meta.file.clone(), declarations)
        };
        let mut database = self.intern.borrow_mut();
        database.parse(ROOT_FILE.to_string(), vec![(ROOT_FILE.to_string(), Self::root_text(&file, &declarations))]);
        Ok(())
    }

    fn check_diagnostics(&self, filename: &str) -> Result {
        let err = self.intern.borrow().diag_notations();
        if !err.is_empty() {
            return Err(Error::DBError(filename.to_string(), err));
        }
        Ok(())
    }

    fn run_passes(&self, filename: &str) -> Result {
        let mut database = self.intern.borrow_mut();
        self.progress(format!("Building \"{}\" grammar... ", filename));
        database.grammar_pass();
        let gerr = database.diag_notations();
        if !gerr.is_empty() {
            return Err(Error::DBError(filename.to_string(), gerr).into());
        }
        self.progress(format!("{}\n", "ok".green()));

        self.progress(format!("Parsing \"{}\"... ", filename));
        database.stmt_parse_pass();
        let gerr = database.diag_notations();
        if !gerr.is_empty() {
            return Err(Error::DBError(filename.to_string(), gerr).into());
        }
        self.progress(format!("{}\n", "ok".green()));
        Ok(())
    }

    /// The typecode of each metavariable letter of the loaded database.
    pub fn metavariable_letters(&self) -> BTreeMap<char, String> {
        self.metavariables.borrow().letters.clone()
    }

    /// The names of the metavariables (`&W1`...) in a formula.
    pub fn metavariables_in(&self, formula: &Formula, into: &mut BTreeSet<String>) {
        let database = self.intern.borrow();
        for (label, is_variable) in formula.labels_iter() {
            if is_variable {
                if let Some(name) = Self::variable_name(&database, label).filter(|n| n.starts_with('&')) {
                    into.insert(name);
                }
            }
        }
    }

    pub(crate) fn database(&self) -> std::cell::Ref<'_, Database> {
        self.intern.borrow()
    }

    /// The `$f` labels of a statement's frame, which key its substitutions, in order.
    pub fn floating_labels(&self, label: Label) -> Vec<Label> {
        let database = self.intern.borrow();
        database.get_frame(label).map(|frame| frame.floating().collect()).unwrap_or_default()
    }

    /// Whether `label` names an axiom or a provable statement, which a step may cite.
    pub fn is_assertion(&self, label: Label) -> bool {
        let database = self.intern.borrow();
        database
            .statement_by_label(label)
            .map(|sref| matches!(sref.statement_type(), StatementType::Axiom | StatementType::Provable))
            .unwrap_or(false)
    }

    /// `count` distinct labels of the database, which stand for the hypotheses of a theorem
    /// with no database statement (a new theorem): a hypothesis step only needs a label to
    /// be told from the others.
    pub fn placeholder_labels(&self, count: usize) -> Vec<Label> {
        let database = self.intern.borrow();
        let nset = database.name_result();
        database
            .statements()
            .filter_map(|sref| nset.lookup_label(sref.label()).map(|l| l.atom))
            .take(count)
            .collect()
    }

    /// The name of the typecode of a formula.
    pub fn typecode_name(&self, formula: &Formula) -> String {
        let database = self.intern.borrow();
        as_str(database.name_result().atom_name(formula.get_typecode())).to_string()
    }

    /// The name of the typecode of a statement.
    pub fn label_typecode_name(&self, label: Label) -> String {
        let database = self.intern.borrow();
        as_str(database.name_result().atom_name(database.label_typecode(label))).to_string()
    }

    /// The formula of a step text without its typecode (`( ph -> ps )`), `Err` with the first
    /// unknown symbol or the parse problem.
    pub fn parse_expression(&self, body: &str) -> std::result::Result<Formula, String> {
        let database = self.intern.borrow();
        let nset = database.name_result();
        let mut symbols: Vec<std::result::Result<FormulaToken, StmtParseError>> = Vec::new();
        for name in body.split_whitespace() {
            let symbol = nset.lookup_symbol(name.as_bytes()).ok_or_else(|| format!("unknown symbol {}", name))?;
            symbols.push(Ok(FormulaToken { symbol: symbol.atom, span: metamath_rs::Span::new(0, 0) }));
        }
        let grammar = database.grammar_result().clone();
        grammar
            .parse_formula(&mut symbols.into_iter(), &grammar.typecodes(), false, nset)
            .map_err(|e| format!("cannot parse the expression: {:?}", e))
    }

    /// The symbols of a formula, without its typecode.
    pub fn expression_body(&self, formula: &Formula) -> String {
        let database = self.intern.borrow();
        let shown = format!("{}", formula.as_ref(&database));
        match shown.split_once(' ') {
            Some((_, body)) => body.to_string(),
            None => String::new(),
        }
    }

    /// The formula of the metavariable `&<letter><index>`, if declared.
    pub fn metavariable(&self, letter: char, index: usize) -> Option<Formula> {
        let typecode = self.metavariables.borrow().letters.get(&letter)?.clone();
        let label = self.get_theorem_label(format!("{}{}{}", METAVARIABLE_LABEL_PREFIX, letter, index))?;
        let database = self.intern.borrow();
        let typecode = database.name_result().lookup_symbol(typecode.as_bytes())?.atom;
        Some(Formula::from_float(label, typecode))
    }

    /// The letter of the metavariables of a typecode.
    pub fn metavariable_letter(&self, typecode: &str) -> Option<char> {
        self.metavariables.borrow().letters.iter().find(|(_, t)| t.as_str() == typecode).map(|(l, _)| *l)
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
    use crate::lang::DisplayPair;

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
        deferred.insert(label(&db, "wph"), var(&format!("{}W1", METAVARIABLE_LABEL_PREFIX), wff));
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

    fn fixture(name: &str) -> String {
        format!("{}/tests/fixtures/{}", env!("CARGO_MANIFEST_DIR"), name)
    }

    fn letters(db: &Db) -> Vec<(char, String)> {
        db.metavariable_letters().into_iter().collect()
    }

    /// The letters follow MMX's work variable tags: first letter of the typecode not yet taken.
    #[test]
    fn letters_are_derived_from_the_typecodes() {
        let mut db = Db::default();
        db.parse(&fixture("meta.mm")).unwrap();
        assert_eq!(letters(&db), vec![('C', "class".to_string()), ('W', "wff".to_string())]);
        // dv.mm: `wff` then `setvar`.
        assert_eq!(letters(&dv_db()), vec![('S', "setvar".to_string()), ('W', "wff".to_string())]);
        let mut peano = Db::default();
        peano.parse(&fixture("peano.mm")).unwrap();
        assert_eq!(
            letters(&peano),
            vec![('T', "term".to_string()), ('V', "var".to_string()), ('W', "wff".to_string())]
        );
    }

    #[test]
    fn scripts_set_how_many_metavariables_are_declared() {
        let used = scan_metavariables("$ ( &W9 -> &C12 = &C12x ) $ &x1 &W &W2 // &S7");
        assert_eq!(used, BTreeMap::from([('S', 7), ('W', 9), ('C', 12)]));
        let mut db = Db::default();
        db.require_metavariables(&used).unwrap();
        db.parse(&fixture("meta.mm")).unwrap();
        // The scripts' use, plus the reserve; no ceiling at 5, 7 or 6.
        assert!(db.get_symbol("&W9".to_string()).is_some());
        assert!(db.get_symbol(format!("&C{}", 12 + METAVARIABLE_RESERVE)).is_some());
        assert!(db.get_symbol(format!("&C{}", 13 + METAVARIABLE_RESERVE)).is_none());
        // Letters without a typecode (`S`) are ignored.
        assert!(db.get_symbol("&S1".to_string()).is_none());
    }

    /// More metavariables can be declared later in the same process; what was built stays valid.
    #[test]
    fn metavariables_can_grow_in_the_same_process() {
        let mut db = Db::default();
        db.parse(&fixture("meta.mm")).unwrap();
        let w1 = db.get_symbol("&W1".to_string()).unwrap();
        let wff = db.get_symbol("wff".to_string()).unwrap();
        let before = Formula::from_float(label(&db, &format!("{}W1", METAVARIABLE_LABEL_PREFIX)), wff);
        assert!(db.get_symbol("&W40".to_string()).is_none());
        db.ensure_metavariables(&BTreeMap::from([('W', 40)])).unwrap();
        assert!(db.get_symbol("&W40".to_string()).is_some());
        assert!(db.get_symbol(format!("&W{}", 40 + METAVARIABLE_RESERVE)).is_some());
        assert_eq!(db.get_symbol("&W1".to_string()), Some(w1));
        assert_eq!(format!("{}", DisplayPair(&before, &db)), "wff &W1");
        // Parsing a formula with the new metavariable works.
        assert!(db.get_theorem_label(format!("{}W40", METAVARIABLE_LABEL_PREFIX)).is_some());
    }

    #[test]
    fn a_database_using_the_reserved_label_prefix_is_refused() {
        let mut db = Db::default();
        let error = db.parse(&fixture("reserved.mm")).unwrap_err();
        assert!(format!("{}", error).contains("rumm.mv.W1"), "{}", error);
    }
}
