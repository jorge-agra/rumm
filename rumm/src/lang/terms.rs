//! Formulas as plain terms, and two-sided unification, for the stepwise proof state.
//!
//! `Formula::unify` binds the variables of one side only (the model); the variables of the
//! other side are constants. A proof state has open goals holding *work variables*
//! (metavariables, `&W1`) which an applied tactic must be able to bind, while the variables
//! of the theorem being proved stay constants, and the variables of the cited statement are
//! bound as usual. So the goal's formula and the statement's are turned into terms here,
//! unified with both kinds of variable bindable, and the result is turned back into formulas
//! (through the symbols and the grammar, as `Formula` exposes no constructor).

use super::Db;
use crate::tactics::{TacticsError, TacticsResult};
use metamath_rs::formula::Substitutions;
use metamath_rs::grammar::FormulaToken;
use metamath_rs::statement::SymbolType;
use metamath_rs::{as_str, Database, Formula, Label, Span};
use std::collections::HashMap;

/// A formula as a tree. `Const` is a variable which stands for itself, `Meta` a work variable
/// (bindable) and `Model` a variable of a cited statement (bindable).
#[derive(Clone, Debug, PartialEq)]
pub enum Term {
    Const(Label),
    Meta(Label),
    Model(Label),
    Node(Label, Vec<Term>),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Key {
    Meta(Label),
    Model(Label),
}

impl Term {
    /// Replaces the `Model` variables left in the term, by `f(variable)`.
    pub fn replace_model(&self, f: &mut dyn FnMut(Label) -> TacticsResult<Term>) -> TacticsResult<Term> {
        Ok(match self {
            Term::Model(label) => f(*label)?,
            Term::Node(label, children) => {
                Term::Node(*label, children.iter().map(|c| c.replace_model(f)).collect::<TacticsResult<Vec<_>>>()?)
            }
            other => other.clone(),
        })
    }
}

/// The result of a unification: what each bound work variable and each bound variable of the
/// model stands for. Variables of the model may remain inside (`Term::Model`) when they are
/// not determined by the goal.
#[derive(Debug, Default)]
pub struct Unified {
    pub model: HashMap<Label, Term>,
    pub meta: HashMap<Label, Term>,
}

struct Unifier {
    bindings: HashMap<Key, Term>,
}

impl Unifier {
    fn walk(&self, term: &Term) -> Term {
        let mut current = term.clone();
        loop {
            let key = match &current {
                Term::Meta(l) => Key::Meta(*l),
                Term::Model(l) => Key::Model(*l),
                _ => return current,
            };
            match self.bindings.get(&key) {
                Some(next) => current = next.clone(),
                None => return current,
            }
        }
    }

    fn resolve(&self, term: &Term) -> Term {
        match self.walk(term) {
            Term::Node(l, children) => Term::Node(l, children.iter().map(|c| self.resolve(c)).collect()),
            other => other,
        }
    }

    fn occurs(&self, key: Key, term: &Term) -> bool {
        match self.walk(term) {
            Term::Meta(l) => key == Key::Meta(l),
            Term::Model(l) => key == Key::Model(l),
            Term::Node(_, children) => children.iter().any(|c| self.occurs(key, c)),
            Term::Const(_) => false,
        }
    }

    fn bind(&mut self, key: Key, term: Term) -> bool {
        if self.occurs(key, &term) {
            return false;
        }
        self.bindings.insert(key, term);
        true
    }

    fn unify(&mut self, a: &Term, b: &Term) -> bool {
        let (a, b) = (self.walk(a), self.walk(b));
        match (&a, &b) {
            (Term::Model(x), Term::Model(y)) if x == y => true,
            (Term::Meta(x), Term::Meta(y)) if x == y => true,
            (Term::Model(x), _) => self.bind(Key::Model(*x), b.clone()),
            (_, Term::Model(y)) => self.bind(Key::Model(*y), a.clone()),
            (Term::Meta(x), _) => self.bind(Key::Meta(*x), b.clone()),
            (_, Term::Meta(y)) => self.bind(Key::Meta(*y), a.clone()),
            (Term::Const(x), Term::Const(y)) => x == y,
            (Term::Node(l1, c1), Term::Node(l2, c2)) => {
                l1 == l2 && c1.len() == c2.len() && c1.iter().zip(c2).all(|(x, y)| self.unify(x, y))
            }
            _ => false,
        }
    }
}

/// Makes `acc` hold the bindings of `new` too: every value is substituted by the other, so
/// that no bound variable is left inside a value.
pub fn compose_bindings(acc: &mut Substitutions, new: &Substitutions) {
    let mut all = Substitutions::new();
    for (label, formula) in acc.iter() {
        all.insert(*label, formula.substitute(new));
    }
    for (label, formula) in new.iter() {
        all.insert(*label, formula.clone());
    }
    // Values of `new` may mention what `acc` bound: settle until nothing changes (a loop
    // would need a cycle, which the occurs check of the unifier excludes).
    for _ in 0..64 {
        let mut changed = false;
        let mut next = Substitutions::new();
        for (label, formula) in all.iter() {
            let substituted = formula.substitute(&all);
            changed |= substituted != *formula;
            next.insert(*label, substituted);
        }
        all = next;
        if !changed {
            break;
        }
    }
    *acc = all;
}

impl Db {
    /// Whether `label` is the `$f` of a metavariable.
    pub fn is_metavariable(&self, label: Label) -> bool {
        let database = self.database();
        Self::label_is_metavariable(&database, label)
    }

    fn label_is_metavariable(database: &Database, label: Label) -> bool {
        database.name_result().atom_name(label).starts_with(super::database::METAVARIABLE_LABEL_PREFIX.as_bytes())
    }

    /// How many subterms a node of this syntax axiom has: its variables.
    fn arity(database: &Database, label: Label) -> usize {
        let Some(sref) = database.statement_by_label(label) else { return 0 };
        let nset = database.name_result();
        sref.math_iter()
            .skip(1)
            .filter(|token| nset.lookup_symbol(token.slice).map(|s| s.stype == SymbolType::Variable).unwrap_or(false))
            .count()
    }

    /// The term of a formula. With `model`, the variables which are not metavariables are those
    /// of a cited statement (bindable); else they are constants.
    pub fn term_of(&self, formula: &Formula, model: bool) -> Term {
        let database = self.database();
        let mut labels = formula.labels_iter().peekable();
        fn build(database: &Database, labels: &mut dyn Iterator<Item = (Label, bool)>, model: bool) -> Term {
            let (label, is_variable) = labels.next().expect("a formula is a complete tree");
            if is_variable {
                if Db::label_is_metavariable(database, label) {
                    Term::Meta(label)
                } else if model {
                    Term::Model(label)
                } else {
                    Term::Const(label)
                }
            } else {
                let arity = Db::arity(database, label);
                Term::Node(label, (0..arity).map(|_| build(database, labels, model)).collect())
            }
        }
        build(&database, &mut labels, model)
    }

    /// Unifies a goal with the formula of a statement. With `model_vars`, the variables of the
    /// statement are bound by it (an application), else the statement is read as it is (a
    /// hypothesis: only the work variables of the goal are bound).
    pub fn unify_terms(&self, goal: &Formula, model: &Formula, model_vars: bool) -> TacticsResult<Unified> {
        let (goal, model) = (self.term_of(goal, false), self.term_of(model, model_vars));
        let mut unifier = Unifier { bindings: HashMap::new() };
        if !unifier.unify(&goal, &model) {
            return Err(TacticsError::UnificationFailed);
        }
        let mut unified = Unified::default();
        for (key, term) in &unifier.bindings {
            let resolved = unifier.resolve(term);
            match key {
                Key::Meta(l) => unified.meta.insert(*l, resolved),
                Key::Model(l) => unified.model.insert(*l, resolved),
            };
        }
        Ok(unified)
    }

    /// The tokens of a term, as a formula would write them.
    fn flatten(database: &Database, term: &Term, out: &mut Vec<String>) {
        match term {
            Term::Const(l) | Term::Meta(l) | Term::Model(l) => {
                if let Some(sref) = database.statement_by_label(*l) {
                    out.push(as_str(sref.math_at(1).slice).to_string());
                }
            }
            Term::Node(label, children) => {
                let Some(sref) = database.statement_by_label(*label) else { return };
                let nset = database.name_result();
                let mut children = children.iter();
                for token in sref.math_iter().skip(1) {
                    let is_variable =
                        nset.lookup_symbol(token.slice).map(|s| s.stype == SymbolType::Variable).unwrap_or(false);
                    if !is_variable {
                        out.push(as_str(token.slice).to_string());
                    } else if let Some(child) = children.next() {
                        Self::flatten(database, child, out);
                    }
                }
            }
        }
    }

    fn root_label(term: &Term) -> Label {
        match term {
            Term::Const(l) | Term::Meta(l) | Term::Model(l) | Term::Node(l, _) => *l,
        }
    }

    /// The formula of a term, whose typecode is the one of its root.
    pub fn formula_of(&self, term: &Term) -> TacticsResult<Formula> {
        let database = self.database();
        let root = Self::root_label(term);
        let typecode = database.label_typecode(root);
        if let Term::Const(l) | Term::Meta(l) | Term::Model(l) = term {
            return Ok(Formula::from_float(*l, typecode));
        }
        let mut tokens = Vec::new();
        Self::flatten(&database, term, &mut tokens);
        let nset = database.name_result();
        let symbols: Vec<std::result::Result<FormulaToken, _>> = tokens
            .iter()
            .map(|name| {
                nset.lookup_symbol(name.as_bytes())
                    .map(|s| Ok(FormulaToken { symbol: s.atom, span: Span::new(0, 0) }))
                    .unwrap_or(Err(metamath_rs::diag::StmtParseError::ParsedStatementNoTypeCode))
            })
            .collect();
        database
            .grammar_result()
            .parse_formula(&mut symbols.into_iter(), &[typecode], false, nset)
            .map_err(|_| TacticsError::UnificationFailed)
    }
}
