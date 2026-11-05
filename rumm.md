# The Rumm Language

This description of the Rumm language provides syntax where expressions in brackets like `<formula>` are syntactic constructs. It also provides examples, which assume the `set.mm` database is used.

The Rumm language deals with three kinds of expressions:
- [formulas](#formulas),
- [theorems](#theorems),
- [tactics](#tactics).

At top level, Rumm files list tactic scripts and proofs.
Tactic scripts are sub-routine-like proof elements which can be called with variable parameters. The `tactics` keyword allows to declare such a tactics script:
```
tactics <tactics name> (<parameter ID> ... <parameter ID>) <tactics>
```
Tactics scripts allow modularity. Common proof schemes can be described in script tactics, and reused in several proofs, or as sub-tactics.

Proofs simply tell the Rumm program to apply the given tactics to generate a proof for a given theorem statement. They are the starting point for proof elaboration.
```
proof <statement> <tactics>
```
In addition, the `load` keyword tells the program to load the specified MM database file.
```
load <filename>
```

## Metavariables

For practical purposes, it's convenient to make a distinction between formulas that contain metavariables and the ones that don't. A metavariable in Rumm is written `&` followed by an uppercase letter and a number: `&W1`, `&C12`, `&S3`.

**No `.mm` file declares them.** The database loaded by a script is a plain one. Rumm loads it through a synthetic, in-memory root file which includes the database and then declares the metavariables as `$v` and `$f` (nothing is written to disk). Their `$f` labels start with `rumm.mv.`; a database already using that prefix is refused.

- **The letter gives the typecode**, derived from the database the way MMX derives its work variables: the typecodes having a `$f`, in order of their first `$f`, each take the first letter of their name (uppercased, A-Z only) not already taken, else the first free letter. On set.mm this gives `&W` for `wff`, `&S` for `setvar` and `&C` for `class` (on a Peano-style database with `wff`, `term` and `var`, `&W`, `&T` and `&V`). The typecode is enforced: binding a class metavariable to a wff, for instance as the value of a `with` substitution, fails with a `WrongTypecode` tactic error. A letter that maps to no typecode is an unknown symbol.
- **There is no limit** set by a declaration. Rumm scans the script for the highest index used for each letter, and declares that many, plus a reserve of 8 for fresh ones. The synthetic segment can be regenerated larger later in the same process (`Db::ensure_metavariables`), reparsing incrementally; the formulas built before stay valid.
- **A metavariable never reaches a finished proof.** A proof which still contains one, in a step or in the substitution of a citation, is not complete: it is reported as `Failure: UnresolvedMetavariables("&C2")` naming them, and nothing is exported. A metavariable bound by a `match` or `find` is substituted before that, so the proof is fine. (This also covers the `$d` pairs holding a metavariable, which can only be checked once it is bound.)

## Tactics

When evaluated, tactics generate proofs. Tactics are evaluated within a *context* with the following properties:
- a **goal**: the goal is the formula to be currently proven. In Rumm, there is always a single goal at any point of the program.
- **hypotheses**: this is a set of formulas known to be proven. When a proof is initiated for a given theorem, this includes all theorem's (`\$e`, essential) hypotheses. Along the proof process, intermediate subgoals are added to this list.
- **local variables**: variables are strongly typed and can be either formula variables (with identifiers prefixed with `+`), theorem variables (prefixed with `≈`), or tactics variables (prefixed with `@`).

Tactics may succeed and return a proof, or fail. Tactics themselves are generally enclosed within brackets `{ ... }`. 

### **The `!` built-in tactics**

This is the simplest possible tactics: it attempts to match the goal with one of the hypotheses or already proven subgoals. Its syntax is a single exclamation mark sign, `!`.

---

### **The `?` built-in tactics**

This is only a dummy proof placeholder. In a batch run it always fails, but allows to build a syntactically correct Rumm file where a tactics is needed. Its syntax is a single question mark sign, `?`.

In a [stepwise request](#stepwise-requests) (`apply`, see `PROTOCOL.md`) it does not fail: the goal becomes an **open goal** of the returned proof state.

---

### **The `decide` built-in tactics**

`{ decide ring-eval simp }` leaves the goal to *deciders*, which are named. The names are free text (identifiers, possibly none); rumm does not know what they mean. In a stepwise request the goal is returned as an open goal tagged with the names (`"deciders": ["ring-eval", "simp"]`), and the caller hands it to whoever decides. It is the stage one of deciders: rumm never calls one.

In a batch run nothing returns a state, so a proof with an open goal is not complete: it is reported as `Failure: OpenGoals(...)` naming the deciders. Inside `try` or `find` the tactics succeeds (it always does), so a `try` which should move on past it needs to be ordered after the alternatives that really prove the goal.

---

### **The `apply` built-in tactics**

This is the atomic building block for proofs, applying a single theorem.
```
{ apply <statement> <tactics> ... <tactics> with <statement> <formula> ... <statement> <formula> }
```
The theorem specified by `<statement>` is applied. A list of tactics is provided following the theorem's statement name, which will be used to recursively prove each of the theorem's essential hypotheses. The single goal for these tactics will be the hypothesis, with the theorems variables substitued in the current context. In some cases, there are variables which don't appear in the theorem's statement. 

This example applies the `~a1i` theorem, and attempts to match the hypothesis with already proven statements.
```
{ apply ~a1i ! }
```

This example applies syllogism `~syl` to the current goal:
```
syl.1 $e |- ( ph -> ps ) $.
syl.2 $e |- ( ps -> ch ) $.
$( An inference version of the transitive laws for implication $)
syl $p |- ( ph -> ch ) $= ( wi a1i mpd ) ABCDBCFAEGH $.
```
Since `~syl`'s final statement, `( ph -> ch )`, does not include the `ps` wff variable, one has to provide it manually using the `with` keyword.
```
{ apply ~syl ! ! with ~wps $ A e. V $ }
```

---

### **The `subgoal` built-in tactics**

Rumm generally works top-down, i.e. one starts with a proof for the last step of the final results, and then works one's way to more elementary sub-proofs. This tactics allows to write proofs "bottom up", i.e. first provide a proof for an arbitrary statement, and then the proof for the current goal, whereas the subgoal is already proven.
```
{ subgoal <tactics> <formula> <tactics> }
```
The formula provided is the statement of the subgoal.
The first tactics, listed before that formula, is applied to find a proof for that subgoal.
The second tactics, listed after the formula, is applied to find a proof for the final goal, whereas the formula is a known true statement, and can be found e.g. using the `!` tactics.

---

### **The `try` built-in tactics**

This tactics allows to try a sequence of different tactics.
```
{ try <tactics> ... <tactics> }
```
Each tactics is applied to prove the current goal, and the `try` tactics return the proof provided by first successful sub-tactics. This tactics fails if *all* sub-tactics fail. In the current implementation tactics are tried in the order they are provided.

---

### **The `match` built-in tactics**

This tactics attempts to match a given fixed formula with a list of formulas, and applies different tactics based on the match.
```
{ match <formula> <formula> <tactics> ... <formula> <tactics> }
```
The formula to match is provided first. It is often the current goal.
Then, a list of couples for formula pattern and tactics are provided. 

Example:
```
{ match goal
    $ ( &W1 -> &W2 ) $ @T1
    $ ( &W1 /\ &W2 ) $ @T2
}
```
If the current goal is an implication `->`, this tactics applies `@T1`.
If it is a conjunction `/\`, it applies `@T2`.

The metavariables used in the matched formula pattern hold an expression that can be used in the provided tactics:
```
proof ~alinexa
{ match goal
    $ ( A. x &W1 <-> -. E. x &W2 ) $
    { apply ~bitri
        { apply ~imnang }
        { apply ~alnex }
        with ~wps $ A. x -. &W2 $
    }
}
```
The example above provides a tactics-based proof of [~alinexa](https://us.metamath.org/mpeuni/alinexa.html). The goal matches with the provided formula pattern `$ ( A. x &W1 <-> -. E. x &W2 ) $`, therefore the metavariable `&W1` holds the wff formula `( ph -> -. ps )`, while `&W2` holds `( ph /\ ps )`. Since `~bitri`'s final statement does not include the wff variable `ps`, the expression carried by `&W2` is used by an apply tactics to provide a substitution for it.

This mechanism is useful to imitate [mmj2](https://github.com/digama0/mmj2) work variables, which Rumm currently does not support. The main advantage of work variables is the ability to manipulate formulas without knowing their full extention during the proof process.

---

### **The `find` built-in tactics**

This tactics finds in the loaded database a theorem matching the given formula template, and applies the given tactics.
```
{ find <tactics> <formula> <tactics> }
```
If a match with the given formula is found, the first tactics provided is used to find a proof for the theorem's hypotheses. Note that only one tactics is provided for all hypotheses.
Then the second tactics is applied to prove the given formula itself.

The formula is matched against each theorem's statement in either direction: the statement's variables may be bound to parts of the formula (the formula is an instance of the statement), or the formula's metavariables may be bound to parts of the statement. The first is tried first. The `finddf` tactics is the same, restricted to definitions (axioms labelled `df-...`).

---

### **The `findhyp` built-in tactics**
This tactics finds an hypothesis matching the given formula template and applies the given tactics when a match is found. 
```
{ findhyp <formula> <tactics> }
```
Similarly to the `match` tactics, the metavariables in the formula template can be used in the provided tactic to resolve the goal.
```
proof ~con3i
{ findhyp
    $ ( &W1 -> &W2 ) $
    { apply ~nsyl
        { apply ~id }
        !
        with ~wps $ &W2 $
    }
}
```
The above example provides a tactics-based proof of [~con3i](https://us.metamath.org/mpeuni/con3i.html). The metavariable `&W1` holds the wff formula `ph`, while `&W2` holds the wff formula `ps`, the latter is used by the `with` keyword to provide a formula for the unknown wff variable of `~nsyl`.

---

### **The `use` built-in tactics**

This tactics allows to use a generic tactics script.
```
{ use <tactics name> <parameter> ... <parameter> }
```
Each parameter is evaluated, and the tactics script is executed with additional context variables corresponding to each of the parameters.
The `<parameter>` tag represents either a formula `<formula>`, a theorem `<statement>`, a tactics `<tactics>` or a substitution list provided with the `with` keyword.

In the example below, a tactics script named "example" is defined, taking one tactics parameter named `@T`.
It is then used to prove a theorem `~ex1`, whereas the tactics `!` is going to be applied for parameter `@T`.
```
tactics example(@T) {
    apply ~a1i @T
}

proof ~ex1 {
    use example !
}
```
The following example contains a tactics script that takes a substitution list `*U` as parameter.
Such parameter is used to prove the theorem [~pm2.43a](https://us.metamath.org/mpeuni/pm2.43a.html), where an explicit list is provided as substitution for `*U`.
```
tactics example ( with *U )
{ apply ~mpid 
    { apply ~id }
    !
    with *U
}

proof ~pm2.43a {
    use example with ~wch $ ps $
}
```
The `with` keyword can also be combined with the substitution keyword `s/`:
```
tactics example ( with *U )
{ match goal
    $ ( &W1 -> ( &W2 -> &W3 ) ) $
    { apply ~syl9
        !
        { apply ~pm2.27 }
        with ~wch s/ *U / $ &W3 $
    }
}

proof ~com23 {
    use example with ~wps $ ch $
}
```
The metavariable  `&W3` holds the formula `( ps -> th )`, derived from the `match` tactics. The explicit substitution list given as parameter to the `use` tactics is then used to replace `ps` with `ch` in `&W3`, therefore deriving `( ch -> th )`, which is the sub-formula we need to prove [~com23](https://us.metamath.org/mpeuni/com23.html).

---

## Stepwise requests

Besides the batch run (`rumm file.rmm`), a caller who holds a *proof state* can ask rumm to apply one tactics to one of its open goals (`apply`, in `rumm serve`; the format is in `PROTOCOL.md`). The state is given in full and returned in full, rumm keeps nothing. Running the tactics is the same as in a batch run, with these differences, which apply to a stepwise request only:

- **`?` and `decide` leave open goals.** The tactics which fail still fail their branch, so `try`, `match` and `find` branch as before. A leaf which is `?` or `{ decide ... }` is not a failure: the goal becomes an open goal in the new state.
- **Partial progress.** A tactics which gets as far as `?` or `decide` leaves keeps what it did before. `tactics half () { apply ~syl ? ? }` applied to `( ph -> ch )` cites `syl` and returns the two open goals `( ph -> &W1 )` and `( &W1 -> ch )`. A tactics which fails anywhere else returns nothing: the state is unchanged.
- **Work variables.** What `apply ~syl` leaves undetermined (the `ps` of the example) is a fresh work variable, never a variable of the cited statement, which would read as the theorem's own. The goal may hold work variables itself: `apply` and `!` bind them when the statement or the hypothesis fixes them (`( ph -> &W1 )` with `apply ~id` binds `&W1` to `ph`), and the binding is applied to every step and open goal of the returned state, and to the subgoals after the one which bound it. A tactics written in a library should not use the work variable names of the state in its own `match` patterns (`&W1` there is a pattern variable, not the state's).
- **`find`, `finddf`, `findhyp` and `match` do not bind the work variables of the goal** (their metavariables are patterns, as in a batch run). Use `apply` and `!` to bind.
- **Limits.** A goal closed by a hypothesis alone (`!` as the whole tactics) is not a step of its own: the steps which cited it cite the hypothesis. That is refused for the conclusion, which nothing cites. A `subgoal` does not pass the work variables bound in its first tactics to its second.

## Depth limit

Tactics may call each other recursively, and a script can make them cycle (`equality` calling `deduction` calling `equality`...). To end such a run with an error rather than a stack overflow, the nesting depth of tactics is limited. **The default limit is 100** (the stock `set.rmm` proofs nest about 20 deep), and the command line switch `--max-depth <N>` changes it. A tactics nested deeper than the limit fails, as any tactics would, with `DepthLimitExceeded`: `try` can move on to its next alternative, and otherwise the proof fails and the next proof of the script runs.

## Failures

A proof which cannot be built, or whose export panics (for instance because a work variable was left unbound), is reported as `Failure` for that proof; the following proofs still run. Errors in loading the database or the script are reported with their diagnostic and file, and rumm exits with status 1.

## Theorems

"Constant" theorems are refered to by their name in the loaded database, prefixed with a tilde sign `~`. For example,
```
~syl
```
Refers to the `syl` theorem of the loaded database.

Variable theorems are referred to by identifiers with the "approximately equal" sign `≈` prefix (two tildes).


## Formulas

A constant formula is written within dollar signs `$`. For example,
```
$ ( 1 + 1 ) = 2 $
```
Such constant formulas must be syntactically correct for the loaded database.

Variable formulas are referred to by identifiers with the plus sign `+` prefix.

---

### **The `goal` generic formula**

This resolves to the current goal.
```
goal
```

---

### **The `statement` generic formula**

This resolves to the provided theorem's final statement.
```
statement <statement>
```

For example, this would resolve to `( ph -> ch )`:
```
statement ~syl
```
---

### **The substitution `s/` keyword**
The substitution keyword replaces a subformula inside a formula with another formula.

```
s/ <formula> / <formula> / <formula>
```

The first formula is the subformula that we want to replace, while the second formula is the replacement of the first formula. The third formula is the expression where the replacement is applied.

In the following example, the wff formula `( ph -> ps )` is substituted with `ph` in `$ A. x ( ph -> ps ) $`, therefore resulting in `$ A. x ph $`, which is what is needed to prove [~stdpc5v](https://us.metamath.org/mpeuni/stdpc5v.html).

```
proof ~stdpc5v
{ apply ~syl5
    { apply ~ax-5 }
    { apply ~alim }
    with ~wps s/ $ ( ph -> ps ) $ / $ ph $ / $ A. x ( ph -> ps ) $
}
```
This feature is particularly useful when the full formula is not known:
```
proof ~stdpc5v
{ match goal
    $ ( A. x &W1 -> &W2 ) $
    { apply ~syl5
        { apply ~ax-5 }
        { apply ~alim }
        with ~wps s/ $ &W1 $ / $ ph $ / $ A. x &W1 $
    }
}
```
The metvariable `&W1` holds a wff expression determined by the match tactic, which can be subsequently extracted and replaced with the `s/` keyword as shown above.

---
