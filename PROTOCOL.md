# rumm serve: the JSON-lines protocol

`rumm serve --db <file.mm> [--trace] [--max-depth N]` loads the plain Metamath database once,
then reads **one JSON object per line on stdin** until EOF and writes **one JSON object per line
on stdout** for each, flushed at once. Blank lines are skipped. Responses come in request order and
carry the request's `id`.

stdout carries nothing but responses. The trace of proof searches is silent unless `--trace`
is given, and then goes to stderr. Load progress is never printed. `rumm file.rmm` (batch)
is unchanged.

rumm keeps no proof state between requests: each `prove` parses its library afresh, and nothing
it defines (tactics, proofs) is visible to the next request. The only thing that persists is the
loaded database (and the metavariables declared in it, which grow on demand).

## Requests

Every request is an object with a `method` and an optional `id` (any JSON value, echoed back;
`null` if absent).

`{"id": 1, "method": "ping"}` answers `{"id": 1, "ok": true, "loads": 1}`. `loads` counts database
loads in the process: it stays 1 however many requests are served.

```
{"id": <any>, "method": "prove",
 "library": "<path to a .rmm file>"   // or "library_text": "<.rmm text>", exactly one of them
 "theorem": "<label, no ~>",
 "tactic": "<optional tactics expression, e.g. { apply ~ax-mp ! ! }>",
 "max_depth": <optional non-negative integer>}
```

- The library holds `tactics` definitions (and may hold `proof` lines). Its `load` directive is
  **ignored**, with a message in `warnings`: the database of the process is in force.
- `tactic` is the `.rmm` tactics expression to run on the theorem. By default, the library's first
  `proof ~theorem` line.
- `max_depth` overrides the nesting budget of tactics (default 100, or `--max-depth`). A tactic
  that goes deeper fails as an ordinary error.
- Metavariables (`&W1`, `&C12`...) used by the library and the tactic are declared as needed.

## Responses

```
{"id": ..., "ok": true|false,
 "proof": {"theorem": "<label>",
           "steps": [{"label": "...", "hyps": ["..."], "ref": "<label>", "expr": "|- ..."}],
           "dv": [["x", "ph"], ...]}  | null,
 "error": {"kind": "...", "message": "..."} | null,
 "warnings": ["..."]}
```

`steps` is an `.mmp` worksheet in structured form, each step after the ones it cites:

- Hypotheses of the theorem come first as `h1`, `h2`... with `ref` the database `$e` label and no `hyps`.
- The other steps are `s<n>`; the last, the conclusion, is `qed`. `ref` is the cited axiom or
  theorem.
- `hyps` lists the steps cited, in order: a derived step by its label (`s3`), a hypothesis step
  by its **number** (`"1"` for `h1`), as mmj2 `.mmp` syntax requires.
- `expr` is the statement with its typecode (`|- ...`).
- `dv` is the `$d` the proof needs, one pair of variables each.

Printing each step as `<label>:<hyps joined by ,>:<ref> <expr>`, after the `$d` lines and a
`$( <MM> <PROOF_ASST> THEOREM=<theorem>  LOC_AFTER=? ` header, gives a worksheet which `verify-mmp`
accepts as is, with no relabelling.

`error.kind` is one of:

| kind | when |
|---|---|
| `invalid-json`, `invalid-request` | the line is not JSON, or not an object, or a field has the wrong type |
| `missing-field` | `method`, `theorem` or `library`/`library_text` missing |
| `unknown-method` | `method` is not `ping`, `prove` or `apply` |
| `library-file`, `library-parse`, `tactic-parse` | the library can't be read or parsed; the tactic can't be parsed |
| `unknown-theorem`, `no-proof` | the label is not in the database; no `tactic` and no proof line in the library |
| `panic` | a panic inside the request, caught: the process keeps serving |
| the name of a tactics error, in kebab-case | the tactics failed: `no-match-found`, `depth-limit-exceeded`, `distinct-variable`, `cited-after-goal`, `unresolved-metavariables`... (`message` is the error as rumm prints it) |

Any failure is `"ok": false` with `proof: null`, and the process keeps serving.

## The stepwise request: `apply`

`apply` takes a **proof state**, one open goal of it and a tactic, and returns the new state. The
caller owns the state: rumm reads it afresh each time and keeps nothing (the loaded database
apart). The state is JSON rather than `.mmp` text (which needs a worksheet parser in rumm and ties
it to one editor's text) or MMX's internal `mmx` format.

```
{"id": <any>, "method": "apply",
 "state": {"theorem": "<label>" | null,
           "steps": [{"label": "h1", "expr": "|- ( ph -> ps )", "ref": "sylex.1", "hyps": []},
                     {"label": "s1", "expr": "|- ( ph -> &W1 )", "ref": null, "hyps": []},
                     {"label": "qed", "expr": "|- ( ph -> ch )", "ref": "syl", "hyps": ["s1", "s2"]}],
           "dv": [["x", "ph"]]},
 "goal": "<label of an open step>",
 "tactic": "<tactics expression, e.g. { apply ~syl ? ? }>",
 "library": "<path>" | "library_text": "<.rmm text>"   // optional: tactics definitions
 "max_depth": <optional>}
```

**The state.** `theorem` is the database theorem the steps prove, which gives the position (a step
can cite only what comes before it) and the `$d` it declares; `null` is a new theorem, which may cite
any statement and whose `$d` are the pairs the steps need. A step is:

- a **hypothesis** step, labelled `h<n>`: `ref` is the label of its `$e` (for a database theorem it
  must be one of the theorem's own, with the same expression; for `null`, any label), no `hyps`;
- an **open goal**: `ref` is `null`, no `hyps`. An open goal left by `{ decide ... }` also has
  `"deciders": [names]`, which rumm sets and keeps;
- a **proved step**: `ref` is the axiom or theorem it cites, `hyps` the steps it cites as its
  hypotheses, in order: a step by its label, a hypothesis step by its **number** (`"1"`), as in
  `rumm serve`'s `prove` and mmj2.

`expr` is the whole statement with its typecode. **Work variables** are `&W1` (wff), `&C1` (class),
`&S1` (setvar) (the letter comes from the typecode, as MMX's work variable tags do); a shared work
variable is the same name in every step. Steps come in any order the caller likes; rumm puts new steps
before the goal. rumm checks the state it is given: a step which doesn't follow from its `ref` and
`hyps`, a `ref` which is not in the database (**local theorems are not supported**), a
`$d` the theorem doesn't declare, are errors naming the step.

```
{"id": ..., "ok": true|false,
 "produced": ["s1", "s2"],   // labels of the steps the tactic added
 "updated": ["qed"],         // existing steps which changed: the goal, and steps whose work variable was bound
 "removed": [],              // the goal, when a hypothesis alone closed it (see below)
 "state": {...},             // the new state; on an error, the state of the request as it was sent
 "open": [{"label": "s1", "expr": "|- ( ph -> &W1 )", "deciders": null | ["names"]}, ...],
 "proved": false,            // no open goal and no work variable left
 "error": null | {"kind": "...", "message": "..."},
 "warnings": [...]}
```

- The tactic runs on the goal's expression, with the hypothesis steps as its hypotheses. The goal keeps
  its label and gets the `ref` and `hyps` the tactic found; the steps it needs are new steps, labelled
  `s<n>` with the lowest numbers no step of the state uses, placed before the goal. Identical proved
  steps are built once. Steps which were proved before are not run again.
- **`?` and `{ decide <names> }` leave open goals** (stepwise requests only): the goal becomes an open
  step, and `decide` tags it with the names. Every other failure fails its branch (`try`, `match` and
  `find` move on) and, at the top, the request: `ok: false`, an `error`, `produced` empty and the state
  unchanged. A tactic which gets partway through (`tactics half () { apply ~syl ? ? }`) keeps what it
  reached: `syl` and two open goals.
- **Work variables.** What a cited statement leaves undetermined becomes a fresh work variable (the lowest
  index above every `&W<n>` of the state, the tactic and the library; the database declares them on demand).
  `apply` and `!` bind the work variables of the goal; the bindings are applied to every step of the new
  state, and so `( ph -> &W1 )` and `( &W1 -> ch )` stay in step. A tactic written with `&W1` in its own
  patterns should avoid the names the state uses.
- **`$d`.** The returned `dv` is the request's `dv` plus the pairs the steps need. A database theorem
  must declare them (`distinct-variable` otherwise); for `theorem: null` they are exported to be declared.
  Pairs holding a work variable are checked when it is bound.
- A goal which a hypothesis alone closes (`!` is the whole tactic) is not a step: it is removed, and the
  steps which cited it cite the hypothesis (`removed`, `updated`). `goal-is-a-hypothesis` if nothing cites it.
- When no open goal is left and a work variable still is, the request fails `unresolved-metavariables`
  (the state would be stuck). `proved: true` means the state is a complete proof.

Error kinds beyond the ones above: `unknown-goal`, `goal-not-open`, `invalid-state`, `invalid-expression`,
`unknown-ref`, `step-mismatch` (the tactic's result is not the goal: a bug in a library tactic), `goal-is-a-hypothesis`, `metavariables`,
`open-goals` (batch only), and the tactic errors (`unification-failed`, `no-match-found`, ...).

A worked example (the state of `sylex`, and an `!` which binds `&W1`):

```
> {"id":1,"method":"apply","state":{"theorem":"sylex","steps":[{"label":"h1","expr":"|- ( ph -> ps )","ref":"sylex.1","hyps":[]},{"label":"h2","expr":"|- ( ps -> ch )","ref":"sylex.2","hyps":[]},{"label":"qed","expr":"|- ( ph -> ch )","ref":null,"hyps":[]}],"dv":[]},"goal":"qed","tactic":"{ apply ~syl ? ? }"}
< {"id":1,"ok":true,"produced":["s1","s2"],"updated":["qed"],"removed":[],"open":[{"label":"s1","expr":"|- ( ph -> &W1 )","deciders":null},{"label":"s2","expr":"|- ( &W1 -> ch )","deciders":null}],"proved":false,"state":{...},"error":null,"warnings":[]}
> {"id":2,"method":"apply","state":{...the state above...},"goal":"s1","tactic":"!"}
< {"id":2,"ok":true,"produced":[],"updated":["s2","qed"],"removed":["s1"],"open":[{"label":"s2","expr":"|- ( ps -> ch )","deciders":null}],"proved":false,...}
```

(`tests/stepwise.rs` runs these, over `tests/fixtures/step.mm`, and two complete proofs on set.mm.)

## Trying it by hand

```sh
cd rumm/tests/fixtures
printf '%s\n' \
  '{"id":1,"method":"ping"}' \
  '{"id":2,"method":"prove","library_text":"","theorem":"panics","tactic":"{ apply ~ax-mp ! ! with ~wph $ ph $ }"}' \
  '{"id":3,"method":"nonsense"}' \
  '{"id":4,"method":"ping"}' | cargo run -q -- serve --db mini.mm
```

prints, one object per line (field order may differ):

```
{"id":1,"loads":1,"ok":true}
{"id":2,"ok":true,"proof":{"theorem":"panics","steps":[{"label":"h1","hyps":[],"ref":"panics.1","expr":"|- ph"},{"label":"h2","hyps":[],"ref":"panics.2","expr":"|- ( ph -> ps )"},{"label":"qed","hyps":["1","2"],"ref":"ax-mp","expr":"|- ps"}],"dv":[]},"error":null,"warnings":[]}
{"id":3,"ok":false,"proof":null,"error":{"kind":"unknown-method","message":"unknown method \"nonsense\""},"warnings":[]}
{"id":4,"loads":1,"ok":true}
```

## Library use

`rumm::Engine::load(path)` then `Engine::prove(&ProveRequest, Option<TraceSink>) -> ProveOutcome` and
`Engine::apply(&rumm::stepwise::ApplyRequest, Option<TraceSink>) -> ApplyOutcome`;
`rumm::serve::serve(&mut engine, reader, writer, trace)` speaks this protocol over any reader and
writer. Nothing in the library prints.
