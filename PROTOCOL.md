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
| `unknown-method` | `method` is neither `ping` nor `prove` |
| `library-file`, `library-parse`, `tactic-parse` | the library can't be read or parsed; the tactic can't be parsed |
| `unknown-theorem`, `no-proof` | the label is not in the database; no `tactic` and no proof line in the library |
| `panic` | a panic inside the request, caught: the process keeps serving |
| the name of a tactics error, in kebab-case | the tactics failed: `no-match-found`, `depth-limit-exceeded`, `distinct-variable`, `cited-after-goal`, `unresolved-metavariables`... (`message` is the error as rumm prints it) |

Any failure is `"ok": false` with `proof: null`, and the process keeps serving.

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

`rumm::Engine::load(path)` then `Engine::prove(&ProveRequest, Option<TraceSink>) -> ProveOutcome`;
`rumm::serve::serve(&mut engine, reader, writer, trace)` speaks this protocol over any reader and
writer. Nothing in the library prints.
