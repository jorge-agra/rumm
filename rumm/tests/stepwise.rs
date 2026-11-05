//! Tests of the stepwise request (`apply`, see PROTOCOL.md): a tactic applied to one goal of
//! a proof state, over `tests/fixtures/step.mm` and `dv.mm`.
//!
//! None needs set.mm, except `worked_sequences_on_setmm`, which runs only when the environment
//! variable `RUMM_SETMM` holds the path to a set.mm. It also checks its results with MMXcli's
//! `verify-mmp` when `RUMM_MMXCLI` holds the path to the directory of the MMXcli `bin/` (the
//! repo's `MMXcli`) and `node` is available.

use rumm::serve::handle_line;
use rumm::Engine;
use serde_json::{json, Value};
use std::path::{Path, PathBuf};
use std::process::Command;

fn fixture(name: &str) -> String {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests").join("fixtures").join(name).to_string_lossy().into_owned()
}

/// A process answering `apply` requests, which keeps nothing between them.
struct Session {
    engine: Engine,
    next: u64,
}

impl Session {
    fn on(db: &str) -> Session {
        Session { engine: Engine::load(db).unwrap(), next: 0 }
    }

    fn call(&mut self, mut request: Value) -> Value {
        self.next += 1;
        request["id"] = json!(self.next);
        let line = handle_line(&mut self.engine, &request.to_string(), None);
        let response: Value = serde_json::from_str(&line).unwrap();
        assert_eq!(response["id"], json!(self.next));
        response
    }

    fn apply(&mut self, state: &Value, goal: &str, tactic: &str) -> Value {
        self.apply_with(state, goal, tactic, "")
    }

    fn apply_with(&mut self, state: &Value, goal: &str, tactic: &str, library: &str) -> Value {
        self.call(json!({ "method": "apply", "library_text": library, "state": state, "goal": goal, "tactic": tactic }))
    }
}

fn step(label: &str, expr: &str, reference: Option<&str>, hyps: &[&str]) -> Value {
    json!({ "label": label, "expr": expr, "ref": reference, "hyps": hyps })
}

/// The goal `( ph -> ch )` of `sylex`, with its two hypotheses.
fn sylex() -> Value {
    json!({ "theorem": "sylex", "dv": [], "steps": [
        step("h1", "|- ( ph -> ps )", Some("sylex.1"), &[]),
        step("h2", "|- ( ps -> ch )", Some("sylex.2"), &[]),
        step("qed", "|- ( ph -> ch )", None, &[]),
    ] })
}

fn exprs(open: &Value) -> Vec<String> {
    open.as_array().unwrap().iter().map(|g| g["expr"].as_str().unwrap().to_string()).collect()
}

fn labels(list: &Value) -> Vec<String> {
    list.as_array().unwrap().iter().map(|l| l.as_str().unwrap().to_string()).collect()
}

fn ok(response: &Value) -> &Value {
    assert_eq!(response["ok"], json!(true), "{}", response);
    assert_eq!(response["error"], Value::Null);
    response
}

fn step_of<'a>(state: &'a Value, label: &str) -> &'a Value {
    state["steps"].as_array().unwrap().iter().find(|s| s["label"] == json!(label)).unwrap_or_else(|| panic!("no step {} in {}", label, state))
}

#[test]
fn an_apply_request_returns_what_it_produced_the_new_state_and_the_open_goals() {
    let mut session = Session::on(&fixture("step.mm"));
    let r = session.apply(&sylex(), "qed", "{ apply ~syl ? ? }");
    ok(&r);
    assert_eq!(labels(&r["produced"]), ["s1", "s2"]);
    assert_eq!(exprs(&r["open"]), ["|- ( ph -> &W1 )", "|- ( &W1 -> ch )"]);
    assert_eq!(r["open"][0], json!({ "label": "s1", "expr": "|- ( ph -> &W1 )", "deciders": null }));
    assert_eq!(r["proved"], json!(false));
    assert_eq!(r["warnings"], json!([]));
    // The goal now cites `syl` on the two new goals, which come before it.
    assert_eq!(
        r["state"],
        json!({ "theorem": "sylex", "dv": [], "steps": [
            step("h1", "|- ( ph -> ps )", Some("sylex.1"), &[]),
            step("h2", "|- ( ps -> ch )", Some("sylex.2"), &[]),
            step("s1", "|- ( ph -> &W1 )", None, &[]),
            step("s2", "|- ( &W1 -> ch )", None, &[]),
            step("qed", "|- ( ph -> ch )", Some("syl"), &["s1", "s2"]),
        ] })
    );
    assert_eq!(labels(&r["updated"]), ["qed"]);
}

#[test]
fn a_composite_tactic_keeps_its_progress_up_to_its_leaves() {
    let mut session = Session::on(&fixture("step.mm"));
    let library = "tactics half () { apply ~syl ? ? }\ntactics deeper () { apply ~syl { apply ~id } ? }";
    // `half` reaches `syl` and leaves two goals open.
    let r = session.apply_with(&sylex(), "qed", "{ use half }", library);
    ok(&r);
    assert_eq!(labels(&r["produced"]), ["s1", "s2"]);
    assert_eq!(r["open"].as_array().unwrap().len(), 2);
    assert_eq!(step_of(&r["state"], "qed")["ref"], json!("syl"));
    // `deeper` goes one level further: `id` closes the first goal (binding `&W1` to `ph`), and
    // the second is left open with that binding applied.
    let r = session.apply_with(&sylex(), "qed", "{ use deeper }", library);
    ok(&r);
    assert_eq!(exprs(&r["open"]), ["|- ( ph -> ch )"]);
    let state = &r["state"];
    assert_eq!(step_of(state, "s1")["ref"], json!("id"));
    assert_eq!(step_of(state, "s1")["expr"], json!("|- ( ph -> ph )"));
    assert_eq!(step_of(state, "qed")["hyps"], json!(["s1", "s2"]));
}

#[test]
fn a_tactic_which_does_not_fit_returns_an_error_and_leaves_the_state_unchanged() {
    let mut session = Session::on(&fixture("step.mm"));
    let state = ok(&session.apply(&sylex(), "qed", "{ apply ~syl ? ? }"))["state"].clone();
    // `ax-1` is not the shape of `( &W1 -> ch )`.
    let r = session.apply(&state, "s2", "{ apply ~ax-1 }");
    assert_eq!(r["ok"], json!(false), "{}", r);
    assert_eq!(r["error"]["kind"], json!("unification-failed"));
    assert_eq!(r["state"], state);
    assert_eq!(r["produced"], json!([]));
    assert_eq!(r["updated"], json!([]));
    // The other goals are listed as they were.
    assert_eq!(exprs(&r["open"]), ["|- ( ph -> &W1 )", "|- ( &W1 -> ch )"]);
    // A goal which is not open, one which doesn't exist, a cited statement which is not there.
    assert_eq!(session.apply(&state, "qed", "!")["error"]["kind"], json!("goal-not-open"));
    assert_eq!(session.apply(&state, "nope", "!")["error"]["kind"], json!("unknown-goal"));
    assert_eq!(session.apply(&state, "h1", "!")["error"]["kind"], json!("goal-not-open"));
    let r = session.apply(&state, "s1", "{ apply ~nosuch }");
    assert_eq!(r["error"]["kind"], json!("tactic-parse"));
    assert_eq!(r["state"], state);
}

#[test]
fn a_failed_branch_inside_try_leaves_nothing_behind() {
    let mut session = Session::on(&fixture("step.mm"));
    let plain = session.apply(&sylex(), "qed", "{ apply ~syl ? ? }");
    // The first branch cites `syl`, then fails on its second goal: nothing of it remains, not
    // even the number of the work variable it used.
    let tried = session.apply(&sylex(), "qed", "{ try { apply ~syl ? { apply ~ax-1 } } { apply ~syl ? ? } }");
    ok(&tried);
    assert_eq!(tried["state"], plain["state"]);
    assert_eq!(tried["open"], plain["open"]);
    assert_eq!(exprs(&tried["open"]), ["|- ( ph -> &W1 )", "|- ( &W1 -> ch )"]);
    // When every branch fails, the request fails and the state is the one sent.
    let failed = session.apply(&sylex(), "qed", "{ try { apply ~syl ? { apply ~ax-1 } } { apply ~ax-1 } }");
    assert_eq!(failed["ok"], json!(false));
    assert_eq!(failed["state"], sylex());
}

#[test]
fn a_work_variable_shared_by_two_goals_is_updated_in_the_other() {
    let mut session = Session::on(&fixture("step.mm"));
    let state = ok(&session.apply(&sylex(), "qed", "{ apply ~syl ? ? }"))["state"].clone();
    // A hypothesis binds `&W1` in the first goal; the second is updated, and the first is
    // gone: the steps which cited it cite the hypothesis (by number).
    let r = session.apply(&state, "s1", "!");
    ok(&r);
    assert_eq!(exprs(&r["open"]), ["|- ( ps -> ch )"]);
    assert_eq!(labels(&r["removed"]), ["s1"]);
    assert_eq!(labels(&r["updated"]), ["s2", "qed"]);
    assert_eq!(step_of(&r["state"], "s2")["expr"], json!("|- ( ps -> ch )"));
    assert_eq!(step_of(&r["state"], "qed")["hyps"], json!(["1", "s2"]));
    assert!(r["state"]["steps"].as_array().unwrap().iter().all(|s| s["label"] != json!("s1")));
    // An application binds it too: `id` makes `&W1` be `ph`.
    let r = session.apply(&state, "s2", "{ apply ~id }");
    ok(&r);
    assert_eq!(step_of(&r["state"], "s1")["expr"], json!("|- ( ph -> ch )"));
    assert_eq!(step_of(&r["state"], "s2")["expr"], json!("|- ( ch -> ch )"));
    assert_eq!(step_of(&r["state"], "s2")["ref"], json!("id"));
    assert_eq!(labels(&r["updated"]), ["s2", "s1"]);
    assert_eq!(exprs(&r["open"]), ["|- ( ph -> ch )"]);
    // Then the last goal is a hypothesis-free `syl` of the two: finish with them.
    let r = ok(&session.apply(&r["state"], "s1", "{ apply ~syl ! ! }"))["state"].clone();
    assert!(r["steps"].as_array().unwrap().iter().all(|s| s["ref"] != Value::Null));
}

#[test]
fn a_state_can_run_to_a_complete_proof_over_separate_requests() {
    let mut session = Session::on(&fixture("step.mm"));
    let a = ok(&session.apply(&sylex(), "qed", "{ apply ~syl ? ? }"))["state"].clone();
    let b = ok(&session.apply(&a, "s1", "!"))["state"].clone();
    // A fresh process answers the same: rumm keeps no state.
    let mut other = Session::on(&fixture("step.mm"));
    let c = other.apply(&b, "s2", "!");
    ok(&c);
    assert_eq!(c["proved"], json!(true));
    assert_eq!(c["open"], json!([]));
    assert_eq!(step_of(&c["state"], "qed")["hyps"], json!(["1", "2"]));
}

#[test]
fn decide_returns_its_leaf_open_and_tagged() {
    let mut session = Session::on(&fixture("step.mm"));
    let r = session.apply(&sylex(), "qed", "{ apply ~syl { decide ring-eval } { decide simp lia } }");
    ok(&r);
    assert_eq!(r["open"][0], json!({ "label": "s1", "expr": "|- ( ph -> &W1 )", "deciders": ["ring-eval"] }));
    assert_eq!(r["open"][1], json!({ "label": "s2", "expr": "|- ( &W1 -> ch )", "deciders": ["simp", "lia"] }));
    assert_eq!(step_of(&r["state"], "s1")["deciders"], json!(["ring-eval"]));
    // The tags stay with the state: after another request, they are still reported, and bound
    // work variables are updated.
    let r = session.apply(&r["state"], "s1", "{ decide other }");
    assert_eq!(r["open"][0]["deciders"], json!(["other"]));
    assert_eq!(r["open"][1]["deciders"], json!(["simp", "lia"]));
    // As a named tactic, and with no name at all.
    let r = session.apply_with(&sylex(), "qed", "{ use gate }", "tactics gate () { decide }");
    assert_eq!(r["open"], json!([{ "label": "qed", "expr": "|- ( ph -> ch )", "deciders": [] }]));
}

#[test]
fn a_goal_of_a_new_theorem_may_cite_every_statement_and_exports_the_dv_it_needs() {
    let mut session = Session::on(&fixture("dv.mm"));
    let new = json!({ "theorem": null, "dv": [], "steps": [step("qed", "|- ( ph -> A. x ph )", None, &[])] });
    // `later` is last in the database: only a goal with no position may cite it.
    let r = session.apply(&new, "qed", "{ apply ~later }");
    assert_eq!(r["ok"], json!(false), "{}", r);
    assert_eq!(r["error"]["kind"], json!("unification-failed"));
    let stated = json!({ "theorem": null, "dv": [], "steps": [step("qed", "|- ( ph -> ph )", None, &[])] });
    let r = session.apply(&stated, "qed", "{ apply ~later }");
    ok(&r);
    assert_eq!(r["proved"], json!(true));
    let earlier = json!({ "theorem": "earlier", "dv": [], "steps": [step("qed", "|- ( ph -> ph )", None, &[])] });
    assert_eq!(session.apply(&earlier, "qed", "{ apply ~later }")["error"]["kind"], json!("cited-after-goal"));
    // `ax-5` needs `ph` and `x` disjoint: they are the `$d` of the new theorem.
    let r = session.apply(&new, "qed", "{ apply ~ax-5 }");
    ok(&r);
    assert_eq!(r["proved"], json!(true));
    assert_eq!(r["state"]["dv"], json!([["ph", "x"]]));
    // A theorem of the database must declare it itself.
    let declared = json!({ "theorem": "dvok", "dv": [], "steps": [step("qed", "|- ( ph -> A. x ph )", None, &[])] });
    assert_eq!(ok(&session.apply(&declared, "qed", "{ apply ~ax-5 }"))["state"]["dv"], json!([["ph", "x"]]));
    let undeclared = json!({ "theorem": "dvbad", "dv": [], "steps": [step("qed", "|- ( ph -> A. x ph )", None, &[])] });
    let r = session.apply(&undeclared, "qed", "{ apply ~ax-5 }");
    assert_eq!(r["error"]["kind"], json!("distinct-variable"));
    assert_eq!(r["state"], undeclared);
    // A new theorem has hypotheses of its own: the steps `h<n>`, whatever they cite.
    let with_hyp = json!({ "theorem": null, "dv": [], "steps": [
        step("h1", "|- ph", Some("my.1"), &[]),
        step("h2", "|- ( ph -> ps )", Some("my.2"), &[]),
        step("qed", "|- ps", None, &[]),
    ] });
    let r = ok(&session.apply(&with_hyp, "qed", "{ apply ~ax-mp ! ! }")).clone();
    assert_eq!(r["proved"], json!(true));
    assert_eq!(step_of(&r["state"], "qed")["hyps"], json!(["1", "2"]));
    assert_eq!(step_of(&r["state"], "h1")["ref"], json!("my.1"));
}

#[test]
fn a_state_citing_a_statement_which_is_not_in_the_database_is_refused() {
    let mut session = Session::on(&fixture("step.mm"));
    let state = json!({ "theorem": null, "dv": [], "steps": [
        step("s1", "|- ( ph -> ph )", Some("my-local-theorem"), &[]),
        step("qed", "|- ( ph -> ph )", None, &[]),
    ] });
    let r = session.apply(&state, "qed", "{ apply ~id }");
    assert_eq!(r["ok"], json!(false));
    assert_eq!(r["error"]["kind"], json!("unknown-ref"));
    assert!(r["error"]["message"].as_str().unwrap().contains("my-local-theorem"), "{}", r);
    assert_eq!(r["state"], state);
    // So is a step which does not follow from what it cites.
    let wrong = json!({ "theorem": null, "dv": [], "steps": [
        step("s1", "|- ( ph -> ps )", Some("id"), &[]),
        step("qed", "|- ( ph -> ph )", None, &[]),
    ] });
    assert_eq!(session.apply(&wrong, "qed", "{ apply ~id }")["error"]["kind"], json!("invalid-state"));
}

#[test]
fn new_steps_never_take_a_label_of_the_state_and_work_variables_are_fresh() {
    let mut session = Session::on(&fixture("step.mm"));
    // `s1` and `s2` exist, and `&W7` is in use: the new steps are `s3`, `s4` and the new
    // work variable is `&W8`. A theorem with no database position (`null`) is used.
    let state = json!({ "theorem": null, "dv": [], "steps": [
        step("h1", "|- ( ph -> &W7 )", Some("x.1"), &[]),
        step("s1", "|- ( ph -> ph )", Some("id"), &[]),
        step("s2", "|- ( ph -> ph )", None, &[]),
        step("qed", "|- ( ph -> ch )", None, &[]),
    ] });
    let r = session.apply(&state, "qed", "{ apply ~syl ? ? }");
    ok(&r);
    assert_eq!(labels(&r["produced"]), ["s3", "s4"]);
    assert_eq!(exprs(&r["open"]), ["|- ( ph -> ph )", "|- ( ph -> &W8 )", "|- ( &W8 -> ch )"]);
    // Many work variables at once: the numbering goes on, and the database grows as needed.
    let big = json!({ "theorem": null, "dv": [], "steps": [step("qed", "|- ( &W40 -> ch )", None, &[])] });
    let r = session.apply(&big, "qed", "{ apply ~syl ? ? }");
    assert_eq!(exprs(&r["open"]), ["|- ( &W40 -> &W41 )", "|- ( &W41 -> ch )"]);
    let r = session.apply(&r["state"], "s2", "{ apply ~syl ? ? }");
    assert_eq!(exprs(&r["open"]), ["|- ( &W40 -> &W41 )", "|- ( &W41 -> &W42 )", "|- ( &W42 -> ch )"]);
}

#[test]
fn a_goal_closed_by_a_hypothesis_alone_cannot_be_the_conclusion() {
    let mut session = Session::on(&fixture("step.mm"));
    let state = json!({ "theorem": "sylex", "dv": [], "steps": [
        step("h1", "|- ( ph -> ps )", Some("sylex.1"), &[]),
        step("qed", "|- ( ph -> ps )", None, &[]),
    ] });
    let r = session.apply(&state, "qed", "!");
    assert_eq!(r["error"]["kind"], json!("goal-is-a-hypothesis"));
    assert_eq!(r["state"], state);
}

/// `proved` is a claim about the whole state: a work variable left in a state with no open
/// goal can't be proved, and the request which would leave it fails.
#[test]
fn a_state_with_no_open_goal_and_a_work_variable_left_is_not_complete() {
    let mut session = Session::on(&fixture("step.mm"));
    let state = json!({ "theorem": null, "dv": [], "steps": [step("qed", "|- ( ph -> ( &W1 -> ph ) )", None, &[])] });
    let r = session.apply(&state, "qed", "{ apply ~ax-1 }");
    assert_eq!(r["ok"], json!(false), "{}", r);
    assert_eq!(r["error"]["kind"], json!("unresolved-metavariables"));
    assert!(r["error"]["message"].as_str().unwrap().contains("&W1"));
    assert_eq!(r["state"], state);
    // With an open goal left, a work variable is fine.
    let r = session.apply(&state, "qed", "{ apply ~syl ? ? }");
    ok(&r);
    assert_eq!(r["proved"], json!(false));
}

#[test]
fn a_hypothesis_of_a_theorem_must_be_one_of_its_own() {
    let mut session = Session::on(&fixture("step.mm"));
    let state = json!({ "theorem": "sylex", "dv": [], "steps": [
        step("h1", "|- ( ph -> ps )", Some("syl.1"), &[]),
        step("qed", "|- ( ph -> ch )", None, &[]),
    ] });
    assert_eq!(session.apply(&state, "qed", "{ apply ~syl ? ? }")["error"]["kind"], json!("invalid-state"));
}

fn batch(script: &str) -> String {
    let dir = std::env::temp_dir().join(format!("rumm-stepwise-{}-{}", std::process::id(), script.len()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("script.rmm"), script.replace("MINI", &fixture("step.mm"))).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_rumm")).arg("script.rmm").current_dir(&dir).output().unwrap();
    String::from_utf8_lossy(&output.stdout).into_owned()
}

/// In batch use `?` still fails a proof, and so does the open goal of a `decide`: nothing
/// returns a state there.
#[test]
fn in_a_batch_run_an_open_goal_fails_the_proof() {
    let out = batch("load \"MINI\"\nproof ~sylex { apply ~syl ! ? with ~wps $ ps $ }\nproof ~sylex { apply ~syl ! { decide ring } with ~wps $ ps $ }\nproof ~sylex { apply ~syl ! ! with ~wps $ ps $ }\n");
    let outcomes: Vec<&str> = out.lines().filter(|l| *l == "Success" || l.starts_with("Failure")).collect();
    assert_eq!(outcomes.len(), 3, "{}", out);
    assert_eq!(outcomes[0], "Failure: Skipped");
    assert!(outcomes[1].starts_with("Failure: OpenGoals(") && outcomes[1].contains("ring"), "{}", outcomes[1]);
    assert_eq!(outcomes[2], "Success");
}

// ---------------------------------------------------------------------------------------------
// The worked sequences on set.mm, checked by an independent verifier.

fn setmm() -> Option<String> {
    match std::env::var("RUMM_SETMM") {
        Ok(path) => Some(path),
        Err(_) => {
            println!("skipped: RUMM_SETMM not set");
            None
        }
    }
}

/// A state as an `.mmp` worksheet, with the header and the `$d` lines `verify-mmp` wants.
fn worksheet(state: &Value) -> String {
    let mut out = format!("$( <MM> <PROOF_ASST> THEOREM={}  LOC_AFTER=? \n\n", state["theorem"].as_str().unwrap());
    for pair in state["dv"].as_array().unwrap() {
        out.push_str(&format!("$d {} {}\n", pair[0].as_str().unwrap(), pair[1].as_str().unwrap()));
    }
    for s in state["steps"].as_array().unwrap() {
        let hyps: Vec<&str> = s["hyps"].as_array().unwrap().iter().map(|h| h.as_str().unwrap()).collect();
        out.push_str(&format!(
            "{}:{}:{} {}\n",
            s["label"].as_str().unwrap(),
            hyps.join(","),
            s["ref"].as_str().expect("a complete state: no open goal"),
            s["expr"].as_str().unwrap()
        ));
    }
    out.push_str("\n$)\n");
    out
}

/// Runs MMXcli's `verify-mmp` on a worksheet, if `RUMM_MMXCLI` says where MMXcli is.
fn verify_independently(setmm: &str, name: &str, state: &Value) {
    let Ok(cli) = std::env::var("RUMM_MMXCLI") else {
        println!("skipped independent verification of {}: RUMM_MMXCLI not set", name);
        return;
    };
    let file: PathBuf = std::env::temp_dir().join(format!("rumm-stepwise-{}-{}.mmp", std::process::id(), name));
    std::fs::write(&file, worksheet(state)).unwrap();
    let output = Command::new("node")
        .arg(Path::new(&cli).join("bin").join("MMXcli.mjs"))
        .args(["verify-mmp", file.to_str().unwrap(), "--db", setmm])
        .output()
        .expect("cannot run node");
    let text = format!("{}{}", String::from_utf8_lossy(&output.stdout), String::from_utf8_lossy(&output.stderr));
    assert!(output.status.success() && text.contains("proved"), "verify-mmp rejected {}:\n{}\n{}", name, worksheet(state), text);
    println!("verify-mmp {}: {}", name, text.trim());
}

/// `rehalfcl` in four requests, binding work variables on the way, and `nfv` which needs a
/// `$d`; each result is a complete proof of a theorem of set.mm.
#[test]
fn worked_sequences_on_setmm() {
    let Some(setmm) = setmm() else { return };
    let mut session = Session::on(&setmm);

    let rehalfcl = json!({ "theorem": "rehalfcl", "dv": [], "steps": [step("qed", "|- ( A e. RR -> ( A / 2 ) e. RR )", None, &[])] });
    let a = ok(&session.apply(&rehalfcl, "qed", "{ apply ~mp3an23 ? ? ? }")).clone();
    assert_eq!(exprs(&a["open"]).len(), 3, "{}", a);
    // The third goal fixes both work variables of the other two.
    let goal = a["open"][2]["label"].as_str().unwrap().to_string();
    let b = ok(&session.apply(&a["state"], &goal, "{ apply ~redivcl }")).clone();
    assert_eq!(exprs(&b["open"]), ["|- 2 e. RR", "|- 2 =/= 0"], "{}", b);
    let first = b["open"][0]["label"].as_str().unwrap().to_string();
    let c = ok(&session.apply(&b["state"], &first, "{ apply ~2re }")).clone();
    let second = c["open"][0]["label"].as_str().unwrap().to_string();
    let d = ok(&session.apply(&c["state"], &second, "{ apply ~2ne0 }")).clone();
    assert_eq!(d["proved"], json!(true), "{}", d);
    assert_eq!(d["open"], json!([]));
    verify_independently(&setmm, "rehalfcl", &d["state"]);

    let nfv = json!({ "theorem": "nfv", "dv": [], "steps": [step("qed", "|- F/ x ph", None, &[])] });
    let a = ok(&session.apply(&nfv, "qed", "{ apply ~nfi ? }")).clone();
    let goal = a["open"][0]["label"].as_str().unwrap().to_string();
    let b = ok(&session.apply(&a["state"], &goal, "{ apply ~ax5ea }")).clone();
    assert_eq!(b["proved"], json!(true), "{}", b);
    assert_eq!(b["state"]["dv"], json!([["ph", "x"]]));
    verify_independently(&setmm, "nfv", &b["state"]);
}
