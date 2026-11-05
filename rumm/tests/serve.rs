//! Tests of the library and of `rumm serve`, the JSON-lines protocol of PROTOCOL.md.
//!
//! None needs set.mm, except `ellimc_on_setmm`, which runs only when the environment variable
//! `RUMM_SETMM` holds the path to a set.mm.

use rumm::{Engine, Library, ProveRequest, TraceSink};
use serde_json::{json, Value};
use std::sync::{Arc, Mutex};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

fn fixtures() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests").join("fixtures")
}

fn mini() -> String {
    fixtures().join("mini.mm").to_string_lossy().into_owned()
}

/// Runs `rumm serve` on `db` with `args`, feeds it `lines`, and returns (stdout lines, stderr).
fn serve_with(db: &str, args: &[&str], lines: &[String]) -> (Vec<String>, String) {
    let mut child = Command::new(env!("CARGO_BIN_EXE_rumm"))
        .args(&["serve", "--db", db])
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("cannot run rumm");
    let mut stdin = child.stdin.take().unwrap();
    for line in lines {
        writeln!(stdin, "{}", line).unwrap();
    }
    drop(stdin); // EOF ends the session
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    (
        String::from_utf8_lossy(&output.stdout).lines().map(str::to_string).collect(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

/// Every line of stdout is a JSON object, one per request, in order.
fn responses(db: &str, requests: &[Value]) -> Vec<Value> {
    let lines: Vec<String> = requests.iter().map(|r| r.to_string()).collect();
    let (out, _) = serve_with(db, &[], &lines);
    assert_eq!(out.len(), requests.len(), "one response line per request: {:?}", out);
    out.iter().map(|l| serde_json::from_str(l).unwrap_or_else(|e| panic!("not JSON ({}): {}", e, l))).collect()
}

const PANICS_LIBRARY: &str = "";
const PANICS_TACTIC: &str = "{ apply ~ax-mp ! ! with ~wph $ ph $ }";

fn panics_request(id: Value) -> Value {
    json!({ "id": id, "method": "prove", "library_text": PANICS_LIBRARY, "theorem": "panics", "tactic": PANICS_TACTIC })
}

#[test]
fn the_library_proves_a_theorem_and_traces_to_its_sink_only() {
    let mut engine = Engine::load(&mini()).unwrap();
    let lines = Arc::new(Mutex::new(Vec::<String>::new()));
    let sink = lines.clone();
    let trace: TraceSink = Arc::new(move |line: &str| sink.lock().unwrap().push(line.to_string()));
    let request = ProveRequest {
        library: Library::Text(String::new()),
        theorem: "panics".to_string(),
        tactic: Some(PANICS_TACTIC.to_string()),
        max_depth: None,
    };
    let outcome = engine.prove(&request, Some(trace));
    let proof = outcome.proof.expect("proved");
    assert_eq!(proof.theorem, "panics");
    let labels: Vec<_> = proof.steps.iter().map(|s| (s.label.as_str(), s.reference.as_str(), s.hyps.clone())).collect();
    assert_eq!(
        labels,
        vec![
            ("h1", "panics.1", vec![]),
            ("h2", "panics.2", vec![]),
            ("qed", "ax-mp", vec!["1".to_string(), "2".to_string()]),
        ]
    );
    assert_eq!(proof.steps[2].expr, "|- ps");
    assert!(lines.lock().unwrap().iter().any(|l| l.contains("Apply ax-mp")), "{:?}", lines.lock().unwrap());
    // Without a sink, nothing is traced.
    assert!(engine.prove(&request, None).proof.is_ok());
    assert_eq!(engine.loads(), 1);
}

#[test]
fn the_database_is_loaded_once_for_many_requests() {
    let db = mini();
    let out = responses(
        &db,
        &[
            json!({ "id": 1, "method": "ping" }),
            panics_request(json!(2)),
            panics_request(json!(3)),
            json!({ "id": 4, "method": "ping" }),
        ],
    );
    assert_eq!(out[0], json!({ "id": 1, "ok": true, "loads": 1 }));
    assert_eq!(out[3], json!({ "id": 4, "ok": true, "loads": 1 }));
    // Responses are matched by id, whatever the id is.
    assert_eq!(out[1]["id"], json!(2));
    assert_eq!(out[1]["ok"], json!(true));
    assert_eq!(out[1]["error"], Value::Null);
    assert_eq!(out[1]["warnings"], json!([]));
    assert_eq!(out[1]["proof"]["steps"][2]["label"], json!("qed"));
    let odd = json!({ "k": [1, "two"] });
    assert_eq!(responses(&db, &[json!({ "id": odd, "method": "ping" })])[0]["id"], odd);
}

#[test]
fn a_request_names_a_library_file_and_uses_its_proof_line() {
    let find = fixtures().join("find.rmm").to_string_lossy().into_owned();
    let out = responses(
        &mini(),
        &[json!({ "id": "f", "method": "prove", "library": find, "theorem": "dftru" })],
    );
    let r = &out[0];
    assert_eq!(r["ok"], json!(true), "{}", r);
    assert_eq!(r["proof"]["theorem"], json!("dftru"));
    assert_eq!(r["proof"]["steps"][0], json!({ "label": "qed", "hyps": [], "ref": "df-tru", "expr": "|- ( T. <-> ( ph -> ph ) )" }));
    // The library's own `load` is ignored, with a warning: the process's database is in force.
    assert!(r["warnings"][0].as_str().unwrap().contains("load \"mini.mm\" ignored"), "{}", r);
}

#[test]
fn a_proof_carries_the_dv_it_needs() {
    let dv = fixtures().join("dv.mm").to_string_lossy().into_owned();
    let out = responses(
        &dv,
        &[json!({ "id": 1, "method": "prove", "library_text": "", "theorem": "dvok", "tactic": "{ apply ~ax-5 }" })],
    );
    assert_eq!(out[0]["ok"], json!(true), "{}", out[0]);
    assert_eq!(out[0]["proof"]["dv"], json!([["ph", "x"]]));
}

#[test]
fn bad_requests_get_an_error_response_and_the_process_keeps_serving() {
    let lines: Vec<String> = vec![
        "this is not json".to_string(),
        "[1, 2]".to_string(),
        json!({ "id": 1 }).to_string(),
        json!({ "id": 2, "method": "dance" }).to_string(),
        json!({ "id": 3, "method": "prove", "library_text": "" }).to_string(),
        json!({ "id": 4, "method": "prove", "theorem": "panics", "tactic": "!" }).to_string(),
        json!({ "id": 5, "method": "prove", "library_text": "", "theorem": "nope", "tactic": "!" }).to_string(),
        json!({ "id": 6, "method": "prove", "library_text": "", "theorem": "panics", "tactic": "{ frobnicate }" }).to_string(),
        json!({ "id": 7, "method": "prove", "library_text": "proof ~panics", "theorem": "panics" }).to_string(),
        json!({ "id": 8, "method": "prove", "library_text": "", "theorem": "panics" }).to_string(),
        json!({ "id": 9, "method": "prove", "library": "/no/such/file.rmm", "theorem": "panics" }).to_string(),
        json!({ "id": 10, "method": "prove", "library_text": "", "theorem": "panics", "tactic": "!", "max_depth": -1 }).to_string(),
        panics_request(json!(11)).to_string(),
    ];
    let (out, _) = serve_with(&mini(), &[], &lines);
    assert_eq!(out.len(), lines.len(), "{:?}", out);
    let r: Vec<Value> = out.iter().map(|l| serde_json::from_str(l).unwrap()).collect();
    let kinds: Vec<(&Value, &str)> = r.iter().map(|v| (&v["id"], v["error"]["kind"].as_str().unwrap_or("-"))).collect();
    let expected = [
        ("invalid-json", Value::Null),
        ("invalid-request", Value::Null),
        ("missing-field", json!(1)),
        ("unknown-method", json!(2)),
        ("missing-field", json!(3)),
        ("missing-field", json!(4)),
        ("unknown-theorem", json!(5)),
        ("tactic-parse", json!(6)),
        ("library-parse", json!(7)),
        ("no-proof", json!(8)),
        ("library-file", json!(9)),
        ("invalid-request", json!(10)),
        ("-", json!(11)),
    ];
    for (got, (kind, id)) in kinds.iter().zip(expected.iter()) {
        assert_eq!((got.0, got.1), (id, *kind));
    }
    for v in &r[..12] {
        assert_eq!(v["ok"], json!(false), "{}", v);
        assert_eq!(v["proof"], Value::Null);
        assert!(v["error"]["message"].as_str().unwrap().len() > 0);
    }
    // The last request is fine: the process is still serving.
    assert_eq!(r[12]["ok"], json!(true), "{}", r[12]);
}

#[test]
fn a_tactic_hitting_the_depth_budget_is_an_error_response_and_the_process_keeps_serving() {
    let library = "tactics forever () { use forever }";
    let request = |id: i32, depth: Value| {
        let mut r = json!({ "id": id, "method": "prove", "library_text": library, "theorem": "dftru", "tactic": "{ use forever }" });
        if !depth.is_null() {
            r["max_depth"] = depth;
        }
        r
    };
    let out = responses(&mini(), &[request(1, json!(10)), request(2, Value::Null), panics_request(json!(3))]);
    assert_eq!(out[0]["ok"], json!(false), "{}", out[0]);
    assert_eq!(out[0]["error"]["kind"], json!("depth-limit-exceeded"));
    assert_eq!(out[0]["error"]["message"], json!("DepthLimitExceeded(10)"));
    // The default budget applies when the request sets none.
    assert_eq!(out[1]["error"]["message"], json!("DepthLimitExceeded(100)"));
    assert_eq!(out[2]["ok"], json!(true), "{}", out[2]);
}

#[test]
fn a_request_does_not_depend_on_the_ones_before_it() {
    // The first request uses metavariables beyond the reserve (the database grows), and a
    // tactic and a theorem the second one doesn't know.
    let greedy = json!({ "id": "a", "method": "prove", "theorem": "dftru",
        "library_text": "tactics mine () { apply ~df-tru }",
        "tactic": "{ match goal $ ( T. <-> &W40 ) $ { use mine } }" });
    let second = json!({ "id": "b", "method": "prove", "theorem": "dftru", "library_text": "", "tactic": "{ use mine }" });
    let alone = responses(&mini(), &[second.clone()]);
    let after = responses(&mini(), &[greedy.clone(), second.clone()]);
    assert_eq!(after[0]["ok"], json!(true), "{}", after[0]);
    // `mine` was defined by the first request's library only.
    assert_eq!(alone[0]["ok"], json!(false), "{}", alone[0]);
    assert_eq!(after[1], alone[0]);
    // And a request which succeeds gives the same answer first or later.
    let first = responses(&mini(), &[panics_request(json!(1))]);
    let later = responses(&mini(), &[greedy, panics_request(json!(1))]);
    assert_eq!(first[0], later[1]);
}

#[test]
fn the_trace_is_never_on_the_protocol_stream() {
    let lines = vec![
        json!({ "id": 1, "method": "ping" }).to_string(),
        panics_request(json!(2)).to_string(),
        "garbage".to_string(),
    ];
    // Without --trace: the trace goes nowhere.
    let (out, err) = serve_with(&mini(), &[], &lines);
    assert_eq!(out.len(), 3);
    for line in &out {
        serde_json::from_str::<Value>(line).unwrap_or_else(|e| panic!("not JSON ({}): {}", e, line));
    }
    assert!(!err.contains("Apply ax-mp"), "{}", err);
    // With --trace: it is on stderr, and stdout is the same.
    let (out_traced, err) = serve_with(&mini(), &["--trace"], &lines);
    assert_eq!(out_traced, out);
    assert!(err.contains(">> Apply ax-mp"), "{}", err);
    assert!(out.iter().all(|l| !l.contains("Apply") && !l.contains("Loading")));
}

fn setmm() -> Option<String> {
    match std::env::var("RUMM_SETMM") {
        Ok(path) => Some(path),
        Err(_) => {
            println!("skipped: RUMM_SETMM not set");
            None
        }
    }
}

/// The stock proof of `ellimc` through the protocol, on the plain set.mm, gated on `RUMM_SETMM`.
#[test]
fn ellimc_on_setmm() {
    let Some(setmm) = setmm() else { return };
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
    let rmm = std::fs::read_to_string(root.join("set.rmm")).unwrap();
    // The library of set.rmm, without its `load` and its first proof (both in the example database).
    let library: String = rmm
        .lines()
        .filter(|l| !l.starts_with("load ") && !l.starts_with("proof ~rummex1") && !l.starts_with("{ use reals_closure }"))
        .collect::<Vec<_>>()
        .join("\n");
    let out = responses(&setmm, &[json!({ "id": 1, "method": "prove", "library_text": library, "theorem": "ellimc" })]);
    let r = &out[0];
    assert_eq!(r["ok"], json!(true), "{}", r);
    let steps = r["proof"]["steps"].as_array().unwrap();
    assert_eq!(steps.last().unwrap()["label"], json!("qed"));
    assert!(steps.iter().any(|s| s["label"].as_str().unwrap().starts_with("h") && s["ref"] == json!("limcval.j")));
    assert!(!r["proof"]["dv"].as_array().unwrap().is_empty());
}
