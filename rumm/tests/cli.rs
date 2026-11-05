//! End-to-end tests: run the `rumm` binary on the scripts of `tests/fixtures/`.
//!
//! None of them needs set.mm. `stock_proofs_on_setmm` does, and runs only when the
//! environment variable `RUMM_SETMM` holds the path to a set.mm.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn fixtures() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests").join("fixtures")
}

/// Run rumm in `dir` (the paths in `load` are relative to the working directory).
fn rumm(dir: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_rumm"))
        .args(args)
        .current_dir(dir)
        .output()
        .expect("cannot run rumm")
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

/// The outcome of each proof of a run, in order: "Success" or the "Failure..." line.
fn outcomes(stdout: &str) -> Vec<String> {
    stdout
        .lines()
        .filter(|l| *l == "Success" || l.starts_with("Failure"))
        .map(|l| l.to_string())
        .collect()
}

#[test]
fn find_unifies_in_both_directions() {
    let output = rumm(&fixtures(), &["find.rmm"]);
    let out = stdout(&output);
    assert!(output.status.success(), "{}{}", out, stderr(&output));
    // 1. finddf: the goal is an instance of the definition `df-tru` (65b1343's case),
    // 2. finddf: the pattern has a metavariable, bound to a part of `df-tru` (the case before 65b1343),
    // 3. the same with `find`.
    assert_eq!(outcomes(&out), vec!["Success", "Success", "Success"], "{}", out);
    assert!(out.contains("Found match with df-tru"));
    // The first proof really is the definition instantiated with ph := ( ph -> ps ).
    assert!(out.contains("|- ( T. <-> ( ( ph -> ps ) -> ( ph -> ps ) ) )"));
}

#[test]
fn database_error_is_reported_not_a_panic() {
    let output = rumm(&fixtures(), &["missing_include.rmm"]);
    let err = stderr(&output);
    assert_eq!(output.status.code(), Some(1), "{}", err);
    assert!(!err.contains("panicked"), "{}", err);
    assert!(err.contains("missing_include.mm"), "the file is named: {}", err);
    assert!(err.contains("No such file"), "the diagnostic is shown: {}", err);
}

#[test]
fn unreadable_script_is_reported_not_a_panic() {
    let output = rumm(&fixtures(), &["no-such-script.rmm"]);
    let err = stderr(&output);
    assert_eq!(output.status.code(), Some(1), "{}", err);
    assert!(!err.contains("panicked"), "{}", err);
    assert!(err.contains("no-such-script.rmm"), "{}", err);
}

#[test]
fn cycling_tactics_fail_within_the_depth_budget() {
    let output = rumm(&fixtures(), &["cycle.rmm"]);
    let out = stdout(&output);
    // The process ends normally: no stack overflow (an abort has no exit code), no panic.
    assert_eq!(output.status.code(), Some(0), "{}", stderr(&output));
    assert!(!stderr(&output).contains("overflow"), "{}", stderr(&output));
    // The cycling proof fails, because the limit was hit (default: 100) ...
    assert!(out.contains("DepthLimitExceeded(100)"), "limit not reported");
    assert!(outcomes(&out)[0].starts_with("Failure"), "{:?}", outcomes(&out));
    // ... and the next proof of the script still runs.
    assert_eq!(outcomes(&out)[1], "Success");
}

#[test]
fn depth_budget_is_set_on_the_command_line() {
    let output = rumm(&fixtures(), &["--max-depth", "10", "cycle.rmm"]);
    let out = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{}", stderr(&output));
    assert!(out.contains("DepthLimitExceeded(10)"));
    assert!(!out.contains("DepthLimitExceeded(100)"));
    // The trace is no deeper than the budget.
    let deepest = out.lines().map(|l| l.len() - l.trim_start().len()).max().unwrap();
    assert!(deepest <= 12, "indentation {}", deepest);
}

#[test]
fn panic_while_building_a_proof_fails_that_proof_only() {
    let output = rumm(&fixtures(), &["export_panic.rmm"]);
    let out = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{}", stderr(&output));
    let results = outcomes(&out);
    assert_eq!(results.len(), 2, "{}", out);
    assert!(results[0].starts_with("Failure: panic:"), "{:?}", results);
    assert!(results[0].contains("No substitution for wph"), "{:?}", results);
    assert_eq!(results[1], "Success");
    assert!(out.contains("df-tru"), "the later proof is exported");
}

/// Stock proofs of `set.rmm` on the real set.mm, gated on `RUMM_SETMM`.
#[test]
fn stock_proofs_on_setmm() {
    let setmm = match std::env::var("RUMM_SETMM") {
        Ok(path) => path,
        Err(_) => {
            println!("skipped: RUMM_SETMM not set");
            return;
        }
    };
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
    let dir = std::env::temp_dir().join(format!("rumm-test-{}", std::process::id()));
    fs::create_dir_all(dir.join("examples")).unwrap();
    let examples = fs::read_to_string(root.join("rumm/examples/examples.mm")).unwrap();
    let examples = examples
        .lines()
        .map(|l| if l.starts_with("$[") { format!("$[ {} $]", setmm) } else { l.to_string() })
        .collect::<Vec<_>>()
        .join("\n");
    fs::write(dir.join("examples/examples.mm"), examples).unwrap();
    fs::copy(root.join("set.rmm"), dir.join("set.rmm")).unwrap();

    let output = rumm(&dir, &["set.rmm"]);
    let out = stdout(&output);
    let _ = fs::remove_dir_all(&dir);
    assert!(output.status.success(), "{}", stderr(&output));
    // Which of the stock proofs succeeded: the text after `Proof for "<name>":` up to the next one.
    let succeeded = |name: &str| {
        let header = format!("Proof for \"{}\":", name);
        let section = out.split(&header).nth(1).expect("proof not run");
        let section = section.split("Proof for \"").next().unwrap();
        section.lines().any(|l| l == "Success")
    };
    for name in &["rummex1", "ellimc", "ajfval", "ismidb", "inftmrel"] {
        assert!(succeeded(name), "{} failed", name);
    }
}
