//! End-to-end tests: run the `rumm` binary on the scripts of `tests/fixtures/`.
//!
//! None of them needs set.mm, except `stock_proofs_on_setmm` and `sample_proofs_on_setmm`, which run
//! only when the environment variable `RUMM_SETMM` holds the path to a set.mm.

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

/// The section of the output for the `n`th proof of a run (1-based): from its
/// `Proof for "<name>":` line to the next one.
fn section(out: &str, n: usize) -> &str {
    let starts: Vec<usize> = out.match_indices("Proof for \"").map(|(i, _)| i).collect();
    let end = starts.get(n).copied().unwrap_or(out.len());
    &out[starts[n - 1]..end]
}

fn succeeded(section: &str) -> bool {
    section.lines().any(|l| l == "Success")
}

#[test]
fn distinct_variables_are_checked_during_the_search() {
    let output = rumm(&fixtures(), &["dv.rmm"]);
    let out = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{}", stderr(&output));
    let results = outcomes(&out);
    assert_eq!(results.len(), 6, "{}", out);

    // 1. The theorem declares `$d x ph`: the citation of `ax-5` is fine, and the export has the `$d`.
    assert_eq!(results[0], "Success");
    assert!(section(&out, 1).lines().any(|l| l == "$d ph x"), "{}", section(&out, 1));
    assert!(section(&out, 1).contains(":ax-5 "));

    // 2. No `$d` declared: `ax-5` fails as a tactic, `try` reaches the second branch.
    assert_eq!(results[1], "Success");
    let second = section(&out, 2);
    assert!(second.contains("Apply violates $d"), "{}", second);
    assert!(second.contains(":ax-5alt "), "{}", second);
    assert!(!second.contains(":ax-5 "), "{}", second);
    assert!(!second.lines().any(|l| l.starts_with("$d")), "no $d needed: {}", second);

    // 3. Without an alternative the proof fails, naming the constraint.
    assert!(results[2].starts_with("Failure: DistinctVariable"), "{:?}", results);
    assert!(results[2].contains("doesn't declare $d x ph"), "{:?}", results);

    // 4. `ph := x = y` contains `x`, which `$d x ph` forbids even though the theorem declares `$d x y`.
    assert_eq!(results[3], "Success");
    assert!(section(&out, 4).contains(":ax-5alt "));
    assert!(results[4].starts_with("Failure: DistinctVariable"), "{:?}", results);
    assert!(results[4].contains("both contain x"), "{:?}", results);

    // 5. `find` goes past the statement which violates its `$d`.
    assert_eq!(results[5], "Success");
    let found = section(&out, 6);
    assert!(found.contains("Found match with ax-5alt"), "{}", found);
    assert!(!found.contains(":ax-5 "), "{}", found);
}

#[test]
fn statements_from_the_goal_on_cannot_be_cited() {
    let output = rumm(&fixtures(), &["order.rmm"]);
    let out = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{}", stderr(&output));
    let results = outcomes(&out);
    assert_eq!(results.len(), 5, "{}", out);
    // `later` follows `earlier` and has the same statement (the shape of rehalfcl / rehalfcld).
    assert_eq!(results[0], "Failure: CitedAfterGoal(\"later\")", "{:?}", results);
    assert!(results[1].starts_with("Failure"), "find doesn't see `later` or the goal: {:?}", results);
    assert!(!section(&out, 2).contains("Found match with later"));
    // A theorem can't cite itself either.
    assert!(results[2].starts_with("Failure"), "{:?}", results);
    // The later theorem can cite the earlier one, with `apply` and with `find`.
    assert_eq!(results[3], "Success");
    assert_eq!(results[4], "Success");
    assert!(section(&out, 5).contains("Found match with earlier"));
}

/// Runs `script` (a rumm script loading "examples/examples.mm", as `set.rmm` does) on the real
/// set.mm, in a scratch directory. `None` (after saying so) when `RUMM_SETMM` is not set.
fn run_on_setmm(script: &str) -> Option<String> {
    let setmm = match std::env::var("RUMM_SETMM") {
        Ok(path) => path,
        Err(_) => {
            println!("skipped: RUMM_SETMM not set");
            return None;
        }
    };
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
    let dir = std::env::temp_dir().join(format!("rumm-test-{}-{}", std::process::id(), script.len()));
    fs::create_dir_all(dir.join("examples")).unwrap();
    let examples = fs::read_to_string(root.join("rumm/examples/examples.mm")).unwrap();
    let examples = examples
        .lines()
        .map(|l| if l.starts_with("$[") { format!("$[ {} $]", setmm) } else { l.to_string() })
        .collect::<Vec<_>>()
        .join("\n");
    fs::write(dir.join("examples/examples.mm"), examples).unwrap();
    fs::write(dir.join("script.rmm"), script).unwrap();

    let output = rumm(&dir, &["script.rmm"]);
    let out = stdout(&output);
    let _ = fs::remove_dir_all(&dir);
    assert!(output.status.success(), "{}", stderr(&output));
    Some(out)
}

/// The library of `set.rmm`: everything before its first `proof`.
fn set_rmm_library() -> String {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
    let rmm = fs::read_to_string(root.join("set.rmm")).unwrap();
    let library: Vec<&str> = rmm.lines().take_while(|l| !l.starts_with("proof ")).collect();
    library.join("\n")
}

/// The section of the output for the proof of `name`.
fn section_of<'a>(out: &'a str, name: &str) -> &'a str {
    let header = format!("Proof for \"{}\":", name);
    let section = out.split(&header).nth(1).unwrap_or_else(|| panic!("{} was not run", name));
    section.split("Proof for \"").next().unwrap()
}

/// Stock proofs of `set.rmm` on the real set.mm, gated on `RUMM_SETMM`.
#[test]
fn stock_proofs_on_setmm() {
    let script = fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().join("set.rmm")).unwrap();
    let out = match run_on_setmm(&script) {
        Some(out) => out,
        None => return,
    };
    for name in &["rummex1", "ellimc", "ajfval", "ismidb"] {
        assert!(succeeded(section_of(&out, name)), "{} failed", name);
    }
    // The proofs which need `$d` export them.
    assert!(section_of(&out, "ellimc").lines().any(|l| l == "$d y z"));
    assert!(section_of(&out, "ajfval").lines().any(|l| l == "$d x y"));
    // `inftmrel` used to be reported as a success, though it violates a `$d`.
    let inftmrel = section_of(&out, "inftmrel");
    assert!(!succeeded(inftmrel), "inftmrel must not succeed");
    assert!(inftmrel.contains("DistinctVariable"), "it fails because of a $d");
}

/// The proofs of the 0526 sample (`reals`, `definition`...), gated on `RUMM_SETMM`. Their
/// `rehalfcl` and `absval` are the shapes which used to go wrong: citing `rehalfcld`, which depends
/// on `rehalfcl`, and `$d`.
#[test]
fn sample_proofs_on_setmm() {
    let sample = fs::read_to_string(fixtures().join("sample_0526.rmm")).unwrap();
    let out = match run_on_setmm(&format!("{}\n{}", set_rmm_library(), sample)) {
        Some(out) => out,
        None => return,
    };
    for name in &["rehalfcl", "absval", "reval", "fzval"] {
        let section = section_of(&out, name);
        assert!(succeeded(section), "{} failed: {}", name, section);
    }
    assert!(section_of(&out, "absval").lines().any(|l| l == "$d A x"));
    assert!(section_of(&out, "fzval").lines().any(|l| l == "$d k m"));
    // The proof of `rehalfcl` doesn't cite `rehalfcld`, or anything after it.
    assert!(!section_of(&out, "rehalfcl").contains(":rehalfcld "));
}
