//! The JSON-lines protocol (see `PROTOCOL.md`): one JSON object per line in, one per line out.

use crate::{Engine, Failure, Library, ProveRequest, TraceSink};
use serde_json::{json, Map, Value};
use std::io::{BufRead, Write};
use std::panic::{catch_unwind, AssertUnwindSafe};

/// Answers each non-blank line of `input` with one line of `output`, flushed, until `input`
/// ends. The trace of proof searches goes to `trace` only.
pub fn serve<R: BufRead, W: Write>(
    engine: &mut Engine,
    input: R,
    mut output: W,
    trace: Option<TraceSink>,
) -> std::io::Result<()> {
    for line in input.lines() {
        let line = line?;
        if line.trim().is_empty() {
            continue;
        }
        writeln!(output, "{}", handle_line(engine, &line, trace.clone()))?;
        output.flush()?;
    }
    Ok(())
}

/// The response (a JSON object on one line) to one request line.
pub fn handle_line(engine: &mut Engine, line: &str, trace: Option<TraceSink>) -> String {
    let response = match serde_json::from_str::<Value>(line) {
        Err(e) => failure(Value::Null, Failure::new("invalid-json", e.to_string())),
        Ok(Value::Object(request)) => {
            let id = request.get("id").cloned().unwrap_or(Value::Null);
            catch_unwind(AssertUnwindSafe(|| handle(engine, &id, &request, trace)))
                .unwrap_or_else(|panic| failure(id.clone(), Failure::from_panic(panic)))
        }
        Ok(_) => failure(Value::Null, Failure::new("invalid-request", "a request is a JSON object")),
    };
    response.to_string()
}

fn failure(id: Value, error: Failure) -> Value {
    json!({ "id": id, "ok": false, "proof": null, "error": error, "warnings": [] })
}

fn handle(engine: &mut Engine, id: &Value, request: &Map<String, Value>, trace: Option<TraceSink>) -> Value {
    match request.get("method").and_then(Value::as_str) {
        None => failure(id.clone(), Failure::new("missing-field", "missing field \"method\" (a string)")),
        Some("ping") => json!({ "id": id, "ok": true, "loads": engine.loads() }),
        Some("prove") => match parse_prove(request) {
            Err(error) => failure(id.clone(), error),
            Ok(prove) => {
                let outcome = engine.prove(&prove, trace);
                match outcome.proof {
                    Ok(proof) => json!({ "id": id, "ok": true, "proof": proof, "error": null, "warnings": outcome.warnings }),
                    Err(error) => json!({ "id": id, "ok": false, "proof": null, "error": error, "warnings": outcome.warnings }),
                }
            }
        },
        Some(other) => failure(id.clone(), Failure::new("unknown-method", format!("unknown method \"{}\"", other))),
    }
}

fn text_field(request: &Map<String, Value>, name: &str) -> std::result::Result<Option<String>, Failure> {
    match request.get(name) {
        None | Some(Value::Null) => Ok(None),
        Some(Value::String(text)) => Ok(Some(text.clone())),
        Some(_) => Err(Failure::new("invalid-request", format!("field \"{}\" must be a string", name))),
    }
}

fn parse_prove(request: &Map<String, Value>) -> std::result::Result<ProveRequest, Failure> {
    let library = match (text_field(request, "library")?, text_field(request, "library_text")?) {
        (Some(path), None) => Library::Path(path),
        (None, Some(text)) => Library::Text(text),
        (None, None) => return Err(Failure::new("missing-field", "missing field \"library\" (a path) or \"library_text\"")),
        (Some(_), Some(_)) => return Err(Failure::new("invalid-request", "give \"library\" or \"library_text\", not both")),
    };
    let theorem = text_field(request, "theorem")?
        .ok_or_else(|| Failure::new("missing-field", "missing field \"theorem\" (a label)"))?;
    let max_depth = match request.get("max_depth") {
        None | Some(Value::Null) => None,
        Some(value) => Some(value.as_u64().ok_or_else(|| {
            Failure::new("invalid-request", "field \"max_depth\" must be a non-negative integer")
        })? as usize),
    };
    Ok(ProveRequest { library, theorem, tactic: text_field(request, "tactic")?, max_depth })
}
