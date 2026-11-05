//! A Metamath Proof Assistant

mod context;
pub mod error;
mod lang;
pub mod parser;
pub mod script;
pub mod tactics;
use annotate_snippets::display_list::DisplayList;
use clap::{clap_app, crate_version};
use context::DEFAULT_MAX_DEPTH;
use error::{Error, Result};
use script::Script;
use typed_arena::Arena;
use std::fs;

/// Stack size of the thread running the script. Tactics nest as deep as `--max-depth`
/// allows, and each level uses several Rust stack frames.
const STACK_SIZE: usize = 256 << 20;

fn run() -> Result {
    let default_depth = DEFAULT_MAX_DEPTH.to_string();
    let app = clap_app!(("rumm") =>
        (version: crate_version!())
        (about: "A tactics based proof language for Metamath")
        (@arg MAX_DEPTH: --("max-depth") +takes_value default_value(&default_depth) "Maximum nesting depth of tactics; a tactics going deeper fails")
        (@arg RMM_FILE: "Rumm file to load"));
    let matches = app.get_matches();
    let path = matches.value_of("RMM_FILE").unwrap_or("../set.rmm");
    let max_depth = match matches.value_of("MAX_DEPTH").unwrap_or("").parse::<usize>() {
        Ok(depth) => depth,
        Err(_) => {
            eprintln!("error: --max-depth expects a non-negative integer");
            std::process::exit(2);
        }
    };
    let data = fs::read_to_string(path).map_err(|e| Error::FileError(path.to_string(), e))?;
    let mut script = Script::from_str(path.to_string(), &data)?;
    script.max_depth = max_depth;
    script.execute()
}

fn run_and_report() -> bool {
    let arena: Arena<String> = Arena::new();
    match run() {
        Ok(()) => {
            println!("Done.");
            true
        }
        Err(error) => {
            eprintln!("{}", DisplayList::from(error.to_snippet(&arena)));
            false
        }
    }
}

fn main() {
    let worker = std::thread::Builder::new()
        .stack_size(STACK_SIZE)
        .spawn(run_and_report)
        .expect("cannot spawn the script thread");
    match worker.join() {
        Ok(true) => {}
        Ok(false) => std::process::exit(1),
        Err(_) => std::process::exit(101),
    }
}
