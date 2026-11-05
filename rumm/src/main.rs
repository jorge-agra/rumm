//! The `rumm` command: `rumm [file.rmm]` proves the proofs of a script, `rumm serve --db <file.mm>`
//! answers JSON-lines requests (see PROTOCOL.md).

use annotate_snippets::display_list::DisplayList;
use clap::{App, Arg, SubCommand, crate_version};
use rumm::error::{Error, Result};
use rumm::script::Script;
use rumm::{Engine, TraceSink, DEFAULT_MAX_DEPTH, STACK_SIZE};
use std::fs;
use std::io::{self, BufReader};
use std::sync::Arc;
use typed_arena::Arena;

fn depth_arg<'a>(default: &'a str) -> Arg<'a, 'a> {
    Arg::with_name("MAX_DEPTH")
        .long("max-depth")
        .takes_value(true)
        .default_value(default)
        .help("Maximum nesting depth of tactics; a tactics going deeper fails")
}

fn max_depth(value: Option<&str>) -> usize {
    match value.unwrap_or("").parse::<usize>() {
        Ok(depth) => depth,
        Err(_) => {
            eprintln!("error: --max-depth expects a non-negative integer");
            std::process::exit(2);
        }
    }
}

/// Runs the command; the result says whether to print `Done.` (not in `serve`, whose stdout is
/// the protocol stream).
fn run() -> Result<bool> {
    let default_depth = DEFAULT_MAX_DEPTH.to_string();
    let app = App::new("rumm")
        .version(crate_version!())
        .about("A tactics based proof language for Metamath")
        .arg(depth_arg(&default_depth))
        .arg(Arg::with_name("RMM_FILE").help("Rumm file to load"))
        .subcommand(
            SubCommand::with_name("serve")
                .about("Answer JSON-lines requests on stdin, on stdout (see PROTOCOL.md)")
                .arg(Arg::with_name("DB").long("db").takes_value(true).required(true).help("The Metamath database to load, once"))
                .arg(Arg::with_name("TRACE").long("trace").help("Print the trace of proof searches on stderr"))
                .arg(depth_arg(&default_depth)),
        );
    let matches = app.get_matches();
    if let Some(serve) = matches.subcommand_matches("serve") {
        let path = serve.value_of("DB").unwrap();
        let mut engine = Engine::load(path)?;
        engine.max_depth = max_depth(serve.value_of("MAX_DEPTH"));
        let trace: Option<TraceSink> = if serve.is_present("TRACE") {
            Some(Arc::new(|line: &str| eprintln!("{}", line)))
        } else {
            None
        };
        let stdin = io::stdin();
        rumm::serve::serve(&mut engine, BufReader::new(stdin.lock()), io::stdout(), trace).map_err(Error::IoError)?;
        return Ok(false);
    }
    let path = matches.value_of("RMM_FILE").unwrap_or("../set.rmm");
    let max_depth = max_depth(matches.value_of("MAX_DEPTH"));
    let data = fs::read_to_string(path).map_err(|e| Error::FileError(path.to_string(), e))?;
    let mut script = Script::from_str(path.to_string(), &data)?;
    script.max_depth = max_depth;
    script.execute()?;
    Ok(true)
}

fn run_and_report() -> bool {
    let arena: Arena<String> = Arena::new();
    match run() {
        Ok(done) => {
            if done {
                println!("Done.");
            }
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
