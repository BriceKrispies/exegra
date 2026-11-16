//! `exegra-sim`: reads one engine input JSON from stdin and writes one trace JSON to stdout.
//! Input that cannot be run gives exit status 1 and a message on stderr.

#![forbid(unsafe_code)]

use std::io::{Read, Write};
use std::process::ExitCode;

fn main() -> ExitCode {
    let mut input = String::new();
    if let Err(e) = std::io::stdin().read_to_string(&mut input) {
        eprintln!("exegra-sim: cannot read stdin: {e}");
        return ExitCode::from(1);
    }
    match exegra_engine::run_input(&input) {
        Ok(trace) => {
            let mut out = std::io::stdout().lock();
            if let Err(e) = out
                .write_all(trace.as_bytes())
                .and_then(|()| out.write_all(b"\n"))
                .and_then(|()| out.flush())
            {
                eprintln!("exegra-sim: cannot write stdout: {e}");
                return ExitCode::from(1);
            }
            ExitCode::SUCCESS
        }
        Err(message) => {
            eprintln!("exegra-sim: {message}");
            ExitCode::from(1)
        }
    }
}
