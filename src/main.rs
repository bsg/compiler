use clap::Parser;
use eval::Eval;
use repl::Repl;
use std::{fs, time::Instant};

mod ast;
mod eval;
mod lexer;
mod parser;
mod repl;

#[derive(Parser)]
#[command()]
struct Args {
    #[arg(short, long)]
    interactive: bool,

    path: Option<String>,
}

fn main() {
    let args = Args::parse();
    if args.interactive {
        Repl::start();
    } else if let Some(path) = args.path {
        let code = fs::read_to_string(path).unwrap();

        let start = Instant::now();
        let ctx = Eval::new();
        ctx.eval(code.as_str());
        println!("Parsed and executed in {} ms", (Instant::now() - start).as_millis());
    }
}
