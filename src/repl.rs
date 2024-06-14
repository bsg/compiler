use std::io::{self, Write};

use crate::eval::Eval;

pub struct Repl {}

impl Repl {
    pub fn start() {
        let mut buffer = String::new();
        let stdin = io::stdin();
        let mut stdout = io::stdout();

        println!("monke go");

        let ctx = Eval::new();
        loop {
            print!("> ");
            stdout.flush().unwrap();
            match stdin.read_line(&mut buffer) {
                Ok(_) => {
                    println!("{}", ctx.eval(buffer.clone().as_str()));
                }
                Err(_) => break,
            }
            buffer.clear();
        }
    }
}
