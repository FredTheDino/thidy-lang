use crate::error::Error;
use crate::{Prog, Block, Op};
use std::cell::RefCell;
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;
use std::borrow::Borrow;

const PREAMBLE: &str = "pub fn main() {\n";
const POSTAMBLE: &str = "\n}\n";

// TODO(ed): Handle the errors.

pub fn generate(target: &PathBuf, prog: &Prog) -> Result<(), Vec<Error>> {
    let mut file = if let Ok(file) = std::fs::File::create(target) {
        file
    } else {
        return Err(Vec::new());
    };

    file.write(PREAMBLE.as_bytes()).unwrap();
    for block in prog.blocks.iter() {
        let block: &RefCell<Block> = block.borrow();
        if block.borrow().name == "/preamble" { continue; }
        GenVM::new().generate(&mut file, &block.borrow());
    }
    file.write(POSTAMBLE.as_bytes()).unwrap();

    Ok(())
}

macro_rules! gen {
    ($file:expr, $( $str:expr),* ) => {
        $file.write(format!($( $str ),*).as_bytes()).unwrap()
    }
}

struct GenVM {
    stack: Vec<String>,
}

impl GenVM {
    fn new() -> Self {
        Self {
            stack: vec!["/empty/".to_string()],
        }
    }

    fn generate(&mut self, file: &mut File, block: &Block) {
        for op in block.ops.iter() {
            match op {
                Op::OpenScope => {
                    gen!(file, "{{");
                }

                Op::CloseScope(n) => {
                    self.stack.truncate(*n);
                    gen!(file, "}}");
                }

                Op::Constant(_n) => {
                    self.stack.push("1".to_string());
                }

                Op::Define(_) => {
                    let value = self.stack.pop().unwrap();
                    let var = "a";
                    gen!(file, "let {} = {};", var, value);
                    self.stack.push(var.to_string());
                }

                Op::Add => {
                    let a = self.stack.pop().unwrap();
                    let b = self.stack.pop().unwrap();
                    self.stack.push(format!("{} + {}", a, b));
                }

                Op::Return => {
                    // TODO(ed): Fix this
                    gen!(file, "return;");
                }

                Op::Print => {
                    // TODO(ed): Fix this
                    let value = self.stack.last().unwrap();
                    gen!(file, "let tmp = {};", value);
                    gen!(file, "println!(\"{{}}\", tmp);");
                }

                _ => {}
                // _ => unimplemented!(),
            }
        }
    }
}

