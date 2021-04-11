use crate::error::Error;
use crate::{Prog, Block, Op};
use std::cell::RefCell;
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;
use std::borrow::Borrow;

const PREAMBLE: &str = "pub fn main() { _start_sy(); }\n";

// TODO(ed): Handle the errors.

pub fn generate(target: &PathBuf, prog: &Prog) -> Result<(), Vec<Error>> {
    let mut file = if let Ok(file) = std::fs::File::create(target) {
        file
    } else {
        return Err(Vec::new());
    };

    file.write(include_str!("runtime_value.rs").as_bytes()).unwrap();
    file.write(PREAMBLE.as_bytes()).unwrap();
    for block in prog.blocks.iter() {
        let block: &RefCell<Block> = block.borrow();
        if block.borrow().name == "/preamble" { continue; }
        GenVM::new(&mut file).generate(prog, &block.borrow());
    }

    Ok(())
}

macro_rules! gen {
    ($vm:expr, $( $str:expr),* ) => {
        $vm.file.write(format!($( $str ),*).as_bytes()).unwrap()
    }
}

macro_rules! push {
    ($vm:expr, $( $str:expr),* ) => {
        {
            gen!($vm, "let mut local_{} = ", $vm.stack_size);
            $vm.stack_size += 1;
            gen!($vm, $( $str ),*);
            gen!($vm, ";");
        }
    }
}

macro_rules! bin_op {
    ($vm:expr, $name:expr) => {
        {
            let b = $vm.pop();
            let a = $vm.pop();
            push!($vm, "op::{}(&{}, &{})", $name, a, b);
        }
    }
}

macro_rules! uni_op {
    ($vm:expr, $name:expr) => {
        {
            let a = $vm.pop();
            push!($vm, "op::{}(&{})", $name, a);
        }
    }
}


struct GenVM<'t> {
    file: &'t File,
    stack_size: usize,
}

impl<'t> GenVM<'t> {
    fn new(file: &'t mut File) -> Self {
        Self {
            stack_size: 1,
            file,
        }
    }

    fn pop(&mut self) -> String {
        assert!(self.stack_size > 1);
        let local = self.local(self.stack_size - 1);
        self.stack_size -= 1;
        local
    }

    fn local(&mut self, n: usize) -> String {
        assert!(n < self.stack_size);
        format!("local_{}", n)
    }

    fn generate(&mut self, prog: &Prog, block: &Block) {
        assert_eq!(self.stack_size, 1);
        gen!(self, "{} {{", block.compiled_declaration());
        for op in block.ops.iter() {
            match op {
                Op::OpenScope => {
                    gen!(self, "{{");
                }

                Op::CloseScope(n) => {
                    self.stack_size = *n;
                    gen!(self, "}}");
                }

                Op::Constant(n) => {
                    push!(self, "{}", prog.constants[*n].compiled());
                }

                Op::ReadLocal(n) => {
                    let var = self.local(*n);
                    push!(self, "{}.clone()", var);
                }

                Op::AssignLocal(n) => {
                    let top = self.pop();
                    let target = self.local(*n);
                    gen!(self, "{} = {}.clone();", target, top);
                }

                Op::Define(_) => { /* empty */ }

                Op::Add => bin_op!(self, "add"),
                Op::Sub => bin_op!(self, "sub"),
                Op::Mul => bin_op!(self, "mul"),
                Op::Div => bin_op!(self, "div"),
                Op::And => bin_op!(self, "and"),
                Op::Or => bin_op!(self, "or"),

                Op::Not => uni_op!(self, "not"),
                Op::Neg => uni_op!(self, "neg"),

                Op::Return => {
                    // TODO(ed): Fix this
                    let value = self.pop();
                    gen!(self, "return {};", value);
                }

                Op::Print => {
                    let a = self.pop();
                    gen!(self, "println!(\"PRINT {{:?}}\", {});", a);
                }

                _ => {}
                // _ => unimplemented!(),
            }
        }
        gen!(self, "}}");
        assert_eq!(self.stack_size, 1);
    }
}

