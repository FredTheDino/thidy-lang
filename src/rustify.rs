use crate::error::Error;
use crate::{Prog, Block, Op, Value};
use std::cell::RefCell;
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;
use std::borrow::Borrow;

const PREAMBLE: &str = "pub fn main() { _start_sy(&[]); }\n";

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
        if block.borrow().name == "/preamble" || block.borrow().lambda { continue; }
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
            push!($vm);
            gen!($vm, $( $str ),*);
            gen!($vm, ";");
        }
    };

    ($vm:expr) => {
        {
            gen!($vm, "let mut _local_{} = ", $vm.stack_size);
            $vm.stack_size += 1;
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
        format!("_local_{}", n)
    }

    fn generate(&mut self, prog: &Prog, block: &Block) {
        self.stack_size = 1 + block.args().len();
        let (pre, post) = block.compiled_declaration();
        gen!(self, "{} {{", pre);
        for (i, op) in block.ops.iter().enumerate() {
            assert!(self.stack_size > block.args().len());
            match op {
                Op::OpenScope => {
                    gen!(self, "{{");
                }

                Op::Pop => {
                    self.pop();
                }

                Op::CloseScope(n) => {
                    self.stack_size = *n;
                    gen!(self, "}}");
                }

                Op::Constant(n) => {
                    let value = prog.constants[*n].clone();
                    if let Value::Function(_ups, block) = &value {
                        let block = (**block).borrow();
                        if block.lambda {
                            push!(self);
                            gen!(self, "Value::Function(");
                            let ss = self.stack_size;
                            self.stack_size = 1;
                            self.generate(prog, &*block);
                            self.stack_size = ss;
                            gen!(self, ");");
                        } else {
                            push!(self,
                                "Value::Function(Rc::new(RefCell::new(|_args| _{}_sy(_args))))",
                                block.name);
                        }
                    } else {
                        push!(self, "{}", value.compiled());
                    }
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

                Op::Equal => bin_op!(self, "eq"),
                Op::Less => bin_op!(self, "less"),
                Op::Greater => bin_op!(self, "greater"),

                Op::Not => uni_op!(self, "not"),
                Op::Neg => uni_op!(self, "neg"),

                Op::Call(n) => {
                    let args = (0..*n).map(|_| self.pop())
                        .rev()
                        .collect::<Vec<String>>()
                        .join(" , ");
                    let f = self.pop();
                    push!(self, "op::call(&{}, &[{}])", f, args);
                }

                Op::Return => {
                    // TODO(ed): Fix this
                    let value = self.pop();
                    gen!(self, "return {};", value);
                }

                Op::Print => {
                    let a = self.pop();
                    gen!(self, "println!(\"PRINT {{:?}}\", {});", a);
                }

                Op::If => {
                    let a = self.pop();
                    gen!(self, "if matches!({}, Value::Bool(true)) ", a);
                }

                Op::Else => {
                    gen!(self, "else");
                }

                Op::Assert => {
                    let value = self.pop();
                    gen!(self, "assert!(matches!({}, Value::Bool(true)), \"\nAssert failed: {}:{}\n\");",
                        value,
                        block.file.display(),
                        block.line(i));
                }

                Op::Unreachable => {
                    gen!(self, "unreachable!(\"\nReached unreachable line: {}:{}\n\")",
                        block.file.display(),
                        block.line(i));
                }

                _ => {}
                // _ => unimplemented!(),
            }
        }
        gen!(self, "}} {}", post);
    }
}

