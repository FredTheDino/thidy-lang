use crate::error::Error;
use crate::{Prog, Block, Op, Value};
use std::cell::RefCell;
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;
use std::borrow::Borrow;
use std::collections::HashSet;

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

    let all_fields: HashSet<_> = prog.constants.iter().filter_map(|x|
        match x {
            Value::Blob(x) => Some(x.fields.keys()),
            _ => None
        }
    ).flatten().collect();
    println!("All fields: {:?}", all_fields);

    for block in prog.blocks.iter().skip(1) {
        let block: &RefCell<Block> = block.borrow();
        if block.borrow().lambda { continue; }
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
            gen!($vm, "let _local_{} = ", $vm.stack_size);
            $vm.stack_size += 1;
        }
    }
}

macro_rules! bin_op {
    ($vm:expr, $name:expr) => {
        {
            let b = $vm.pop();
            let a = $vm.pop();
            push!($vm, "Var::new(op::{}(&{}, &{}))", $name, a, b);
        }
    }
}

macro_rules! uni_op {
    ($vm:expr, $name:expr) => {
        {
            let a = $vm.pop();
            push!($vm, "Var::new(op::{}(&{}))", $name, a);
        }
    }
}

fn local(n: usize) -> String {
    format!("_local_{}", n)
}

fn upvalue(n: usize) -> String {
    format!("_upvalue_{}", n)
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
        let local = local(self.stack_size - 1);
        self.stack_size -= 1;
        format!("{}.value()", local)
    }

    fn pop_raw(&mut self) -> String {
        assert!(self.stack_size > 1);
        let local = local(self.stack_size - 1);
        self.stack_size -= 1;
        format!("{}", local)
    }

    fn generate(&mut self, prog: &Prog, block: &Block) {
        self.stack_size = 1 + block.args().len();
        let (pre, post) = block.compiled_declaration();
        gen!(self, "{} {{", pre);
        for (i, op) in block.ops.iter().enumerate() {
            assert!(self.stack_size > block.args().len(), "Failed in \"{}\" on \"{:?}({})\"", block.name, op, i);
            match op.clone() {
                Op::OpenScope => {
                    gen!(self, "{{");
                }

                Op::Pop => {
                    self.pop();
                }

                Op::CloseScope(n) => {
                    self.stack_size = n;
                    gen!(self, "}}");
                }

                Op::Constant(n) => {
                    let value = prog.constants[n].clone();
                    if let Value::Function(_ups, block) = &value {
                        let block = (**block).borrow();
                        if block.lambda {
                            for (i, (slot, is_upvalue, _)) in block.upvalues.iter().enumerate() {
                                gen!(self, "let {} = ", upvalue(i));
                                let var = if *is_upvalue {
                                    upvalue(*slot)
                                } else {
                                    local(*slot)
                                };
                                gen!(self, "{}.clone();", var);
                            }

                            push!(self);
                            gen!(self, "Var::new(Value::Function(");
                            let ss = self.stack_size;
                            self.stack_size = 1;
                            self.generate(prog, &*block);
                            self.stack_size = ss;
                            gen!(self, "));");
                        } else {
                            push!(self,
                                "Var::new(Value::Function(Rc::new(RefCell::new(_{}_sy))))",
                                block.name);
                        }
                    } else {
                        push!(self, "Var::new({})", value.compiled());
                    }
                }

                Op::List(n) => {
                    let args = (0..n)
                        .map(|_| self.pop())
                        .collect::<Vec<String>>()
                        .into_iter()
                        .rev()
                        .collect::<Vec<String>>()
                        .join(" , ");
                    push!(self, "Var::new(Value::List(vec![{}]))", args);
                }

                Op::Tuple(n) => {
                    let args = (0..n)
                        .map(|_| self.pop())
                        .collect::<Vec<String>>()
                        .into_iter()
                        .rev()
                        .collect::<Vec<String>>()
                        .join(" , ");
                    push!(self, "Var::new(Value::Tuple(vec![{}]))", args);
                }

                Op::Set(n) => {
                    let args = (0..n)
                        .map(|_| self.pop())
                        .collect::<Vec<String>>()
                        .into_iter()
                        .rev()
                        .collect::<Vec<String>>()
                        .join(" , ");
                    push!(self, "Var::new(Value::Set([{}].iter().cloned().collect()))", args);
                }

                Op::Dict(n) => {
                    let args = (0..n)
                        .map(|_| self.pop())
                        .collect::<Vec<String>>()
                        .into_iter()
                        .rev()
                        .collect::<Vec<String>>()
                        .join(" , ");
                    push!(self, "Var::new(Value::Dict([{}].chunks_exact(2).map(|a| (a[0].clone(), a[1].clone())).collect()))", args);
                }

                Op::ReadLocal(n) => {
                    let var = local(n);
                    push!(self, "{}.clone()", var);
                }

                Op::AssignLocal(n) => {
                    let top = self.pop_raw();
                    let target = local(n);
                    gen!(self, "{}.assign({}.value());", target, top);
                }

                Op::ReadUpvalue(n) => {
                    push!(self, "{}.clone()", upvalue(n));
                }

                Op::AssignUpvalue(n) => {
                    let value = self.pop_raw();
                    gen!(self, "{}.assign({}.value());", upvalue(n), value);
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

                Op::Contains => bin_op!(self, "contains"),

                Op::Call(n) => {
                    let args = (0..n)
                        .map(|_| self.pop())
                        .collect::<Vec<String>>()
                        .into_iter()
                        .rev()
                        .collect::<Vec<String>>()
                        .join(" , ");
                    let f = self.pop_raw();
                    push!(self, "op::call(&{}, &[{}])", f, args);
                }

                Op::Return => {
                    // TODO(ed): Fix this
                    let value = self.pop_raw();
                    gen!(self, "return {}.value();", value);
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

                Op::For => {
                    let var = self.pop();
                    gen!(self, "for {} in {}.iter().map(|x| Var::new(x))", local(self.stack_size), var);
                    self.stack_size += 1;
                }

                Op::GetIndex => {
                    let index = self.pop_raw();
                    let var = self.pop_raw();
                    push!(self, "Var::new({}.value().index({}.value()))", var, index);
                }

                Op::AssignIndex => {
                    let value = self.pop_raw();
                    let index = self.pop_raw();
                    let var = self.pop_raw();
                    gen!(self, "{}.assign_index({}.value(), {}.value());", var, index, value);
                }

                Op::Assert => {
                    let value = self.pop();
                    gen!(self, "assert!(matches!({}, Value::Bool(true)), \"\nAssert failed: {}:{}\n\");",
                        value,
                        block.file.display(),
                        block.line(i));
                    push!(self, "Var::new({})", Value::Nil.compiled());
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

