use error::{Error, RuntimeError};
use gumdrop::Options;
use owo_colors::OwoColorize;
use std::borrow::Borrow;
use std::cell::RefCell;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::rc::Rc;

pub mod error;
pub mod value;
mod compiler;
mod sectionizer;
mod tokenizer;
mod rustify;

/// A linkable external function. Created either manually or using
/// [sylt_macro::extern_function].
pub type RustFunction = fn(&[Value], bool) -> Result<Value, RuntimeError>;

use value::{Value, Type, Blob};

pub trait Next {
    fn next(&self) -> Self;
}

/// Compiles, links and runs the given file. The supplied functions are callable
/// external functions.
pub fn run_file(args: &Args, functions: Vec<(String, RustFunction)>) -> Result<(), Vec<Error>> {
    let prog = compile(args, functions)?;
    for block in prog.blocks.iter() {
        let block: &RefCell<Block> = block.borrow();
        block.borrow().debug_print();
    }
    rustify::generate(args.target.as_ref().unwrap(), &prog)?;
    Ok(())
    // typecheck(&prog, &args)?;
    // run(&prog, &args)
}

pub fn typecheck(_prog: &Prog, _args: &Args) -> Result<(), Vec<Error>> {
    Ok(())
}

pub fn run(_prog: &Prog, _args: &Args) -> Result<(), Vec<Error>> {
    Ok(())
}

fn compile(args: &Args, functions: Vec<(String, RustFunction)>) -> Result<Prog, Vec<Error>> {
    let path = match &args.file {
        Some(file) => file,
        None => {
            return Err(vec![Error::NoFileGiven]);
        }
    };
    let sections = sectionizer::sectionize(&path)?;
    let prog = compiler::Compiler::new(sections).compile("/preamble", &path, &functions)?;
    typecheck(&prog, &args)?;
    Ok(prog)
}

#[derive(Default, Debug, Options)]
pub struct Args {
    #[options(free)]
    pub file: Option<PathBuf>,

    #[options(short = "o", long = "output", help = "A file to write the generated rust code to")]
    pub target: Option<PathBuf>,

    #[options(short = "v", no_long, count, help = "Increase verbosity, up to max 2")]
    pub verbosity: u32,

    #[options(help = "Print this help")]
    pub help: bool,
}

pub fn path_to_module(current_file: &Path, module: &str) -> PathBuf {
    let mut res = PathBuf::from(current_file);
    res.pop();
    res.push(format!("{}.sy", module));
    res
}

///
/// Ops are opperations that the virtual
/// machine carries out when running the
/// "byte-code".
///
#[derive(Debug, Clone)]
pub enum Op {
    /// This instruction should never be run.
    /// Finding it in a program is a critical error.
    Illegal,

    /// Remove the top value from the stack.
    ///
    /// {A} - Pop - {}
    Pop,

    /// Opens a new scope for variables, a semantic marker to
    /// aid compilation and analysis.
    ///
    /// {A} - OpenScope - {A}
    OpenScope,
    /// Closes the scope and sets the stacksize, discarding the top values.
    ///
    /// {A, B} - CloseScope(1) - {A}
    CloseScope(usize),
    /// Copies the N values on the top of the stack
    /// and puts them on top of the stack.
    ///
    /// {A, B} - Copy(2) - {A, B, A, B}
    Copy(usize),
    /// Adds the value indexed in the `constants-vector` to the top of the stack.
    /// Also links upvalues if the value is a function.
    ///
    /// {A} - Constant(B) - {A, B}
    Constant(usize),

    /// Creates a new [Value::Tuple] with the given size and place it on the top
    /// of the stack.
    ///
    /// {A, B, C} - Tuple(3) - {D(A, B, C)}
    Tuple(usize),
    /// Creates a new [Value::List] with the given size and place it on the top
    /// of the stack.
    ///
    /// {A, B, C} - List(3) - {D(A, B, C)}
    List(usize),
    /// Creates a new [Value::Set] with the given elements and place it on the top
    /// of the stack.
    ///
    /// {A, B, A} - Set(3) - {D(A, B)}
    Set(usize),
    /// Creates a new [Value::Dict] with the given elements and place it on the top
    /// of the stack.
    ///
    /// {A, B, C, D, A, E} - Dict(6) - {D(A:E, C:D)}
    Dict(usize),

    /// Indexes something indexable,
    /// and adds that element to the stack.
    ///
    /// {T, I} - Index - {T[I]}
    GetIndex,
    /// Assigns the indexes of something indexable.
    /// T[I] = V
    ///
    /// {T, I, V} - Index - {}
    AssignIndex,
    /// Looks up a field by the given name
    /// and replaces the parent with it.
    /// Currently only expects [Value::Blob].
    /// (name is looked up in the internal string-list)
    ///
    /// {O} - Get(F) - {O.F}
    Contains,
    /// Checks if the given value is inside the container.
    /// Pushes a bool to the stack.
    ///
    /// {I, A} - Contains - {I in A}
    GetField(usize),
    /// Looks up a field by the given name
    /// and replaces the current value in the object.
    /// Currently only expects [Value::Blob].
    /// (name is looked up in the internal string-list)
    ///
    /// {O} - Set(F) - {}
    AssignField(usize),

    /// Adds the two top elements on the stack,
    /// using the function [op::add]. The result
    /// is the pushed.
    ///
    /// {A, B} - Add - {A + B}
    Add,
    /// Sub the two top elements on the stack,
    /// using the function [op::sub]. The result
    /// is the pushed.
    ///
    /// {A, B} - Sub - {A - B}
    Sub,
    /// Multiples the two top elements on the stack,
    /// using the function [op::mul]. The result
    /// is the pushed.
    ///
    /// {A, B} - Mul - {A - B}
    Mul,
    /// Divides the two top elements on the stack,
    /// using the function [op::div]. The result
    /// is the pushed.
    ///
    /// {A, B} - Div - {A / B}
    Div,
    /// Negates the top element on the stack.
    ///
    /// {A} - Neg - {-A}
    Neg,

    /// Performs a boolean and on the
    /// top 2 stack elements using [op::and].
    ///
    /// {A, B} - And - {A && B}
    And,
    /// Performs a boolean or on the
    /// top 2 stack elements using [op::or].
    ///
    /// {A, B} - Or - {A || B}
    Or,
    /// Performs a boolean not on the
    /// top stack element using [op::not].
    ///
    /// {A} - Not - {!A}
    Not,

    /// Compares the two topmost elements
    /// on the stack for equality, and pushes
    /// the result. Compares using [op::eq].
    ///
    /// {A, B} - Equal - {A == B}
    Equal,
    /// Compares the two topmost elements
    /// on the stack for order, and pushes the result.
    /// Compares using [op::less].
    ///
    /// {A, B} - Less - {A < B}
    Less,
    /// Compares the two topmost elements
    /// on the stack for order, and pushes the result.
    /// Compares using [op::less].
    ///
    /// {A, B} - Greater - {B < A}
    Greater,

    /// Pops the top value of the stack, and
    /// crashes the program if it is false.
    ///
    /// {A} - Assert - {}
    Assert,
    /// This instruction should not be executed.
    /// If it is the program crashes.
    ///
    /// Does not affect the stack.
    Unreachable,

    /// If the top stack value is true, the following
    /// scope (between OpenScope and CloseScope) is run.
    If,
    /// If the top stack value is true, the following
    /// scope (between OpenScope and CloseScope) is skipped.
    Else,
    /// Marks the next scope a for-loop, and uses the top
    /// stack value as an iterator.
    For,

    /// Reads the value counted from the
    /// bottom of the stack and adds it
    /// to the top.
    ///
    /// {A, B} - ReadLocal(0) - {A, B, A}
    ReadLocal(usize),
    /// Sets the value at the given index
    /// of the stack, to the topmost value.
    /// Pops the topsmost element.
    ///
    /// {A, B} - AssignLocal(0) - {B}
    AssignLocal(usize),

    /// Reads the upvalue, and adds it
    /// to the top of the stack.
    ///
    /// {} - ReadUpvalue(0) - {A}
    ReadUpvalue(usize),
    /// Sets the given upvalue, and pops
    /// the topmost element.
    ///
    /// {A} - AssignUpvalue(0) - {}
    AssignUpvalue(usize),

    /// A helper instruction for the type checker.
    /// *Makes sure* that the top value on the stack
    /// is of the given type, and is meant to signal
    /// that the "variable" is added.
    /// (The type is looked up in the constants vector.)
    ///
    /// Does not affect the stack.
    Define(usize),
    /// A helper instruction for the typechecker,
    /// *assumes* top value on the stack
    /// is of the given type. Usefull for helping the
    /// type system where it just can't do it.
    /// (The type is looked up in the constants vector)
    ///
    /// Does not affect the stack.
    Force(usize),

    /// Links the upvalues for the given constant
    /// function. This updates the constant stack.
    ///
    /// Does not affect the stack.
    Link(usize),

    /// Calls "something" with the given number
    /// of arguments. The callable value is
    /// then replaced with the result.
    ///
    /// Callable things are: [Value::Blob], [Value::Function],
    /// and [Value::ExternFunction].
    ///
    /// {F, A, B} - Call(2) - {F(A, B)}
    Call(usize),

    /// Prints and pops the top value on the stack.
    ///
    /// {A} - Print - {}
    Print,

    /// Pops the current stackframe and replaces
    /// slot 0 with the top value. Also pops
    /// upvalues.
    ///
    /// {F, A, B} - Return - {..., B}
    Return,
}

#[derive(Debug)]
pub struct Block {
    pub ty: Type,
    upvalues: Vec<(usize, bool, Type)>,

    pub name: String,
    pub file: PathBuf,
    pub lambda: bool,
    ops: Vec<Op>,
    last_line_offset: usize,
    line_offsets: HashMap<usize, usize>,
}

impl Block {
    pub fn new(name: &str, lambda: bool, file: &Path) -> Self {
        Self {
            ty: Type::Void,
            upvalues: Vec::new(),

            name: String::from(name),
            file: file.to_owned(),
            lambda,
            ops: Vec::new(),
            last_line_offset: 0,
            line_offsets: HashMap::new(),
        }
    }

    // TODO(ed): Move this to rustify.rs
    fn compiled_declaration(&self) -> (String, String) {
        let name = self.name.clone();
        let args = self.args().iter()
            .enumerate()
            .map(|(i, _)| format!("let _local_{}: Value = _args[{}].clone();", i + 1, i))
            .collect::<Vec<String>>()
            .join("");

        // TODO(ed): The arg count isn't checked during runtime
        if self.lambda {
            (
                format!("/* {} */ Rc::new(RefCell::new(|_args: &[Value]| -> Value {{ {}", name, args),
                String::from("}))")
            )
        } else {
            (
                format!("pub fn _{}_sy ( _args: &[Value]) -> Value {{ {}", name, args),
                String::from("}")
            )
        }
    }

    // Used to create empty functions.
    fn stubbed_block(ty: &Type) -> Self {
        let mut block = Block::new("/empty/", false, Path::new(""));
        block.ty = ty.clone();
        block
    }

    pub fn args(&self) -> &Vec<Type> {
        if let Type::Function(ref args, _) = self.ty {
            args
        } else {
            unreachable!()
        }
    }

    pub fn ret(&self) -> &Type {
        if let Type::Function(_, ref ret) = self.ty {
            ret
        } else {
            unreachable!()
        }
    }

    pub fn add_line(&mut self, token_position: usize) {
        if token_position != self.last_line_offset {
            self.line_offsets.insert(self.curr(), token_position);
            self.last_line_offset = token_position;
        }
    }

    pub fn line(&self, ip: usize) -> usize {
        for i in (0..=ip).rev() {
            if let Some(line) = self.line_offsets.get(&i) {
                return *line;
            }
        }
        0
    }

    pub fn debug_print(&self) {
        println!("     === {} ===", self.name.blue());
        for (i, s) in self.ops.iter().enumerate() {
            println!(
                "{}{}",
                if self.line_offsets.contains_key(&i) {
                    format!("{:5} ", self.line_offsets[&i].blue())
                } else {
                    format!("    {} ", "|".blue())
                },
                format!("{:05} {:?}", i.red(), s)
            );
        }
        println!();
    }

    fn add(&mut self, op: Op, token_position: usize) -> usize {
        let len = self.curr();
        self.add_line(token_position);
        self.ops.push(op);
        len
    }

    fn add_from(&mut self, ops: &[Op], token_position: usize) -> usize {
        let len = self.curr();
        self.add_line(token_position);
        self.ops.extend_from_slice(ops);
        len
    }

    fn curr(&self) -> usize {
        self.ops.len()
    }
}

#[derive(Clone)]
pub struct Prog {
    pub blocks: Vec<Rc<RefCell<Block>>>,
    pub functions: Vec<RustFunction>,
    pub constants: Vec<Value>,
    pub strings: Vec<String>,
}

#[cfg(test)]
mod tests {
    #[macro_export]
    macro_rules! assert_errs {
        ($result:expr, $expect:pat) => {
            let errs = $result.err().unwrap_or(Vec::new());

            #[allow(unused_imports)]
            use $crate::error::Error;
            if !matches!(errs.as_slice(), $expect) {
                eprintln!("===== Got =====");
                for err in errs {
                    eprint!("{}", err);
                }
                eprintln!("===== Expect =====");
                eprint!("{}\n\n", stringify!($expect));
                assert!(false);
            }
        };
    }

    #[macro_export]
    macro_rules! test_file {
        ($fn:ident, $path:literal, $print:expr, $errs:pat) => {
            #[test]
            fn $fn() {
                #[allow(unused_imports)]
                use $crate::error::RuntimeError;
                #[allow(unused_imports)]
                use $crate::Type;

                let mut args = $crate::Args::default();
                args.file = Some(std::path::PathBuf::from($path));
                args.verbosity = if $print { 1 } else { 0 };
                let res = $crate::run_file(
                    &args,
                    sylt_macro::link!(crate::dbg as dbg, crate::push as push, crate::len as len,),
                );
                $crate::assert_errs!(res, $errs);
            }
        };
    }

    // TODO(ed): Reenable the tests once it kinda works again!
    // sylt_macro::find_tests!();
}

// The "standard library"
use crate as sylt;

pub fn dbg(values: &[Value], _typecheck: bool) -> Result<Value, RuntimeError> {
    println!(
        "{}: {:?}, {:?}",
        "DBG".purple(),
        values.iter().map(Type::from).collect::<Vec<_>>(),
        values
    );
    Ok(Value::Nil)
}

pub fn push(values: &[Value], typecheck: bool) -> Result<Value, RuntimeError> {
    match (values, typecheck) {
        ([Value::List(ls), v], true) => {
            let ls: &RefCell<_> = ls.borrow();
            let ls = &ls.borrow();
            assert!(ls.len() == 1);
            let ls = Type::from(&ls[0]);
            let v: Type = Type::from(&*v);
            if ls == v {
                Ok(Value::Nil)
            } else {
                Err(RuntimeError::TypeMismatch(ls, v))
            }
        }
        ([Value::List(ls), v], false) => {
            // NOTE(ed): Deliberately no type checking.
            let ls: &RefCell<_> = ls.borrow();
            ls.borrow_mut().push(v.clone());
            Ok(Value::Nil)
        }
        (values, _) => Err(RuntimeError::ExternTypeMismatch(
            "push".to_string(),
            values.iter().map(Type::from).collect(),
        )),
    }
}

sylt_macro::extern_function!(
    len
    [Value::List(ls)] -> Type::Int => {
        let ls: &RefCell<Vec<Value>> = ls.borrow();
        let ls = ls.borrow();
        Ok(Value::Int(ls.len() as i64))
    },
    [Value::Tuple(ls)] -> Type::Int => {
        Ok(Value::Int(ls.len() as i64))
    },
);
