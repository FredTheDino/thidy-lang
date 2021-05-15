use crate::rc::Rc;
use crate::rcmut::RcMut;

use error::{Error, RuntimeError};
use gumdrop::Options;
use owo_colors::OwoColorize;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};

pub mod error;
pub mod vm;
pub mod typechecker;

mod compiler;
mod rc;
mod rcmut;
mod sectionizer;
mod tokenizer;

// Lingon linking layer
#[cfg(feature = "lingon")]
pub mod lingon_sylt;
pub mod lib_sylt;

/// Generates the linking for the standard library, and lingon if it's active.
pub fn lib_bindings() -> Vec<(String, RustFunction)> {
    let mut lib = Vec::new();

    lib.append(&mut lib_sylt::_sylt_link());

    #[cfg(feature = "lingon")]
    lib.append(&mut lingon_sylt::_sylt_link());

    lib
}

pub trait Next {
    fn next(&self) -> Self;
}

/// Compiles, links and runs the given file. The supplied functions are callable
/// external functions.
pub fn run_file(args: &Args, functions: Vec<(String, RustFunction)>) -> Result<(), Vec<Error>> {
    let prog = compile(args, functions)?;
    typechecker::typecheck(&prog, &args)?;
    run(&prog, &args)
}

pub fn run(prog: &Prog, args: &Args) -> Result<(), Vec<Error>> {
    let mut vm = vm::VM::new();
    vm.print_bytecode = args.verbosity >= 1;
    vm.print_exec = args.verbosity >= 2;
    vm.init(&prog);
    if let Err(e) = vm.run() {
        Err(vec![e])
    } else {
        Ok(())
    }
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
    typechecker::typecheck(&prog, &args)?;
    Ok(prog)
}

#[derive(Default, Debug, Options)]
pub struct Args {
    #[options(free)]
    pub file: Option<PathBuf>,

    #[options(short = "r", long = "run", help = "Runs a precompiled sylt binary")]
    pub is_binary: bool,

    #[options(short = "c", long = "compile", help = "Compile a sylt binary")]
    pub compile_target: Option<PathBuf>,

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

/// A linkable external function. Created either manually or using
/// [sylt_macro::extern_function].
pub type RustFunction = fn(&[Value], bool) -> Result<Value, RuntimeError>;

#[derive(Debug, Clone)]
pub enum Type {
    Ty,
    Field(String),
    Void,
    Unknown,
    Int,
    Float,
    Bool,
    String,
    Tuple(Vec<Type>),
    Union(HashSet<Type>),
    List(Box<Type>),
    Set(Box<Type>),
    Dict(Box<Type>, Box<Type>),
    Iter(Box<Type>),
    Function(Vec<Type>, Box<Type>),
    Blob(Rc<Blob>),
    Instance(Rc<Blob>),
    ExternFunction(usize),
}

impl Hash for Type {
    fn hash<H: Hasher>(&self, h: &mut H) {
        // TODO(ed): We can use the fancy macro here instead.
        match self {
            Type::Ty => 18,
            Type::Field(_) => unimplemented!(),
            Type::Void => 0,
            Type::Unknown => 1,
            Type::Int => 2,
            Type::Float => 3,
            Type::Bool => 4,
            Type::String => 5,
            Type::Tuple(ts) => {
                for t in ts.iter() {
                    t.hash(h);
                }
                6
            }
            Type::List(t) => {
                t.as_ref().hash(h);
                12
            }
            Type::Set(t) => {
                t.as_ref().hash(h);
                13
            }
            Type::Dict(k, v) => {
                k.as_ref().hash(h);
                v.as_ref().hash(h);
                14
            }
            Type::Iter(t) => {
                t.as_ref().hash(h);
                15
            }
            Type::Union(ts) => {
                for t in ts {
                    t.hash(h);
                }
                7
            }
            Type::Function(args, ret) => {
                ret.hash(h);
                for t in args.iter() {
                    t.hash(h);
                }
                8
            }
            Type::Blob(b) => {
                for t in b.fields.values() {
                    t.hash(h);
                }
                10
            }
            Type::Instance(b) => {
                for t in b.fields.values() {
                    t.hash(h);
                }
                11
            }
            Type::ExternFunction(_) => {
                16
            }
        }
        .hash(h);
    }
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Type::Void, Type::Void) => true,
            (Type::Instance(a), Type::Instance(b)) => *a == *b,
            (Type::Blob(a), Type::Blob(b)) => *a == *b,
            (Type::Int, Type::Int) => true,
            (Type::Float, Type::Float) => true,
            (Type::Bool, Type::Bool) => true,
            (Type::String, Type::String) => true,
            (Type::Tuple(a), Type::Tuple(b)) => a.iter().zip(b.iter()).all(|(a, b)| a == b),
            (Type::Union(a), b) | (b, Type::Union(a)) => a.iter().any(|x| x == b),
            (Type::List(a), Type::List(b)) => a == b,
            (Type::Set(a), Type::Set(b)) => a == b,
            (Type::Dict(ak, av), Type::Dict(bk, bv)) => ak == bk && av == bv,
            (Type::Iter(a), Type::Iter(b)) => a == b,
            (Type::Function(a_args, a_ret), Type::Function(b_args, b_ret)) => {
                a_args == b_args && a_ret == b_ret
            }
            _ => false,
        }
    }
}

impl Eq for Type {}

fn maybe_union_type<'a>(v: impl Iterator<Item = &'a Value>) -> Type {
    let set: HashSet<_> = v.map(Type::from).collect();
    match set.len() {
        0 => Type::Unknown,
        1 => set.into_iter().next().unwrap(),
        _ => Type::Union(set),
    }
}

impl From<&Value> for Type {
    fn from(value: &Value) -> Type {
        match value {
            Value::Field(s) => Type::Field(s.clone()),
            Value::Instance(b, _) => Type::Instance(Rc::clone(b)),
            Value::Blob(b) => Type::Blob(Rc::clone(b)),
            Value::Tuple(v) => Type::Tuple(v.iter().map(Type::from).collect()),
            Value::List(v) => {
                let t = maybe_union_type(v.iter());
                Type::List(Box::new(t))
            }
            Value::Set(v) => {
                let t = maybe_union_type(v.iter());
                Type::Set(Box::new(t))
            }
            Value::Dict(v) => {
                let k = maybe_union_type(v.keys());
                let v = maybe_union_type(v.values());
                Type::Dict(Box::new(k), Box::new(v))
            }
            Value::Iter(t, _) => Type::Iter(Box::new(t.clone())),
            Value::Union(v) => Type::Union(v.iter().map(Type::from).collect()),
            Value::Int(_) => Type::Int,
            Value::Float(_) => Type::Float,
            Value::Bool(_) => Type::Bool,
            Value::String(_) => Type::String,
            Value::Function(_, block) => {
                block.borrow().ty.clone()
            }
            Value::Unknown => Type::Unknown,
            Value::ExternFunction(n) => Type::ExternFunction(*n),
            Value::Nil => Type::Void,
            Value::Ty(_) => Type::Ty,
        }
    }
}

impl From<Value> for Type {
    fn from(value: Value) -> Type {
        Type::from(&value)
    }
}

impl From<&Type> for Value {
    fn from(ty: &Type) -> Self {
        match ty {
            Type::Field(s) => Value::Field(s.clone()),
            Type::Void => Value::Nil,
            Type::Blob(b) => Value::Blob(Rc::clone(b)),
            Type::Instance(b) => Value::Instance(Rc::clone(b), RcMut::new(HashMap::new())),
            Type::Tuple(fields) => Value::Tuple(Rc::new(fields.iter().map(Value::from).collect())),
            Type::Union(v) => Value::Union(v.iter().map(Value::from).collect()),
            Type::List(v) => Value::List(RcMut::new(vec![Value::from(v.as_ref())])),
            Type::Set(v) => {
                let mut s = HashSet::new();
                s.insert(Value::from(v.as_ref()));
                Value::Set(RcMut::new(s))
            }
            Type::Dict(k, v) => {
                let mut s = HashMap::new();
                s.insert(Value::from(k.as_ref()), Value::from(v.as_ref()));
                Value::Dict(RcMut::new(s))
            }
            Type::Iter(v) => Value::Iter(v.as_ref().clone(), RcMut::new(Box::new(|| None))),
            Type::Unknown => Value::Unknown,
            Type::Int => Value::Int(1),
            Type::Float => Value::Float(1.0),
            Type::Bool => Value::Bool(true),
            Type::String => Value::String(Rc::new("".to_string())),
            Type::Function(_, _) => Value::Function(
                Rc::new(Vec::new()),
                RcMut::new(Block::stubbed_block(ty)),
            ),
            Type::ExternFunction(x) => Value::ExternFunction(*x),
            Type::Ty => Value::Ty(Type::Void),
        }
    }
}

impl From<Type> for Value {
    fn from(ty: Type) -> Self {
        Value::from(&ty)
    }
}

impl Type {
    /// Checks if the other type is valid in a place where the self type is. It's an asymmetrical
    /// comparison for types useful when checking assignment.
    pub fn fits(&self, other: &Self) -> bool {
        match (self, other) {
            (_, Type::Unknown) => true,
            (Type::List(a), Type::List(b)) => a.fits(b),
            (Type::Set(a), Type::Set(b)) => a.fits(b),
            (Type::Dict(ak, av), Type::Dict(bk, bv)) => ak.fits(bk) && av.fits(bv),
            (Type::Union(a), Type::Union(b)) => b.iter().all(|x| a.contains(x)),
            (_, Type::Union(_)) => false,
            (a, b) => a == b,
        }
    }

    fn is_nil(&self) -> bool {
        matches!(self, Type::Void)
    }

    fn maybe_union<'a>(v: impl Iterator<Item = &'a Type>) -> Type {
        let set: HashSet<_> = v.cloned().collect();
        match set.len() {
            0 => Type::Unknown,
            1 => set.into_iter().next().unwrap(),
            _ => Type::Union(set),
        }
    }
}

pub type IterFn = dyn FnMut() -> Option<Value>;

#[derive(Clone)]
pub enum Value {
    Field(String),
    Ty(Type),
    Blob(Rc<Blob>),
    Instance(Rc<Blob>, RcMut<HashMap<String, Value>>),
    Tuple(Rc<Vec<Value>>),
    List(RcMut<Vec<Value>>),
    Set(RcMut<HashSet<Value>>),
    Dict(RcMut<HashMap<Value, Value>>),
    Iter(Type, RcMut<Box<IterFn>>),
    Union(HashSet<Value>),
    Float(f64),
    Int(i64),
    Bool(bool),
    String(Rc<String>),
    Function(Rc<Vec<RcMut<UpValue>>>, RcMut<Block>),
    ExternFunction(usize),
    /// This value should not be present when running, only when type checking.
    /// Most operations are valid but produce funky results.
    Unknown,
    /// Should not be present when running.
    Nil,
}

#[derive(Clone)]
pub enum MatchableValue<'t> {
    Empty,
    One(&'t Value),
    Two(&'t Value, &'t Value),
    Three(&'t Value, &'t Value, &'t Value),
    Four(&'t Value, &'t Value, &'t Value, &'t Value),
    Five(&'t Value, &'t Value, &'t Value, &'t Value, &'t Value),
}

pub fn make_matchable<'t>(value: &'t Value) -> MatchableValue<'t> {
    use crate::Value::*;
    use MatchableValue::*;

    match value {
        Tuple(inner) => {
            match (inner.get(0), inner.get(1), inner.get(2), inner.get(3), inner.get(4)) {
                (Some(a), Some(b), Some(c), Some(d), Some(e), ..) => Five(a, b, c, d, e),
                (Some(a), Some(b), Some(c), Some(d), ..) => Four(a, b, c, d),
                (Some(a), Some(b), Some(c), ..) => Three(a, b, c),
                (Some(a), Some(b), ..) => Two(a, b),
                (Some(a), ..) => One(a),
                _ => Empty,
            }
        },
        x => One(x),
    }
}

impl Debug for Value {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // TODO(ed): This needs some cleaning
        match self {
            Value::Field(s) => write!(fmt, "( .{} )", s),
            Value::Ty(ty) => write!(fmt, "(type {:?})", ty),
            Value::Blob(b) => write!(fmt, "(blob {})", b.name),
            Value::Instance(b, v) => write!(fmt, "(inst {} {:?})", b.name, v),
            Value::Float(f) => write!(fmt, "(float {})", f),
            Value::Int(i) => write!(fmt, "(int {})", i),
            Value::Bool(b) => write!(fmt, "(bool {})", b),
            Value::String(s) => write!(fmt, "(string \"{}\")", s),
            Value::List(v) => write!(fmt, "(array {:?})", v),
            Value::Set(v) => write!(fmt, "(set {:?})", v),
            Value::Dict(v) => write!(fmt, "(dict {:?})", v),
            Value::Iter(v, _) => write!(fmt, "(iter {:?})", v),
            Value::Function(_, block) => {
                write!(fmt, "(fn {}: {:?})", block.name, block.ty)
            }
            Value::ExternFunction(slot) => write!(fmt, "(extern fn {})", slot),
            Value::Unknown => write!(fmt, "(unknown)"),
            Value::Nil => write!(fmt, "(nil)"),
            Value::Tuple(v) => write!(fmt, "({:?})", v),
            Value::Union(v) => write!(fmt, "(U {:?})", v),
        }
    }
}

impl PartialEq<Value> for Value {
    fn eq(&self, other: &Value) -> bool {
        match (self, other) {
            (Value::Float(a), Value::Float(b)) => a == b,
            (Value::Int(a), Value::Int(b)) => a == b,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::String(a), Value::String(b)) => a == b,
            (Value::Tuple(a), Value::Tuple(b)) => {
                a.len() == b.len() && a.iter().zip(b.iter()).all(|(a, b)| a == b)
            }
            (Value::List(a), Value::List(b)) => a == b,
            (Value::Set(a), Value::Set(b)) => a == b,
            (Value::Dict(a), Value::Dict(b)) => a == b,
            (Value::Union(a), b) | (b, Value::Union(a)) => a.iter().any(|x| x == b),
            (Value::Nil, Value::Nil) => true,
            _ => false,
        }
    }
}

impl Eq for Value {}

impl Hash for Value {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Value::Float(a) => {
                // We have to limit the values, because
                // floats are wierd.
                assert!(a.is_finite());
                a.to_bits().hash(state);
            }
            Value::Int(a) => a.hash(state),
            Value::Bool(a) => a.hash(state),
            Value::String(a) => a.hash(state),
            Value::Tuple(a) => a.hash(state),
            Value::Nil => state.write_i8(0),
            _ => {}
        };
    }
}

impl Value {
    fn is_nil(&self) -> bool {
        matches!(self, Value::Nil)
    }
}

#[doc(hidden)]
#[derive(Clone, Debug)]
pub struct UpValue {
    slot: usize,
    value: Value,
}

impl UpValue {
    fn new(value: usize) -> Self {
        Self {
            slot: value,
            value: Value::Nil,
        }
    }

    fn get(&self, stack: &[Value]) -> Value {
        if self.is_closed() {
            self.value.clone()
        } else {
            stack[self.slot].clone()
        }
    }

    fn set(&mut self, stack: &mut [Value], value: Value) {
        if self.is_closed() {
            self.value = value;
        } else {
            stack[self.slot] = value;
        }
    }

    fn is_closed(&self) -> bool {
        self.slot == 0
    }

    fn close(&mut self, value: Value) {
        self.slot = 0;
        self.value = value;
    }
}

#[derive(Debug, Clone)]
pub struct Blob {
    pub id: usize,
    pub name: String,
    /// Maps field names to their slot and type.
    pub fields: HashMap<String, Type>,
}

impl PartialEq for Blob {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Blob {
    fn new(id: usize, name: &str) -> Self {
        Self {
            id,
            name: String::from(name),
            fields: HashMap::new(),
        }
    }

    fn add_field(&mut self, name: &str, ty: Type) -> Result<(), ()> {
        let entry = self.fields.entry(String::from(name));
        match entry {
            Entry::Occupied(_) => Err(()),
            Entry::Vacant(v) => {
                v.insert(ty);
                Ok(())
            }
        }
    }
}

///
/// Ops are opperations that the virtual
/// machine carries out when running the
/// "byte-code".
///
#[derive(Debug, Copy, Clone)]
pub enum Op {
    /// This instruction should never be run.
    /// Finding it in a program is a critical error.
    Illegal,

    /// Pops one value from the stack.
    ///
    /// {A, B} - Pop - {A}
    Pop,
    /// Assumes the value on the top of the
    /// stack has an upvalue, and closes that
    /// upvalue.
    ///
    /// {A, B} - Pop - {A}
    PopUpvalue,
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

    /// Turns the top element on the stack into an iterator.
    ///
    /// Iter(Iter(A)) = Iter(A)
    ///
    /// {A} - Iter - {Iter(A)}
    Iter,
    /// Steps the iterator on top of the stack one step and pushes
    /// the new value. If the iterator is consumed, jumps to the address
    /// and pushes [Value::Nil]. Errors if the top element isn't an iterator.
    ///
    /// {I} - JmpNext(line) - {I, A}
    JmpNext(usize),

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

    /// Sets the instruction pointer
    /// to the given value.
    ///
    /// Does not affect the stack.
    Jmp(usize),
    /// Sets the instruction pointer
    /// to the given value, if the
    /// topmost value is false, also
    /// pops this value.
    ///
    /// {A} - JmpFalse(n) - {}
    JmpFalse(usize),
    /// Sets the instruction pointer
    /// to the given value and pops
    /// the given amount of values.
    ///
    /// Used for 'break' and 'continue'.
    ///
    /// {A, B, C} - JmpNPop(n, 2) - {A}
    JmpNPop(usize, usize),

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

    /// Temporarily stops execution and returns
    /// to the call site.
    ///
    /// Does not affect the stack.
    Yield,
}

#[derive(Debug)]
enum BlockLinkState {
    Linked,
    Unlinked,
    Nothing,
}

#[derive(Debug)]
pub struct Block {
    pub ty: Type,
    upvalues: Vec<(usize, bool, Type)>,
    linking: BlockLinkState,

    pub name: String,
    pub file: PathBuf,
    ops: Vec<Op>,
    last_line_offset: usize,
    line_offsets: HashMap<usize, usize>,
}

impl Block {
    fn new(name: &str, file: &Path) -> Self {
        Self {
            ty: Type::Void,
            upvalues: Vec::new(),
            linking: BlockLinkState::Nothing,

            name: String::from(name),
            file: file.to_owned(),
            ops: Vec::new(),
            last_line_offset: 0,
            line_offsets: HashMap::new(),
        }
    }

    fn mark_constant(&mut self) {
        if self.upvalues.is_empty() {
            return;
        }
        self.linking = BlockLinkState::Unlinked;
    }

    // Used to create empty functions.
    fn stubbed_block(ty: &Type) -> Self {
        let mut block = Block::new("/empty/", Path::new(""));
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

    fn add_line(&mut self, token_position: usize) {
        if token_position != self.last_line_offset {
            self.line_offsets.insert(self.curr(), token_position);
            self.last_line_offset = token_position;
        }
    }

    fn line(&self, ip: usize) -> usize {
        for i in (0..=ip).rev() {
            if let Some(line) = self.line_offsets.get(&i) {
                return *line;
            }
        }
        0
    }

    pub fn debug_print(&self, constants: Option<&[Value]>) {
        println!("     === {} ===", self.name.blue());
        for (i, s) in self.ops.iter().enumerate() {
            println!(
                "{}{:05} {:?}{}",
                if self.line_offsets.contains_key(&i) {
                    format!("{:5} ", self.line_offsets[&i].blue())
                } else {
                    format!("    {} ", "|".blue())
                },
                i.red(),
                s,
                if let (Op::Constant(c), Some(constants)) = (s, constants) {
                    format!("    => {:?}", &constants[*c])
                } else {
                    "".to_string()
                }
            );
        }
        println!();
    }

    fn add(&mut self, op: Op, token_position: usize) -> usize {
        let mut len = self.curr();
        if matches!(op, Op::Pop) && len > 1 {
            len -= 1;
            match self.ops.last().unwrap() {
                Op::Copy(n) => {
                    if *n == 1 {
                        self.ops.pop();
                        return len - 1;
                    } else {
                        self.ops[len] = Op::Copy(*n - 1);
                        return len;
                    }
                }
                Op::Constant(_) | Op::ReadLocal(_) | Op::ReadUpvalue(_) => {
                    self.ops.pop();
                    return len - 1;
                }
                _ => {}
            }
        }
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

    fn patch(&mut self, op: Op, pos: usize) {
        self.ops[pos] = op;
    }
}

#[derive(Clone)]
pub struct Prog {
    pub blocks: Vec<RcMut<Block>>,
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
                    $crate::lib_sylt::_sylt_link(),
                );
                $crate::assert_errs!(res, $errs);
            }
        };
    }

    sylt_macro::find_tests!();
}
