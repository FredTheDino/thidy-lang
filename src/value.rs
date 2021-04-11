#![allow(dead_code)]
use std::borrow::Borrow;
use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use crate::{Block};

#[derive(Debug, Clone)]
pub enum Type {
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
}

impl Hash for Type {
    fn hash<H: Hasher>(&self, h: &mut H) {
        // TODO(ed): We can use the fancy macro here instead.
        match self {
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
                for (_, t) in b.fields.values() {
                    t.hash(h);
                }
                10
            }
            Type::Instance(b) => {
                for (_, t) in b.fields.values() {
                    t.hash(h);
                }
                11
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
            Value::Instance(b, _) => Type::Instance(Rc::clone(b)),
            Value::Blob(b) => Type::Blob(Rc::clone(b)),
            Value::Tuple(v) => Type::Tuple(v.iter().map(Type::from).collect()),
            Value::List(v) => {
                let v: &RefCell<_> = v.borrow();
                let v = &v.borrow();
                let t = maybe_union_type(v.iter());
                Type::List(Box::new(t))
            }
            Value::Set(v) => {
                let v: &RefCell<_> = v.borrow();
                let v = &v.borrow();
                let t = maybe_union_type(v.iter());
                Type::Set(Box::new(t))
            }
            Value::Dict(v) => {
                let v: &RefCell<_> = v.borrow();
                let v = &v.borrow();
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
                let block: &RefCell<_> = block.borrow();
                let block = &block.borrow();
                block.borrow().ty.clone()
            }
            Value::Unknown => Type::Unknown,
            Value::Nil | Value::Ty(_) | Value::ExternFunction(_) => Type::Void,
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
            Type::Void => Value::Nil,
            Type::Blob(b) => Value::Blob(Rc::clone(b)),
            Type::Instance(b) => Value::Instance(Rc::clone(b), Rc::new(RefCell::new(Vec::new()))),
            Type::Tuple(fields) => Value::Tuple(Rc::new(fields.iter().map(Value::from).collect())),
            Type::Union(v) => Value::Union(v.iter().map(Value::from).collect()),
            Type::List(v) => Value::List(Rc::new(RefCell::new(vec![Value::from(v.as_ref())]))),
            Type::Set(v) => {
                let mut s = HashSet::new();
                s.insert(Value::from(v.as_ref()));
                Value::Set(Rc::new(RefCell::new(s)))
            }
            Type::Dict(k, v) => {
                let mut s = HashMap::new();
                s.insert(Value::from(k.as_ref()), Value::from(v.as_ref()));
                Value::Dict(Rc::new(RefCell::new(s)))
            }
            Type::Iter(v) => Value::Iter(v.as_ref().clone(), Rc::new(RefCell::new(|| None))),
            Type::Unknown => Value::Unknown,
            Type::Int => Value::Int(1),
            Type::Float => Value::Float(1.0),
            Type::Bool => Value::Bool(true),
            Type::String => Value::String(Rc::new("".to_string())),
            Type::Function(_, _) => Value::Function(
                Rc::new(Vec::new()),
                Rc::new(RefCell::new(Block::stubbed_block(ty))),
            ),
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
}

pub type IterFn = dyn FnMut() -> Option<Value>;

#[derive(Clone)]
pub enum Value {
    Ty(Type),
    Blob(Rc<Blob>),
    Instance(Rc<Blob>, Rc<RefCell<Vec<Value>>>),
    Tuple(Rc<Vec<Value>>),
    List(Rc<RefCell<Vec<Value>>>),
    Set(Rc<RefCell<HashSet<Value>>>),
    Dict(Rc<RefCell<HashMap<Value, Value>>>),
    #[allow(dead_code)]
    Iter(Type, Rc<RefCell<IterFn>>),
    Union(HashSet<Value>),
    Float(f64),
    Int(i64),
    Bool(bool),
    String(Rc<String>),
    Function(Rc<Vec<Type>>, Rc<RefCell<Block>>),
    ExternFunction(usize),
    /// This value should not be present when running, only when type checking.
    /// Most operations are valid but produce funky results.
    Unknown,
    /// Should not be present when running.
    Nil,
}


impl Value {
    pub fn compiled(&self) -> String {
        match self {
            Value::Float(f) => format!("Value::Float({})", f),
            Value::Int(i) => format!("Value::Int({})", i),
            Value::Bool(b) => format!("Value::Bool({})", b),
            Value::Nil => format!("Value::Nil"),
            // TODO(ed): This won't support everything, right?
            Value::String(s) => format!("Value::String(Rc::new(\"{}\".to_string()))", s),
            x => unimplemented!("compiled not implemented for \"{:?}\"", x),
        }
    }
}

impl Debug for Value {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // TODO(ed): This needs some cleaning
        match self {
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
                let block: &RefCell<_> = block.borrow();
                let block = &block.borrow();
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

#[derive(Debug, Clone)]
pub struct Blob {
    pub id: usize,
    pub name: String,
    /// Maps field names to their slot and type.
    pub fields: HashMap<String, (usize, Type)>,
}

impl PartialEq for Blob {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Blob {
    pub fn new(id: usize, name: &str) -> Self {
        Self {
            id,
            name: String::from(name),
            fields: HashMap::new(),
        }
    }

    pub fn add_field(&mut self, name: &str, ty: Type) -> Result<(), ()> {
        let size = self.fields.len();
        let entry = self.fields.entry(String::from(name));
        match entry {
            Entry::Occupied(_) => Err(()),
            Entry::Vacant(v) => {
                v.insert((size, ty));
                Ok(())
            }
        }
    }
}

mod op {
    use super::{Type, Value};
    use std::collections::HashSet;
    use std::rc::Rc;

    fn tuple_bin_op(
        a: &Rc<Vec<Value>>,
        b: &Rc<Vec<Value>>,
        f: fn(&Value, &Value) -> Value,
    ) -> Value {
        Value::Tuple(Rc::new(
            a.iter().zip(b.iter()).map(|(a, b)| f(a, b)).collect(),
        ))
    }

    fn tuple_un_op(a: &Rc<Vec<Value>>, f: fn(&Value) -> Value) -> Value {
        Value::Tuple(Rc::new(a.iter().map(f).collect()))
    }

    fn union_un_op(a: &HashSet<Value>, f: fn(&Value) -> Value) -> Value {
        a.iter()
            .find_map(|x| {
                let x = f(x);
                if matches!(x, Value::Nil) {
                    None
                } else {
                    Some(x)
                }
            })
            .unwrap_or(Value::Nil)
    }

    fn union_bin_op(a: &HashSet<Value>, b: &Value, f: fn(&Value, &Value) -> Value) -> Value {
        a.iter()
            .find_map(|x| {
                let x = f(x, b);
                if matches!(x, Value::Nil) {
                    None
                } else {
                    Some(x)
                }
            })
            .unwrap_or(Value::Nil)
    }

    pub fn neg(value: &Value) -> Value {
        match value {
            Value::Float(a) => Value::Float(-*a),
            Value::Int(a) => Value::Int(-*a),
            Value::Tuple(a) => tuple_un_op(a, neg),
            Value::Union(v) => union_un_op(&v, neg),
            Value::Unknown => Value::Unknown,
            _ => Value::Nil,
        }
    }

    pub fn not(value: &Value) -> Value {
        match value {
            Value::Bool(a) => Value::Bool(!*a),
            Value::Tuple(a) => tuple_un_op(a, not),
            Value::Union(v) => union_un_op(&v, not),
            Value::Unknown => Value::from(Type::Bool),
            _ => Value::Nil,
        }
    }

    pub fn add(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Float(a), Value::Float(b)) => Value::Float(a + b),
            (Value::Int(a), Value::Int(b)) => Value::Int(a + b),
            (Value::String(a), Value::String(b)) => Value::String(Rc::from(format!("{}{}", a, b))),
            (Value::Tuple(a), Value::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, add),
            (Value::Unknown, a) | (a, Value::Unknown) if !matches!(a, Value::Unknown) => add(a, a),
            (Value::Unknown, Value::Unknown) => Value::Unknown,
            (Value::Union(a), b) | (b, Value::Union(a)) => union_bin_op(&a, b, add),
            _ => Value::Nil,
        }
    }

    pub fn sub(a: &Value, b: &Value) -> Value {
        add(a, &neg(b))
    }

    pub fn mul(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Float(a), Value::Float(b)) => Value::Float(a * b),
            (Value::Int(a), Value::Int(b)) => Value::Int(a * b),
            (Value::Tuple(a), Value::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, mul),
            (Value::Unknown, a) | (a, Value::Unknown) if !matches!(a, Value::Unknown) => mul(a, a),
            (Value::Unknown, Value::Unknown) => Value::Unknown,
            (Value::Union(a), b) | (b, Value::Union(a)) => union_bin_op(&a, b, mul),
            _ => Value::Nil,
        }
    }

    pub fn div(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Float(a), Value::Float(b)) => Value::Float(a / b),
            (Value::Int(a), Value::Int(b)) => Value::Int(a / b),
            (Value::Tuple(a), Value::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, div),
            (Value::Unknown, a) | (a, Value::Unknown) if !matches!(a, Value::Unknown) => div(a, a),
            (Value::Unknown, Value::Unknown) => Value::Unknown,
            (Value::Union(a), b) | (b, Value::Union(a)) => union_bin_op(&a, b, div),
            _ => Value::Nil,
        }
    }

    pub fn eq(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Float(a), Value::Float(b)) => Value::Bool(a == b),
            (Value::Int(a), Value::Int(b)) => Value::Bool(a == b),
            (Value::String(a), Value::String(b)) => Value::Bool(a == b),
            (Value::Bool(a), Value::Bool(b)) => Value::Bool(a == b),
            (Value::Tuple(a), Value::Tuple(b)) if a.len() == b.len() => {
                for (a, b) in a.iter().zip(b.iter()) {
                    match eq(a, b) {
                        Value::Bool(true) => {}
                        Value::Bool(false) => {
                            return Value::Bool(false);
                        }
                        Value::Nil => {
                            return Value::Nil;
                        }
                        _ => unreachable!("Equality should only return bool or nil."),
                    }
                }
                Value::Bool(true)
            }
            (Value::Unknown, a) | (a, Value::Unknown) if !matches!(a, Value::Unknown) => eq(a, a),
            (Value::Unknown, Value::Unknown) => Value::Unknown,
            (Value::Union(a), b) | (b, Value::Union(a)) => union_bin_op(&a, b, eq),
            (Value::Nil, Value::Nil) => Value::Bool(true),
            (Value::List(a), Value::List(b)) => {
                let a = a.borrow();
                let b = b.borrow();
                if a.len() != b.len() {
                    return Value::Bool(false);
                }
                for (a, b) in a.iter().zip(b.iter()) {
                    match eq(a, b) {
                        Value::Bool(true) => {}
                        Value::Bool(false) => {
                            return Value::Bool(false);
                        }
                        Value::Nil => {
                            return Value::Nil;
                        }
                        _ => unreachable!("Equality should only return bool or nil."),
                    }
                }
                Value::Bool(true)
            }
            _ => Value::Nil,
        }
    }

    pub fn less(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Float(a), Value::Float(b)) => Value::Bool(a < b),
            (Value::Int(a), Value::Int(b)) => Value::Bool(a < b),
            (Value::String(a), Value::String(b)) => Value::Bool(a < b),
            (Value::Bool(a), Value::Bool(b)) => Value::Bool(a < b),
            (Value::Tuple(a), Value::Tuple(b)) if a.len() == b.len() => a
                .iter()
                .zip(b.iter())
                .find_map(|(a, b)| match less(a, b) {
                    Value::Bool(true) => None,
                    a => Some(a),
                })
                .unwrap_or(Value::Bool(true)),
            (Value::Unknown, a) | (a, Value::Unknown) if !matches!(a, Value::Unknown) => less(a, a),
            (Value::Unknown, Value::Unknown) => Value::Unknown,
            (Value::Union(a), b) | (b, Value::Union(a)) => union_bin_op(&a, b, less),
            _ => Value::Nil,
        }
    }

    pub fn greater(a: &Value, b: &Value) -> Value {
        less(b, a)
    }

    pub fn and(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Bool(a), Value::Bool(b)) => Value::Bool(*a && *b),
            (Value::Tuple(a), Value::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, and),
            (Value::Unknown, a) | (a, Value::Unknown) if !matches!(a, Value::Unknown) => and(a, a),
            (Value::Unknown, Value::Unknown) => Value::Unknown,
            (Value::Union(a), b) | (b, Value::Union(a)) => union_bin_op(&a, b, and),
            _ => Value::Nil,
        }
    }

    pub fn or(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Bool(a), Value::Bool(b)) => Value::Bool(*a || *b),
            (Value::Tuple(a), Value::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, or),
            (Value::Unknown, a) | (a, Value::Unknown) if !matches!(a, Value::Unknown) => or(a, a),
            (Value::Unknown, Value::Unknown) => Value::Unknown,
            (Value::Union(a), b) | (b, Value::Union(a)) => union_bin_op(&a, b, or),
            _ => Value::Nil,
        }
    }
}
