#![allow(dead_code, unused_imports, unused_mut, unreachable_patterns, unused_assignments, non_camel_case_types)]

use std::borrow::Borrow;
use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

pub type Fun = Rc<RefCell<dyn FnMut(&[Value]) -> Value>>;

#[derive(Clone)]
pub enum Value {
    Float(f64),
    Int(i64),
    Bool(bool),
    String(String),
    Function(Fun),
    List(Vec<Value>),
    Tuple(Vec<Value>),
    Set(HashSet<Value>),
    Dict(HashMap<Value, Value>),
    Instance(HashMap<Field, Value>),
    Nil,
}

impl Value {
    fn iter(&self) -> std::vec::IntoIter<Value> {
        match self {
            Value::List(v) | Value::Tuple(v) => v.clone().into_iter(),
            Value::Set(v) => v.iter().cloned().collect::<Vec<Value>>().into_iter(),
            Value::Dict(v) => v.iter().map(|(k, v)| Value::Tuple(vec![k.clone(), v.clone()])).collect::<Vec<Value>>().into_iter(),
            x => unimplemented!("Cannot itrate over \"{:?}\"", x),
        }
    }

    fn index(self, index: Value) -> Value {
        match self {
            Value::List(v) |  Value::Tuple(v) => {
                match index {
                    Value::Int(i) => v[i as usize].clone(),
                    x => unimplemented!("Cannot index with value \"{:?}\"", x),
                }
            }
            Value::Dict(v) => {
                v.get(&index).cloned().or(Some(Value::Nil)).unwrap()
            }
            x => unimplemented!("Cannot index \"{:?}\"", x),
        }
    }

    fn assign_index(&mut self, index: Value, value: Value) {
        match self {
            Value::List(v) |  Value::Tuple(v) => {
                match index {
                    Value::Int(i) => v[i as usize] = value,
                    x => unimplemented!("Cannot index with value \"{:?}\"", x),
                }
            }
            Value::Dict(v) => {
                v.insert(index, value);
            }
            x => unimplemented!("Cannot index assign to \"{:?}\"", x),
        };
    }
}

#[derive(Clone)]
pub struct Var {
    value: Rc<RefCell<Value>>,
}

impl Var {
    fn new(value: Value) -> Self {
        Self {
            value: Rc::new(RefCell::new(value)),
        }
    }

    pub fn value(&self) -> Value {
        let value: &RefCell<_> = self.value.borrow();
        value.borrow().clone()
    }

    pub fn assign(&self, from: Value) {
        let value: &RefCell<_> = self.value.borrow();
        let mut from = from;
        std::mem::swap(&mut *value.borrow_mut(), &mut from);
    }

    pub fn assign_index(&self, index: Value, value: Value) {
        let lhs: &RefCell<_> = self.value.borrow();
        lhs.borrow_mut().assign_index(index, value);
    }

}

impl Debug for Value {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // TODO(ed): This needs some cleaning
        match self {
            Value::Float(f) => write!(fmt, "(float {})", f),
            Value::Int(i) => write!(fmt, "(int {})", i),
            Value::Bool(b) => write!(fmt, "(bool {})", b),
            Value::String(s) => write!(fmt, "(string \"{}\")", s),
            Value::Function(_) => write!(fmt, "(function)"),
            Value::List(v) => write!(fmt, "(list {:?})", v),
            Value::Tuple(v) => write!(fmt, "(tuple {:?})", v),
            Value::Set(v) => write!(fmt, "(set {:?})", v),
            Value::Dict(v) => write!(fmt, "(dict {:?})", v),
            Value::Instance(v) => write!(fmt, "(instance {:?})", v),
            Value::Nil => write!(fmt, "(nil)"),
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
            Value::Nil => state.write_i8(0),
            _ => {}
        };
    }
}

mod op {
    use super::{Value, Var};
    use std::collections::HashSet;
    use std::rc::Rc;
    use std::cell::RefCell;

    pub fn neg(value: &Value) -> Value {
        match value {
            Value::Float(a) => Value::Float(-*a),
            Value::Int(a) => Value::Int(-*a),
            _ => Value::Nil,
        }
    }

    pub fn not(value: &Value) -> Value {
        match value {
            Value::Bool(a) => Value::Bool(!*a),
            _ => Value::Nil,
        }
    }

    pub fn add(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Float(a), Value::Float(b)) => Value::Float(a + b),
            (Value::Int(a), Value::Int(b)) => Value::Int(a + b),
            (Value::String(a), Value::String(b)) => Value::String(format!("{}{}", a, b)),
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
            _ => Value::Nil,
        }
    }

    pub fn div(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Float(a), Value::Float(b)) => Value::Float(a / b),
            (Value::Int(a), Value::Int(b)) => Value::Int(a / b),
            _ => Value::Nil,
        }
    }

    pub fn eq(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Float(a), Value::Float(b)) => Value::Bool(a == b),
            (Value::Int(a), Value::Int(b)) => Value::Bool(a == b),
            (Value::String(a), Value::String(b)) => Value::Bool(a == b),
            (Value::Bool(a), Value::Bool(b)) => Value::Bool(a == b),
            (Value::Nil, Value::Nil) => Value::Bool(true),
            _ => Value::Nil,
        }
    }

    pub fn less(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Float(a), Value::Float(b)) => Value::Bool(a < b),
            (Value::Int(a), Value::Int(b)) => Value::Bool(a < b),
            (Value::String(a), Value::String(b)) => Value::Bool(a < b),
            (Value::Bool(a), Value::Bool(b)) => Value::Bool(a < b),
            _ => Value::Nil,
        }
    }

    pub fn greater(a: &Value, b: &Value) -> Value {
        less(b, a)
    }

    pub fn and(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Bool(a), Value::Bool(b)) => Value::Bool(*a && *b),
            _ => Value::Nil,
        }
    }

    pub fn or(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Bool(a), Value::Bool(b)) => Value::Bool(*a || *b),
            _ => Value::Nil,
        }
    }

    pub fn contains(element: &Value, collection: &Value) -> Value {
        match collection {
            Value::List(v) | Value::Tuple(v) => Value::Bool(v.contains(element)),
            Value::Set(v) => Value::Bool(v.contains(element)),
            Value::Dict(v) => Value::Bool(v.contains_key(element)),
            _ => Value::Nil,
        }
    }

    pub fn call(f: &Var, args: &[Value]) -> Value {
        let value: &RefCell<Value> = &*f.value;
        let mut value: &Value = &mut value.borrow_mut();
        if let Value::Function(f) = value {
            let f: &RefCell<_> = &*f;
            f.borrow_mut()(args)
        } else {
            unreachable!();
        }
    }
}
