#![allow(dead_code, unused_imports, unused_mut, unreachable_patterns, unused_assignments)]

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
    Nil,
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

    fn value(&self) -> Value {
        let value: &RefCell<_> = self.value.borrow();
        value.borrow().clone()
    }

    fn assign(&self, from: Value) {
        let value: &RefCell<_> = self.value.borrow();
        let mut from = from;
        std::mem::swap(&mut *value.borrow_mut(), &mut from);
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
