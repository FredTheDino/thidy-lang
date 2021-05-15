use crate::*;
use crate as sylt;

#[sylt_macro::sylt_doc(dbg, "Writes the type and value of anything you enter", [One(Value(val))] Type::Void)]
#[sylt_macro::sylt_link(dbg, "sylt::lib_sylt")]
pub fn dbg(values: &[Value], _typecheck: bool) -> Result<Value, RuntimeError> {
    println!(
        "{}: {:?}, {:?}",
        "DBG".purple(),
        values.iter().map(Type::from).collect::<Vec<_>>(),
        values
    );
    Ok(Value::Nil)
}

#[sylt_macro::sylt_doc(push, "Appends an element to the end of a list", [One(List(ls)), One(Value(val))] Type::Void)]
#[sylt_macro::sylt_link(push, "sylt::lib_sylt")]
pub fn push(values: &[Value], typecheck: bool) -> Result<Value, RuntimeError> {
    match (values, typecheck) {
        ([Value::List(ls), v], true) => {
            let ls = ls.as_ref();
            assert!(ls.len() == 1);
            let ls = Type::from(&ls[0]);
            let v: Type = Type::from(&*v);
            if ls == v || matches!(ls, Type::Unknown) {
                Ok(Value::Nil)
            } else {
                Err(RuntimeError::TypeMismatch(ls, v))
            }
        }
        ([Value::List(ls), v], false) => {
            // NOTE(ed): Deliberately no type checking.
            ls.get_mut().push(v.clone());
            Ok(Value::Nil)
        }
        (values, _) => Err(RuntimeError::ExternTypeMismatch(
            "push".to_string(),
            values.iter().map(Type::from).collect(),
        )),
    }
}

#[sylt_macro::sylt_doc(clear, "Removes all elements from the list", [One(List(ls))] Type::Void)]
#[sylt_macro::sylt_link(clear, "sylt::lib_sylt")]
pub fn clear(values: &[Value], typecheck: bool) -> Result<Value, RuntimeError> {
    match (values, typecheck) {
        ([Value::List(ls)], _) => {
            ls.get_mut().clear();
            Ok(Value::Nil)
        }
        (values, _) => Err(RuntimeError::ExternTypeMismatch(
            "empty".to_string(),
            values.iter().map(Type::from).collect(),
        )),
    }
}


#[sylt_macro::sylt_doc(prepend, "Adds an element to the start of a list", [One(List(ls)), One(Value(val))] Type::Void)]
#[sylt_macro::sylt_link(prepend, "sylt::lib_sylt")]
pub fn prepend(values: &[Value], typecheck: bool) -> Result<Value, RuntimeError> {
    match (values, typecheck) {
        ([Value::List(ls), v], true) => {
            let ls = ls.as_ref();
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
            ls.get_mut().insert(0, v.clone());
            Ok(Value::Nil)
        }
        (values, _) => Err(RuntimeError::ExternTypeMismatch(
            "prepend".to_string(),
            values.iter().map(Type::from).collect(),
        )),
    }
}

#[sylt_macro::sylt_doc(len, "Gives the length of tuples and lists", [One(Tuple(ls))] Type::Int, [One(List(ls))] Type::Int)]
#[sylt_macro::sylt_link(len, "sylt::lib_sylt")]
pub fn len(values: &[Value], _: bool) -> Result<Value, RuntimeError> {
    match values {
        [Value::Tuple(ls)] => {
            Ok(Value::Int(ls.len() as i64))
        }
        [Value::List(ls)] => {
            Ok(Value::Int(ls.as_ref().len() as i64))
        }
        [_] => {
            Ok(Value::Int(0))
        }
        values => Err(RuntimeError::ExternTypeMismatch(
            "len".to_string(),
            values.iter().map(Type::from).collect(),
        )),
    }
}

sylt_macro::extern_function!(
    "sylt::lib_sylt"
    atan2
    ""
    [One(Float(x)), One(Float(y))] -> Type::Float => {
        Ok(Float(y.atan2(*x)))
    },
);


sylt_macro::extern_function!(
    "sylt::lib_sylt"
    sin
    "The sine function you know and love from trigonometry class"
    [One(Float(t))] -> Type::Float => {
        Ok(Float(t.sin()))
    },
);

sylt_macro::extern_function!(
    "sylt::lib_sylt"
    cos
    "The cosine function you know and love from trigonometry class"
    [One(Float(t))] -> Type::Float => {
        Ok(Float(t.cos()))
    },
);

sylt_macro::extern_function!(
    "sylt::lib_sylt"
    as_float
    "Converts the int to a float"
    [One(Int(t))] -> Type::Float => {
        Ok(Float(*t as f64))
    },
    [Two(Int(t), Int(u))] -> Type::Tuple(vec![Type::Float, Type::Float]) => {
        Ok(Tuple(Rc::new(vec![Float(*t as f64), Float(*u as f64)])))
    },
);

sylt_macro::extern_function!(
    "sylt::lib_sylt"
    as_int
    "Converts the int to a float"
    [One(Float(t))] -> Type::Int => {
        Ok(Int(*t as i64))
    },
);

sylt_macro::extern_function!(
    "sylt::lib_sylt"
    sqrt
    "Returns the square root"
    [One(Float(x))] -> Type::Float => {
        Ok(Float(x.sqrt()))
    },
);

sylt_macro::extern_function!(
    "sylt::lib_sylt"
    abs
    "Returns the square root"
    [One(Float(x))] -> Type::Float => {
        Ok(Float(x.abs()))
    },
);

sylt_macro::extern_function!(
    "sylt::lib_sylt"
    clamp
    "Clamps the value 'a' between 'lo' and 'hi'"
    [One(Float(a)), One(Float(lo)), One(Float(hi))] -> Type::Float => {
        Ok(Float(a.min(*hi).max(*lo)))
    },
    [One(Int(a)), One(Int(lo)), One(Int(hi))] -> Type::Int => {
        Ok(Int(*a.min(hi).max(lo))) //TODO Other borrows than above
    },
);

sylt_macro::extern_function!(
    "sylt::lib_sylt"
    min
    "Returns the smallest"
    [One(Float(a)), One(Float(b))] -> Type::Float => {
        Ok(Float(a.min(*b)))
    },
);

sylt_macro::extern_function!(
    "sylt::lib_sylt"
    max
    "Returns the largest"
    [One(Float(a)), One(Float(b))] -> Type::Float => {
        Ok(Float(a.max(*b)))
    },
);

sylt_macro::extern_function!(
    "sylt::lib_sylt"
    rem
    "Returns the remainder after division"
    [One(Float(x)), One(Float(y))] -> Type::Float => {
        Ok(Float(x % y))
    },
    [One(Int(x)), One(Int(y))] -> Type::Int => {
        Ok(Int(x % y))
    },
);



pub fn union_type(a: Type, b: Type) -> Type{
    if a.fits(&b) {
        a
    } else if b.fits(&a) {
        b
    } else {
        match (a, b) {
            (Type::Union(a), Type::Union(b)) => {
                Type::Union(a.union(&b).cloned().collect())
            }
            (b, Type::Union(a)) | (Type::Union(a), b) => {
                let mut a = a.clone();
                a.insert(b.clone());
                Type::Union(a)
            }
            (a, b) => {
                Type::Union([a, b].iter().cloned().collect())
            }
        }
    }
}

#[sylt_macro::sylt_doc(pop, "Removes the last element in the list, and returns it", [One(List(l))] Type::Value)]
#[sylt_macro::sylt_link(pop, "sylt::lib_sylt")]
pub fn pop(values: &[Value], typecheck: bool) -> Result<Value, RuntimeError> {
    match (values, typecheck) {
        ([Value::List(ls)], true) => {
            let ls = ls.as_ref();
            // TODO(ed): Write correct typing
            let ls = Type::from(&ls[0]);
            let ret = union_type(ls, Type::Void);
            Ok(Value::from(ret))
        }
        ([Value::List(ls)], false) => {
            // NOTE(ed): Deliberately no type checking.
            let last = ls.get_mut().pop().unwrap_or(Value::Nil);
            Ok(last)
        }
        (values, _) => Err(RuntimeError::ExternTypeMismatch(
            "pop".to_string(),
            values.iter().map(Type::from).collect(),
        )),
    }
}

#[sylt_macro::sylt_doc(inf, "Returns an infinite iterator, spitting out the value you give it", [One(Value(val))] Type::Iter)]
#[sylt_macro::sylt_link(inf, "sylt::lib_sylt")]
pub fn inf(values: &[Value], _typecheck: bool) -> Result<Value, RuntimeError> {
    match values {
        [x] => {
            let t: Type = Type::from(&*x);
            let x = x.clone();
            Ok(Value::Iter(t, RcMut::new(Box::new(move || Some(x.clone())))))
        }
        values => Err(RuntimeError::ExternTypeMismatch(
            "inf".to_string(),
            values.iter().map(Type::from).collect(),
        )),
    }
}

sylt_macro::sylt_link_gen!("sylt::lib_sylt");
