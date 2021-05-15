use std::collections::{HashSet, HashMap};
use crate::error::{Error, RuntimeError, RuntimePhase};
use crate::{Type, Value, Prog, Args, Block, Op, BlockLinkState};
use owo_colors::OwoColorize;

use crate::rc::Rc;
use crate::rcmut::RcMut;

macro_rules! error {
    ( $thing:expr, $kind:expr) => {
        return Err($thing.error($kind, None));
    };
    ( $thing:expr, $kind:expr, $( $msg:expr ),*) => {
        {
            let msg = Some(format!($( $msg ),*).into());
            return Err($thing.error($kind, msg));
        }
    };
}

macro_rules! one_op {
    ( $self:expr, $op:expr, $fun:expr ) => {
        let a = $self.pop();
        let b = $fun(&a);
        if b.is_nil() {
            $self.push(b);
            error!($self, RuntimeError::TypeError($op, vec![a.into()]));
        }
        $self.push(b);
    };
}

macro_rules! two_op {
    ( $self:expr, $op:expr, $fun:expr ) => {
        let (a, b) = $self.poppop();
        let c = $fun(&a, &b);
        if c.is_nil() {
            $self.push(c);
            error!($self, RuntimeError::TypeError($op, vec![a.into(), b.into()]));
        }
        $self.push(c);
    };
}


pub struct VM {
    upvalues: Vec<Type>,
    stack: Vec<Type>,
    ip: usize,
    block: RcMut<Block>,
}

// Checks the program for type errors.
pub(crate) fn typecheck(prog: &Prog, args: &Args) -> Result<(), Vec<Error>> {
    let mut errors = Vec::new();
    for block in prog.blocks.iter() {
        errors.append(&mut typecheck_block(RcMut::clone(block), prog, &args));
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}


fn typecheck_block(block: RcMut<Block>, prog: &Prog, args: &Args) -> Vec<Error> {
    let print_bytecode = args.verbosity > 0;
    let print_exec = args.verbosity > 0;
    if print_bytecode {
        println!(
            "\n    [[{} - {}]]\n",
            "TYPECHECKING".purple(),
            block.as_ref().name
        );
        block.as_ref().debug_print(Some(&prog.constants));
    }

    let mut vm = VM::new(&block);
    let mut errors = Vec::new();
    for (ip, op) in (*block).ops.iter().enumerate() {
        vm.ip = ip;

        #[cfg(debug_assertions)]
        if print_exec {
            vm.print_stack()
        }

        if let Err(e) = vm.check_op(*op, prog) {
            errors.push(e);
        }
    }

    if print_bytecode {
        println!(
            "\n    [[{} - {}]]\n",
            "DONE".purple(),
            block.borrow().name
        );
    }

    errors
}


impl VM {
    pub(crate) fn new(block: &RcMut<Block>) -> Self {
        let mut vm = Self {
            upvalues: block.borrow().upvalues.iter().map(|(_, _, ty)| ty).cloned().collect(),
            stack: Vec::new(),
            ip: 0,
            block: RcMut::clone(block),
        };

        vm.push(block.borrow().ty.clone());
        for arg in block.borrow().args() {
            vm.push(arg.clone());
        }

        vm
    }

    fn print_stack(&self) {
        print!("        [", );
        for (i, s) in self.stack.iter().enumerate() {
            if i != 0 {
                print!(" ");
            }
            print!("{:?}", s.green());
        }
        println!("]");

        println!(
            "{:5} {:05} {:?}",
            self.block.borrow().line(self.ip).blue(),
            self.ip.red(),
            self.block.borrow().ops[self.ip]
        );
    }

    fn push(&mut self, ty: Type) {
        self.stack.push(ty);
    }

    fn pop(&mut self) -> Type {
        match self.stack.pop() {
            Some(x) => x,
            None => self.crash_and_burn(),
        }
    }

    fn poppop(&mut self) -> (Type, Type) {
        let (a, b) = (
            self.stack.remove(self.stack.len() - 1),
            self.stack.remove(self.stack.len() - 1),
        );
        (b, a) // this matches the order they were on the stack
    }

    fn error(&self, kind: RuntimeError, message: Option<String>) -> Error {
        Error::RuntimeError {
            kind,
            phase: RuntimePhase::Typecheck,
            file: self.block.borrow().file.clone(),
            line: self.block.borrow().line(self.ip),
            message,
        }
    }

    /// Stop the program, violently
    fn crash_and_burn(&self) -> ! {
        println!("Typecheck failed for {}", self.block.borrow().name);
        self.print_stack();
        unreachable!();
    }


    /// Checks the current operation for type errors.
    fn check_op(&mut self, op: Op, prog: &Prog) -> Result<(), Error> {
        match op {
            Op::Illegal => {}
            Op::Unreachable => {}
            Op::Jmp(_line) => {}
            Op::Yield => {}

            Op::Pop => { self.pop(); }
            Op::Copy(n) => {
                let end = Vec::from(&self.stack[self.stack.len() - n..]);
                self.stack.extend(end);
            }
            Op::ReadLocal(n) => {
                let ty = self.stack[n].clone();
                self.push(ty);
            }

            Op::Constant(slot) => {
                let value = &prog.constants[slot];
                self.push(Type::from(value));

                while let Value::Function(_, block) = value {
                    match block.borrow().linking {
                        BlockLinkState::Linked => break,
                        BlockLinkState::Unlinked => {
                            error!(self,
                                RuntimeError::InvalidProgram,
                                "Calling function '{}' before all captured variables are declared",
                                block.borrow().name);
                        }
                        BlockLinkState::Nothing => {},
                    }

                    let mut types = Vec::new();
                    for (slot, is_up, ty) in block.borrow().upvalues.iter() {
                        if *is_up {
                            types.push(ty.clone());
                        } else {
                            types.push((&self.stack[*slot]).clone());
                        }
                    }

                    let block_mut = block.get_mut();
                    for (i, (_, is_up, ty)) in block_mut.upvalues.iter_mut().enumerate() {
                        if *is_up {
                            continue;
                        }

                        let suggestion = &types[i];
                        if matches!(ty, Type::Unknown) {
                            *ty = suggestion.clone();
                        } else if ty != suggestion {
                            error!(
                                self,
                                RuntimeError::CannotInfer(ty.clone(), suggestion.clone())
                            );
                        }
                    }
                    break;
                }

            }

            Op::AssignField(field) => {
                let (inst, expect) = self.poppop();
                match inst {
                    Type::Instance(ty) => {
                        let field = &prog.strings[field];
                        match ty.fields.get(field) {
                            Some(ty) => {
                                if ty != &expect {
                                    error!(
                                        self,
                                        RuntimeError::TypeMismatch(expect, ty.clone()),
                                        "Types of field and variable do not match"
                                    );
                                }
                            }
                            _ => {
                                error!(
                                    self,
                                    RuntimeError::UnknownField(ty.name.clone(), field.clone())
                                );
                            }
                        };
                    }
                    inst => {
                        error!(
                            self,
                            RuntimeError::TypeError(Op::AssignField(field), vec![Type::from(inst)])
                        );
                    }
                }
            }

            Op::GetField(field) => {
                match self.pop() {
                    Type::Instance(ty) => {
                        match &*prog.strings[field] {
                            "_id" => { self.push(Type::Int); }
                            "_name" => { self.push(Type::String); }
                            field => {
                                match ty.fields.get(field) {
                                    Some(ty) => {
                                        self.push(ty.clone());
                                    }
                                    _ => {
                                        self.push(Type::Unknown);
                                        error!(
                                            self,
                                            RuntimeError::UnknownField(ty.name.clone(), field.to_string())
                                        );
                                    }
                                }
                            }
                        }
                    }
                    inst => {
                        error!(
                            self,
                            RuntimeError::TypeError(Op::GetField(field), vec![Type::from(inst)])
                        );
                    }
                }
            }

            Op::PopUpvalue => {
                self.pop();
            }

            Op::ReadUpvalue(slot) => {
                let ty = self.upvalues.get(slot).unwrap().clone();
                self.push(ty);
            }

            Op::AssignUpvalue(slot) => {
                let var = self.upvalues.get(slot).unwrap().clone();
                let up = self.pop();
                if var != up {
                    error!(
                        self,
                        RuntimeError::TypeMismatch(up, var),
                        "Captured varibles type doesn't match upvalue"
                    );
                }
            }

            Op::AssignLocal(slot) => {
                let var = self.stack[slot].clone();
                let other = self.pop();
                if var != other {
                    error!(
                        self,
                        RuntimeError::TypeMismatch(var, other),
                        "Cannot assign to different type"
                    );
                }
            }

            Op::Return => {
                let to_ret = self.pop();
                let ret = self.block.borrow().ret().clone();
                if to_ret != ret {
                    error!(
                        self,
                        RuntimeError::TypeMismatch(ret, to_ret),
                        "Value does not match return type"
                    );
                }
            }

            Op::Print => {
                self.pop();
            }

            Op::Define(ty) => {
                let ty = if let Value::Ty(ty) = &prog.constants[ty] {
                    ty.clone()
                } else {
                    unreachable!("Cannot define variable to non-type");
                };
                let top_type = self.stack.last().unwrap().clone();
                match (ty, top_type) {
                    (Type::Unknown, top_type) if top_type != Type::Unknown => {}
                    (a, b) if a.fits(&b) => {
                        let last = self.stack.len() - 1;
                        self.stack[last] = a;
                    }
                    (a, b) => {
                        error!(
                            self,
                            RuntimeError::TypeMismatch(a.clone(), b),
                            "Cannot assign mismatching types"
                        );
                    }
                }
            }

            Op::Iter => {
                let ty: Type = match Type::from(self.pop()) {
                    i if matches!(i, Type::Iter(_)) => {
                        self.push(i);
                        return Ok(());
                    }
                    Type::List(e) => {
                        e.as_ref().clone()
                    }
                    Type::Tuple(v) => {
                        let set: HashSet<_> = v.into_iter().collect();
                        match set.len() {
                            0 => Type::Unknown,
                            1 => set.into_iter().next().unwrap(),
                            _ => Type::Union(set),
                        }
                    }
                    Type::Set(v) => {
                        v.as_ref().clone()
                    }
                    Type::Dict(k, v) => {
                        Type::Tuple(vec![k.as_ref().clone(), v.as_ref().clone()])
                    }
                    i => {
                        error!(
                            self,
                            RuntimeError::TypeError(Op::Iter, vec![i]),
                            "Cannot convert to iterator"
                        );
                    }
                };
                self.push(Type::Iter(Box::new(ty)));
            }

            Op::JmpNext(_) => {
                if let Some(Type::Iter(ty)) = self.stack.last() {
                    let ty = (**ty).clone();
                    self.push(ty);
                } else {
                    error!(
                        self,
                        RuntimeError::InvalidProgram,
                        "Can only 'next' iterators"
                    );
                }
            }

            Op::Force(ty) => {
                self.pop();
                if let Value::Ty(ty) = &prog.constants[ty] {
                    self.push(ty.clone());
                } else {
                    error!(self, RuntimeError::InvalidProgram, "Can only force types");
                }
            }

            Op::Link(slot) => {
                match &prog.constants[slot] {
                    Value::Function(_, block) => {
                        block.get_mut().linking = BlockLinkState::Linked;

                        let mut types = Vec::new();
                        for (slot, is_up, ty) in block.borrow().upvalues.iter() {
                            if *is_up {
                                types.push(ty.clone());
                            } else {
                                types.push(self.stack[*slot].clone());
                            }
                        }

                        let block_mut = block.get_mut();
                        for (i, (_, is_up, ty)) in block_mut.upvalues.iter_mut().enumerate() {
                            if *is_up {
                                continue;
                            }

                            let suggestion = &types[i];
                            if matches!(ty, Type::Unknown) {
                                *ty = suggestion.clone();
                            } else if ty != suggestion {
                                error!(
                                    self,
                                    RuntimeError::CannotInfer(ty.clone(), suggestion.clone())
                                );
                            }
                        }

                    }

                    value => {
                        error!(
                            self,
                            RuntimeError::TypeError(op, vec![]),
                            "Cannot link non-function {:?}",
                            value
                        );
                    }
                };
            }

            Op::GetIndex => {
                match self.poppop() {
                    (Type::List(a), b) if b.fits(&Type::Int) => {
                        self.push((*a).clone());
                    }
                    (Type::Tuple(a), b) if b.fits(&Type::Int) => {
                        self.push(Type::Union(a.iter().cloned().collect()));
                    }
                    (Type::Dict(k, v), i) if k.fits(&i) => {
                        self.push((*v).clone());
                    }
                    _ => {
                        self.push(Type::Void);
                    }
                }
            }

            Op::AssignIndex => {
                let value = self.pop();
                let slot = self.pop();
                let indexable = self.pop();
                match (indexable, slot, value) {
                    (Type::List(v), Type::Int, n) => match (v.as_ref(), &n) {
                        (Type::Unknown, top_type) if top_type != &Type::Unknown => {}
                        (a, b) if a.fits(b) => {}
                        (a, b) => {
                            error!(
                                self,
                                RuntimeError::TypeMismatch(a.clone(), b.clone()),
                                "Cannot assign mismatching types"
                            );
                        }
                    },
                    (Type::Dict(k, v), i, n) => {
                        if !k.fits(&i) {
                            error!(
                                self,
                                RuntimeError::TypeMismatch(k.as_ref().clone(), i),
                                "Cannot index mismatching types"
                            );
                        }

                        if !v.fits(&n) {
                            error!(
                                self,
                                RuntimeError::TypeMismatch(v.as_ref().clone(), n),
                                "Cannot assign mismatching types"
                            );
                        }
                    }
                    (indexable, slot, _) => {
                        self.stack.push(Type::Void);
                        error!(
                            self,
                            RuntimeError::TypeError(Op::AssignIndex, vec![indexable, slot])
                        );
                    }
                }
            }

            Op::Contains => {
                let (element, container) = self.poppop();
                match (Type::from(container), Type::from(element)) {
                    (Type::List(v), e) | (Type::Set(v), e) | (Type::Dict(v, _), e) => {
                        self.push(Type::Bool);
                        if !v.fits(&e) {
                            error!(
                                self,
                                RuntimeError::TypeMismatch(v.as_ref().clone(), e),
                                "Container does not contain the type"
                            );
                        }
                    }
                    (indexable, e) => {
                        self.push(Type::Void);
                        error!(self, RuntimeError::IndexError(indexable.into(), e.into()));
                    }
                }
            }

            Op::Call(num_args) => {
                let new_base = self.stack.len() - 1 - num_args;
                let callable = &self.stack[new_base];

                let call_callable = |callable: &Type| {
                    let args = self.stack[new_base + 1..].to_vec();
                    match callable {
                        Type::Blob(blob) => {
                            let values = self.stack[new_base+1..]
                                .chunks_exact(2)
                                .map(|b| {
                                    if let Type::Field(f) = &b[0] {
                                        (f.clone(), b[1].clone())
                                    } else {
                                        unreachable!("Got {:?}, expected field", b[0]);
                                    }
                                }).collect::<HashMap<String, Type>>();

                            for (field, ty) in values.iter() {
                                match blob.fields.get(field) {
                                    Some(given_ty) if given_ty.fits(ty) => {}
                                    Some(given_ty) => {
                                        return Err(RuntimeError::FieldTypeMismatch(
                                                blob.name.clone(),
                                                field.clone(),
                                                ty.clone(),
                                                given_ty.clone(),
                                        ));
                                    }
                                    None => {
                                        return Err(RuntimeError::UnknownField(
                                                blob.name.clone(),
                                                field.clone(),
                                        ));
                                    }
                                }
                            }

                            for (field, ty) in blob.fields.iter() {
                                match (values.get(field), ty) {
                                    (Some(t), ty) if ty.fits(t) => {}
                                    (Some(t), ty) => {
                                        return Err(RuntimeError::FieldTypeMismatch(
                                                blob.name.clone(),
                                                field.clone(),
                                                ty.clone(),
                                                t.clone(),
                                        ))
                                    }
                                    (None, ty) if ty.fits(&Type::Void) => {}
                                    (None, ty) => {
                                        return Err(RuntimeError::FieldTypeMismatch(
                                                blob.name.clone(),
                                                field.clone(),
                                                ty.clone(),
                                                Type::Void,
                                        ));
                                    }
                                }
                            }

                            Ok(Type::Instance(Rc::clone(blob)))
                        }

                        Type::Function(fargs, fret) => {
                            if fargs != &args {
                                Err(RuntimeError::ArgumentType(fargs.clone(), args))
                            } else {
                                Ok((**fret).clone())
                            }
                        }

                        Type::ExternFunction(slot) => {
                            let extern_func = prog.functions[*slot];
                            let args: Vec<_> = self.stack[new_base + 1..].to_vec().into_iter().map(Value::from).collect();
                            extern_func(&args, true).map(|r| r.into())
                        }

                        _ => Err(RuntimeError::InvalidProgram),
                    }
                };

                let mut err = None;
                self.stack[new_base] = match callable {
                    Type::Union(alts) => {
                        let mut returns = HashSet::new();
                        for alt in alts.iter() {
                            if let Ok(res) = call_callable(&alt) {
                                returns.insert(Type::from(res));
                            }
                        }
                        if returns.is_empty() {
                            err = Some(RuntimeError::InvalidProgram);
                            Type::Void
                        } else {
                            Type::Union(returns)
                        }
                    }
                    _ => match call_callable(callable) {
                        Err(e) => {
                            err = Some(e);
                            Type::Void
                        }
                        Ok(v) => Type::from(v),
                    },
                };
                self.stack.truncate(new_base + 1);
                if let Some(err) = err {
                    error!(self, err);
                }
            }

            Op::JmpFalse(_) => match self.pop() {
                Type::Bool => {}
                a => {
                    error!(self, RuntimeError::TypeError(op, vec![a.into()]))
                }
            },

            Op::JmpNPop(_, _) => {}

            Op::Tuple(n) => {
                let n = self.stack.len() - n;
                let end = self.stack.split_off(n);
                self.push(Type::Tuple(end));
            }

            Op::List(n) => {
                let n = self.stack.len() - n;
                let ty = Type::maybe_union(self.stack.split_off(n).iter());
                self.push(Type::List(Box::new(ty)));
            }

            Op::Set(n) => {
                let n = self.stack.len() - n;
                let ty = Type::maybe_union(self.stack.split_off(n).iter());
                self.push(Type::Set(Box::new(ty)));
            }

            Op::Dict(n) => {
                let n = self.stack.len() - n;
                let elems = self.stack.split_off(n);
                let key = Type::maybe_union(elems.iter().step_by(2));
                let value = Type::maybe_union(elems.iter().skip(1).step_by(2));
                self.push(Type::Dict(Box::new(key), Box::new(value)));
            }

            // TODO(ed): These look the same as in vm.rs, since the macros and functions hide the
            // rest, maybe merge them?
            Op::Neg => {
                one_op!(self, Op::Neg, op::neg);
            }

            Op::Add => {
                two_op!(self, Op::Add, op::add);
            }

            Op::Sub => {
                two_op!(self, Op::Sub, op::sub);
            }

            Op::Mul => {
                two_op!(self, Op::Mul, op::mul);
            }

            Op::Div => {
                two_op!(self, Op::Div, op::div);
            }

            Op::Equal => {
                two_op!(self, Op::Equal, op::eq);
            }

            Op::Less => {
                two_op!(self, Op::Less, op::less);
            }

            Op::Greater => {
                two_op!(self, Op::Greater, op::greater);
            }

            Op::And => {
                two_op!(self, Op::And, op::and);
            }

            Op::Or => {
                two_op!(self, Op::Or, op::or);
            }

            Op::Not => {
                one_op!(self, Op::Not, op::not);
            }

            Op::Assert => {
                let ty = self.stack.last().unwrap().clone();
                if !matches!(ty, Type::Bool) {
                    error!(
                        self,
                        RuntimeError::TypeMismatch(ty, Type::Bool),
                        "Can only assert on bools"
                    );
                }
            }
        }
        Ok(())
    }

}

///
/// Module with all the operators that can be applied
/// to values.
///
/// Broken out because they need to be recursive.
mod op {
    use super::Type;
    use std::collections::HashSet;

    fn tuple_bin_op(
        a: &Vec<Type>,
        b: &Vec<Type>,
        f: fn(&Type, &Type) -> Type,
    ) -> Type {
        Type::Tuple(a.iter().zip(b.iter()).map(|(a, b)| f(a, b)).collect())
    }

    fn tuple_un_op(a: &Vec<Type>, f: fn(&Type) -> Type) -> Type {
        Type::Tuple(a.iter().map(f).collect())
    }

    fn union_un_op(a: &HashSet<Type>, f: fn(&Type) -> Type) -> Type {
        a.iter()
            .find_map(|x| {
                let x = f(x);
                if x.is_nil() {
                    None
                } else {
                    Some(x)
                }
            })
            .unwrap_or(Type::Void)
    }

    fn union_bin_op(a: &HashSet<Type>, b: &Type, f: fn(&Type, &Type) -> Type) -> Type {
        a.iter()
            .find_map(|x| {
                let x = f(x, b);
                if x.is_nil() {
                    None
                } else {
                    Some(x)
                }
            })
            .unwrap_or(Type::Void)
    }

    pub fn neg(value: &Type) -> Type {
        match value {
            Type::Float => Type::Float,
            Type::Int => Type::Int,
            Type::Tuple(a) => tuple_un_op(a, neg),
            Type::Union(v) => union_un_op(&v, neg),
            Type::Unknown => Type::Unknown,
            _ => Type::Void,
        }
    }

    pub fn not(value: &Type) -> Type {
        match value {
            Type::Bool => Type::Bool,
            Type::Tuple(a) => tuple_un_op(a, not),
            Type::Union(v) => union_un_op(&v, not),
            Type::Unknown => Type::Bool,
            _ => Type::Void,
        }
    }

    pub fn add(a: &Type, b: &Type) -> Type {
        match (a, b) {
            (Type::Float, Type::Float) => Type::Float,
            (Type::Int, Type::Int) => Type::Int,
            (Type::String, Type::String) => Type::String,
            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, add),
            (Type::Unknown, a) | (a, Type::Unknown) if !matches!(a, Type::Unknown) => add(a, a),
            (Type::Unknown, Type::Unknown) => Type::Unknown,
            (Type::Union(a), b) | (b, Type::Union(a)) => union_bin_op(&a, b, add),
            _ => Type::Void,
        }
    }

    pub fn sub(a: &Type, b: &Type) -> Type {
        add(a, &neg(b))
    }

    pub fn mul(a: &Type, b: &Type) -> Type {
        match (a, b) {
            (Type::Float, Type::Float) => Type::Float,
            (Type::Int, Type::Int) => Type::Int,
            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, mul),
            (Type::Unknown, a) | (a, Type::Unknown) if !matches!(a, Type::Unknown) => mul(a, a),
            (Type::Unknown, Type::Unknown) => Type::Unknown,
            (Type::Union(a), b) | (b, Type::Union(a)) => union_bin_op(&a, b, mul),
            _ => Type::Void,
        }
    }

    pub fn div(a: &Type, b: &Type) -> Type {
        match (a, b) {
            (Type::Float, Type::Float) => Type::Float,
            (Type::Int, Type::Int) => Type::Int,
            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, div),
            (Type::Unknown, a) | (a, Type::Unknown) if !matches!(a, Type::Unknown) => div(a, a),
            (Type::Unknown, Type::Unknown) => Type::Unknown,
            (Type::Union(a), b) | (b, Type::Union(a)) => union_bin_op(&a, b, div),
            _ => Type::Void,
        }
    }

    pub fn eq(a: &Type, b: &Type) -> Type {
        match (a, b) {
            (Type::Float, Type::Float) => Type::Bool,
            (Type::Int, Type::Int) => Type::Bool,
            (Type::String, Type::String) => Type::Bool,
            (Type::Bool, Type::Bool) => Type::Bool,
            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() =>
                a.iter()
                .zip(b.iter())
                .find_map(|(a, b)| match less(a, b) {
                    Type::Bool => None,
                    a => Some(a),
                })
                .unwrap_or(Type::Bool),
            (Type::Unknown, a) | (a, Type::Unknown) if !matches!(a, Type::Unknown) => eq(a, a),
            (Type::Unknown, Type::Unknown) => Type::Unknown,
            (Type::Union(a), b) | (b, Type::Union(a)) => union_bin_op(&a, b, eq),
            (Type::Void, Type::Void) => Type::Bool,
            (Type::List(a), Type::List(b)) => eq(a, b),
            _ => Type::Void,
        }
    }

    pub fn less(a: &Type, b: &Type) -> Type {
        match (a, b) {
            (Type::Float, Type::Float) => Type::Bool,
            (Type::Int, Type::Int) => Type::Bool,
            (Type::String, Type::String) => Type::Bool,
            (Type::Bool, Type::Bool) => Type::Bool,
            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() =>
                a.iter()
                .zip(b.iter())
                .find_map(|(a, b)| match less(a, b) {
                    Type::Bool => None,
                    a => Some(a),
                })
                .unwrap_or(Type::Bool),
            (Type::Unknown, a) | (a, Type::Unknown) if !matches!(a, Type::Unknown) => less(a, a),
            (Type::Unknown, Type::Unknown) => Type::Unknown,
            (Type::Union(a), b) | (b, Type::Union(a)) => union_bin_op(&a, b, less),
            _ => Type::Void,
        }
    }

    pub fn greater(a: &Type, b: &Type) -> Type {
        less(b, a)
    }

    pub fn and(a: &Type, b: &Type) -> Type {
        match (a, b) {
            (Type::Bool, Type::Bool) => Type::Bool,
            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, and),
            (Type::Unknown, a) | (a, Type::Unknown) if !matches!(a, Type::Unknown) => and(a, a),
            (Type::Unknown, Type::Unknown) => Type::Unknown,
            (Type::Union(a), b) | (b, Type::Union(a)) => union_bin_op(&a, b, and),
            _ => Type::Void,
        }
    }

    pub fn or(a: &Type, b: &Type) -> Type {
        match (a, b) {
            (Type::Bool, Type::Bool) => Type::Bool,
            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, or),
            (Type::Unknown, a) | (a, Type::Unknown) if !matches!(a, Type::Unknown) => or(a, a),
            (Type::Unknown, Type::Unknown) => Type::Unknown,
            (Type::Union(a), b) | (b, Type::Union(a)) => union_bin_op(&a, b, or),
            _ => Type::Void,
        }
    }
}
