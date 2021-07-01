use std::cell::RefCell;
use std::collections::{hash_map::Entry, HashMap};
use std::path::PathBuf;
use sylt_common::error::Error;
use sylt_common::prog::Prog;
use sylt_common::rc::Rc;
use sylt_common::{Blob, Block, Op, RustFunction, Type, Value};
use sylt_parser::{
    Assignable, AssignableKind, Expression, ExpressionKind, Identifier, Module, Op as ParserOp,
    Span, Statement, StatementKind, Type as ParserType, TypeKind, VarKind, AST,
};

type VarSlot = usize;

#[derive(Debug, Clone)]
struct Variable {
    name: String,
    ty: Type,
    slot: usize,
    line: usize,
    kind: VarKind,

    captured: bool,
    active: bool,
}

impl Variable {
    fn new(name: String, kind: VarKind, ty: Type, slot: usize, span: Span) -> Self {
        Self {
            name,
            ty,
            slot,
            kind,
            line: span.line,

            captured: false,
            active: false,
        }
    }
}

#[derive(Debug, Clone)]
struct Upvalue {
    parent: usize,
    upupvalue: bool,

    name: String,
    ty: Type,
    slot: usize,
    line: usize,
    kind: VarKind,
}

enum Lookup {
    Upvalue(Upvalue),
    Variable(Variable),
}

impl Upvalue {
    fn capture(var: &Variable) -> Self {
        Self {
            parent: var.slot,
            upupvalue: false,

            name: var.name.clone(),
            ty: var.ty.clone(),
            slot: 0,
            line: var.line,
            kind: var.kind,
        }
    }

    fn loft(up: &Upvalue) -> Self {
        Self {
            parent: up.slot,
            upupvalue: true,
            slot: 0,
            ..up.clone()
        }
    }
}

#[derive(Debug, Copy, Clone)]
struct Context {
    block_slot: BlockID,
    namespace: NamespaceID,
    scope: usize,
    frame: usize,
}

impl Context {
    fn from_namespace(namespace: NamespaceID) -> Self {
        Self {
            namespace,
            block_slot: 0,
            scope: 0,
            frame: 0,
        }
    }
}

type Namespace = HashMap<String, Name>;
type ConstantID = usize;
type NamespaceID = usize;
type BlobID = usize;
type BlockID = usize;
#[derive(Debug, Copy, Clone)]
enum Name {
    Global(ConstantID),
    Blob(BlobID),
    Namespace(NamespaceID),
}

#[derive(Debug)]
struct Frame {
    variables: Vec<Variable>,
    upvalues: Vec<Upvalue>,
}

impl Frame {
    fn new(name: &str, span: Span) -> Self {
        let variables = vec![Variable::new(
            name.to_string(),
            VarKind::Const,
            Type::Void,
            0,
            span,
        )];
        Self {
            variables,
            upvalues: Vec::new(),
        }
    }
}

struct Compiler {
    blocks: Vec<Block>,
    namespace_id_to_path: HashMap<NamespaceID, String>,

    namespaces: Vec<Namespace>,
    blobs: Vec<Blob>,

    frames: Vec<Frame>,
    functions: HashMap<String, (usize, RustFunction)>,

    panic: bool,
    errors: Vec<Error>,

    strings: Vec<String>,
    constants: Vec<Value>,

    values: HashMap<Value, usize>,
}

macro_rules! error {
    ($compiler:expr, $ctx:expr, $span:expr, $( $msg:expr ),+ ) => {
        if !$compiler.panic {
            $compiler.panic = true;

            let msg = format!($( $msg ),*).into();
            let err = Error::CompileError {
                file: $compiler.file_from_namespace($ctx.namespace).into(),
                line: $span.line,
                message: Some(msg),
            };
            $compiler.errors.push(err);
        }
    };
}

impl Compiler {
    fn new() -> Self {
        Self {
            blocks: Vec::new(),

            namespace_id_to_path: HashMap::new(),
            namespaces: Vec::new(),
            blobs: Vec::new(),

            frames: Vec::new(),
            functions: HashMap::new(),

            panic: false,
            errors: Vec::new(),

            strings: Vec::new(),
            constants: Vec::new(),

            values: HashMap::new(),
        }
    }

    fn push_frame_and_block(&mut self, ctx: Context, name: &str, span: Span) -> Context {
        let file_as_path = PathBuf::from(self.file_from_namespace(ctx.namespace));

        let block = Block::new(&name, ctx.namespace, &file_as_path);
        self.blocks.push(block);

        self.frames.push(Frame::new(name, span));
        Context {
            block_slot: self.blocks.len() - 1,
            frame: self.frames.len() - 1,
            ..ctx
        }
    }

    fn pop_frame(&mut self, ctx: Context) -> Frame {
        assert_eq!(
            self.frames.len() - 1,
            ctx.frame,
            "Can only pop top stackframe"
        );
        self.frames.pop().unwrap()
    }

    fn file_from_namespace(&self, namespace: usize) -> &str {
        self.namespace_id_to_path.get(&namespace).unwrap()
    }

    fn string(&mut self, string: &str) -> usize {
        self.strings
            .iter()
            .enumerate()
            .find_map(|(i, x)| if x == string { Some(i) } else { None })
            .unwrap_or_else(|| {
                let slot = self.strings.len();
                self.strings.push(string.into());
                slot
            })
    }

    fn constant(&mut self, value: Value) -> Op {
        let slot = match self.values.entry(value.clone()) {
            Entry::Vacant(e) => {
                let slot = self.constants.len();
                e.insert(slot);
                self.constants.push(value);
                slot
            }
            Entry::Occupied(e) => *e.get(),
        };
        Op::Constant(slot)
    }

    fn add_op(&mut self, ctx: Context, span: Span, op: Op) -> usize {
        self.blocks
            .get_mut(ctx.block_slot)
            .expect("Invalid block id")
            .add(op, span.line)
    }

    fn patch(&mut self, ctx: Context, ip: usize, op: Op) {
        self.blocks
            .get_mut(ctx.block_slot)
            .expect("Invalid block id")
            .ops[ip] = op;
    }

    fn next_ip(&mut self, ctx: Context) -> usize {
        self.blocks
            .get_mut(ctx.block_slot)
            .expect("Invalid block id")
            .curr()
    }

    fn assignable(&mut self, ass: &Assignable, ctx: Context) -> Option<usize> {
        use AssignableKind::*;

        match &ass.kind {
            Read(ident) => {
                return self.read_identifier(&ident.name, ass.span, ctx, ctx.namespace);
            }
            Call(a, expr) => {
                self.assignable(a, ctx);
                for expr in expr.iter() {
                    self.expression(expr, ctx);
                }
                self.add_op(ctx, ass.span, Op::Call(expr.len()));
            }
            Access(a, field) => {
                if let Some(namespace) = self.assignable(a, ctx) {
                    return self.read_identifier(&field.name, field.span, ctx, namespace);
                } else {
                    let slot = self.string(&field.name);
                    self.add_op(ctx, field.span, Op::GetField(slot));
                }
            }
            Index(a, b) => {
                self.assignable(a, ctx);
                if let ExpressionKind::Int(n) = b.kind {
                    self.add_op(ctx, ass.span, Op::GetConstIndex(n));
                } else {
                    self.expression(b, ctx);
                    self.add_op(ctx, ass.span, Op::GetIndex);
                }
            }
        }
        None
    }

    fn un_op(&mut self, a: &Expression, ops: &[Op], span: Span, ctx: Context) {
        self.expression(&a, ctx);
        for op in ops {
            self.add_op(ctx, span, *op);
        }
    }

    fn bin_op(&mut self, a: &Expression, b: &Expression, ops: &[Op], span: Span, ctx: Context) {
        self.expression(&a, ctx);
        self.expression(&b, ctx);
        for op in ops {
            self.add_op(ctx, span, *op);
        }
    }

    fn push(&mut self, value: Value, span: Span, ctx: Context) {
        let value = self.constant(value);
        self.add_op(ctx, span, value);
    }

    fn expression(&mut self, expression: &Expression, ctx: Context) {
        use ExpressionKind::*;

        match &expression.kind {
            Get(a) => {
                self.assignable(a, ctx);
            }

            Add(a, b) => self.bin_op(a, b, &[Op::Add], expression.span, ctx),
            Sub(a, b) => self.bin_op(a, b, &[Op::Sub], expression.span, ctx),
            Mul(a, b) => self.bin_op(a, b, &[Op::Mul], expression.span, ctx),
            Div(a, b) => self.bin_op(a, b, &[Op::Div], expression.span, ctx),

            Eq(a, b) => self.bin_op(a, b, &[Op::Equal], expression.span, ctx),
            Neq(a, b) => self.bin_op(a, b, &[Op::Equal, Op::Not], expression.span, ctx),
            Gt(a, b) => self.bin_op(a, b, &[Op::Greater], expression.span, ctx),
            Gteq(a, b) => self.bin_op(a, b, &[Op::Less, Op::Not], expression.span, ctx),
            Lt(a, b) => self.bin_op(a, b, &[Op::Less], expression.span, ctx),
            Lteq(a, b) => self.bin_op(a, b, &[Op::Greater, Op::Not], expression.span, ctx),

            AssertEq(a, b) => self.bin_op(a, b, &[Op::Equal, Op::Assert], expression.span, ctx),

            Neg(a) => self.un_op(a, &[Op::Neg], expression.span, ctx),

            In(a, b) => self.bin_op(a, b, &[Op::Contains], expression.span, ctx),

            And(a, b) => {
                self.expression(a, ctx);

                self.add_op(ctx, expression.span, Op::Copy(1));
                let jump = self.add_op(ctx, expression.span, Op::Illegal);
                self.add_op(ctx, expression.span, Op::Pop);

                self.expression(b, ctx);

                let op = Op::JmpFalse(self.next_ip(ctx));
                self.patch(ctx, jump, op);
            }
            Or(a, b) => {
                self.expression(a, ctx);

                self.add_op(ctx, expression.span, Op::Copy(1));
                let skip = self.add_op(ctx, expression.span, Op::Illegal);
                let jump = self.add_op(ctx, expression.span, Op::Illegal);

                let op = Op::JmpFalse(self.next_ip(ctx));
                self.patch(ctx, skip, op);
                self.add_op(ctx, expression.span, Op::Pop);

                self.expression(b, ctx);
                let op = Op::Jmp(self.next_ip(ctx));
                self.patch(ctx, jump, op);
            }
            Not(a) => self.un_op(a, &[Op::Not], expression.span, ctx),

            #[rustfmt::skip]
            If { condition, pass, fail } => {
                self.expression(condition, ctx);

                let jump_from = self.add_op(ctx, condition.span, Op::Illegal);
                self.statement(pass, ctx);
                let jump_out = self.add_op(ctx, condition.span, Op::Illegal);
                self.statement(fail, ctx);

                self.patch(ctx, jump_from, Op::JmpFalse(jump_out + 1));

                let end = self.next_ip(ctx);
                self.patch(ctx, jump_out, Op::Jmp(end));
            }

            Function {
                name,
                params,
                ret,
                body,
            } => {
                let file = self.file_from_namespace(ctx.namespace);
                let name = format!("fn {} {}:{}", name, file, expression.span.line);

                // === Frame begin ===
                let inner_ctx = self.push_frame_and_block(ctx, &name, expression.span);
                let mut param_types = Vec::new();
                for (ident, ty) in params.iter() {
                    param_types.push(self.resolve_type(&ty, inner_ctx));
                    let param = self.define(&ident.name, VarKind::Const, ident.span);
                    self.activate(param);
                }
                let ret = self.resolve_type(&ret, inner_ctx);
                let ty = Type::Function(param_types, Box::new(ret));
                self.blocks[inner_ctx.block_slot].ty = ty.clone();

                self.statement(&body, inner_ctx);

                if !all_paths_return(&body) {
                    let nil = self.constant(Value::Nil);
                    self.add_op(inner_ctx, body.span, nil);
                    self.add_op(inner_ctx, body.span, Op::Return);
                }

                self.blocks[inner_ctx.block_slot].upvalues = self
                    .pop_frame(inner_ctx)
                    .upvalues
                    .into_iter()
                    .map(|u| (u.parent, u.upupvalue, u.ty))
                    .collect();
                let function = Value::Function(Rc::new(Vec::new()), ty, inner_ctx.block_slot);
                // === Frame end ===

                let function = self.constant(function);
                self.add_op(ctx, expression.span, function);
            }

            Instance { blob, fields } => {
                self.assignable(blob, ctx);
                for (name, field) in fields.iter() {
                    let name = self.constant(Value::Field(name.clone()));
                    self.add_op(ctx, field.span, name);
                    self.expression(field, ctx);
                }
                self.add_op(ctx, expression.span, Op::Call(fields.len() * 2));
            }

            Tuple(x) | List(x) | Set(x) | Dict(x) => {
                for expr in x.iter() {
                    self.expression(expr, ctx);
                }
                self.add_op(
                    ctx,
                    expression.span,
                    match &expression.kind {
                        Tuple(_) => Op::Tuple(x.len()),
                        List(_) => Op::List(x.len()),
                        Set(_) => Op::Set(x.len()),
                        Dict(_) => Op::Dict(x.len()),
                        _ => unreachable!(),
                    },
                );
            }

            Float(a) => self.push(Value::Float(*a), expression.span, ctx),
            Bool(a) => self.push(Value::Bool(*a), expression.span, ctx),
            Int(a) => self.push(Value::Int(*a), expression.span, ctx),
            Str(a) => self.push(Value::String(Rc::new(a.clone())), expression.span, ctx),
            Nil => self.push(Value::Nil, expression.span, ctx),
        }
    }

    fn resolve_and_capture(&mut self, name: &str, frame: usize, span: Span) -> Result<Lookup, ()> {
        // Frame 0 has globals which cannot be captured.
        if frame == 0 {
            return Err(());
        }

        for var in self.frames[frame].variables.iter().rev() {
            if &var.name == name && var.active {
                return Ok(Lookup::Variable(var.clone()));
            }
        }

        for up in self.frames[frame].upvalues.iter().rev() {
            if &up.name == name {
                return Ok(Lookup::Upvalue(up.clone()));
            }
        }

        let up = match self.resolve_and_capture(name, frame - 1, span) {
            Ok(Lookup::Upvalue(up)) => Upvalue::loft(&up),
            Ok(Lookup::Variable(var)) => Upvalue::capture(&var),
            _ => {
                return Err(());
            }
        };
        let up = self.upvalue(up, frame);
        Ok(Lookup::Upvalue(up))
    }

    fn read_identifier(
        &mut self,
        name: &str,
        span: Span,
        ctx: Context,
        namespace: usize,
    ) -> Option<usize> {
        match self.resolve_and_capture(name, ctx.frame, span) {
            Ok(Lookup::Upvalue(up)) => {
                let op = Op::ReadUpvalue(up.slot);
                self.add_op(ctx, span, op);
            }

            Ok(Lookup::Variable(var)) => {
                let op = Op::ReadLocal(var.slot);
                self.add_op(ctx, span, op);
            }

            Err(()) => match self.namespaces[namespace].get(name) {
                Some(Name::Global(slot)) => {
                    let op = Op::ReadGlobal(*slot);
                    self.add_op(ctx, span, op);
                }
                Some(Name::Blob(blob)) => {
                    let op = Op::Constant(*blob);
                    self.add_op(ctx, span, op);
                }
                Some(Name::Namespace(new_namespace)) => return Some(*new_namespace),
                None => {
                    if let Some((slot, _)) = self.functions.get(name) {
                        let slot = *slot;
                        let op = self.constant(Value::ExternFunction(slot));
                        self.add_op(ctx, span, op);
                    } else {
                        error!(
                            self,
                            ctx,
                            span,
                            "Cannot read '{}' in '{}.sy'",
                            name,
                            self.file_from_namespace(namespace)
                        );
                    }
                }
            },
        }
        None
    }

    fn set_identifier(&mut self, name: &str, span: Span, ctx: Context, namespace: usize) {
        match self.resolve_and_capture(name, ctx.frame, span) {
            Ok(Lookup::Upvalue(up)) => {
                let op = Op::AssignUpvalue(up.slot);
                self.add_op(ctx, span, op);
                return;
            }

            Ok(Lookup::Variable(var)) => {
                let op = Op::AssignLocal(var.slot);
                self.add_op(ctx, span, op);
                return;
            }

            Err(()) => match self.namespaces[namespace].get(name) {
                Some(Name::Global(slot)) => {
                    let var = &self.frames[0].variables[*slot];
                    if var.kind.immutable() && ctx.frame != 0 {
                        error!(self, ctx, span, "Cannot mutate constant '{}'", name);
                    } else {
                        let op = Op::AssignGlobal(var.slot);
                        self.add_op(ctx, span, op);
                    }
                }

                _ => {
                    error!(
                        self,
                        ctx,
                        span,
                        "Cannot assign '{}' in '{}.sy'",
                        name,
                        self.file_from_namespace(namespace)
                    );
                }
            },
        }
    }

    fn resolve_type_namespace(
        &mut self,
        assignable: &Assignable,
        namespace: usize,
        ctx: Context,
    ) -> Option<usize> {
        use AssignableKind::*;
        match &assignable.kind {
            Access(inner, ident) => self
                .resolve_type_namespace(&inner, namespace, ctx)
                .and_then(|namespace| self.namespaces[namespace].get(&ident.name))
                .and_then(|o| match o {
                    Name::Namespace(namespace) => Some(*namespace),
                    _ => None,
                })
                .or_else(|| {
                    error!(
                        self,
                        ctx,
                        assignable.span,
                        "While parsing type '{}' is not a namespace",
                        ident.name
                    );
                    None
                }),
            Read(_) => {
                // Should be unreachable
                error!(self, ctx, assignable.span, "This is not a namespace");
                None
            }
            Call(_, _) => {
                error!(self, ctx, assignable.span, "Cannot have calls in types");
                None
            }
            Index(_, _) => {
                error!(self, ctx, assignable.span, "Cannot have indexing in types");
                None
            }
        }
    }

    fn resolve_type_ident(
        &mut self,
        assignable: &Assignable,
        namespace: usize,
        ctx: Context,
    ) -> Type {
        use AssignableKind::*;
        match &assignable.kind {
            Read(ident) => self.namespaces[namespace]
                .get(&ident.name)
                .and_then(|name| match name {
                    Name::Blob(blob) => Some(Type::Instance(*blob)),
                    _ => None,
                })
                .unwrap_or_else(|| {
                    error!(
                        self,
                        ctx, assignable.span, "While parsing type '{}' is not a blob", ident.name
                    );
                    Type::Void
                }),
            Access(inner, ident) => self
                .resolve_type_namespace(&inner, namespace, ctx)
                .and_then(|namespace| self.namespaces[namespace].get(&ident.name))
                .and_then(|name| match name {
                    Name::Blob(blob) => Some(Type::Instance(*blob)),
                    _ => None,
                })
                .unwrap_or_else(|| {
                    error!(
                        self,
                        ctx, assignable.span, "While parsing type '{}' is not a blob", ident.name
                    );
                    Type::Void
                }),
            Call(_, _) => {
                error!(self, ctx, assignable.span, "Cannot have calls in types");
                Type::Void
            }
            Index(_, _) => {
                error!(self, ctx, assignable.span, "Cannot have indexing in types");
                Type::Void
            }
        }
    }

    fn resolve_type(&mut self, ty: &ParserType, ctx: Context) -> Type {
        use TypeKind::*;
        match &ty.kind {
            Implied => Type::Unknown,
            Resolved(ty) => ty.clone(),
            UserDefined(assignable) => self.resolve_type_ident(&assignable, ctx.namespace, ctx),
            Union(a, b) => match (self.resolve_type(a, ctx), self.resolve_type(b, ctx)) {
                (Type::Union(_), _) => panic!("Didn't expect union on RHS - check parser"),
                (a, Type::Union(mut us)) => {
                    us.insert(a);
                    Type::Union(us)
                }
                (a, b) => Type::Union(vec![a, b].into_iter().collect()),
            },
            Fn(params, ret) => {
                let params = params.iter().map(|t| self.resolve_type(t, ctx)).collect();
                let ret = Box::new(self.resolve_type(ret, ctx));
                Type::Function(params, ret)
            }
            Tuple(fields) => {
                Type::Tuple(fields.iter().map(|t| self.resolve_type(t, ctx)).collect())
            }
            List(kind) => Type::List(Box::new(self.resolve_type(kind, ctx))),
            Set(kind) => Type::Set(Box::new(self.resolve_type(kind, ctx))),
            Dict(key, value) => Type::Dict(
                Box::new(self.resolve_type(key, ctx)),
                Box::new(self.resolve_type(value, ctx)),
            ),
        }
    }

    fn define(&mut self, name: &str, kind: VarKind, span: Span) -> VarSlot {
        let frame = &mut self.frames.last_mut().unwrap().variables;
        let slot = frame.len();
        let var = Variable::new(name.to_string(), kind, Type::Unknown, slot, span);
        frame.push(var);
        slot
    }

    fn upvalue(&mut self, mut up: Upvalue, frame: usize) -> Upvalue {
        let ups = &mut self.frames[frame].upvalues;
        let slot = ups.len();
        up.slot = slot;
        ups.push(up.clone());
        up
    }

    fn activate(&mut self, slot: VarSlot) {
        self.frames.last_mut().unwrap().variables[slot].active = true;
    }

    fn statement(&mut self, statement: &Statement, ctx: Context) {
        use StatementKind::*;
        self.panic = false;

        match &statement.kind {
            Use { .. } | EmptyStatement => {}

            Blob { name, fields } => {
                if let Some(Name::Blob(slot)) = self.namespaces[ctx.namespace].get(name) {
                    let slot = *slot;
                    self.blobs[slot].fields = fields
                        .clone()
                        .into_iter()
                        .map(|(k, v)| (k, self.resolve_type(&v, ctx)))
                        .collect();
                } else {
                    error!(
                        self,
                        ctx, statement.span, "No blob with the name '{}' in this namespace", name
                    );
                }
            }

            Print { value } => {
                self.expression(value, ctx);
                self.add_op(ctx, statement.span, Op::Print);
            }

            #[rustfmt::skip]
            Definition { ident, kind, ty, value } => {
                // TODO(ed): Don't use type here - type check the tree first.
                self.expression(value, ctx);

                if ctx.frame == 0 {
                    // Global
                    self.set_identifier(&ident.name, statement.span, ctx, ctx.namespace);
                } else {
                    // Local variable
                    let slot = self.define(&ident.name, *kind, statement.span);
                    let ty = self.resolve_type(ty, ctx);
                    let op = if let Op::Constant(ty) = self.constant(Value::Ty(ty)) {
                        if kind.force() {
                            Op::Force(ty)
                        } else {
                            Op::Define(ty)
                        }
                    } else {
                        error!(self, ctx, statement.span, "Failed to add type declaration");
                        Op::Illegal
                    };
                    self.add_op(ctx, statement.span, op);
                    self.activate(slot);
                }
            }

            #[rustfmt::skip]
            Assignment { target, value, kind } => {
                use AssignableKind::*;
                use ParserOp::*;

                let mutator = |kind| matches!(kind, Add | Sub | Mul | Div);

                let write_mutator_op = |comp: &mut Self, ctx, kind| {
                    let op = match kind {
                        Add => Op::Add,
                        Sub => Op::Sub,
                        Mul => Op::Mul,
                        Div => Op::Div,
                        Nop => {
                            return;
                        }
                    };
                    comp.add_op(ctx, statement.span, op);
                };

                match &target.kind {
                    Read(ident) => {
                        if mutator(*kind) {
                            self.read_identifier(&ident.name, statement.span, ctx, ctx.namespace);
                        }
                        self.expression(value, ctx);

                        write_mutator_op(self, ctx, *kind);

                        self.set_identifier(&ident.name, statement.span, ctx, ctx.namespace);
                    }
                    Call(_, _) => {
                        error!(
                            self,
                            ctx, statement.span, "Cannot assign to result from function call"
                        );
                    }
                    Access(a, field) => {
                        self.assignable(a, ctx);
                        let slot = self.string(&field.name);

                        if mutator(*kind) {
                            self.add_op(ctx, statement.span, Op::Copy(1));
                            self.add_op(ctx, field.span, Op::GetField(slot));
                        }
                        self.expression(value, ctx);
                        write_mutator_op(self, ctx, *kind);

                        self.add_op(ctx, field.span, Op::AssignField(slot));
                    }
                    Index(a, b) => {
                        self.assignable(a, ctx);
                        self.expression(b, ctx);

                        if mutator(*kind) {
                            self.add_op(ctx, statement.span, Op::Copy(2));
                            self.add_op(ctx, statement.span, Op::GetIndex);
                        }
                        self.expression(value, ctx);
                        write_mutator_op(self, ctx, *kind);

                        self.add_op(ctx, statement.span, Op::AssignIndex);
                    }
                }
            }

            StatementExpression { value } => {
                self.expression(value, ctx);
                self.add_op(ctx, statement.span, Op::Pop);
            }

            Block { statements } => {
                let stack_size = self.frames[ctx.frame].variables.len();

                for statement in statements {
                    self.statement(statement, ctx);
                }

                while stack_size < self.frames[ctx.frame].variables.len() {
                    let var = self.frames[ctx.frame].variables.pop().unwrap();
                    if var.captured {
                        self.add_op(ctx, statement.span, Op::PopUpvalue);
                    } else {
                        self.add_op(ctx, statement.span, Op::Pop);
                    }
                }
            }

            Loop { condition, body } => {
                let start = self.next_ip(ctx);
                self.expression(condition, ctx);
                let jump_from = self.add_op(ctx, condition.span, Op::Illegal);
                self.statement(body, ctx);
                self.add_op(ctx, body.span, Op::Jmp(start));
                let out = self.next_ip(ctx);
                self.patch(ctx, jump_from, Op::JmpFalse(out));
            }

            Unreachable {} => {
                self.add_op(ctx, statement.span, Op::Unreachable);
            }

            Ret { value } => {
                self.expression(value, ctx);
                self.add_op(ctx, statement.span, Op::Return);
            }
        }
    }

    fn module_functions(&mut self, module: &Module, ctx: Context) {
        for statement in module.statements.iter() {
            match statement.kind {
                StatementKind::Definition {
                    value:
                        Expression {
                            kind: ExpressionKind::Function { .. },
                            ..
                        },
                    ..
                } => {
                    self.statement(statement, ctx);
                }
                _ => (),
            }
        }
    }

    fn module_not_functions(&mut self, module: &Module, ctx: Context) {
        for statement in module.statements.iter() {
            match statement.kind {
                StatementKind::Definition {
                    value:
                        Expression {
                            kind: ExpressionKind::Function { .. },
                            ..
                        },
                    ..
                } => (),
                _ => {
                    self.statement(statement, ctx);
                }
            }
        }
    }

    fn compile(
        mut self,
        tree: AST,
        functions: &[(String, RustFunction)],
    ) -> Result<Prog, Vec<Error>> {
        assert!(!tree.modules.is_empty(), "Cannot compile an empty program");
        let num_functions = functions.len();
        self.functions = functions
            .to_vec()
            .into_iter()
            .enumerate()
            .map(|(i, (s, f))| (s, (i, f)))
            .collect();
        assert_eq!(
            num_functions,
            self.functions.len(),
            "There are {} names and {} extern functions - some extern functions share name",
            self.functions.len(),
            num_functions
        );

        let name = "/preamble/";
        let mut block = Block::new(name, 0, &tree.modules[0].0);
        block.ty = Type::Function(Vec::new(), Box::new(Type::Void));
        self.blocks.push(block);
        self.frames.push(Frame::new(name, Span { line: 0 }));
        let mut ctx = Context {
            block_slot: self.blocks.len() - 1,
            frame: self.frames.len() - 1,
            ..Context::from_namespace(0)
        };

        let path_to_namespace_id = self.extract_globals(&tree);

        for (full_path, module) in tree.modules.iter() {
            let path = full_path.file_stem().unwrap().to_str().unwrap();
            ctx.namespace = path_to_namespace_id[path];
            self.module_functions(module, ctx);
        }

        for (full_path, module) in tree.modules.iter() {
            let path = full_path.file_stem().unwrap().to_str().unwrap();
            ctx.namespace = path_to_namespace_id[path];
            self.module_not_functions(module, ctx);
        }
        let module = &tree.modules[0].1;

        self.read_identifier("start", Span { line: 0 }, ctx, 0);
        self.add_op(ctx, Span { line: 0 }, Op::Call(0));

        let nil = self.constant(Value::Nil);
        self.add_op(ctx, module.span, nil);
        self.add_op(ctx, module.span, Op::Return);

        self.pop_frame(ctx);

        if self.errors.is_empty() {
            Ok(Prog {
                blocks: self
                    .blocks
                    .into_iter()
                    .map(|x| Rc::new(RefCell::new(x)))
                    .collect(),
                functions: functions.iter().map(|(_, f)| *f).collect(),
                blobs: self.blobs,
                constants: self.constants,
                strings: self.strings,
            })
        } else {
            Err(self.errors)
        }
    }

    fn extract_globals(&mut self, tree: &AST) -> HashMap<String, usize> {
        let mut path_to_namespace_id = HashMap::new();
        for (full_path, _) in tree.modules.iter() {
            let slot = path_to_namespace_id.len();
            let path = full_path.file_stem().unwrap().to_str().unwrap().to_owned();
            match path_to_namespace_id.entry(path) {
                Entry::Vacant(vac) => {
                    vac.insert(slot);
                    self.namespaces.push(Namespace::new());
                }

                Entry::Occupied(_) => {
                    error!(
                        self,
                        Context::from_namespace(slot),
                        Span { line: 0 },
                        "Reading module '{}' twice! How?",
                        full_path.display()
                    );
                }
            }
        }

        self.namespace_id_to_path = path_to_namespace_id
            .iter()
            .map(|(a, b)| (b.clone(), a.clone()))
            .collect();

        for (path, module) in tree.modules.iter() {
            let path = path.file_stem().unwrap().to_str().unwrap();
            let slot = path_to_namespace_id[path];
            let ctx = Context::from_namespace(slot);

            for statement in module.statements.iter() {
                use StatementKind::*;
                let mut namespace = self.namespaces.remove(slot);
                match &statement.kind {
                    Blob { name, .. } => match namespace.entry(name.to_owned()) {
                        Entry::Vacant(_) => {
                            let id = self.blobs.len();
                            self.blobs.push(crate::Blob::new(id, slot, name));
                            let blob = self.constant(Value::Blob(id));
                            if let Op::Constant(slot) = blob {
                                namespace.insert(name.to_owned(), Name::Blob(slot));
                            } else {
                                unreachable!();
                            }
                        }

                        Entry::Occupied(_) => {
                            error!(
                                self,
                                ctx,
                                statement.span,
                                "A global variable with the name '{}' already exists",
                                name
                            );
                        }
                    },

                    // Handled below.
                    _ => (),
                }
                self.namespaces.insert(slot, namespace);
            }
        }

        for (path, module) in tree.modules.iter() {
            let path = path.file_stem().unwrap().to_str().unwrap();
            let slot = path_to_namespace_id[path];
            let ctx = Context::from_namespace(slot);

            for statement in module.statements.iter() {
                use StatementKind::*;
                let mut namespace = self.namespaces.remove(slot);
                match &statement.kind {
                    Use {
                        file: Identifier { name, span },
                    } => {
                        let other = path_to_namespace_id[name];
                        match namespace.entry(name.to_owned()) {
                            Entry::Vacant(vac) => {
                                vac.insert(Name::Namespace(other));
                            }
                            Entry::Occupied(_) => {
                                error!(
                                    self,
                                    ctx,
                                    span,
                                    "A global variable with the name '{}' already exists",
                                    name
                                );
                            }
                        }
                    }

                    #[rustfmt::skip]
                    Definition { ident: Identifier { name, .. }, kind, ty, .. } => {
                        let var = self.define(name, *kind, statement.span);
                        self.activate(var);

                        match namespace.entry(name.to_owned()) {
                            Entry::Vacant(_) => {
                                namespace.insert(name.to_owned(), Name::Global(var));
                            }
                            Entry::Occupied(_) => {
                                error!(
                                    self,
                                    ctx,
                                    statement.span,
                                    "A global variable with the name '{}' already exists",
                                    name
                                );
                            }
                        }

                        // Just fill in an empty slot since we have no idea.
                        // Unknown is overwritten by the Op::Force in the type checker.
                        let unknown = self.constant(Value::Unknown);
                        self.add_op(ctx, Span { line: 0 }, unknown);

                        let ty = self.resolve_type(ty, ctx);
                        let op = if let Op::Constant(ty) = self.constant(Value::Ty(ty)) {
                            Op::Force(ty)
                        } else {
                            error!(self, ctx, statement.span, "Failed to resolve the type");
                            Op::Illegal
                        };
                        self.add_op(ctx, Span { line: 0 }, op);
                    }

                    // Already handled in the loop before.
                    Blob { .. } => (),

                    _ => {
                        error!(self, ctx, statement.span, "Invalid outer statement");
                    }
                }
                self.namespaces.insert(slot, namespace);
            }
        }
        path_to_namespace_id
    }
}

pub fn compile(prog: AST, functions: &[(String, RustFunction)]) -> Result<Prog, Vec<Error>> {
    Compiler::new().compile(prog, functions)
}

fn all_paths_return(statement: &Statement) -> bool {
    match &statement.kind {
        StatementKind::Use { .. }
        | StatementKind::Blob { .. }
        | StatementKind::Print { .. }
        | StatementKind::Assignment { .. }
        | StatementKind::Definition { .. }
        | StatementKind::Unreachable
        | StatementKind::EmptyStatement => false,

        StatementKind::StatementExpression { value } => match &value.kind {
            ExpressionKind::If { pass, fail, .. } => all_paths_return(&*pass) && all_paths_return(&*fail),
            _ => false,
        }

        StatementKind::Loop { body, .. } => all_paths_return(body),
        StatementKind::Block { statements } => statements.iter().any(all_paths_return),

        StatementKind::Ret { .. } => true,
    }
}
