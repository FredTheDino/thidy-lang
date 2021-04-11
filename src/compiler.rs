use std::cell::RefCell;
use std::collections::{hash_map::Entry, HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::rc::Rc;

use crate::error::Error;
use crate::sectionizer::Section;
use crate::tokenizer::Token;
use crate::{path_to_module, Blob, Block, Next, Op, Prog, RustFunction, Type, Value};

macro_rules! syntax_error {
    ($thing:expr, $( $msg:expr ),* ) => {
        {
            let msg = format!($( $msg ),*).into();
            let err = Error::SyntaxError {
                file: $thing.current_file().into(),
                line: $thing.line(),
                token: $thing.peek(),
                message: Some(msg),
            };
            $thing.error(err);
        }
    };
}

macro_rules! expect {
    ($thing:expr, $exp_head:pat $( | $exp_rest:pat ),* , $( $msg:expr ),*) => {
        match $thing.peek() {
            $exp_head $( | $exp_rest )* => { $thing.eat(); true },
            _ => { syntax_error!($thing, $( $msg ),*); false } ,
        }
    };
}

macro_rules! rest_of_line_contains {
    ($compiler:expr, $head:pat $( | $tail:pat )* ) => {
        {
            let mut i = 0;
            while match $compiler.peek_at(i) {
                Token::Newline | Token::EOF => false,
                $head $( | $tail )* => false,
                _ => true,
            } {
                i += 1;
            }
            matches!($compiler.peek_at(i), $head $( | $tail )*)
        }
    }
}

macro_rules! push_frame {
    ($compiler:expr, $block:expr, $code:tt) => {
        {
            $compiler.frames_mut().push(Frame::new());

            // Return value stored as a variable
            let var = Variable::new("", true, Type::Unknown);
            $compiler.define(var).unwrap();

            $code

            let frame = $compiler.frames_mut().pop().unwrap();
            // 0-th slot is the function itself.
            for var in frame.stack.iter().skip(1) {
                if !(var.read || var.upvalue) {
                    $compiler.error(Error::SyntaxError {
                        file: $compiler.current_file().into(),
                        line: var.line,
                        token: Token::Identifier(var.name.clone()),
                        message: Some(format!("Unused value '{}'", var.name)),
                    });
                }
                $compiler.panic = false;
            }
            // The 0th slot is the return value, which is passed out
            // from functions, and should not be popped.
            0
        }
    };
}

macro_rules! push_scope {
    ($compiler:expr, $block:expr, $code:tt) => {
        let ss = $compiler.stack().len();
        $compiler.frame_mut().scope += 1;
        add_op($compiler, $block, Op::OpenScope);

        $code;

        $compiler.frame_mut().scope -= 1;
        add_op($compiler, $block, Op::CloseScope(ss));
        $compiler.stack_mut().truncate(ss);
    };
}

#[derive(sylt_macro::Next, PartialEq, PartialOrd, Clone, Copy, Debug)]
pub enum Prec {
    No,
    Assert,
    BoolOr,
    BoolAnd,
    Comp,
    Term,
    Factor,
    Index,
}

#[derive(Clone, Debug)]
struct Variable {
    name: String,
    typ: Type,
    scope: usize,
    slot: usize,
    line: usize,

    outer_slot: usize,
    outer_upvalue: bool,

    active: bool,
    upvalue: bool,
    captured: bool,
    mutable: bool,
    read: bool,
}

impl Variable {
    fn new(name: &str, mutable: bool, typ: Type) -> Self {
        Self {
            name: String::from(name),
            typ,
            scope: 0,
            slot: 0,
            line: 0,

            outer_slot: 0,
            outer_upvalue: false,

            active: false,
            upvalue: false,
            captured: false,
            mutable,
            read: false,
        }
    }

    fn activate(mut self) -> Self {
        self.active = true;
        self
    }
}

#[derive(Debug)]
struct Frame {
    stack: Vec<Variable>,
    upvalues: Vec<Variable>,
    scope: usize,
}

impl Frame {
    fn new() -> Self {
        Self {
            stack: Vec::new(),
            upvalues: Vec::new(),
            scope: 0,
        }
    }

    fn find_outer(&self, name: &str) -> Option<Variable> {
        // Only really makes sense in the outermost frame
        // where declaration order doesn't matter
        for var in self.stack.iter().rev() {
            if var.name == name {
                return Some(var.clone());
            }
        }
        None
    }

    fn find_local(&self, name: &str) -> Option<Variable> {
        for var in self.stack.iter().rev() {
            if var.name == name && var.active {
                return Some(var.clone());
            }
        }
        None
    }

    fn find_upvalue(&self, name: &str) -> Option<Variable> {
        for var in self.upvalues.iter().rev() {
            if var.name == name && var.active {
                return Some(var.clone());
            }
        }
        None
    }

    fn add_upvalue(&mut self, variable: Variable) -> Variable {
        let new_variable = Variable {
            outer_upvalue: variable.upvalue,
            outer_slot: variable.slot,
            slot: self.upvalues.len(),
            active: true,
            upvalue: true,
            ..variable
        };
        self.upvalues.push(new_variable.clone());
        new_variable
    }
}

type Namespace = HashMap<String, Name>;

#[derive(Debug)]
struct CompilerContext {
    frames: Vec<Frame>,
    namespace: Namespace,
}

impl CompilerContext {
    fn new() -> Self {
        Self {
            frames: vec![Frame::new()],
            namespace: Namespace::new(),
        }
    }
}

#[derive(Debug, Clone)]
enum Name {
    Slot(usize, usize),
    Unknown(usize, usize),
    Namespace(PathBuf),
}

pub(crate) struct Compiler {
    current_token: usize,
    current_section: usize,
    sections: Vec<Section>,

    contextes: HashMap<PathBuf, CompilerContext>,

    panic: bool,
    errors: Vec<Error>,

    blocks: Vec<Rc<RefCell<Block>>>,
    blob_id: usize,

    functions: HashMap<String, (usize, RustFunction)>,

    strings: Vec<String>,

    constants: Vec<Value>,
    values: HashMap<Value, usize>,
}

/// Helper function for adding operations to the given block.
fn add_op(compiler: &Compiler, block: &mut Block, op: Op) -> usize {
    block.add(op, compiler.line())
}

impl Compiler {
    pub(crate) fn new(sections: Vec<Section>) -> Self {
        let contextes = sections
            .iter()
            .map(|section| (section.path.to_path_buf(), CompilerContext::new()))
            .collect();

        Self {
            current_token: 0,
            current_section: 0,
            sections,

            contextes,

            panic: false,
            errors: vec![],

            blocks: Vec::new(),
            blob_id: 0,

            functions: HashMap::new(),

            strings: Vec::new(),

            constants: vec![],
            values: HashMap::new(),
        }
    }

    fn new_blob_id(&mut self) -> usize {
        let id = self.blob_id;
        self.blob_id += 1;
        id
    }

    fn add_namespace(&mut self, name: String, path: PathBuf) {
        match self.names_mut().entry(name.clone()) {
            Entry::Vacant(v) => {
                v.insert(Name::Namespace(path));
            }
            Entry::Occupied(_) => {
                syntax_error!(self, "Namespace {} already present", name);
            }
        }
    }

    fn add_constant(&mut self, value: Value) -> usize {
        if matches!(
            value,
            Value::Float(_)
                | Value::Int(_)
                | Value::Bool(_)
                | Value::String(_)
                | Value::Tuple(_)
                | Value::Nil
        ) {
            let entry = self.values.entry(value.clone());
            if let Entry::Occupied(entry) = entry {
                *entry.get()
            } else {
                let slot = self.constants.len();
                self.constants.push(value);
                entry.or_insert(slot);
                slot
            }
        } else {
            self.constants.push(value);
            self.constants.len() - 1
        }
    }

    fn intern_string(&mut self, string: String) -> usize {
        self.strings.push(string);
        self.strings.len() - 1
    }

    fn section(&self) -> &Section {
        &self.sections[self.current_section]
    }

    fn current_file(&self) -> &Path {
        &self.section().path
    }

    fn current_context(&self) -> &CompilerContext {
        self.contextes.get(self.current_file()).unwrap()
    }

    fn current_context_mut(&mut self) -> &mut CompilerContext {
        let file = self.current_file().to_path_buf();
        self.contextes.get_mut(&file).unwrap()
    }

    fn frame(&self) -> &Frame {
        self.current_context().frames.last().unwrap()
    }

    fn frame_mut(&mut self) -> &mut Frame {
        self.current_context_mut().frames.last_mut().unwrap()
    }

    fn frames(&self) -> &[Frame] {
        &self.current_context().frames
    }

    fn frames_mut(&mut self) -> &mut Vec<Frame> {
        &mut self.current_context_mut().frames
    }

    fn names(&self) -> &Namespace {
        &self.current_context().namespace
    }

    fn names_mut(&mut self) -> &mut Namespace {
        &mut self.current_context_mut().namespace
    }

    /// Marks a variable as read. Also marks upvalues.
    fn mark_read(&mut self, frame_id: usize, var: &Variable) {
        // Early out
        if var.read {
            return;
        }

        match self.frames()[frame_id].upvalues.get(var.slot) {
            Some(up) if up.name == var.name => {
                let mut inner_var = self.frames()[frame_id].upvalues[var.slot].clone();
                inner_var.slot = inner_var.outer_slot;
                self.mark_read(frame_id - 1, &inner_var);
                self.frames_mut()[frame_id].upvalues[var.slot].read = true;
            }
            _ => {
                self.frames_mut()[frame_id].stack[var.slot].read = true;
            }
        }
    }

    fn stack(&self) -> &[Variable] {
        &self.frame().stack.as_ref()
    }

    fn stack_mut(&mut self) -> &mut Vec<Variable> {
        &mut self.frame_mut().stack
    }

    /// Used to recover from a panic so the rest of the code can be parsed.
    fn clear_panic(&mut self) {
        if self.panic {
            self.panic = false;

            while !matches!(self.peek(), Token::EOF | Token::Newline)  {
                self.eat();
            }
            self.eat();
        }
    }

    fn error(&mut self, error: Error) {
        if self.panic {
            return;
        }
        self.panic = true;
        self.errors.push(error);
    }

    fn init_section(&mut self, section: usize) {
        self.current_token = 0;
        self.current_section = section;
    }

    fn peek(&self) -> Token {
        self.peek_at(0)
    }

    fn peek_at(&self, at: usize) -> Token {
        if self.section().tokens.len() <= self.current_token + at {
            crate::tokenizer::Token::EOF
        } else {
            self.section().tokens[self.current_token + at].0.clone()
        }
    }

    // TODO(ed): Const generics
    fn peek_four(&self) -> (Token, Token, Token, Token) {
        (
            self.peek_at(0),
            self.peek_at(1),
            self.peek_at(2),
            self.peek_at(3),
        )
    }

    fn eat(&mut self) -> Token {
        let t = self.peek();
        self.current_token += 1;
        if let Token::GitConflictBegin = t {
            self.current_token -= 1;
            let start = self.line();
            self.current_token += 1;
            while !matches!(self.eat(), Token::GitConflictEnd) {}
            self.panic = false;
            self.error(Error::GitConflictError {
                file: self.current_file().into(),
                start: start,
                end: self.line(),
            });
            self.panic = true;
        }
        t
    }

    /// The line of the current token.
    fn line(&self) -> usize {
        if self.section().tokens.is_empty() {
            0
        } else {
            self.section().tokens
                [std::cmp::min(self.current_token, self.section().tokens.len() - 1)]
            .1
        }
    }

    fn precedence(&self, token: Token) -> Prec {
        match token {
            Token::LeftBracket => Prec::Index,

            Token::Star | Token::Slash => Prec::Factor,

            Token::Minus | Token::Plus => Prec::Term,

            Token::EqualEqual
            | Token::Greater
            | Token::GreaterEqual
            | Token::Less
            | Token::LessEqual
            | Token::NotEqual => Prec::Comp,

            Token::And => Prec::BoolAnd,
            Token::Or => Prec::BoolOr,

            Token::AssertEqual => Prec::Assert,

            _ => Prec::No,
        }
    }

    fn prefix(&mut self, token: Token, block: &mut Block) -> bool {
        match token {
            Token::Identifier(_) => self.variable_expression(block),
            Token::LeftParen => self.grouping_or_tuple(block),
            Token::Minus => self.unary(block),
            Token::LeftBracket => self.list(block),
            Token::LeftBrace => self.set_or_dict(block),

            Token::Float(_) | Token::Int(_) | Token::Bool(_) | Token::String(_) | Token::Nil => {
                self.value(block)
            }

            Token::Bang => self.unary(block),

            _ => {
                return false;
            }
        }
        true
    }

    fn infix(&mut self, token: Token, block: &mut Block) -> bool {
        match token {
            Token::And
            | Token::Or
            | Token::Minus
            | Token::Plus
            | Token::Slash
            | Token::Star
            | Token::AssertEqual
            | Token::EqualEqual
            | Token::Greater
            | Token::GreaterEqual
            | Token::Less
            | Token::LessEqual
            | Token::NotEqual => self.binary(block),

            Token::In => self.contains(block),

            _ => {
                return false;
            }
        }
        true
    }

    fn value(&mut self, block: &mut Block) {
        let value = match self.eat() {
            Token::Float(f) => Value::Float(f),
            Token::Int(i) => Value::Int(i),
            Token::Bool(b) => Value::Bool(b),
            Token::Nil => Value::Nil,
            Token::String(s) => Value::String(Rc::from(s)),
            _ => {
                syntax_error!(self, "Cannot parse value");
                Value::Bool(false)
            }
        };
        let constant = self.add_constant(value);
        add_op(self, block, Op::Constant(constant));
    }

    fn list(&mut self, block: &mut Block) {
        expect!(self, Token::LeftBracket, "Expected '[' at start of list");
        let mut num_args = 0;
        loop {
            match self.peek() {
                Token::RightBracket | Token::EOF => {
                    break;
                }
                Token::Newline => {
                    self.eat();
                }
                Token::Comma => {
                    syntax_error!(self, "Lists must begin with an element or ']'");
                    return;
                }
                _ => {
                    self.expression(block);
                    num_args += 1;
                    match self.peek() {
                        Token::Comma => {
                            self.eat();
                        }
                        Token::RightBracket => {}
                        _ => {
                            syntax_error!(self, "Expected ',' or ']' after list element");
                            return;
                        }
                    }
                }
            }
        }
        expect!(self, Token::RightBracket, "Expected ']' after list");
        add_op(self, block, Op::List(num_args));
    }

    fn set_or_dict(&mut self, block: &mut Block) {
        expect!(
            self,
            Token::LeftBrace,
            "Expected '{{' for set or dict"
        );

        let mut is_dict: Option<bool> = None;
        let mut num_args = 0;
        loop {
            match self.peek() {
                Token::RightBrace => {
                    if is_dict.is_none() {
                        is_dict = Some(false);
                    }
                    break;
                }

                Token::Colon => {
                    if is_dict.is_none() {
                        is_dict = Some(true);
                    } else {
                        syntax_error!(self, "Unexpected ':' in set");
                    }
                    self.eat();
                    break;
                }

                Token::EOF => {
                    break;
                }
                Token::Newline => {
                    self.eat();
                }
                _ => {
                    self.expression(block);
                    num_args += 1;
                    // TODO(ed): Someone who's more awake might
                    // be able to fix this.
                    match is_dict {
                        Some(false) => match self.peek() {
                            Token::Comma => {
                                self.eat();
                            }
                            Token::RightBrace => {}
                            _ => {
                                syntax_error!(self, "Expected ',' or '}}' after set element");
                            }
                        },
                        Some(true) => {
                            expect!(self, Token::Colon, "Expected ':' after dict element");
                            self.expression(block);
                            match self.peek() {
                                Token::Comma => {
                                    self.eat();
                                }
                                Token::RightBrace => {}
                                _ => {
                                    syntax_error!(self, "Expected ',' or '}}' after set element");
                                }
                            }
                        }
                        None => match self.peek() {
                            Token::Comma => {
                                is_dict = Some(false);
                                self.eat();
                            }
                            Token::RightBrace => {
                                is_dict = Some(false);
                            }
                            Token::Colon => {
                                is_dict = Some(true);
                                expect!(self, Token::Colon, "Expected ':' after dict element");
                                self.expression(block);
                                match self.peek() {
                                    Token::Comma => {
                                        self.eat();
                                    }
                                    Token::RightBrace => {}
                                    _ => {
                                        syntax_error!(self, "Expected ',' or '}}' after set element");
                                    }
                                }
                            }
                            _ => {
                                syntax_error!(self, "Expected ',' ':' or '}}' after element");
                                return;
                            }
                        },
                    }
                }
            }
        }

        expect!(
            self,
            Token::RightBrace,
            "Expected '}}' after set or dict"
        );
        match is_dict {
            Some(true) => {
                add_op(self, block, Op::Dict(num_args * 2));
            }
            Some(false) => {
                add_op(self, block, Op::Set(num_args));
            }
            None => syntax_error!(self, "Don't know if set or dict"),
        }
    }

    fn grouping_or_tuple(&mut self, block: &mut Block) {
        expect!(
            self,
            Token::LeftParen,
            "Expected '(' for grouping or tuple."
        );

        let mut num_args = 0;
        let trailing_comma = loop {
            match self.peek() {
                Token::RightParen | Token::EOF => {
                    break false;
                }
                Token::Newline => {
                    self.eat();
                }
                _ => {
                    self.expression(block);
                    num_args += 1;
                    match self.peek() {
                        Token::Comma => {
                            self.eat();
                            if matches!(self.peek(), Token::RightParen) {
                                break true;
                            }
                        }
                        Token::RightParen => {}
                        _ => {
                            syntax_error!(self, "Expected ',' or ')' after tuple element");
                            return;
                        }
                    }
                }
            }
        };
        if trailing_comma || num_args != 1 {
            add_op(self, block, Op::Tuple(num_args));
        }
        expect!(self, Token::RightParen, "Expected ')' after tuple");
    }

    fn unary(&mut self, block: &mut Block) {
        let op = match self.eat() {
            Token::Minus => Op::Neg,
            Token::Bang => Op::Not,
            _ => {
                syntax_error!(self, "Invalid unary operator");
                Op::Neg
            }
        };
        self.parse_precedence(block, Prec::Factor);
        add_op(self, block, op);
    }

    fn contains(&mut self, block: &mut Block) {
        expect!(self, Token::In, "Expected 'in' at start of contains");
        self.parse_precedence(block, Prec::Index);
        add_op(self, block, Op::Contains);
    }

    fn binary(&mut self, block: &mut Block) {
        let op = self.eat();

        self.parse_precedence(block, self.precedence(op.clone()).next());

        let op: &[Op] = match op {
            Token::And => &[Op::And],
            Token::Or => &[Op::Or],
            Token::Plus => &[Op::Add],
            Token::Minus => &[Op::Sub],
            Token::Star => &[Op::Mul],
            Token::Slash => &[Op::Div],
            Token::AssertEqual => &[Op::Equal, Op::Assert],
            Token::EqualEqual => &[Op::Equal],
            Token::Less => &[Op::Less],
            Token::Greater => &[Op::Greater],
            Token::NotEqual => &[Op::Equal, Op::Not],
            Token::LessEqual => &[Op::Greater, Op::Not],
            Token::GreaterEqual => &[Op::Less, Op::Not],
            _ => {
                syntax_error!(self, "Illegal operator");
                &[]
            }
        };
        block.add_from(op, self.line());
    }

    /// Entry point for all expression parsing.
    fn expression(&mut self, block: &mut Block) {
        match self.peek_four() {
            (Token::Fn, ..) => {
                self.function(block, None);
            }
            _ => self.parse_precedence(block, Prec::No),
        }
    }

    fn parse_precedence(&mut self, block: &mut Block, precedence: Prec) {
        if !self.prefix(self.peek(), block) {
            syntax_error!(self, "Invalid expression");
        }

        while precedence <= self.precedence(self.peek()) {
            if !self.infix(self.peek(), block) {
                break;
            }
        }
    }

    fn find_namespace(&self, name: &str) -> Option<&Namespace> {
        match self.names().get(name) {
            Some(Name::Namespace(path)) => Some(&self.contextes.get(path).unwrap().namespace),
            _ => None,
        }
    }

    fn find_and_capture_variable<'i, I>(name: &str, mut iterator: I) -> Option<Variable>
    where
        I: Iterator<Item = &'i mut Frame>,
    {
        if let Some(frame) = iterator.next() {
            if let Some(res) = frame.find_local(name) {
                frame.stack[res.slot].captured = true;
                return Some(res);
            }
            if let Some(res) = frame.find_upvalue(name) {
                return Some(res);
            }

            if let Some(res) = Self::find_and_capture_variable(name, iterator) {
                return Some(frame.add_upvalue(res));
            }
        }
        None
    }

    fn find_extern_function(&self, name: &str) -> Option<usize> {
        self.functions.get(name).map(|(i, _)| *i)
    }

    fn find_variable(&mut self, name: &str) -> Option<Variable> {
        if let Some(res) = self.frame().find_local(name) {
            return Some(res);
        }

        if let Some(res) = self.frame().find_upvalue(name) {
            return Some(res);
        }

        Self::find_and_capture_variable(name, self.frames_mut().iter_mut().rev())
    }

    fn find_constant(&mut self, name: &str) -> usize {
        match self.names_mut().entry(name.to_string()) {
            Entry::Occupied(entry) => match entry.get() {
                Name::Slot(i, _) => {
                    return *i;
                }
                Name::Unknown(i, _) => {
                    return *i;
                }
                _ => {
                    syntax_error!(
                        self,
                        "Tried to find constant '{}' but it was a namespace", name
                    );
                    return 0;
                }
            },
            Entry::Vacant(_) => {}
        };

        let slot = self.add_constant(Value::Unknown);
        let line = self.line();
        self.names_mut()
            .insert(name.to_string(), Name::Unknown(slot, line));
        slot
    }

    fn named_constant(&mut self, name: String, value: Value) -> usize {
        let line = self.line();
        match self.names_mut().entry(name.clone()) {
            Entry::Occupied(mut entry) => {
                let slot = if let Name::Unknown(slot, _) = entry.get() {
                    *slot
                } else {
                    syntax_error!(self, "Constant named \"{}\" already has a value", name);
                    return 0;
                };
                entry.insert(Name::Slot(slot, line));
                self.constants[slot] = value;
                return slot;
            }
            Entry::Vacant(_) => {}
        }
        let slot = self.add_constant(value);
        self.names_mut().insert(name, Name::Slot(slot, line));
        slot
    }

    fn forward_constant(&mut self, name: String) -> usize {
        let line = self.line();
        let slot = self.add_constant(Value::Unknown);
        match self.names_mut().entry(name.clone()) {
            Entry::Occupied(_) => {
                syntax_error!(self, "Constant named \"{}\" already has a value", name);
                0
            }
            Entry::Vacant(entry) => {
                entry.insert(Name::Unknown(slot, line));
                slot
            }
        }
    }

    fn call_maybe(&mut self, block: &mut Block) -> bool {
        if matches!(self.peek(), Token::Bang | Token::LeftParen) {
            self.call(block);
            true
        } else {
            false
        }
    }

    fn call(&mut self, block: &mut Block) {
        let mut arity = 0;
        match self.peek() {
            Token::LeftParen => {
                self.eat();
                loop {
                    match self.peek() {
                        Token::EOF => {
                            syntax_error!(self, "Unexpected EOF in function call");
                            break;
                        }
                        Token::RightParen => {
                            self.eat();
                            break;
                        }
                        _ => {
                            self.expression(block);
                            arity += 1;
                            if !matches!(self.peek(), Token::RightParen) {
                                expect!(self, Token::Comma, "Expected ',' after argument");
                            }
                        }
                    }
                    if self.panic {
                        break;
                    }
                }
            }

            Token::Bang => {
                self.eat();
                loop {
                    match self.peek() {
                        Token::EOF => {
                            syntax_error!(self, "Unexpected EOF in function call");
                            break;
                        }
                        Token::Newline => {
                            break;
                        }
                        _ => {
                            self.expression(block);
                            arity += 1;
                            if matches!(self.peek(), Token::Comma) {
                                self.eat();
                            }
                        }
                    }
                    if self.panic {
                        break;
                    }
                }
            }

            _ => {
                syntax_error!(self, "Invalid function call. Expected '!' or '('");
            }
        }

        add_op(self, block, Op::Call(arity));
    }

    // TODO(ed): de-complexify
    fn function(&mut self, block: &mut Block, in_name: Option<&str>) {
        expect!(self, Token::Fn, "Expected 'fn' at start of function");

        let name = if let Some(name) = in_name {
            String::from(name)
        } else {
            format!("λ {}@{:03}", self.current_file().display(), self.line())
        };

        let mut args = Vec::new();
        let mut return_type = Type::Void;
        let mut function_block = Block::new(&name, in_name.is_none(), self.current_file());

        let block_id = self.blocks.len();
        let temp_block = Block::new(&name, true, self.current_file());
        self.blocks.push(Rc::new(RefCell::new(temp_block)));

        let _ret = push_frame!(self, function_block, {
            loop {
                match self.peek() {
                    Token::Identifier(name) => {
                        self.eat();
                        expect!(self, Token::Colon, "Expected ':' after parameter name");
                        if let Ok(typ) = self.parse_type() {
                            args.push(typ.clone());
                            let mut var = Variable::new(&name, true, typ);
                            var.read = true;
                            if let Ok(slot) = self.define(var) {
                                self.stack_mut()[slot].active = true;
                            }
                        } else {
                            syntax_error!(self, "Failed to parse parameter type");
                        }
                        if !matches!(self.peek(), Token::Arrow | Token::LeftBrace) {
                            expect!(self, Token::Comma, "Expected ',' after parameter");
                        }
                    }
                    Token::LeftBrace => {
                        break;
                    }
                    Token::Arrow => {
                        self.eat();
                        if let Ok(typ) = self.parse_type() {
                            return_type = typ;
                        } else {
                            syntax_error!(self, "Failed to parse return type");
                        }
                        break;
                    }
                    _ => {
                        syntax_error!(
                            self,
                            "Expected '->' or more paramters in function definition"
                        );
                        break;
                    }
                }
            }

            self.scope(&mut function_block);

            for var in self.frame().upvalues.iter() {
                function_block
                    .upvalues
                    .push((var.outer_slot, var.outer_upvalue, var.typ.clone()));
            }
        });

        let nil = self.add_constant(Value::Nil);
        for op in function_block.ops.iter().rev() {
            match op {
                // Op::Pop | Op::PopUpvalue => {}
                Op::Return => {
                    break;
                }
                _ => {
                    add_op(self, &mut function_block, Op::Constant(nil));
                    add_op(self, &mut function_block, Op::Return);
                    break;
                }
            }
        }

        if function_block.ops.is_empty() {
            add_op(self, &mut function_block, Op::Constant(nil));
            add_op(self, &mut function_block, Op::Return);
        }

        function_block.ty = Type::Function(args, Box::new(return_type));
        let function_block = Rc::new(RefCell::new(function_block));

        // Note(ed): We deliberately add the constant as late as possible.
        // This behaviour is used in `constant_statement`.
        let function = Value::Function(Rc::new(Vec::new()), Rc::clone(&function_block));
        self.blocks[block_id] = function_block;
        let constant = if in_name.is_some() {
            self.named_constant(name, function)
        } else {
            self.add_constant(function)
        };
        add_op(self, block, Op::Constant(constant));
    }

    fn variable_expression(&mut self, block: &mut Block) {
        let name = match self.peek() {
            Token::Identifier(name) => name,
            _ => unreachable!(),
        };

        // TODO(ed): This is a clone I would love to get rid of...
        if let Some(mut namespace) = self.find_namespace(&name).cloned() {
            self.eat();
            loop {
                if self.eat() != Token::Dot {
                    syntax_error!(self, "Expect '.' after namespace");
                    return;
                }
                if let Token::Identifier(field) = self.eat() {
                    match namespace.get(&field) {
                        Some(Name::Slot(slot, _)) | Some(Name::Unknown(slot, _)) => {
                            add_op(self, block, Op::Constant(*slot));
                            self.call_maybe(block);
                            return;
                        }
                        Some(Name::Namespace(inner_name)) => {
                            namespace = self.contextes.get(inner_name).unwrap().namespace.clone();
                        }
                        _ => {
                            syntax_error!(self, "Invalid namespace field");
                        }
                    }
                } else {
                    syntax_error!(self, "Expected fieldname after '.'");
                }
            }
        }

        self.eat();

        // Global functions take precedence
        if let Some(slot) = self.find_extern_function(&name) {
            let string = self.add_constant(Value::ExternFunction(slot));
            add_op(self, block, Op::Constant(string));
            self.call(block);
            return;
        }

        // Variables
        if let Some(var) = self.find_variable(&name) {
            self.mark_read(self.frames().len() - 1, &var);
            if var.upvalue {
                add_op(self, block, Op::ReadUpvalue(var.slot));
            } else {
                add_op(self, block, Op::ReadLocal(var.slot));
            }
            loop {
                match self.peek() {
                    Token::Dot => {
                        self.eat();
                        if let Token::Identifier(field) = self.eat() {
                            let string = self.intern_string(field);
                            add_op(self, block, Op::GetField(string));
                        } else {
                            syntax_error!(self, "Expected fieldname after '.'");
                            return;
                        }
                    }
                    Token::LeftBracket => {
                        // TODO(ed): The code here is very duplicated from blob_field,
                        // which is a wierd name, we can refactor this out and get something
                        // more readable.
                        self.eat();
                        self.expression(block);
                        expect!(self, Token::RightBracket, "Expected ']' after indexing");

                        let nil = self.add_constant(Value::Nil);
                        let op = match self.peek() {
                            Token::Equal => {
                                self.eat();
                                self.expression(block);
                                add_op(self, block, Op::AssignIndex);
                                add_op(self, block, Op::Constant(nil));
                                return;
                            }

                            Token::PlusEqual => Op::Add,
                            Token::MinusEqual => Op::Sub,
                            Token::StarEqual => Op::Mul,
                            Token::SlashEqual => Op::Div,

                            _ => {
                                add_op(self, block, Op::GetIndex);
                                continue;
                            }
                        };

                        add_op(self, block, Op::Copy(2));
                        add_op(self, block, Op::GetIndex);
                        self.eat();
                        self.expression(block);
                        add_op(self, block, op);
                        add_op(self, block, Op::AssignIndex);
                        add_op(self, block, Op::Constant(nil));
                        return;
                    }
                    _ => {
                        if !self.call_maybe(block) {
                            return;
                        }
                    }
                }
            }
        }

        // Blobs - Always returns a blob since it's filled in if it isn't used.
        let con = self.find_constant(&name);
        add_op(self, block, Op::Constant(con));
        self.call_maybe(block);
    }

    fn define(&mut self, mut var: Variable) -> Result<usize, ()> {
        let frame = self.frame();

        if let Some(res) = frame
            .find_local(&var.name)
            .or_else(|| frame.find_upvalue(&var.name))
        {
            if res.scope == frame.scope {
                syntax_error!(self, "Multiple definitions of '{}' in this block", res.name);
                return Err(());
            }
        }

        let slot = self.stack().len();
        var.slot = slot;
        var.scope = frame.scope;
        var.line = self.line();
        self.stack_mut().push(var);
        Ok(slot)
    }

    fn definition_statement(&mut self, name: &str, typ: Type, force: bool, block: &mut Block) {
        if self.frames().len() <= 1 {
            // Global
            let var = self.frame().find_outer(name);
            if var.is_none() {
                syntax_error!(self, "Couldn't find variable '{}' during prepass", name);
                return;
            }
            let var = var.unwrap();
            assert!(var.mutable);

            self.expression(block);
            self.stack_mut()[var.slot].active = true;
        } else {
            // Local
            let var = Variable::new(name, true, typ.clone());
            let slot = self.define(var);
            self.expression(block);
            let constant = self.add_constant(Value::Ty(typ));
            if force {
                add_op(self, block, Op::Force(constant));
            } else {
                add_op(self, block, Op::Define(constant));
            }

            if let Ok(slot) = slot {
                self.stack_mut()[slot].active = true;
            }
        }
    }

    fn constant_statement(&mut self, name: &str, typ: Type, block: &mut Block) {
        // Magical global constants
        if self.frames().len() <= 1 && self.peek() == Token::Fn {
            self.function(block, Some(name));
            // Remove the function, since it's a constant and we already
            // added it.
            block.ops.pop().unwrap();
            return;
        }

        if self.frames().len() <= 1 {
            // Global
            let var = self.frame().find_outer(name);
            if var.is_none() {
                syntax_error!(self, "Couldn't find constant '{}' during prepass", name);
                return;
            }
            let var = var.unwrap();
            assert!(!var.mutable);

            self.expression(block);
            self.stack_mut()[var.slot].active = true;
        } else {
            // Local
            let var = Variable::new(name, false, typ);
            let slot = self.define(var);
            self.expression(block);

            if let Ok(slot) = slot {
                self.stack_mut()[slot].active = true;
            }
        }
    }

    fn assign(&mut self, block: &mut Block) {
        let name = match self.eat() {
            Token::Identifier(name) => name,
            _ => {
                syntax_error!(self, "Expected identifier in assignment");
                return;
            }
        };

        let op = match self.eat() {
            Token::Equal => None,

            Token::PlusEqual => Some(Op::Add),
            Token::MinusEqual => Some(Op::Sub),
            Token::StarEqual => Some(Op::Mul),
            Token::SlashEqual => Some(Op::Div),

            _ => {
                syntax_error!(self, "Expected '=' in assignment");
                return;
            }
        };

        if let Some(var) = self.find_variable(&name) {
            if !var.mutable {
                // TODO(ed): Maybe a better syntax_error than "SyntaxError".
                syntax_error!(self, "Cannot assign to constant '{}'", var.name);
            }
            if let Some(op) = op {
                if var.upvalue {
                    add_op(self, block, Op::ReadUpvalue(var.slot));
                } else {
                    add_op(self, block, Op::ReadLocal(var.slot));
                }
                self.expression(block);
                add_op(self, block, op);
            } else {
                self.expression(block);
            }

            if var.upvalue {
                add_op(self, block, Op::AssignUpvalue(var.slot));
            } else {
                add_op(self, block, Op::AssignLocal(var.slot));
            }
        } else {
            syntax_error!(self, "Using undefined variable {}", name);
        }
    }

    fn scope(&mut self, block: &mut Block) {
        if !expect!(self, Token::LeftBrace, "Expected '{{' at start of block") {
            return;
        }

        push_scope!(self, block, {
            while !matches!(self.peek(), Token::RightBrace | Token::EOF) {
                self.statement(block);
                match self.peek() {
                    Token::Newline => {
                        self.eat();
                    }
                    Token::RightBrace => {
                        break;
                    }
                    _ => {
                        syntax_error!(self, "Expect newline after statement");
                    }
                }
            }
        });

        expect!(self, Token::RightBrace, "Expected '}}' at end of block");
    }

    fn if_statment(&mut self, block: &mut Block) {
        expect!(self, Token::If, "Expected 'if' at start of if-statement");
        self.expression(block);
        add_op(self, block, Op::If);
        push_scope!(self, block, {
            add_op(self, block, Op::Pop);
            self.scope(block);
        });

        if Token::Else != self.peek() {
            return;
        }

        self.eat();

        add_op(self, block, Op::Else);
        push_scope!(self, block, {
            add_op(self, block, Op::Pop);
            match self.peek() {
                Token::If => self.if_statment(block),
                Token::LeftBrace => self.scope(block),
                _ => syntax_error!(self, "Epected 'if' or '{{' after else"),
            }
        });
    }

    fn for_loop(&mut self, block: &mut Block) {
        expect!(self, Token::For, "Expected 'for' at start of for-loop");

        // TODO(ed): Destructure tuples? Break this out into function?
        let name = if let Token::Identifier(name) = self.eat() {
            name
        } else {
            syntax_error!(self, "Expected identifier in for-loop");
            return;
        };

        expect!(self, Token::In, "Expected 'in' when parsing for-loop");

        self.expression(block);
        add_op(self, block, Op::For);

        push_scope!(self, block, {
            let var = Variable::new(&name, false, Type::Unknown).activate();
            self.define(var).unwrap();

            self.scope(block);
        });
    }

    fn parse_type(&mut self) -> Result<Type, ()> {
        if self.peek() == Token::LeftBrace {
            // Hashset
            // TODO(ed): This is kinda hacky, but the error
            // messages get really borked if we don't move back.
            let start = self.current_token;
            self.eat();
            if let Ok(ty) = self.parse_type() {
                if self.peek() == Token::RightBrace {
                    self.eat();
                    return Ok(Type::Set(Box::new(ty)));
                }
                expect!(self, Token::Colon, "Expected ':' for dict type");
                if let Ok(val) = self.parse_type() {
                    expect!(self, Token::RightBrace, "Expected '}}' after dict type");
                    return Ok(Type::Dict(Box::new(ty), Box::new(val)));
                }
            }
            self.current_token = start;
            return Err(());
        }

        let mut tys = HashSet::new();
        tys.insert(self.parse_simple_type()?);
        loop {
            match self.peek() {
                Token::QuestionMark => {
                    self.eat();
                    tys.insert(Type::Void);
                    return Ok(Type::Union(tys));
                }

                Token::Pipe => {
                    self.eat();
                    tys.insert(self.parse_simple_type()?);
                }

                _ => {
                    break;
                }
            }
        }
        if tys.len() == 1 {
            Ok(tys.iter().next().unwrap().clone())
        } else {
            Ok(Type::Union(tys))
        }
    }

    fn parse_simple_type(&mut self) -> Result<Type, ()> {
        match self.peek() {
            Token::Fn => {
                self.eat();
                let mut params = Vec::new();
                let return_type = loop {
                    match self.peek() {
                        Token::Identifier(_) | Token::Fn => {
                            if let Ok(ty) = self.parse_type() {
                                params.push(ty);
                                if self.peek() == Token::Comma {
                                    self.eat();
                                }
                            } else {
                                syntax_error!(
                                    self,
                                    "Function type signature contains non-type {:?}",
                                    self.peek()
                                );
                                return Err(());
                            }
                        }
                        Token::Arrow => {
                            self.eat();
                            let return_type = self.parse_type();
                            if return_type.is_err() {
                                syntax_error!(self, "Failed to parse return type, try 'void'");
                                return Err(());
                            }
                            break return_type.unwrap();
                        }
                        Token::Comma | Token::Equal => {
                            break Type::Void;
                        }
                        token => {
                            syntax_error!(
                                self,
                                "Function type signature contains non-type {:?}", token
                            );
                            return Err(());
                        }
                    }
                };
                let f = Type::Function(params, Box::new(return_type));
                Ok(f)
            }

            Token::LeftParen => {
                self.eat();
                let mut element = Vec::new();
                loop {
                    element.push(self.parse_type()?);
                    if self.peek() == Token::RightParen {
                        self.eat();
                        return Ok(Type::Tuple(element));
                    }
                    if !expect!(self, Token::Comma, "Expect comma efter element in tuple") {
                        return Err(());
                    }
                }
            }

            Token::LeftBracket => {
                self.eat();
                let ty = self.parse_type();
                expect!(self, Token::RightBracket, "Expected ']' after list type");
                match ty {
                    Ok(ty) => Ok(Type::List(Box::new(ty))),
                    Err(_) => Err(()),
                }
            }

            Token::Identifier(x) => {
                self.eat();
                match x.as_str() {
                    "void" => Ok(Type::Void),
                    "int" => Ok(Type::Int),
                    "float" => Ok(Type::Float),
                    "bool" => Ok(Type::Bool),
                    "str" => Ok(Type::String),
                    x => {
                        let blob = self.find_constant(x);
                        if let Value::Blob(blob) = &self.constants[blob] {
                            Ok(Type::Instance(Rc::clone(blob)))
                        } else {
                            // TODO(ed): This is kinda bad. If the type cannot
                            // be found it tries to infer it during runtime
                            // and doesn't verify it.
                            Ok(Type::Unknown)
                        }
                    }
                }
            }
            _ => Err(()),
        }
    }

    fn blob_statement(&mut self, _block: &mut Block) {
        let name = if let Token::Identifier(name) = self.eat() {
            name
        } else {
            syntax_error!(self, "Expected identifier after 'blob'");
            return;
        };
        expect!(
            self,
            Token::ColonColon,
            "Expected '::' when declaring a blob"
        );
        expect!(self, Token::Blob, "Expected 'blob' when declaring a blob");

        expect!(self, Token::LeftBrace, "Expected 'blob' body. AKA '{{'");

        let mut blob = Blob::new(self.new_blob_id(), &name);
        loop {
            if matches!(self.peek(), Token::EOF | Token::RightBrace) {
                break;
            }
            if matches!(self.peek(), Token::Newline) {
                self.eat();
                continue;
            }

            let name = if let Token::Identifier(name) = self.eat() {
                name
            } else {
                syntax_error!(self, "Expected identifier for field");
                continue;
            };

            expect!(self, Token::Colon, "Expected ':' after field name");

            let ty = if let Ok(ty) = self.parse_type() {
                ty
            } else {
                syntax_error!(self, "Failed to parse blob-field type");
                continue;
            };

            if blob.add_field(&name, ty).is_err() {
                syntax_error!(
                    self,
                    "A field named '{}' is defined twice for '{}'", name, blob.name
                );
            }
        }

        expect!(self, Token::RightBrace, "Expected '}}' after 'blob' body");

        let blob = Value::Blob(Rc::new(blob));
        self.named_constant(name, blob);
    }

    fn access_dotted(&mut self, block: &mut Block) {
        let name = match self.peek() {
            Token::Identifier(name) => name,
            _ => unreachable!(),
        };
        if self.find_namespace(&name).is_some() {
            self.expression(block);
        } else if rest_of_line_contains!(
            self,
            Token::Equal
                | Token::PlusEqual
                | Token::MinusEqual
                | Token::StarEqual
                | Token::SlashEqual
        ) {
            self.blob_field(block)
        } else {
            self.expression(block)
        }
    }

    //TODO rename
    fn blob_field(&mut self, block: &mut Block) {
        let name = match self.eat() {
            Token::Identifier(name) => name,
            _ => unreachable!(),
        };

        if let Some(var) = self.find_variable(&name) {
            self.mark_read(self.frames().len() - 1, &var);
            if var.upvalue {
                add_op(self, block, Op::ReadUpvalue(var.slot));
            } else {
                add_op(self, block, Op::ReadLocal(var.slot));
            }
            loop {
                match self.peek() {
                    Token::Dot => {
                        self.eat();
                        let field = if let Token::Identifier(field) = self.eat() {
                            field
                        } else {
                            syntax_error!(self, "Expected fieldname after '.'");
                            return;
                        };

                        let field = self.intern_string(field);
                        let op = match self.peek() {
                            Token::Equal => {
                                self.eat();
                                self.expression(block);
                                add_op(self, block, Op::AssignField(field));
                                return;
                            }

                            Token::PlusEqual => Op::Add,
                            Token::MinusEqual => Op::Sub,
                            Token::StarEqual => Op::Mul,
                            Token::SlashEqual => Op::Div,

                            _ => {
                                add_op(self, block, Op::GetField(field));
                                continue;
                            }
                        };
                        add_op(self, block, Op::Copy(1));
                        add_op(self, block, Op::GetField(field));
                        self.eat();
                        self.expression(block);
                        add_op(self, block, op);
                        add_op(self, block, Op::AssignField(field));
                        return;
                    }
                    Token::LeftBracket => {
                        self.eat();
                        self.expression(block);
                        expect!(self, Token::RightBracket, "Expected ']' after indexing");

                        let op = match self.peek() {
                            Token::Equal => {
                                self.eat();
                                self.expression(block);
                                add_op(self, block, Op::AssignIndex);
                                return;
                            }

                            Token::PlusEqual => Op::Add,
                            Token::MinusEqual => Op::Sub,
                            Token::StarEqual => Op::Mul,
                            Token::SlashEqual => Op::Div,

                            _ => {
                                add_op(self, block, Op::GetIndex);
                                continue;
                            }
                        };

                        add_op(self, block, Op::Copy(2));
                        add_op(self, block, Op::GetIndex);
                        self.eat();
                        self.expression(block);
                        add_op(self, block, op);
                        add_op(self, block, Op::AssignIndex);
                        return;
                    }
                    Token::Newline => {
                        return;
                    }
                    _ => {
                        if !self.call_maybe(block) {
                            syntax_error!(self, "Unexpected token when parsing blob-field");
                            return;
                        }
                    }
                }
            }
        } else {
            syntax_error!(self, "Cannot find variable '{}'", name);
        }
    }

    fn outer_statement(&mut self, block: &mut Block) {
        self.clear_panic();
        match self.peek_four() {
            (Token::Identifier(name), Token::ColonEqual, ..) => {
                self.eat();
                self.eat();
                self.definition_statement(&name, Type::Unknown, false, block);
            }

            (Token::Identifier(_), Token::ColonColon, Token::Blob, ..) => {
                self.blob_statement(block);
            }

            (Token::Identifier(name), Token::ColonColon, ..) => {
                self.eat();
                self.eat();
                self.constant_statement(&name, Type::Unknown, block);
            }

            (Token::Identifier(name), Token::Colon, ..) => {
                self.eat();
                self.eat();
                let force = if self.peek() == Token::Bang {
                    self.eat();
                    true
                } else {
                    false
                };
                if let Ok(typ) = self.parse_type() {
                    expect!(self, Token::Equal, "Expected assignment");
                    self.definition_statement(&name, typ, force, block);
                } else {
                    syntax_error!(self, "Expected type found '{:?}'", self.peek());
                }
            }

            (Token::Newline, ..) => {}

            (a, b, c, d) => {
                syntax_error!(
                    self,
                    "Unknown outer token sequence: {:?} {:?} {:?} {:?}", a, b, c, d
                )
            }
        }
    }

    fn statement(&mut self, block: &mut Block) {
        self.clear_panic();

        match self.peek_four() {
            (Token::Print, ..) => {
                self.eat();
                self.expression(block);
                add_op(self, block, Op::Print);
            }

            (Token::Identifier(_), Token::Equal, ..)
            | (Token::Identifier(_), Token::PlusEqual, ..)
            | (Token::Identifier(_), Token::MinusEqual, ..)
            | (Token::Identifier(_), Token::SlashEqual, ..)
            | (Token::Identifier(_), Token::StarEqual, ..) => {
                self.assign(block);
            }

            (Token::Identifier(_), Token::Dot, ..) => {
                self.access_dotted(block);
            }

            (Token::Identifier(name), Token::ColonEqual, ..) => {
                self.eat();
                self.eat();
                self.definition_statement(&name, Type::Unknown, false, block);
            }

            (Token::Identifier(name), Token::ColonColon, ..) => {
                self.eat();
                self.eat();
                self.constant_statement(&name, Type::Unknown, block);
            }

            (Token::Identifier(name), Token::Colon, ..) => {
                self.eat();
                self.eat();
                let force = if self.peek() == Token::Bang {
                    self.eat();
                    true
                } else {
                    false
                };
                if let Ok(typ) = self.parse_type() {
                    expect!(self, Token::Equal, "Expected assignment");
                    self.definition_statement(&name, typ, force, block);
                } else {
                    syntax_error!(self, "Expected type found '{:?}'", self.peek());
                }
            }

            (Token::If, ..) => {
                self.if_statment(block);
            }

            (Token::For, ..) => {
                self.for_loop(block);
            }

            (Token::Ret, ..) => {
                self.eat();
                if self.peek() == Token::Newline {
                    self.eat();
                    let nil = self.add_constant(Value::Nil);
                    add_op(self, block, Op::Constant(nil));
                } else {
                    self.expression(block);
                }
                add_op(self, block, Op::Return);
            }

            (Token::Unreachable, ..) => {
                self.eat();
                add_op(self, block, Op::Unreachable);
            }

            (Token::LeftBrace, ..) => {
                self.scope(block);
            }

            (Token::Newline, ..) => {}

            _ => {
                self.expression(block);
                add_op(self, block, Op::Pop);
            }
        }
    }

    pub(crate) fn compile(
        &mut self,
        name: &str,
        file: &Path,
        functions: &[(String, RustFunction)],
    ) -> Result<Prog, Vec<Error>> {
        let main = Variable::new("/preamble", false, Type::Void);
        let slot = self.define(main).unwrap();
        self.frame_mut().stack[slot].read = true;

        for section in 0..self.sections.len() {
            self.init_section(section);
            let section = &mut self.sections[section];
            match (
                section.tokens.get(0),
                section.tokens.get(1),
                section.tokens.get(2),
            ) {
                (Some((Token::Use, _)), Some((Token::Identifier(name), _)), ..) => {
                    let path = path_to_module(file, &name);
                    let name = name.to_string();
                    self.add_namespace(name, path);
                }

                (
                    Some((Token::Identifier(name), _)),
                    Some((Token::ColonColon, _)),
                    Some((Token::Fn, _)),
                ) => {
                    let name = name.to_string();
                    self.forward_constant(name);
                }

                (
                    Some((Token::Identifier(name), _)),
                    Some((Token::ColonColon, _)),
                    Some((Token::Blob, _)),
                ) => {
                    let name = name.to_string();
                    self.forward_constant(name);
                }

                (Some((Token::Identifier(name), _)), Some((Token::Colon, _)), ..) => {
                    let name = name.to_string();
                    self.eat();
                    self.eat();
                    if let Ok(ty) = self.parse_type() {
                        let is_mut = self.peek() == Token::Equal;
                        let var = Variable::new(&name, is_mut, ty);
                        let _ = self.define(var).unwrap();
                    } else {
                        syntax_error!(self, "Failed to parse type global '{}'", name);
                    }
                }

                (Some((Token::Identifier(name), _)), Some((Token::ColonColon, _)), ..) => {
                    let var = Variable::new(name, false, Type::Unknown);
                    let _ = self.define(var).unwrap();
                }

                (Some((Token::Identifier(name), _)), Some((Token::ColonEqual, _)), ..) => {
                    let var = Variable::new(name, true, Type::Unknown);
                    let _ = self.define(var).unwrap();
                }

                (None, ..) => {}

                (a, b, c) => {
                    section.faulty = true;
                    syntax_error!(self, "Unknown outer token sequence: {:?} {:?} {:?}. Expected 'use', function, blob or variable", a, b, c);
                }
            }
        }

        self.functions = functions
            .to_vec()
            .into_iter()
            .enumerate()
            .map(|(i, (s, f))| (s, (i, f)))
            .collect();
        let mut block = Block::new(name, true, file);
        for section in 0..self.sections.len() {
            self.init_section(section);
            if self.sections[section].faulty {
                continue;
            }
            while !matches!(self.peek(), Token::EOF | Token::Use) {
                self.outer_statement(&mut block);
                expect!(
                    self,
                    Token::Newline | Token::EOF,
                    "Expect newline or EOF after expression"
                );
            }
        }
        block.ty = Type::Function(Vec::new(), Box::new(Type::Void));

        if !self.names().is_empty() {
            let errors: Vec<_> = self
                .names()
                .iter()
                .filter_map(|(name, kind)| {
                    if let Name::Unknown(_, line) = kind {
                        Some(Error::SyntaxError {
                            file: self.current_file().into(),
                            line: *line,
                            token: Token::Identifier(name.clone()),
                            message: Some(format!("Usage of undefined value: '{}'", name)),
                        })
                    } else {
                        None
                    }
                })
                .collect();
            errors.into_iter().for_each(|e| self.error(e));
        }

        self.init_section(0);
        let constant = self.find_constant("start");
        add_op(self, &mut block, Op::Constant(constant));
        add_op(self, &mut block, Op::Call(0));

        let tmp = self.add_constant(Value::Nil);
        add_op(self, &mut block, Op::Constant(tmp));
        add_op(self, &mut block, Op::Return);

        for var in self.frames_mut().pop().unwrap().stack.iter().skip(1) {
            if !(var.read || var.upvalue) {
                self.error(Error::SyntaxError {
                    file: self.current_file().into(),
                    line: var.line,
                    token: Token::Identifier(var.name.clone()),
                    message: Some(format!("Unused value '{}'", var.name)),
                });
            }
            self.panic = false;
        }

        self.blocks.insert(0, Rc::new(RefCell::new(block)));

        if self.errors.is_empty() {
            Ok(Prog {
                blocks: self.blocks.clone(),
                functions: functions.iter().map(|(_, f)| *f).collect(),
                constants: self.constants.clone(),
                strings: self.strings.clone(),
            })
        } else {
            Err(self.errors.clone())
        }
    }
}
