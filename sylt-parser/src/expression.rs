use sylt_common::error::Error;

use crate::statement::{block_statement, statement};

use super::*;

/// The different kinds of [Expression]s.
///
/// Expressions are recursive and evaluate to some kind of value.
#[derive(Debug, Clone)]
pub enum ExpressionKind {
    /// Read from an [Assignable]. Variables, function calls, module accesses,
    /// blob fields, list indexing, tuple indexing and dict indexing end up here.
    Get(Assignable),

    /// `a + b`
    Add(Box<Expression>, Box<Expression>),
    /// `a - b`
    Sub(Box<Expression>, Box<Expression>),
    /// `a * b`
    Mul(Box<Expression>, Box<Expression>),
    /// `a / b`
    Div(Box<Expression>, Box<Expression>),
    /// `-a`
    Neg(Box<Expression>),

    /// `a == b`
    Eq(Box<Expression>, Box<Expression>),
    /// `a != b`
    Neq(Box<Expression>, Box<Expression>),
    /// `a > b`
    Gt(Box<Expression>, Box<Expression>),
    /// `a >= b`
    Gteq(Box<Expression>, Box<Expression>),
    /// `a < b`
    Lt(Box<Expression>, Box<Expression>),
    /// `a <= b`
    Lteq(Box<Expression>, Box<Expression>),
    /// `a <=> b`
    AssertEq(Box<Expression>, Box<Expression>),

    /// `a in b`
    In(Box<Expression>, Box<Expression>),

    /// `a && b`
    And(Box<Expression>, Box<Expression>),
    /// `a || b`
    Or(Box<Expression>, Box<Expression>),
    /// `!a`
    Not(Box<Expression>),

    /// Makes your code go either here or there.
    ///
    /// `if <expression> <statement> [else <statement>]`.
    If {
        condition: Box<Expression>,
        pass: Box<Statement>,
        fail: Box<Statement>,
    },

    /// Functions and closures.
    Function {
        name: String,
        params: Vec<(Identifier, Type)>,
        ret: Type,

        body: Box<Statement>,
    },
    /// A new instance of a blob.
    Instance {
        blob: Assignable,
        fields: Vec<(String, Expression)>, // Keep calling order
    },
    /// `(a, b, ..)`
    Tuple(Vec<Expression>),
    /// `[a, b, ..]`
    List(Vec<Expression>),
    /// `{a, b, ..}`
    Set(Vec<Expression>),
    /// `{ a: b, c: d, .. }`
    // Has to have even length, listed { k1, v1, k2, v2 }
    Dict(Vec<Expression>),

    Float(f64),
    Int(i64),
    Str(String),
    Bool(bool),
    Nil,
}

/// Expressions evaluate to values. Contains any [ExpressionKind].
#[derive(Debug, Clone)]
pub struct Expression {
    pub span: Span,
    pub kind: ExpressionKind,
}

/// Parse an [ExpressionKind::Function]: `fn a: int, b: bool -> bool <statement>`
fn function<'t>(ctx: Context<'t>) -> ParseResult<'t, Expression> {
    use RuntimeType::Void;
    use TypeKind::Resolved;

    let span = ctx.span();
    let mut ctx = expect!(ctx, T::Fn, "Expected 'fn' for function expression");
    let mut params = Vec::new();
    // Parameters
    let ret = loop {
        match ctx.token() {
            T::Identifier(name) => {
                // Parameter name
                let ident = Identifier {
                    span: ctx.span(),
                    name: name.clone(),
                };
                ctx = expect!(ctx.skip(1), T::Colon, "Expected ':' after parameter name");
                // Parameter type
                let (_ctx, param) = parse_type(ctx)?;
                ctx = _ctx; // assign to outer

                params.push((ident, param));

                ctx = if matches!(ctx.token(), T::Comma | T::Arrow | T::LeftBrace) {
                    ctx.skip_if(T::Comma)
                } else {
                    raise_syntax_error!(ctx, "Expected ',' '{{' or '->' after type parameter")
                };
            }

            // Parse return type
            T::Arrow => {
                ctx = ctx.skip(1);
                break if let Ok((_ctx, ret)) = parse_type(ctx) {
                    ctx = _ctx; // assign to outer
                    ret
                } else {
                    Type {
                        // If we couldn't parse the return type, we assume `-> Void`.
                        span: ctx.span(),
                        kind: Resolved(Void),
                    }
                };
            }

            T::LeftBrace => {
                // No return type so we assume `-> Void`.
                break Type {
                    span: ctx.span(),
                    kind: Resolved(Void),
                };
            }

            t => {
                raise_syntax_error!(ctx, "Didn't expect '{:?}' in function", t);
            }
        }
    };

    // Parse the function statement.
    let (ctx, mut statement) = block_statement(ctx)?;

    // If the return type isn't void, check for and apply implicit returns.

    let statements = if let StatementKind::Block { statements } = &mut statement.kind {
        statements
    } else {
        unreachable!("Function blocks should only be blocks");
    };

    if !matches!(ret.kind, Resolved(Void)) {
        // If the last statement is an expression statement,
        // replace it with a return statement.
        let last_statement = statements.pop();
        if let Some(Statement {
            span,
            kind: StatementKind::StatementExpression { value , .. },
        }) = last_statement
        {
            statements.push(Statement {
                span,
                kind: StatementKind::Ret { value },
            });
        } else if let Some(statement) = last_statement {
            statements.push(statement);
        }
    }

    use ExpressionKind::Function;
    let function = Function {
        name: "lambda".into(),
        params,
        ret,
        body: Box::new(statement),
    };

    Ok((
        ctx,
        Expression {
            span,
            kind: function,
        },
    ))
}

/// Parse an expression until we reach a token with higher precedence.
fn parse_precedence<'t>(ctx: Context<'t>, prec: Prec) -> ParseResult<'t, Expression> {
    // Initial value, e.g. a number value, assignable, ...
    let (mut ctx, mut expr) = prefix(ctx)?;
    while prec <= precedence(ctx.token()) {
        if let Ok((_ctx, _expr)) = infix(ctx, &expr) {
            // assign to outer
            ctx = _ctx;
            expr = _expr;
        } else {
            break;
        }
    }
    Ok((ctx, expr))
}

/// Return a [Token]'s precedence.
///
/// See the documentation on [Prec] for how to interpret and compare the
/// variants.
#[rustfmt::skip]
fn precedence(token: &T) -> Prec {
    use Prec;

    match token {
        T::LeftBracket => Prec::Index,

        T::Star | T::Slash => Prec::Factor,

        T::Minus | T::Plus => Prec::Term,

        T::EqualEqual
        | T::Greater
        | T::GreaterEqual
        | T::Less
        | T::LessEqual
        | T::NotEqual => Prec::Comp,

        T::And => Prec::BoolAnd,
        T::Or => Prec::BoolOr,

        T::In => Prec::Index,

        T::AssertEqual => Prec::Assert,

        T::Arrow => Prec::Arrow,

        _ => Prec::No,
    }
}

/// Parse a single (primitive) value.
fn value<'t>(ctx: Context<'t>) -> Result<(Context<'t>, Expression), (Context<'t>, Vec<Error>)> {
    use ExpressionKind::*;
    let (token, span, ctx) = ctx.eat();
    let kind = match token.clone() {
        T::Float(f) => Float(f),
        T::Int(i) => Int(i),
        T::Bool(b) => Bool(b),
        T::Nil => Nil,
        T::String(s) => Str(s),
        t => {
            raise_syntax_error!(ctx, "Cannot parse value, '{:?}' is not a valid value", t);
        }
    };
    Ok((ctx, Expression { span, kind }))
}

fn nil_statement_expression(span: Span, should_pop: bool) -> Statement {
    let nil = Expression {
        span,
        kind: ExpressionKind::Nil,
    };
    Statement {
        span,
        kind: StatementKind::StatementExpression {
            value: nil,
            should_pop,
        }
    }
}

fn make_statement_expression(statement: Statement) -> Statement {
    let outer_span = statement.span;
    match statement.kind {
        StatementKind::StatementExpression{ .. } => statement,

        StatementKind::Block { mut statements } => {
            let last_statement = statements.last_mut();
            let span = last_statement.as_ref().map(|s| s.span).unwrap_or(outer_span);

            if let Some(Statement {
                kind: StatementKind::StatementExpression { should_pop , .. },
                ..
            }) = last_statement
            {
                *should_pop = false;
            } else {
                statements.push(nil_statement_expression(span, false));
            }

            Statement {
                span,
                kind: StatementKind::Block { statements },
            }
        }

        _ => {
            let statements = vec![
                statement,
                nil_statement_expression(outer_span, false),
            ];
            Statement {
                span: outer_span,
                kind: StatementKind::Block { statements },
            }
        }
    }
}

/// `if <expression> <statement> [else <statement>]`. Note that the else is optional.
fn branch<'t>(ctx: Context<'t>) -> ParseResult<'t, Expression> {
    let span = ctx.span();
    let (ctx, condition) = expression(ctx.skip(1))?;

    let (ctx, pass) = statement(ctx)?;
    let pass = make_statement_expression(pass);
    // else?
    let (ctx, fail) = if matches!(ctx.token(), T::Else) {
        let (ctx, fail) = statement(ctx.skip(1))?;
        let fail = make_statement_expression(fail);
        (ctx, fail)
    } else {
        // No else so we insert an empty statement instead.
        (
            ctx,
            nil_statement_expression(span, false),
        )
    };

    use ExpressionKind::If;
    Ok((
        ctx,
        Expression {
            span,
            kind: If {
                condition: Box::new(condition),
                pass: Box::new(pass),
                fail: Box::new(fail),
            },
        }
    ))
}

/// Parse something that begins at the start of an expression.
fn prefix<'t>(ctx: Context<'t>) -> ParseResult<'t, Expression> {
    use ExpressionKind::Get;

    match ctx.token() {
        T::LeftParen => grouping_or_tuple(ctx),
        T::LeftBracket => list(ctx),
        T::LeftBrace => set_or_dict(ctx),

        T::Float(_) | T::Int(_) | T::Bool(_) | T::String(_) | T::Nil => value(ctx),
        T::Minus | T::Bang => unary(ctx),

        T::If => branch(ctx),

        T::Identifier(_) => {
            // Blob initializations are expressions.
            if let Ok(result) = blob(ctx) {
                Ok(result)
            } else {
                let span = ctx.span();
                let (ctx, assign) = assignable(ctx)?;
                Ok((
                    ctx,
                    Expression {
                        span,
                        kind: Get(assign),
                    },
                ))
            }
        }

        t => {
            raise_syntax_error!(ctx, "No valid expression starts with '{:?}'", t);
        }
    }
}

/// Parse a unary operator followed by an expression, e.g. `-5`.
fn unary<'t>(ctx: Context<'t>) -> ParseResult<'t, Expression> {
    use ExpressionKind::{Neg, Not};

    let (op, span, ctx) = ctx.eat();
    let (ctx, expr) = parse_precedence(ctx, Prec::Factor)?;
    let expr = Box::new(expr);

    let kind = match op {
        T::Minus => Neg(expr),
        T::Bang => Not(expr),

        _ => {
            raise_syntax_error!(ctx, "Invalid unary operator");
        }
    };
    Ok((ctx, Expression { span, kind }))
}

/// Parse an expression starting from an infix operator. Called by `parse_precedence`.
fn infix<'t>(ctx: Context<'t>, lhs: &Expression) -> ParseResult<'t, Expression> {
    use ExpressionKind::*;

    // Parse an operator and a following expression
    // until we reach a token with higher precedence.
    let (op, span, ctx) = ctx.eat();
    let (ctx, rhs) = parse_precedence(ctx, precedence(op).next())?;

    // Left and right of the operator.
    let lhs = Box::new(lhs.clone());
    let rhs = Box::new(rhs);

    // Which expression kind to omit depends on the token.
    let kind = match op {
        // Simple arithmetic.
        T::Plus => Add(lhs, rhs),
        T::Minus => Sub(lhs, rhs),
        T::Star => Mul(lhs, rhs),
        T::Slash => Div(lhs, rhs),
        T::EqualEqual => Eq(lhs, rhs),
        T::NotEqual => Neq(lhs, rhs),
        T::Greater => Gt(lhs, rhs),
        T::GreaterEqual => Gteq(lhs, rhs),
        T::Less => Lt(lhs, rhs),
        T::LessEqual => Lteq(lhs, rhs),

        // Boolean operators.
        T::And => And(lhs, rhs),
        T::Or => Or(lhs, rhs),

        T::AssertEqual => AssertEq(lhs, rhs),

        T::In => In(lhs, rhs),

        // The cool arrow syntax. For example: `a->b(2)` compiles to `b(a, 2)`.
        T::Arrow => {
            use AssignableKind::Call;
            // Rhs has to be an ExpressionKind::Get(AssignableKind::Call).
            if let Get(Assignable {
                kind: Call(callee, mut args),
                ..
            }) = rhs.kind
            {
                // Insert lhs as the first argument.
                args.insert(0, *lhs);
                // Return the new expression.
                Get(Assignable {
                    kind: Call(callee, args),
                    span: rhs.span,
                })
            } else {
                raise_syntax_error!(ctx, "Expected a call-expression after '->'");
            }
        }

        // Unknown infix operator.
        _ => {
            return Err((ctx, Vec::new()));
        }
    };

    Ok((ctx, Expression { span, kind }))
}

/// Parse either a grouping parenthesis or a tuple.
///
/// Essentially, one-element tuples are groupings unless they end with a
/// comma. So `(1)` is parsed as the value `1` while `(1,)` is parsed as the
/// one-sized tuple containing `1`.
///
/// `()` as well as `(,)` are parsed as zero-sized tuples.
fn grouping_or_tuple<'t>(ctx: Context<'t>) -> ParseResult<'t, Expression> {
    let span = ctx.span();
    let mut ctx = expect!(ctx, T::LeftParen, "Expected '('");

    // The expressions contained in the parenthesis.
    let mut exprs = Vec::new();

    let mut is_tuple = matches!(ctx.token(), T::Comma | T::RightParen);
    loop {
        // Any initial comma is skipped since we checked it before entering the loop.
        ctx = ctx.skip_if(T::Comma);
        match ctx.token() {
            // Done.
            T::EOF | T::RightParen => {
                break;
            }

            // Another inner expression.
            _ => {
                let (_ctx, expr) = expression(ctx)?;
                exprs.push(expr);
                ctx = _ctx; // assign to outer

                // Not a tuple, until it is.
                is_tuple |= matches!(ctx.token(), T::Comma);
            }
        }
    }

    ctx = expect!(ctx, T::RightParen, "Expected ')'");

    use ExpressionKind::Tuple;
    let result = if is_tuple {
        Expression {
            span,
            kind: Tuple(exprs),
        }
    } else {
        exprs.remove(0)
    };
    Ok((ctx, result))
}

/// Parse a blob instantiation, e.g. `A { b: 55 }`.
fn blob<'t>(ctx: Context<'t>) -> ParseResult<'t, Expression> {
    let span = ctx.span();
    let (ctx, blob) = assignable(ctx)?;
    let mut ctx = expect!(ctx, T::LeftBrace, "Expected '{{' after blob name");

    // The blob's fields.
    let mut fields = Vec::new();
    loop {
        match ctx.token() {
            T::Newline => {
                ctx = ctx.skip(1);
            }

            // Done with fields.
            T::RightBrace | T::EOF => {
                break;
            }

            // Another field, e.g. `b: 55`.
            T::Identifier(name) => {
                // Get the field name.
                let name = name.clone();

                ctx = expect!(ctx.skip(1), T::Colon, "Expected ':' after field name");
                // Get the value; `55` in the example above.
                let (_ctx, expr) = expression(ctx)?;
                ctx = _ctx; // assign to outer

                if !matches!(ctx.token(), T::Comma | T::Newline | T::RightBrace) {
                    raise_syntax_error!(ctx, "Expected a delimiter: newline or ','");
                }
                ctx = ctx.skip_if(T::Comma);

                fields.push((name, expr));
            }

            t => {
                raise_syntax_error!(ctx, "Unexpected token ('{:?}') in blob initalizer", t);
            }
        }
    }
    let ctx = expect!(ctx, T::RightBrace, "Expected '}}' after blob initalizer");

    if matches!(ctx.token(), T::Else) {
        raise_syntax_error!(ctx, "Parsed a blob instance not an if-statement");
    }

    use ExpressionKind::Instance;
    Ok((
        ctx,
        Expression {
            span,
            kind: Instance { blob, fields },
        },
    ))
}

// Parse a list expression, e.g. `[1, 2, a(3)]`
fn list<'t>(ctx: Context<'t>) -> ParseResult<'t, Expression> {
    let span = ctx.span();
    let mut ctx = expect!(ctx, T::LeftBracket, "Expected '['");

    // `l := [\n1` is valid
    ctx = ctx.skip_while(T::Newline);

    // Inner experssions.
    let mut exprs = Vec::new();
    loop {
        match ctx.token() {
            // Done with inner expressions.
            T::EOF | T::RightBracket => {
                break;
            }

            // Another one.
            _ => {
                let (_ctx, expr) = expression(ctx)?;
                exprs.push(expr);
                ctx = _ctx; // assign to outer
                ctx = ctx.skip_if(T::Comma);
                ctx = ctx.skip_while(T::Newline); // newlines after expression is valid inside lists
            }
        }
    }

    ctx = expect!(ctx, T::RightBracket, "Expected ']'");
    use ExpressionKind::List;
    Ok((
        ctx,
        Expression {
            span,
            kind: List(exprs),
        },
    ))
}

/// Parse either a set or dict expression.
///
/// `{:}` is parsed as the empty dict and {} is parsed as the empty set.
fn set_or_dict<'t>(ctx: Context<'t>) -> ParseResult<'t, Expression> {
    let span = ctx.span();
    let mut ctx = expect!(ctx, T::LeftBrace, "Expected '{{'");

    // The inner values of the set or dict.
    let mut exprs = Vec::new();
    // None => we don't know. Some(b) => we know b.
    let mut is_dict = None;
    loop {
        match ctx.token() {
            // Done.
            T::EOF | T::RightBrace => {
                break;
            }

            // Free-standing colon, i.e. "empty dict pair".
            T::Colon => {
                // Only valid if we don't know yet.
                if let Some(is_dict) = is_dict {
                    raise_syntax_error!(
                        ctx,
                        "Empty dict pair is invalid in a {}",
                        if is_dict { "dict" } else { "set" }
                    );
                }
                is_dict = Some(true);
                ctx = ctx.skip(1);
            }

            // Something that's part of an inner expression.
            _ => {
                // Parse the expression.
                let (_ctx, expr) = expression(ctx)?;
                ctx = _ctx; // assign to outer
                exprs.push(expr);

                // If a) we know we're a dict or b) the next token is a colon, parse the value of the dict.
                // Also, if we didn't know previously, store whether we're a dict or not.
                if *is_dict.get_or_insert_with(|| matches!(ctx.token(), T::Colon)) {
                    ctx = expect!(ctx, T::Colon, "Expected ':' for dict pair");
                    // Parse value expression.
                    let (_ctx, expr) = expression(ctx)?;
                    ctx = _ctx; // assign to outer
                    exprs.push(expr);
                }

                ctx = ctx.skip_if(T::Comma);
            }
        }
    }

    ctx = expect!(ctx, T::RightBrace, "Expected '}}'");

    use ExpressionKind::{Dict, Set};
    // If we still don't know, assume we're a set.
    let kind = if is_dict.unwrap_or(false) {
        Dict(exprs)
    } else {
        Set(exprs)
    };

    Ok((ctx, Expression { span, kind }))
}

/// Parse a single expression.
///
/// An expression is either a function expression or a "normal"
/// expression that follows precedence rules.

pub fn expression<'t>(ctx: Context<'t>) -> ParseResult<'t, Expression> {
    match ctx.token() {
        T::Fn => function(ctx),
        _ => parse_precedence(ctx, Prec::No),
    }
}

// NOTE(ed): It's really hard to write good tests, Rust refuses to deref the boxes
// automatically.
//
// Faulty syntax should be tested in the small language tests.
#[cfg(test)]
mod test {
    use super::ExpressionKind::*;
    use crate::expression;
    use crate::test;
    use crate::Assignable;
    use crate::AssignableKind::*;

    test!(expression, value: "0" => Int(0));
    test!(expression, add: "0 + 1.0" => Add(_, _));
    test!(expression, mul: "\"abc\" * \"abc\"" => Mul(_, _));
    test!(expression, ident: "a" => Get(Assignable { kind: Read(_), .. }));
    test!(expression, access: "a.b" => Get(Assignable { kind: Access(_, _), .. }));
    test!(expression, index_ident: "a[a]" => Get(Assignable { kind: Index(_, _), .. }));
    test!(expression, index_expr: "a[1 + 2 + 3]" => Get(Assignable { kind: Index(_, _), .. }));
    test!(expression, grouping: "(0 * 0) + 1" => Add(_, _));
    test!(expression, grouping_one: "(0)" => Int(0));
    test!(expression, tuple: "(0, 0)" => Tuple(_));
    test!(expression, tuple_one: "(0,)" => Tuple(_));
    test!(expression, tuple_empty: "()" => Tuple(_));
    test!(expression, list: "[0, 0]" => List(_));
    test!(expression, set: "{1, 1}" => Set(_));
    test!(expression, dict: "{1: 1}" => Dict(_));
    test!(expression, zero_set: "{}" => Set(_));
    test!(expression, zero_dict: "{:}" => Dict(_));

    test!(expression, in_list: "a in [1, 2, 3]" => In(_, _));
    test!(expression, in_set: "2 in {1, 1, 2}" => In(_, _));
    test!(expression, in_grouping: "1 + 2 in b" => Add(_, _));
    test!(expression, in_grouping_paren: "(1 + 2) in b" => In(_, _));

    test!(expression, call_simple_paren: "a()" => Get(_));
    test!(expression, call_call: "a()()" => Get(_));
    test!(expression, call_simple_bang: "a'" => Get(_));
    test!(expression, call_chaining_paren: "a().b" => Get(_));
    test!(expression, call_chaining_bang: "a'.b" => Get(_));
    test!(expression, call_args_paren: "a(1, 2, 3)" => Get(_));
    test!(expression, call_args_bang: "a' 1, 2, 3" => Get(_));
    test!(expression, call_args_chaining_paren: "a(1, 2, 3).b" => Get(_));
    test!(expression, call_args_chaining_paren_trailing: "a(1, 2, 3,).b" => Get(_));
    test!(expression, assignable_index: "a[0]" => Get(_));
    test!(expression, assignable_index_twice: "a[0][1]" => Get(_));
    test!(expression, assignable_mixed: "a[0]()" => Get(_));
    test!(expression, assignable_mixed_many: "a()[0]()[1]()()()[2][3]" => Get(_));

    // TODO(ed): This is controverisal
    test!(expression, call_args_chaining_bang: "a' 1, 2, 3 .b" => Get(_));
    test!(expression, call_args_chaining_bang_trailing: "a' 1, 2, 3, .b" => Get(_));

    // TODO(ed): Verify 'a! -> b! -> c! == c(b(a()))' in some way
    test!(expression, call_arrow: "1 + 0 -> a' 2, 3" => Add(_, _));
    test!(expression, call_arrow_grouping: "(1 + 0) -> a' 2, 3" => Get(_));

    test!(expression, instance: "A { a: 1 + 1, b: nil }" => Instance { .. });
    test!(expression, instance_more: "A { a: 2\n c: 2 }" => Instance { .. });
    test!(expression, instance_empty: "A {}" => Instance { .. });

    test!(expression, simple: "fn -> {}" => _);
    test!(expression, argument: "fn a: int -> int { ret a + 1 }" => _);

    test!(expression, booleans: "true && false || !false" => _);
    test!(expression, bool_and: "true && a" => _);
    test!(expression, bool_or: "a || false" => _);
    test!(expression, bool_neg: "!a" => _);
    test!(expression, bool_neg_multiple: "!a && b" => _);
    test!(expression, bool_neg_multiple_rev: "a && !b" => _);

    test!(expression, cmp_eq: "a == b" => _);
    test!(expression, cmp_neq: "a != b" => _);
    test!(expression, cmp_leq: "a <= b" => _);
    test!(expression, cmp_geq: "a >= b" => _);
    test!(expression, cmp_gt: "a > b" => _);
    test!(expression, cmp_lt: "a < b" => _);
    test!(expression, neg: "-a" => _);

    test!(expression, expr: "-a + b < 3 * true && false / 2" => _);

    test!(expression, void_simple: "fn {}" => _);
    test!(expression, void_argument: "fn a: int { ret a + 1 }" => _);
}
