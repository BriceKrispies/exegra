//! Exegra's expression language: tokenizer, parser and evaluator, mirroring `src/core/expr.js`.
//!
//! Grammar (lowest to highest precedence):
//!
//! ```text
//! implies :  a => b            (right associative)
//! or      :  a || b
//! and     :  a && b
//! equality:  a == b, a != b
//! compare :  a < b, a <= b, a > b, a >= b
//! additive:  a + b, a - b      (binary minus needs surrounding spaces next to identifiers)
//! multiply:  a * b, a / b, a % b
//! unary   :  !a, -a
//! primary :  number | 'string' | "string" | true | false | null | reference | ( expr )
//! reference: ident ( '.' ident )*   where ident may contain inner hyphens (entity ids)
//! ```
//!
//! Error messages are part of the trace format and are reproduced verbatim.

use std::fmt;

use crate::value::{js_number_to_string, Value};

/// A parse or evaluation error. `pos` is the source offset where known, else -1; only the
/// message reaches a trace.
#[derive(Clone, Debug, PartialEq)]
pub struct ExprError {
    pub message: String,
    pub pos: i64,
}

impl ExprError {
    fn new(message: impl Into<String>, pos: i64) -> Self {
        ExprError {
            message: message.into(),
            pos,
        }
    }

    fn eval(message: impl Into<String>) -> Self {
        ExprError::new(message, -1)
    }
}

impl fmt::Display for ExprError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for ExprError {}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnOp {
    Not,
    Neg,
}

impl UnOp {
    pub fn as_str(self) -> &'static str {
        match self {
            UnOp::Not => "!",
            UnOp::Neg => "-",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Implies,
    Or,
    And,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

impl BinOp {
    pub fn as_str(self) -> &'static str {
        match self {
            BinOp::Implies => "=>",
            BinOp::Or => "||",
            BinOp::And => "&&",
            BinOp::Eq => "==",
            BinOp::Ne => "!=",
            BinOp::Lt => "<",
            BinOp::Le => "<=",
            BinOp::Gt => ">",
            BinOp::Ge => ">=",
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Rem => "%",
        }
    }

    fn from_op(s: &str) -> Option<BinOp> {
        Some(match s {
            "=>" => BinOp::Implies,
            "||" => BinOp::Or,
            "&&" => BinOp::And,
            "==" => BinOp::Eq,
            "!=" => BinOp::Ne,
            "<" => BinOp::Lt,
            "<=" => BinOp::Le,
            ">" => BinOp::Gt,
            ">=" => BinOp::Ge,
            "+" => BinOp::Add,
            "-" => BinOp::Sub,
            "*" => BinOp::Mul,
            "/" => BinOp::Div,
            "%" => BinOp::Rem,
            _ => return None,
        })
    }
}

/// A parsed expression.
#[derive(Clone, Debug)]
pub enum Ast {
    Lit(Value),
    Ref { path: Vec<String>, pos: i64 },
    Un { op: UnOp, a: Box<Ast> },
    Bin { op: BinOp, a: Box<Ast>, b: Box<Ast> },
}

// ---- tokenizer ------------------------------------------------------------------------------

#[derive(Clone, Debug)]
enum Tok {
    Num(f64),
    Str(String),
    Id(String),
    Op(&'static str),
    End,
}

#[derive(Clone, Debug)]
struct Token {
    tok: Tok,
    pos: i64,
}

impl Token {
    /// The token's value as `${tk.v}` prints it in a message.
    fn text(&self) -> String {
        match &self.tok {
            Tok::Num(n) => js_number_to_string(*n),
            Tok::Str(s) | Tok::Id(s) => s.clone(),
            Tok::Op(o) => (*o).to_string(),
            Tok::End => "null".to_string(),
        }
    }
}

/// Operators in the order the reference tokenizer tries them (two-character ones first).
const OPS: [&str; 18] = [
    "=>", "||", "&&", "==", "!=", "<=", ">=", "<", ">", "+", "-", "*", "/", "%", "!", "(", ")", ".",
];

fn is_ident_start(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'_'
}

fn is_ident_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

fn tokenize(src: &str) -> Result<Vec<Token>, ExprError> {
    let b = src.as_bytes();
    let mut out = Vec::new();
    let mut i = 0usize;
    // Every branch advances over ASCII bytes or up to an ASCII quote, so `i` stays on a
    // character boundary.
    while i < b.len() {
        let c = b[i];
        let pos = i as i64;
        if matches!(c, b' ' | b'\t' | b'\n' | b'\r') {
            i += 1;
            continue;
        }
        if c == b'"' || c == b'\'' {
            match src[i + 1..].find(c as char) {
                None => return Err(ExprError::new("Unterminated string literal", pos)),
                Some(off) => {
                    let end = i + 1 + off;
                    out.push(Token {
                        tok: Tok::Str(src[i + 1..end].to_string()),
                        pos,
                    });
                    i = end + 1;
                }
            }
            continue;
        }
        // NUMBER = /\d+(?:\.\d+)?/ (ASCII digits only).
        if c.is_ascii_digit() {
            let start = i;
            while i < b.len() && b[i].is_ascii_digit() {
                i += 1;
            }
            if i + 1 < b.len() && b[i] == b'.' && b[i + 1].is_ascii_digit() {
                i += 1;
                while i < b.len() && b[i].is_ascii_digit() {
                    i += 1;
                }
            }
            let text = &src[start..i];
            let n: f64 = text.parse().map_err(|_| {
                ExprError::new(format!("Unexpected character '{}'", c as char), pos)
            })?;
            out.push(Token {
                tok: Tok::Num(n),
                pos,
            });
            continue;
        }
        // IDENT = /[A-Za-z_][A-Za-z0-9_]*(?:-[A-Za-z_][A-Za-z0-9_]*)*/
        if is_ident_start(c) {
            let start = i;
            i += 1;
            while i < b.len() && is_ident_char(b[i]) {
                i += 1;
            }
            while i + 1 < b.len() && b[i] == b'-' && is_ident_start(b[i + 1]) {
                i += 2;
                while i < b.len() && is_ident_char(b[i]) {
                    i += 1;
                }
            }
            out.push(Token {
                tok: Tok::Id(src[start..i].to_string()),
                pos,
            });
            continue;
        }
        match OPS.iter().find(|o| src[i..].starts_with(**o)) {
            Some(op) => {
                out.push(Token {
                    tok: Tok::Op(op),
                    pos,
                });
                i += op.len();
            }
            None => {
                let ch = src[i..].chars().next().unwrap_or('?');
                return Err(ExprError::new(format!("Unexpected character '{ch}'"), pos));
            }
        }
    }
    out.push(Token {
        tok: Tok::End,
        pos: src.len() as i64,
    });
    Ok(out)
}

// ---- parser ---------------------------------------------------------------------------------

/// Binary precedence levels, lowest first.
const BINARY: [&[&str]; 7] = [
    &["=>"],
    &["||"],
    &["&&"],
    &["==", "!="],
    &["<", "<=", ">", ">="],
    &["+", "-"],
    &["*", "/", "%"],
];

struct Parser {
    toks: Vec<Token>,
    p: usize,
}

impl Parser {
    fn peek(&self) -> &Token {
        &self.toks[self.p.min(self.toks.len() - 1)]
    }

    fn take(&mut self) -> Token {
        let t = self.peek().clone();
        self.p += 1;
        t
    }

    fn is_op(&self, v: &str) -> bool {
        matches!(self.peek().tok, Tok::Op(o) if o == v)
    }

    fn binary(&mut self, level: usize) -> Result<Ast, ExprError> {
        if level >= BINARY.len() {
            return self.unary();
        }
        let mut left = self.binary(level + 1)?;
        loop {
            let op = match self.peek().tok {
                Tok::Op(o) if BINARY[level].contains(&o) => o,
                _ => break,
            };
            self.p += 1;
            let bop = BinOp::from_op(op).ok_or_else(|| ExprError::eval("Malformed expression"))?;
            if bop == BinOp::Implies {
                let right = self.binary(level)?;
                return Ok(Ast::Bin {
                    op: bop,
                    a: Box::new(left),
                    b: Box::new(right),
                });
            }
            let right = self.binary(level + 1)?;
            left = Ast::Bin {
                op: bop,
                a: Box::new(left),
                b: Box::new(right),
            };
        }
        Ok(left)
    }

    fn unary(&mut self) -> Result<Ast, ExprError> {
        if self.is_op("!") || self.is_op("-") {
            let op = if self.is_op("!") {
                UnOp::Not
            } else {
                UnOp::Neg
            };
            self.p += 1;
            let a = self.unary()?;
            return Ok(Ast::Un { op, a: Box::new(a) });
        }
        self.primary()
    }

    fn primary(&mut self) -> Result<Ast, ExprError> {
        let tk = self.take();
        match &tk.tok {
            Tok::Num(n) => Ok(Ast::Lit(Value::Number(*n))),
            Tok::Str(s) => Ok(Ast::Lit(Value::String(s.clone()))),
            Tok::Id(id) => {
                match id.as_str() {
                    "true" => return Ok(Ast::Lit(Value::Bool(true))),
                    "false" => return Ok(Ast::Lit(Value::Bool(false))),
                    "null" => return Ok(Ast::Lit(Value::Null)),
                    _ => {}
                }
                let mut path = vec![id.clone()];
                while self.is_op(".") {
                    self.p += 1;
                    let next = self.take();
                    match next.tok {
                        Tok::Id(name) => path.push(name),
                        _ => return Err(ExprError::new("Expected a name after \".\"", next.pos)),
                    }
                }
                Ok(Ast::Ref { path, pos: tk.pos })
            }
            Tok::Op("(") => {
                let inner = self.binary(0)?;
                if !self.is_op(")") {
                    return Err(ExprError::new("Expected \")\"", self.peek().pos));
                }
                self.p += 1;
                Ok(inner)
            }
            Tok::End => Err(ExprError::new("Unexpected end of expression", tk.pos)),
            _ => Err(ExprError::new(
                format!("Unexpected \"{}\"", tk.text()),
                tk.pos,
            )),
        }
    }
}

/// Parse an expression.
pub fn parse_expr(src: &str) -> Result<Ast, ExprError> {
    let toks = tokenize(src)?;
    let mut parser = Parser { toks, p: 0 };
    let ast = parser.binary(0)?;
    if !matches!(parser.peek().tok, Tok::End) {
        let t = parser.peek();
        return Err(ExprError::new(
            format!("Unexpected \"{}\"", t.text()),
            t.pos,
        ));
    }
    Ok(ast)
}

// ---- evaluator ------------------------------------------------------------------------------

fn require_type(v: &Value, ty: &str, op: &str) -> Result<(), ExprError> {
    if v.type_name() == ty {
        Ok(())
    } else {
        Err(ExprError::eval(format!(
            "Operator \"{op}\" needs a {ty}, got {}",
            v.type_name()
        )))
    }
}

/// The largest magnitude of an integer without a declared type in the integer fragment
/// (`2^53 - 1`, formal/Exegra/Core/Behav.lean's `maxSafe`).
pub const MAX_SAFE: f64 = 9_007_199_254_740_991.0;
/// The error of an untyped result outside `±(2^53 - 1)` in the integer fragment.
pub const OVERFLOW: &str =
    "Integer overflow: an untyped result is outside -9007199254740991..9007199254740991";
/// The error of an untyped operand outside `±(2^53 - 1)` in the integer fragment.
pub const OPERAND: &str = "An untyped operand is outside -9007199254740991..9007199254740991";

/// Evaluate a parsed expression. `resolve` maps a reference path to its value and returns
/// [`Value::Undefined`] for an unknown reference (which is an error).
pub fn eval_expr(ast: &Ast, resolve: &dyn Fn(&[String]) -> Value) -> Result<Value, ExprError> {
    eval_expr_mode(ast, resolve, false)
}

/// Checks an untyped arithmetic result in the integer fragment: operands and result within
/// `±(2^53 - 1)`, as the behaviour calculus checks them (`checked` at `Ty.num`).
fn checked(integer: bool, x: f64, y: f64, r: f64) -> Result<Value, ExprError> {
    if integer {
        if x.abs() > MAX_SAFE || y.abs() > MAX_SAFE {
            return Err(ExprError::eval(OPERAND));
        }
        if r.abs() > MAX_SAFE {
            return Err(ExprError::eval(OVERFLOW));
        }
    }
    Ok(Value::Number(r))
}

/// Evaluate a parsed expression; with `integer` (an input in the fragment of the behaviour calculus,
/// WG-5681), untyped arithmetic is checked in `±(2^53 - 1)`. The calculus computes untyped numbers as
/// exact rationals (WG-5683); this oracle computes them as doubles, so the two agree on integers and
/// on results a double holds exactly, and differ elsewhere (tests/conformance/expected-differences.json).
pub fn eval_expr_mode(
    ast: &Ast,
    resolve: &dyn Fn(&[String]) -> Value,
    integer: bool,
) -> Result<Value, ExprError> {
    let eval_expr = |a: &Ast, r: &dyn Fn(&[String]) -> Value| eval_expr_mode(a, r, integer);
    match ast {
        Ast::Lit(v) => Ok(v.clone()),
        Ast::Ref { path, pos } => {
            let v = resolve(path);
            if matches!(v, Value::Undefined) {
                return Err(ExprError::new(
                    format!("Unknown reference \"{}\"", path.join(".")),
                    *pos,
                ));
            }
            Ok(v)
        }
        Ast::Un { op, a } => {
            let a = eval_expr(a, resolve)?;
            match op {
                UnOp::Not => {
                    require_type(&a, "boolean", "!")?;
                    Ok(Value::Bool(!matches!(a, Value::Bool(true))))
                }
                UnOp::Neg => {
                    require_type(&a, "number", "-")?;
                    let x = a.as_number().unwrap_or(f64::NAN);
                    checked(integer, x, 0.0, -x)
                }
            }
        }
        Ast::Bin { op, a, b } => {
            let op = *op;
            let name = op.as_str();
            if matches!(op, BinOp::And | BinOp::Or | BinOp::Implies) {
                let av = eval_expr(a, resolve)?;
                require_type(&av, "boolean", name)?;
                let at = matches!(av, Value::Bool(true));
                match op {
                    BinOp::And if !at => return Ok(Value::Bool(false)),
                    BinOp::Or if at => return Ok(Value::Bool(true)),
                    BinOp::Implies if !at => return Ok(Value::Bool(true)),
                    _ => {}
                }
                let bv = eval_expr(b, resolve)?;
                require_type(&bv, "boolean", name)?;
                return Ok(bv);
            }
            let av = eval_expr(a, resolve)?;
            let bv = eval_expr(b, resolve)?;
            match op {
                BinOp::Eq => return Ok(Value::Bool(av.strict_eq(&bv))),
                BinOp::Ne => return Ok(Value::Bool(!av.strict_eq(&bv))),
                _ => {}
            }
            if op == BinOp::Add {
                if let (Value::String(x), Value::String(y)) = (&av, &bv) {
                    let mut s = String::with_capacity(x.len() + y.len());
                    s.push_str(x);
                    s.push_str(y);
                    return Ok(Value::String(s));
                }
            }
            require_type(&av, "number", name)?;
            require_type(&bv, "number", name)?;
            let x = av.as_number().unwrap_or(f64::NAN);
            let y = bv.as_number().unwrap_or(f64::NAN);
            match op {
                BinOp::Lt => Ok(Value::Bool(x < y)),
                BinOp::Le => Ok(Value::Bool(x <= y)),
                BinOp::Gt => Ok(Value::Bool(x > y)),
                BinOp::Ge => Ok(Value::Bool(x >= y)),
                BinOp::Add => checked(integer, x, y, x + y),
                BinOp::Sub => checked(integer, x, y, x - y),
                BinOp::Mul => checked(integer, x, y, x * y),
                BinOp::Div | BinOp::Rem if y == 0.0 => Err(ExprError::eval("Division by zero")),
                BinOp::Div => checked(integer, x, y, x / y),
                // Rust's f64 `%` is fmod, like JavaScript's: the sign of the dividend.
                BinOp::Rem => checked(integer, x, y, x % y),
                _ => Err(ExprError::eval("Malformed expression")),
            }
        }
    }
}

/// Parse and evaluate in one call.
pub fn evaluate(src: &str, resolve: &dyn Fn(&[String]) -> Value) -> Result<Value, ExprError> {
    eval_expr(&parse_expr(src)?, resolve)
}

/// All reference paths an expression uses.
pub fn expr_refs(ast: &Ast) -> Vec<Vec<String>> {
    fn walk(n: &Ast, out: &mut Vec<Vec<String>>) {
        match n {
            Ast::Lit(_) => {}
            Ast::Ref { path, .. } => out.push(path.clone()),
            Ast::Un { a, .. } => walk(a, out),
            Ast::Bin { a, b, .. } => {
                walk(a, out);
                walk(b, out);
            }
        }
    }
    let mut out = Vec::new();
    walk(ast, &mut out);
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::JsObject;

    fn scope(path: &[String]) -> Value {
        match path
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>()
            .as_slice()
        {
            ["a"] => Value::Number(7.0),
            ["b"] => Value::Number(2.0),
            ["s"] => Value::str("ab"),
            ["t"] => Value::Bool(true),
            ["n"] => Value::Null,
            ["o"] => Value::object(JsObject::new()),
            ["event", "amount"] => Value::Number(150.0),
            ["ledger-machine", "state"] => Value::str("ledger-open"),
            _ => Value::Undefined,
        }
    }

    fn ev(src: &str) -> Result<Value, String> {
        evaluate(src, &scope).map_err(|e| e.message)
    }

    fn num(src: &str) -> f64 {
        match ev(src) {
            Ok(Value::Number(n)) => n,
            other => panic!("{src}: expected a number, got {other:?}"),
        }
    }

    fn boolean(src: &str) -> bool {
        match ev(src) {
            Ok(Value::Bool(b)) => b,
            other => panic!("{src}: expected a boolean, got {other:?}"),
        }
    }

    fn parse_err(src: &str) -> String {
        match parse_expr(src) {
            Err(e) => e.message,
            Ok(ast) => panic!("{src}: expected a parse error, got {ast:?}"),
        }
    }

    #[test]
    fn arithmetic_is_double_arithmetic() {
        assert_eq!(num("a + b"), 9.0);
        assert_eq!(num("a - b"), 5.0);
        assert_eq!(num("a * b"), 14.0);
        assert_eq!(num("a / b"), 3.5);
        assert_eq!(num("a % b"), 1.0);
        assert_eq!(num("-a"), -7.0);
        assert_eq!(num("a - -b"), 9.0);
        assert_eq!(num("0.1 + 0.2"), 0.1 + 0.2);
        assert_eq!(num("0.1 + 0.2"), 0.300_000_000_000_000_04);
    }

    #[test]
    fn remainder_has_the_sign_of_the_dividend() {
        assert_eq!(num("-7 % 3"), -1.0);
        assert_eq!(num("7 % -3"), 1.0);
        assert_eq!(num("5.5 % 2"), 1.5);
    }

    #[test]
    fn precedence() {
        assert_eq!(num("1 + 2 * 3 - 8 / 4 % 3"), 5.0);
        assert_eq!(num("(1 + 2) * 3"), 9.0);
        assert!(boolean("true || false && false"));
        assert!(boolean("1 + 1 == 2 && 3 > 2"));
        assert!(!boolean("!t || b >= 3"));
        assert!(boolean("1 < 2 == true"));
    }

    #[test]
    fn left_associativity() {
        assert_eq!(num("10 - 4 - 3"), 3.0);
        assert_eq!(num("24 / 4 / 2"), 3.0);
        assert_eq!(num("17 % 10 % 4"), 3.0);
    }

    #[test]
    fn implication_is_right_associative() {
        assert!(boolean("t => false => true"));
        // (false => false) => false is false; false => (false => false) is true.
        assert!(boolean("false => false => false"));
        assert!(!boolean("t => false"));
        assert!(boolean("false => t"));
    }

    #[test]
    fn short_circuit_skips_evaluation_and_type_checks() {
        assert!(!boolean("false && 1 / 0 > 1"));
        assert!(boolean("true || 1 / 0 > 1"));
        assert!(boolean("false => 1 / 0 > 1"));
        assert!(!boolean("false && 5"));
        assert!(boolean("true || 'x'"));
    }

    #[test]
    fn strings_and_strict_equality() {
        assert!(matches!(ev("s + \"cd\" + 'ef'"), Ok(Value::String(s)) if s == "abcdef"));
        assert!(boolean("s == 'ab'"));
        assert!(!boolean("1 == '1'"));
        assert!(boolean("null == null"));
        assert!(boolean("n == null"));
        assert!(boolean("a != 8"));
        assert!(boolean("ledger-machine.state == 'ledger-open'"));
        assert!(boolean("event.amount >= 100"));
    }

    #[test]
    fn objects_compare_by_identity() {
        let shared = Value::object(JsObject::new());
        let s2 = shared.clone();
        let resolve = move |p: &[String]| match p[0].as_str() {
            "x" | "y" => s2.clone(),
            "z" => Value::object(JsObject::new()),
            _ => Value::Undefined,
        };
        assert!(matches!(
            evaluate("x == y", &resolve),
            Ok(Value::Bool(true))
        ));
        assert!(matches!(
            evaluate("x == z", &resolve),
            Ok(Value::Bool(false))
        ));
        drop(shared);
    }

    #[test]
    fn type_error_messages() {
        assert_eq!(
            ev("s - 1").unwrap_err(),
            "Operator \"-\" needs a number, got string"
        );
        assert_eq!(
            ev("-s").unwrap_err(),
            "Operator \"-\" needs a number, got string"
        );
        assert_eq!(
            ev("!a").unwrap_err(),
            "Operator \"!\" needs a boolean, got number"
        );
        assert_eq!(
            ev("a && t").unwrap_err(),
            "Operator \"&&\" needs a boolean, got number"
        );
        assert_eq!(
            ev("n || t").unwrap_err(),
            "Operator \"||\" needs a boolean, got null"
        );
        assert_eq!(
            ev("t => s").unwrap_err(),
            "Operator \"=>\" needs a boolean, got string"
        );
        assert_eq!(
            ev("a + s").unwrap_err(),
            "Operator \"+\" needs a number, got string"
        );
        assert_eq!(
            ev("s + a").unwrap_err(),
            "Operator \"+\" needs a number, got string"
        );
        assert_eq!(
            ev("o < 1").unwrap_err(),
            "Operator \"<\" needs a number, got object"
        );
        assert_eq!(
            ev("t * 2").unwrap_err(),
            "Operator \"*\" needs a number, got boolean"
        );
    }

    #[test]
    fn division_and_modulo_by_zero() {
        assert_eq!(ev("a / 0").unwrap_err(), "Division by zero");
        assert_eq!(ev("a % 0").unwrap_err(), "Division by zero");
        assert_eq!(ev("a / -0").unwrap_err(), "Division by zero");
    }

    #[test]
    fn unknown_references() {
        assert_eq!(
            ev("missing + 1").unwrap_err(),
            "Unknown reference \"missing\""
        );
        assert_eq!(
            ev("event.nope").unwrap_err(),
            "Unknown reference \"event.nope\""
        );
        assert_eq!(ev("a.b.c").unwrap_err(), "Unknown reference \"a.b.c\"");
    }

    #[test]
    fn identifiers_take_inner_hyphens_only() {
        assert_eq!(num("a - b"), 5.0);
        // "a-b" is one name, so it is an unknown reference.
        assert_eq!(ev("a-b").unwrap_err(), "Unknown reference \"a-b\"");
        // A trailing hyphen is not part of the name: "a-" then "-" ... is a binary minus.
        assert_eq!(num("a- 2"), 5.0);
    }

    #[test]
    fn parse_error_messages() {
        assert_eq!(parse_err("'abc"), "Unterminated string literal");
        assert_eq!(parse_err("a = b"), "Unexpected character '='");
        assert_eq!(parse_err("a +"), "Unexpected end of expression");
        assert_eq!(parse_err("a b"), "Unexpected \"b\"");
        assert_eq!(parse_err("1 2.50"), "Unexpected \"2.5\"");
        assert_eq!(parse_err("a."), "Expected a name after \".\"");
        assert_eq!(parse_err("(a"), "Expected \")\"");
        assert_eq!(parse_err(")"), "Unexpected \")\"");
        assert_eq!(parse_err(""), "Unexpected end of expression");
    }

    #[test]
    fn refs_are_listed() {
        let ast = parse_expr("a + ledger-machine.balance > event.amount").map_err(|e| e.message);
        let refs = expr_refs(&ast.unwrap_or(Ast::Lit(Value::Null)));
        assert_eq!(
            refs,
            vec![
                vec!["a".to_string()],
                vec!["ledger-machine".to_string(), "balance".to_string()],
                vec!["event".to_string(), "amount".to_string()],
            ]
        );
    }
}
