//! JSON-like values with the semantics of the JavaScript values the reference engine holds.
//!
//! - Numbers are IEEE 754 doubles, whatever their spelling in the input.
//! - Objects keep JavaScript's property order (array-index keys first, ascending, then the
//!   other keys in insertion order), so iterating an object visits its entries in the order
//!   `Object.entries` would.
//! - Arrays and objects are shared by reference (`Rc`), and `===` on them is reference
//!   identity, exactly as in JavaScript. [`Value::deep_copy`] makes fresh references; the
//!   engine calls it where the reference engine calls `deepCopy`.
//! - `Undefined` exists only where JavaScript can hold `undefined` (a variable declared without
//!   an initial value). JSON output omits it as an object property and writes `null` for it in
//!   an array, as `JSON.stringify` does.

use std::fmt;
use std::rc::Rc;

use serde::de::{Deserialize, Deserializer, MapAccess, SeqAccess, Visitor};

/// A value of the simulation: a variable's value, a payload, or an expression result.
#[derive(Clone, Debug)]
pub enum Value {
    Undefined,
    Null,
    Bool(bool),
    Number(f64),
    String(String),
    Array(Rc<Vec<Value>>),
    Object(Rc<JsObject>),
}

/// An object with JavaScript property order.
#[derive(Clone, Debug, Default)]
pub struct JsObject {
    entries: Vec<(Rc<str>, Value)>,
}

/// True for a canonical array index ("0", "1", ... up to 2^32 - 2), which JavaScript orders
/// before every other property key.
fn array_index(key: &str) -> Option<u32> {
    if key.is_empty() || key.len() > 10 || !key.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    if key.len() > 1 && key.starts_with('0') {
        return None;
    }
    let n: u64 = key.parse().ok()?;
    if n < u64::from(u32::MAX) {
        u32::try_from(n).ok()
    } else {
        None
    }
}

impl JsObject {
    pub fn new() -> Self {
        Self::default()
    }

    /// The value of an own property, if present (`hasOwn(o, k) ? o[k] : undefined`).
    pub fn get(&self, key: &str) -> Option<&Value> {
        self.entries
            .iter()
            .find(|(k, _)| &**k == key)
            .map(|(_, v)| v)
    }

    pub fn get_mut(&mut self, key: &str) -> Option<&mut Value> {
        self.entries
            .iter_mut()
            .find(|(k, _)| &**k == key)
            .map(|(_, v)| v)
    }

    pub fn contains_key(&self, key: &str) -> bool {
        self.entries.iter().any(|(k, _)| &**k == key)
    }

    /// `o[key] = value`: an existing property keeps its position, a new one goes where
    /// JavaScript would put it.
    pub fn insert(&mut self, key: impl Into<Rc<str>>, value: Value) {
        let key = key.into();
        if let Some(slot) = self.get_mut(&key) {
            *slot = value;
            return;
        }
        let pos = match array_index(&key) {
            Some(n) => self
                .entries
                .iter()
                .position(|(k, _)| array_index(k).is_none_or(|m| m > n))
                .unwrap_or(self.entries.len()),
            None => self.entries.len(),
        };
        self.entries.insert(pos, (key, value));
    }

    /// Entries in `Object.entries` order.
    pub fn iter(&self) -> impl Iterator<Item = (&Rc<str>, &Value)> {
        self.entries.iter().map(|(k, v)| (k, v))
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// A deep copy: every nested array and object is a fresh reference.
    pub fn deep_copy(&self) -> JsObject {
        JsObject {
            entries: self
                .entries
                .iter()
                .map(|(k, v)| (k.clone(), v.deep_copy()))
                .collect(),
        }
    }
}

impl Value {
    pub fn object(o: JsObject) -> Value {
        Value::Object(Rc::new(o))
    }

    pub fn array(items: Vec<Value>) -> Value {
        Value::Array(Rc::new(items))
    }

    pub fn str(s: impl Into<String>) -> Value {
        Value::String(s.into())
    }

    /// The reference engine's `deepCopy`: fresh arrays and objects, primitives as they are.
    pub fn deep_copy(&self) -> Value {
        match self {
            Value::Array(items) => Value::array(items.iter().map(Value::deep_copy).collect()),
            Value::Object(o) => Value::object(o.deep_copy()),
            other => other.clone(),
        }
    }

    /// Whether the value has a reference identity (an array or an object).
    pub fn has_identity(&self) -> bool {
        matches!(self, Value::Array(_) | Value::Object(_))
    }

    /// Whether an array or object value holds an element that has an identity.
    pub fn has_nested_identity(&self) -> bool {
        match self {
            Value::Array(xs) => xs.iter().any(Value::has_identity),
            Value::Object(o) => o.iter().any(|(_, v)| v.has_identity()),
            _ => false,
        }
    }

    /// JavaScript's `typeof`, with `null` reported as `"null"` (as the error messages do).
    pub fn type_name(&self) -> &'static str {
        match self {
            Value::Undefined => "undefined",
            Value::Null => "null",
            Value::Bool(_) => "boolean",
            Value::Number(_) => "number",
            Value::String(_) => "string",
            Value::Array(_) | Value::Object(_) => "object",
        }
    }

    /// The expression language's equality (`==`), structural since WG-4902 (`Value.eqv` in
    /// `formal/Exegra/Value.lean`): arrays element by element, objects by their keys and members
    /// in any order. The engine does not read declared types, so its arithmetic stays untyped.
    pub fn strict_eq(&self, other: &Value) -> bool {
        match (self, other) {
            (Value::Undefined, Value::Undefined) | (Value::Null, Value::Null) => true,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            // f64 `==` is JavaScript's: NaN differs from itself, 0 equals -0.
            (Value::Number(a), Value::Number(b)) => a == b,
            (Value::String(a), Value::String(b)) => a == b,
            (Value::Array(a), Value::Array(b)) => {
                a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| x.strict_eq(y))
            }
            (Value::Object(a), Value::Object(b)) => {
                a.len() == b.len()
                    && a.iter()
                        .all(|(k, x)| b.get(k).is_some_and(|y| x.strict_eq(y)))
            }
            _ => false,
        }
    }

    pub fn as_str(&self) -> Option<&str> {
        match self {
            Value::String(s) => Some(s),
            _ => None,
        }
    }

    pub fn as_number(&self) -> Option<f64> {
        match self {
            Value::Number(n) => Some(*n),
            _ => None,
        }
    }

    pub fn as_object(&self) -> Option<&JsObject> {
        match self {
            Value::Object(o) => Some(o),
            _ => None,
        }
    }

    /// `x === undefined || x === null`, the test behind `??`.
    pub fn is_nullish(&self) -> bool {
        matches!(self, Value::Undefined | Value::Null)
    }

    /// JSON text, as `JSON.stringify` writes it (compact).
    pub fn to_json(&self) -> String {
        let mut out = String::new();
        self.write_json(&mut out);
        out
    }

    pub fn write_json(&self, out: &mut String) {
        match self {
            Value::Undefined | Value::Null => out.push_str("null"),
            Value::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
            Value::Number(n) => write_json_number(*n, out),
            Value::String(s) => write_json_string(s, out),
            Value::Array(items) => {
                out.push('[');
                for (i, v) in items.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    v.write_json(out);
                }
                out.push(']');
            }
            Value::Object(o) => write_json_object(o, out),
        }
    }
}

/// An object as JSON; properties whose value is undefined are left out.
pub fn write_json_object(o: &JsObject, out: &mut String) {
    out.push('{');
    let mut first = true;
    for (k, v) in o.iter() {
        if matches!(v, Value::Undefined) {
            continue;
        }
        if !first {
            out.push(',');
        }
        first = false;
        write_json_string(k, out);
        out.push(':');
        v.write_json(out);
    }
    out.push('}');
}

/// A number as `JSON.stringify` writes it: non-finite values become `null`.
pub fn write_json_number(n: f64, out: &mut String) {
    if n.is_finite() {
        out.push_str(&js_number_to_string(n));
    } else {
        out.push_str("null");
    }
}

/// A string as JSON, with the escapes `JSON.stringify` uses.
pub fn write_json_string(s: &str, out: &mut String) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{8}' => out.push_str("\\b"),
            '\u{c}' => out.push_str("\\f"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
}

/// JavaScript's `Number.prototype.toString()` for a double: the shortest digits that round-trip,
/// plain notation for magnitudes in [1e-6, 1e21), exponent notation (`1e+21`, `1.5e-7`) outside.
pub fn js_number_to_string(n: f64) -> String {
    if n.is_nan() {
        return "NaN".to_string();
    }
    if n.is_infinite() {
        return if n > 0.0 { "Infinity" } else { "-Infinity" }.to_string();
    }
    if n == 0.0 {
        return "0".to_string();
    }
    let a = n.abs();
    if (1e-6..1e21).contains(&a) {
        // Rust's Display prints the shortest round-trip digits without an exponent.
        return format!("{n}");
    }
    let s = format!("{n:e}");
    match s.split_once('e') {
        Some((mantissa, exp)) if exp.starts_with('-') => format!("{mantissa}e{exp}"),
        Some((mantissa, exp)) => format!("{mantissa}e+{exp}"),
        None => s,
    }
}

/// JavaScript's `String(v)` for the values that can reach a refusal message.
pub fn js_display(v: &Value) -> String {
    match v {
        Value::Undefined => "undefined".to_string(),
        Value::Null => "null".to_string(),
        Value::Bool(b) => b.to_string(),
        Value::Number(n) => js_number_to_string(*n),
        Value::String(s) => s.clone(),
        Value::Array(items) => items
            .iter()
            .map(|x| {
                if x.is_nullish() {
                    String::new()
                } else {
                    js_display(x)
                }
            })
            .collect::<Vec<_>>()
            .join(","),
        Value::Object(_) => "[object Object]".to_string(),
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_json())
    }
}

// ---- parsing (JSON.parse semantics) ---------------------------------------------------------

struct ValueVisitor;

impl<'de> Visitor<'de> for ValueVisitor {
    type Value = Value;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("a JSON value")
    }

    fn visit_bool<E>(self, v: bool) -> Result<Value, E> {
        Ok(Value::Bool(v))
    }

    // Integers are exact in u64/i64; `as f64` rounds them to the nearest double, which is the
    // double JSON.parse gives for the same digits.
    fn visit_i64<E>(self, v: i64) -> Result<Value, E> {
        Ok(Value::Number(v as f64))
    }

    fn visit_u64<E>(self, v: u64) -> Result<Value, E> {
        Ok(Value::Number(v as f64))
    }

    fn visit_f64<E>(self, v: f64) -> Result<Value, E> {
        Ok(Value::Number(v))
    }

    fn visit_str<E>(self, v: &str) -> Result<Value, E> {
        Ok(Value::String(v.to_string()))
    }

    fn visit_string<E>(self, v: String) -> Result<Value, E> {
        Ok(Value::String(v))
    }

    fn visit_unit<E>(self) -> Result<Value, E> {
        Ok(Value::Null)
    }

    fn visit_none<E>(self) -> Result<Value, E> {
        Ok(Value::Null)
    }

    fn visit_some<D: Deserializer<'de>>(self, d: D) -> Result<Value, D::Error> {
        Deserialize::deserialize(d)
    }

    fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Value, A::Error> {
        let mut items = Vec::new();
        while let Some(v) = seq.next_element::<Value>()? {
            items.push(v);
        }
        Ok(Value::array(items))
    }

    // Duplicate keys: the last value wins, at the first key's position, as in JSON.parse.
    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Value, A::Error> {
        let mut o = JsObject::new();
        while let Some(k) = map.next_key::<String>()? {
            let v = map.next_value::<Value>()?;
            o.insert(k, v);
        }
        Ok(Value::object(o))
    }
}

impl<'de> Deserialize<'de> for Value {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Value, D::Error> {
        d.deserialize_any(ValueVisitor)
    }
}

/// Parse JSON text into a [`Value`].
pub fn parse_json(text: &str) -> Result<Value, String> {
    serde_json::from_str::<Value>(text).map_err(|e| format!("the input is not JSON: {e}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn numbers_print_like_javascript() {
        assert_eq!(js_number_to_string(3.0), "3");
        assert_eq!(js_number_to_string(0.1 + 0.2), "0.30000000000000004");
        assert_eq!(js_number_to_string(-0.0), "0");
        assert_eq!(js_number_to_string(1e21), "1e+21");
        assert_eq!(js_number_to_string(1.5e-7), "1.5e-7");
        assert_eq!(js_number_to_string(123456.5), "123456.5");
    }

    #[test]
    fn object_order_follows_javascript() {
        let mut o = JsObject::new();
        o.insert("b", Value::Null);
        o.insert("2", Value::Null);
        o.insert("a", Value::Null);
        o.insert("1", Value::Null);
        o.insert("b", Value::Bool(true));
        let keys: Vec<&str> = o.iter().map(|(k, _)| k.as_str()).collect();
        assert_eq!(keys, ["1", "2", "b", "a"]);
        assert!(o.get("b").is_some_and(|v| v.strict_eq(&Value::Bool(true))));
    }

    #[test]
    fn equality_is_structural() {
        let v = Value::object(JsObject::new());
        assert!(v.strict_eq(&v.clone()));
        assert!(v.strict_eq(&v.deep_copy()));
    }

    #[test]
    fn undefined_properties_are_omitted() {
        let mut o = JsObject::new();
        o.insert("a", Value::Undefined);
        o.insert("b", Value::Number(1.0));
        assert_eq!(Value::object(o).to_json(), r#"{"b":1}"#);
    }
}
