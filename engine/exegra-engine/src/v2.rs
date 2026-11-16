//! Format 2 of the engine input and trace, the WG-4664 part: integer time in a declared unit,
//! counted and keyed instances with routes, resources (`use`, `acquire`, `release`, class queues,
//! bounds, overflow, demand factors) and seeded SplitMix64 streams.
//!
//! This is a port of `formal/Exegra/Format2.lean` and `formal/Exegra/Resource.lean`, which define
//! it; the differential check (`tools/differential.js`) compares the two. Comments marked ORDER
//! note where an order decides an observable result. Not here yet (refused when present): links,
//! workloads, timers, meters, request classes, prices, windowed and resource faults and
//! `crash-instance`.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::expr::{eval_expr, expr_refs, parse_expr, Ast};
use crate::random;
use crate::value::{JsObject, Value};

type R<T> = Result<T, String>;

const TWO53: u64 = 1 << 53;
const TWO32: u64 = 1 << 32;

// ---- Input ----------------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub enum Dist {
    Fixed(u64),
    Uniform(u64, u64),
    Table(Vec<(u64, u64)>),
    Choice(Vec<u64>),
}

impl Dist {
    fn draws(&self) -> bool {
        matches!(self, Dist::Uniform(..) | Dist::Table(_))
    }
}

#[derive(Clone, Debug)]
pub enum Instances {
    Single,
    Count(u64),
    Keyed { field: String, max: u64 },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReqKind {
    Use,
    Acquire,
}

#[derive(Clone, Debug)]
pub enum Effect {
    Set {
        var: String,
        to: Option<Value>,
    },
    Sample {
        var: String,
        dist: Dist,
    },
    Emit {
        event: String,
        after: Dist,
        payload: JsObject,
        reply: bool,
    },
    Request {
        kind: ReqKind,
        res: String,
        class: Option<String>,
        units: u64,
        demand: Dist,
        then: String,
        refused: Option<String>,
        payload: JsObject,
    },
    Release {
        res: String,
        class: Option<String>,
        units: u64,
    },
    Malformed,
}

#[derive(Clone, Debug)]
pub struct Transition {
    pub id: String,
    pub from: String,
    pub to: String,
    pub on: String,
    pub guard: Option<String>,
    pub effects: Vec<Effect>,
    pub fault_only: bool,
}

#[derive(Clone, Debug)]
pub struct Behavior {
    pub id: String,
    pub subject: Option<String>,
    pub initial: String,
    pub variables: Vec<(String, Value)>,
    pub transitions: Vec<Transition>,
    pub instances: Instances,
}

#[derive(Clone, Debug)]
pub struct Route {
    pub event: String,
    pub behavior: String,
    pub by: String,
    pub field: Option<String>,
    pub resource: Option<String>,
}

#[derive(Clone, Debug)]
pub enum Occurrence {
    Any,
    Exactly(f64),
    Never,
}

#[derive(Clone, Debug)]
pub struct Fault {
    pub id: String,
    pub kind: Option<String>,
    pub event: Option<String>,
    pub transition: Option<String>,
    pub occurrence: Occurrence,
    pub by: u64,
    pub at: u64,
    pub payload: Value,
}

impl Fault {
    fn is_kind(&self, k: &str) -> bool {
        self.kind.as_deref() == Some(k)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Overflow {
    Refuse,
    Drop,
    ShedOldest,
}

#[derive(Clone, Debug)]
pub enum DemandFactor {
    None,
    Table(Vec<(u64, u64, u64)>),
    Usl(u64, u64, u64, u64),
}

#[derive(Clone, Debug)]
pub struct Class {
    pub id: String,
    pub priority: i64,
    pub reserved: u64,
    pub limit: Option<u64>,
    pub queue_bound: Option<u64>,
    pub max_wait: Option<u64>,
}

#[derive(Clone, Debug)]
pub struct Resource {
    pub id: String,
    pub kind: String,
    pub capacity: u64,
    pub by_priority: bool,
    pub queue_bound: Option<u64>,
    pub overflow: Overflow,
    pub demand_factor: DemandFactor,
    pub classes: Vec<Class>,
}

#[derive(Clone, Debug)]
pub struct Step {
    pub at: u64,
    pub event: String,
    pub payload: Value,
    pub target: Option<(String, Value)>,
}

#[derive(Clone, Debug)]
pub struct Scenario {
    pub id: String,
    pub steps: Vec<Step>,
    pub faults: Vec<String>,
    pub step_limit: u64,
    pub seed: Option<u64>,
    pub horizon: Option<u64>,
    pub warmup: Option<u64>,
    pub stop_at: Option<u64>,
    pub output: String,
}

#[derive(Clone, Debug)]
pub struct Input {
    pub unit: String,
    pub per_second: Option<u64>,
    pub scenario: Scenario,
    pub behaviors: Vec<Behavior>,
    pub events: Vec<String>,
    pub faults: Vec<Fault>,
    pub routes: Vec<Route>,
    pub resources: Vec<Resource>,
}

// ---- Decoding -------------------------------------------------------------------------------

fn field<'v>(o: &'v JsObject, key: &str) -> &'v Value {
    o.get(key).unwrap_or(&Value::Undefined)
}

fn object<'v>(v: &'v Value, what: &str) -> R<&'v JsObject> {
    v.as_object()
        .ok_or_else(|| format!("{what} must be an object."))
}

fn string(o: &JsObject, key: &str, what: &str) -> R<String> {
    match field(o, key) {
        Value::String(s) => Ok(s.clone()),
        _ => Err(format!("{what}: \"{key}\" must be a string.")),
    }
}

fn array<'v>(o: &'v JsObject, key: &str, what: &str) -> R<&'v [Value]> {
    match field(o, key) {
        Value::Array(xs) => Ok(xs.as_slice()),
        _ => Err(format!("{what}: \"{key}\" must be an array.")),
    }
}

fn array_or_empty<'v>(o: &'v JsObject, key: &str) -> &'v [Value] {
    match field(o, key) {
        Value::Array(xs) => xs.as_slice(),
        _ => &[],
    }
}

fn payload_or_empty(v: &Value) -> Value {
    if v.is_nullish() {
        Value::object(JsObject::new())
    } else {
        v.clone()
    }
}

fn int_in(v: &Value, path: &str, lo: u64, hi: u64) -> R<u64> {
    match v {
        Value::Number(x) if x.floor() == *x && *x >= lo as f64 && *x <= hi as f64 => Ok(*x as u64),
        _ => Err(format!(
            "Field \"{path}\" must be an integer in [{lo}, {hi}]."
        )),
    }
}

fn opt_int(o: &JsObject, key: &str, path: &str, lo: u64, hi: u64) -> R<Option<u64>> {
    match field(o, key) {
        Value::Undefined | Value::Null => Ok(None),
        v => int_in(v, path, lo, hi).map(Some),
    }
}

fn int_or(o: &JsObject, key: &str, path: &str, lo: u64, hi: u64, d: u64) -> R<u64> {
    Ok(opt_int(o, key, path, lo, hi)?.unwrap_or(d))
}

fn opt_str(o: &JsObject, key: &str, what: &str) -> R<Option<String>> {
    match field(o, key) {
        Value::Undefined | Value::Null => Ok(None),
        Value::String(s) => Ok(Some(s.clone())),
        _ => Err(format!("{what}: \"{key}\" must be a string.")),
    }
}

fn payload_obj(o: &JsObject, what: &str) -> R<JsObject> {
    match field(o, "payload") {
        Value::Object(fs) => Ok((**fs).clone()),
        x if x.is_nullish() => Ok(JsObject::new()),
        _ => Err(format!("{what}: \"payload\" must be an object.")),
    }
}

fn decode_dist(v: &Value, path: &str) -> R<Dist> {
    match v {
        Value::Number(_) => Ok(Dist::Fixed(int_in(v, path, 0, TWO53 - 1)?)),
        Value::Object(o) => match field(o, "kind").as_str() {
            Some("fixed") => Ok(Dist::Fixed(int_in(
                field(o, "value"),
                &format!("{path}.value"),
                0,
                TWO53 - 1,
            )?)),
            Some("uniform") => {
                let lo = int_in(field(o, "lo"), &format!("{path}.lo"), 0, TWO53 - 1)?;
                let hi = int_in(field(o, "hi"), &format!("{path}.hi"), lo, TWO53 - 1)?;
                Ok(Dist::Uniform(lo, hi))
            }
            Some("table") => {
                let malformed = || format!("Distribution \"{path}\" has a malformed table.");
                let Value::Array(xs) = field(o, "points") else {
                    return Err(malformed());
                };
                let mut pts = Vec::new();
                for (i, p) in xs.iter().enumerate() {
                    match p {
                        Value::Array(pair) if pair.len() == 2 => {
                            let u = int_in(&pair[0], &format!("{path}.points[{i}][0]"), 0, TWO32)?;
                            let x =
                                int_in(&pair[1], &format!("{path}.points[{i}][1]"), 0, TWO53 - 1)?;
                            pts.push((u, x));
                        }
                        _ => return Err(malformed()),
                    }
                }
                let incr = pts.windows(2).all(|w| w[0].0 < w[1].0);
                let nondec = pts.windows(2).all(|w| w[0].1 <= w[1].1);
                if pts.first().map(|p| p.0) != Some(0)
                    || pts.last().map(|p| p.0) != Some(TWO32)
                    || !incr
                    || !nondec
                {
                    return Err(malformed());
                }
                Ok(Dist::Table(pts))
            }
            Some("choice") => {
                let missing = || format!("Distribution \"{path}\" must have \"values\".");
                let Value::Array(xs) = field(o, "values") else {
                    return Err(missing());
                };
                let mut vs = Vec::new();
                for (i, x) in xs.iter().enumerate() {
                    vs.push(int_in(x, &format!("{path}.values[{i}]"), 0, TWO53 - 1)?);
                }
                if vs.is_empty() {
                    return Err(missing());
                }
                Ok(Dist::Choice(vs))
            }
            _ => Err(format!("Distribution \"{path}\" has an unknown kind.")),
        },
        _ => Err(format!(
            "Field \"{path}\" must be an integer or a distribution."
        )),
    }
}

fn decode_effect(v: &Value, what: &str) -> R<Effect> {
    let Value::Object(fx) = v else {
        return Ok(Effect::Malformed);
    };
    if fx.contains_key("set") {
        let var = string(fx, "set", what)?;
        return match field(fx, "to") {
            Value::Object(o) if o.contains_key("sample") => Ok(Effect::Sample {
                var,
                dist: decode_dist(field(o, "sample"), &format!("{what}.to.sample"))?,
            }),
            Value::Undefined => Ok(Effect::Set { var, to: None }),
            other => Ok(Effect::Set {
                var,
                to: Some(other.clone()),
            }),
        };
    }
    if fx.contains_key("emit") {
        let after = match field(fx, "after") {
            Value::Undefined | Value::Null => Dist::Fixed(0),
            x => decode_dist(x, &format!("{what}.after"))?,
        };
        let payload = payload_obj(fx, what)?;
        let event = string(fx, "emit", what)?;
        let reply = match field(fx, "target") {
            Value::Undefined | Value::Null => false,
            Value::String(s) if s == "reply" => true,
            _ => return Err(format!("{what}: \"target\" must be \"reply\".")),
        };
        return Ok(Effect::Emit {
            event,
            after,
            payload,
            reply,
        });
    }
    if fx.contains_key("use") || fx.contains_key("acquire") {
        let kind = if fx.contains_key("use") {
            ReqKind::Use
        } else {
            ReqKind::Acquire
        };
        let res = string(
            fx,
            if kind == ReqKind::Use {
                "use"
            } else {
                "acquire"
            },
            what,
        )?;
        let class = opt_str(fx, "class", what)?;
        let units = int_or(fx, "units", &format!("{what}.units"), 1, TWO32 - 1, 1)?;
        let demand = if kind == ReqKind::Use {
            decode_dist(field(fx, "demand"), &format!("{what}.demand"))?
        } else {
            Dist::Fixed(0)
        };
        let then = string(fx, "then", what)?;
        let refused = opt_str(fx, "refused", what)?;
        let payload = payload_obj(fx, what)?;
        return Ok(Effect::Request {
            kind,
            res,
            class,
            units,
            demand,
            then,
            refused,
            payload,
        });
    }
    if fx.contains_key("release") {
        let res = string(fx, "release", what)?;
        let class = opt_str(fx, "class", what)?;
        let units = int_or(fx, "units", &format!("{what}.units"), 1, TWO32 - 1, 1)?;
        return Ok(Effect::Release { res, class, units });
    }
    Ok(Effect::Malformed)
}

fn decode_transition(v: &Value, what: &str) -> R<Transition> {
    let t = object(v, what)?;
    let mut effects = Vec::new();
    for (k, fx) in array_or_empty(t, "effects").iter().enumerate() {
        effects.push(decode_effect(fx, &format!("{what}.effects[{k}]"))?);
    }
    Ok(Transition {
        id: string(t, "id", what)?,
        from: string(t, "from", what)?,
        to: string(t, "to", what)?,
        on: string(t, "on", what)?,
        guard: field(t, "guard").as_str().map(str::to_string),
        effects,
        fault_only: matches!(field(t, "faultOnly"), Value::Bool(true)),
    })
}

fn decode_behavior(v: &Value, i: usize) -> R<Behavior> {
    let what = format!("behaviors[{i}]");
    let b = object(v, &what)?;
    let id = string(b, "id", &what)?;
    let mut variables = Vec::new();
    for (j, var) in array_or_empty(b, "variables").iter().enumerate() {
        let vw = format!("{what}.variables[{j}]");
        let o = object(var, &vw)?;
        variables.push((string(o, "name", &vw)?, field(o, "initial").clone()));
    }
    let mut transitions = Vec::new();
    for (j, t) in array_or_empty(b, "transitions").iter().enumerate() {
        transitions.push(decode_transition(t, &format!("{what}.transitions[{j}]"))?);
    }
    let subject = field(b, "subject").as_str().map(str::to_string);
    let initial = string(b, "initial", &what)?;
    let instances = match field(b, "instances") {
        Value::Undefined | Value::Null => Instances::Single,
        Value::Object(o) => {
            if o.contains_key("key") {
                let key = string(o, "key", &format!("{what}.instances"))?;
                let max = int_in(
                    field(o, "max"),
                    &format!("{what}.instances.max"),
                    0,
                    TWO32 - 1,
                )?;
                Instances::Keyed { field: key, max }
            } else {
                Instances::Count(int_in(
                    field(o, "count"),
                    &format!("{what}.instances.count"),
                    0,
                    TWO32 - 1,
                )?)
            }
        }
        _ => return Err(format!("{what}: \"instances\" must be an object.")),
    };
    Ok(Behavior {
        id,
        subject,
        initial,
        variables,
        transitions,
        instances,
    })
}

const UNSUPPORTED_FAULTS: [&str; 6] = [
    "scale-demand",
    "set-capacity",
    "set-class-limit",
    "collapse-classes",
    "replace-demand",
    "crash-instance",
];

fn decode_fault(v: &Value, i: usize) -> R<Fault> {
    let what = format!("faults[{i}]");
    let f = object(v, &what)?;
    let kind = opt_str(f, "kind", &what)?;
    if f.contains_key("window") {
        return Err(format!(
            "{what}: windowed faults are not implemented (WG-4664)."
        ));
    }
    if let Some(k) = &kind {
        if UNSUPPORTED_FAULTS.contains(&k.as_str()) {
            return Err(format!(
                "{what}: fault kind \"{k}\" is not implemented (WG-4664)."
            ));
        }
    }
    let occurrence = match field(f, "occurrence") {
        Value::Undefined => Occurrence::Any,
        Value::Number(n) => Occurrence::Exactly(*n),
        _ => Occurrence::Never,
    };
    let by = if kind.as_deref() == Some("delay-event") {
        int_in(field(f, "by"), &format!("{what}.by"), 0, TWO53 - 1)?
    } else {
        0
    };
    let at = if kind.as_deref() == Some("inject-event") {
        int_in(field(f, "at"), &format!("{what}.at"), 0, TWO53 - 1)?
    } else {
        0
    };
    Ok(Fault {
        id: string(f, "id", &what)?,
        event: opt_str(f, "event", &what)?,
        transition: opt_str(f, "transition", &what)?,
        kind,
        occurrence,
        by,
        at,
        payload: payload_or_empty(field(f, "payload")),
    })
}

fn decode_route(v: &Value, i: usize) -> R<Route> {
    let what = format!("routes[{i}]");
    let o = object(v, &what)?;
    let event = string(o, "event", &what)?;
    let behavior = string(o, "behavior", &what)?;
    let by = string(o, "by", &what)?;
    if !["key", "round-robin", "random", "any", "least-busy"].contains(&by.as_str()) {
        return Err(format!(
            "{what}: \"by\" must be key, round-robin, random, any or least-busy."
        ));
    }
    Ok(Route {
        event,
        behavior,
        by,
        field: opt_str(o, "field", &what)?,
        resource: opt_str(o, "resource", &what)?,
    })
}

fn decode_resource(v: &Value, i: usize) -> R<Resource> {
    let what = format!("resources[{i}]");
    let o = object(v, &what)?;
    let id = string(o, "id", &what)?;
    let kind = field(o, "kind").as_str().unwrap_or("pool").to_string();
    let capacity = int_in(
        field(o, "capacity"),
        &format!("{what}.capacity"),
        1,
        TWO32 - 1,
    )?;
    let by_priority = match field(o, "discipline") {
        Value::Undefined | Value::Null => false,
        Value::String(s) if s == "fifo" => false,
        Value::String(s) if s == "priority" => true,
        _ => return Err(format!("{what}: \"discipline\" must be fifo or priority.")),
    };
    let queue_bound = opt_int(o, "queueBound", &format!("{what}.queueBound"), 0, TWO32 - 1)?;
    let overflow = match field(o, "overflow") {
        Value::Undefined | Value::Null => Overflow::Refuse,
        Value::String(s) if s == "refuse" => Overflow::Refuse,
        Value::String(s) if s == "drop" => Overflow::Drop,
        Value::String(s) if s == "shed-oldest" => Overflow::ShedOldest,
        _ => {
            return Err(format!(
                "{what}: \"overflow\" must be refuse, drop or shed-oldest."
            ))
        }
    };
    let malformed = || format!("{what}: malformed \"demandFactor\".");
    let demand_factor = match field(o, "demandFactor") {
        Value::Undefined | Value::Null => DemandFactor::None,
        Value::Array(rows) => {
            let mut rs = Vec::new();
            for (j, r) in rows.iter().enumerate() {
                let p = format!("{what}.demandFactor[{j}]");
                match r {
                    Value::Array(x) if x.len() == 3 => rs.push((
                        int_in(&x[0], &format!("{p}[0]"), 0, TWO32 - 1)?,
                        int_in(&x[1], &format!("{p}[1]"), 0, TWO32 - 1)?,
                        int_in(&x[2], &format!("{p}[2]"), 1, TWO32 - 1)?,
                    )),
                    _ => return Err(malformed()),
                }
            }
            if rs.first().map(|r| r.0) != Some(0) || !rs.windows(2).all(|w| w[0].0 < w[1].0) {
                return Err(malformed());
            }
            DemandFactor::Table(rs)
        }
        Value::Object(u) => match field(u, "usl") {
            Value::Object(p) => {
                let rat = |k: &str| -> R<(u64, u64)> {
                    match field(p, k) {
                        Value::Array(x) if x.len() == 2 => Ok((
                            int_in(
                                &x[0],
                                &format!("{what}.demandFactor.usl.{k}[0]"),
                                0,
                                TWO32 - 1,
                            )?,
                            int_in(
                                &x[1],
                                &format!("{what}.demandFactor.usl.{k}[1]"),
                                1,
                                TWO32 - 1,
                            )?,
                        )),
                        _ => Err(malformed()),
                    }
                };
                let (an, ad) = rat("alpha")?;
                let (bn, bd) = rat("beta")?;
                DemandFactor::Usl(an, ad, bn, bd)
            }
            _ => return Err(malformed()),
        },
        _ => return Err(malformed()),
    };
    let classes = match field(o, "classes") {
        Value::Array(cs) if !cs.is_empty() => {
            let mut out = Vec::new();
            for (j, c) in cs.iter().enumerate() {
                let cw = format!("{what}.classes[{j}]");
                let co = object(c, &cw)?;
                let cid = string(co, "id", &cw)?;
                let perr = || {
                    format!(
                        "Field \"{cw}.priority\" must be an integer in [-4294967295, 4294967295]."
                    )
                };
                let priority = match field(co, "priority") {
                    Value::Undefined | Value::Null => 0,
                    Value::Number(x) if x.floor() == *x && x.abs() < 4_294_967_296.0 => *x as i64,
                    _ => return Err(perr()),
                };
                out.push(Class {
                    id: cid,
                    priority,
                    reserved: int_or(co, "reserved", &format!("{cw}.reserved"), 0, TWO32 - 1, 0)?,
                    limit: opt_int(co, "limit", &format!("{cw}.limit"), 1, TWO32 - 1)?,
                    queue_bound: opt_int(
                        co,
                        "queueBound",
                        &format!("{cw}.queueBound"),
                        0,
                        TWO32 - 1,
                    )?,
                    max_wait: opt_int(co, "maxWait", &format!("{cw}.maxWait"), 0, TWO53 - 1)?,
                });
            }
            out
        }
        _ => vec![Class {
            id: "default".into(),
            priority: 0,
            reserved: 0,
            limit: None,
            queue_bound: None,
            max_wait: None,
        }],
    };
    Ok(Resource {
        id,
        kind,
        capacity,
        by_priority,
        queue_bound,
        overflow,
        demand_factor,
        classes,
    })
}

fn decode_seed(v: &Value) -> R<Option<u64>> {
    let err = || {
        "Field \"scenario.seed\" must be a decimal string in [0, 18446744073709551615].".to_string()
    };
    match v {
        Value::Undefined | Value::Null => Ok(None),
        Value::String(s) => {
            if s.is_empty()
                || !s.bytes().all(|b| b.is_ascii_digit())
                || (s.len() > 1 && s.starts_with('0'))
            {
                return Err(err());
            }
            s.parse::<u64>().map(Some).map_err(|_| err())
        }
        _ => Err(err()),
    }
}

const UNITS: [(&str, Option<u64>); 5] = [
    ("tick", None),
    ("s", Some(1)),
    ("ms", Some(1000)),
    ("us", Some(1_000_000)),
    ("ns", Some(1_000_000_000)),
];

/// Decode a version-2 engine input (format and version already checked).
pub fn decode(root: &JsObject) -> R<Input> {
    let (unit, per_second) = match field(root, "time") {
        Value::Object(t) => match field(t, "unit") {
            Value::String(u) => match UNITS.iter().find(|(n, _)| n == u) {
                Some((n, ps)) => ((*n).to_string(), *ps),
                None => return Err(format!("Unknown time unit \"{u}\".")),
            },
            _ => return Err("Unknown time unit \"undefined\".".into()),
        },
        _ => return Err("Unknown time unit \"undefined\".".into()),
    };
    for k in ["links", "workloads", "requests", "meters", "prices"] {
        if let Value::Array(xs) = field(root, k) {
            if !xs.is_empty() {
                return Err(format!(
                    "Input field \"{k}\" is not implemented by this engine (WG-4715)."
                ));
            }
        }
    }
    let mut events = Vec::new();
    for (i, e) in array(root, "events", "input")?.iter().enumerate() {
        let what = format!("events[{i}]");
        events.push(string(object(e, &what)?, "id", &what)?);
    }
    let mut behaviors = Vec::new();
    for (i, b) in array(root, "behaviors", "input")?.iter().enumerate() {
        behaviors.push(decode_behavior(b, i)?);
    }
    let mut faults = Vec::new();
    for (i, f) in array(root, "faults", "input")?.iter().enumerate() {
        faults.push(decode_fault(f, i)?);
    }
    let mut routes = Vec::new();
    for (i, r) in array_or_empty(root, "routes").iter().enumerate() {
        routes.push(decode_route(r, i)?);
    }
    let mut resources = Vec::new();
    for (i, r) in array_or_empty(root, "resources").iter().enumerate() {
        resources.push(decode_resource(r, i)?);
    }
    let sc = object(field(root, "scenario"), "scenario")?;
    let id = string(sc, "id", "scenario")?;
    let mut steps = Vec::new();
    for (i, st) in array(sc, "steps", "scenario")?.iter().enumerate() {
        let what = format!("scenario.steps[{i}]");
        let o = object(st, &what)?;
        let at = int_in(field(o, "at"), &format!("{what}.at"), 0, TWO53 - 1)?;
        let event = string(o, "event", &what)?;
        let target = match field(o, "target") {
            Value::Object(t) => Some((
                string(t, "behavior", &format!("{what}.target"))?,
                field(t, "instance").clone(),
            )),
            _ => None,
        };
        steps.push(Step {
            at,
            event,
            payload: payload_or_empty(field(o, "payload")),
            target,
        });
    }
    let fault_ids = match field(sc, "faults") {
        Value::Array(xs) => {
            let mut out = Vec::new();
            for x in xs.iter() {
                match x {
                    Value::String(s) => out.push(s.clone()),
                    _ => return Err("scenario.faults must hold strings.".into()),
                }
            }
            out
        }
        x if x.is_nullish() => Vec::new(),
        _ => return Err("scenario: \"faults\" must be an array.".into()),
    };
    let step_limit = int_or(sc, "stepLimit", "scenario.stepLimit", 1, TWO53 - 1, 1000)?;
    let seed = decode_seed(field(sc, "seed"))?;
    let horizon = opt_int(sc, "horizon", "scenario.horizon", 0, TWO53 - 1)?;
    let warmup = opt_int(sc, "warmup", "scenario.warmup", 0, TWO53 - 1)?;
    let stop_at = opt_int(sc, "stopAt", "scenario.stopAt", 0, TWO53 - 1)?;
    let output = field(sc, "output").as_str().unwrap_or("trace").to_string();
    Ok(Input {
        unit,
        per_second,
        scenario: Scenario {
            id,
            steps,
            faults: fault_ids,
            step_limit,
            seed,
            horizon,
            warmup,
            stop_at,
            output,
        },
        behaviors,
        events,
        faults,
        routes,
        resources,
    })
}

// ---- Static helpers -------------------------------------------------------------------------

impl Input {
    fn behavior(&self, id: &str) -> Option<&Behavior> {
        self.behaviors.iter().find(|b| b.id == id)
    }

    fn is_event(&self, id: &str) -> bool {
        self.events.iter().any(|e| e == id)
            && !self.behaviors.iter().any(|b| b.id == id)
            && !self.faults.iter().any(|f| f.id == id)
            && self.scenario.id != id
    }

    fn fault(&self, id: &str) -> Option<&Fault> {
        self.faults.iter().find(|f| f.id == id)
    }

    fn resource(&self, id: &str) -> Option<&Resource> {
        self.resources.iter().find(|r| r.id == id)
    }

    fn route(&self, ev: &str, b: &str) -> Option<&Route> {
        self.routes
            .iter()
            .find(|r| r.event == ev && r.behavior == b)
    }
}

impl Resource {
    fn class_at(&self, i: usize) -> Option<&Class> {
        self.classes.get(i)
    }
    fn limit_of(&self, i: usize) -> Option<u64> {
        self.class_at(i).and_then(|c| c.limit)
    }
    fn reserved_of(&self, i: usize) -> u64 {
        self.class_at(i).map_or(0, |c| c.reserved)
    }
    fn priority_of(&self, i: usize) -> i64 {
        self.class_at(i).map_or(0, |c| c.priority)
    }
    fn class_id(&self, i: usize) -> String {
        self.class_at(i)
            .map_or_else(|| "default".to_string(), |c| c.id.clone())
    }
    fn class_index(&self, c: Option<&str>) -> Option<usize> {
        match c {
            Some(c) => self.classes.iter().position(|k| k.id == c),
            None => (self.classes.len() == 1).then_some(0),
        }
    }
}

impl DemandFactor {
    /// The factor `num/den` at occupancy `o`; `None` when USL leaves 128 bits (then the
    /// service time of any positive draw exceeds 2^53).
    fn at(&self, o: u64) -> Option<(u128, u128)> {
        match self {
            DemandFactor::None => Some((1, 1)),
            DemandFactor::Table(rows) => {
                let mut f = (1, 1);
                for &(n, num, den) in rows {
                    if n <= o {
                        f = (u128::from(num), u128::from(den));
                    }
                }
                Some(f)
            }
            DemandFactor::Usl(an, ad, bn, bd) => {
                let n = u128::from(o.max(1));
                let (an, ad, bn, bd) = (
                    u128::from(*an),
                    u128::from(*ad),
                    u128::from(*bn),
                    u128::from(*bd),
                );
                let a = ad * bd;
                let b = an.checked_mul(bd)?.checked_mul(n - 1)?;
                let c = bn.checked_mul(ad)?.checked_mul(n)?.checked_mul(n - 1)?;
                Some((a.checked_add(b)?.checked_add(c)?, ad * bd))
            }
        }
    }
}

fn machine_key(b: &Behavior, inst: &Value) -> String {
    match b.instances {
        Instances::Single => b.id.clone(),
        _ => format!("{}#{}", b.id, inst.to_json()),
    }
}

fn initial_machine(b: &Behavior) -> Machine {
    let mut vars = JsObject::new();
    for (name, v) in &b.variables {
        vars.insert(name.clone(), v.clone());
    }
    Machine {
        state: b.initial.clone(),
        vars,
    }
}

// ---- Configuration --------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct Machine {
    pub state: String,
    pub vars: JsObject,
}

#[derive(Clone, Debug)]
pub struct Addr {
    pub behavior: String,
    pub inst: Value,
    pub incarnation: u64,
}

#[derive(Clone, Debug)]
pub enum Src {
    Scenario(u64),
    Fault(String),
    Transition(String, String),
    Resource(String, u64, String),
}

#[derive(Clone, Debug)]
pub struct ReqInfo {
    requester: Addr,
    then: String,
    refused: Option<String>,
    payload: JsObject,
    demand: Dist,
    stream: String,
}

#[derive(Clone, Debug)]
pub struct Req {
    id: u64,
    owner: String,
    cls: usize,
    units: u64,
    since: u64,
    kind: ReqKind,
    info: Rc<ReqInfo>,
}

#[derive(Clone, Debug)]
pub struct Hold {
    owner: String,
    cls: usize,
    units: u64,
    req: Option<u64>,
}

#[derive(Clone, Debug, Default)]
pub struct RState {
    capacity: u64,
    holds: Vec<Hold>,
    waiting: Vec<Req>,
}

#[derive(Clone, Debug)]
pub enum EntryKind {
    Event,
    ServiceDone {
        res: String,
        req: Req,
        waited: u64,
        served: u64,
    },
    WaitTimeout {
        res: String,
        request: u64,
    },
}

#[derive(Clone, Debug)]
pub struct Entry {
    seq: u64,
    time: u64,
    scheduled_at: u64,
    event: String,
    payload: Value,
    source: Src,
    kind: EntryKind,
    target: Option<Addr>,
    sender: Option<Addr>,
    routes: Option<Vec<(String, Value)>>,
}

#[derive(Clone, Debug, Default)]
pub struct Conf {
    time: u64,
    machines: Vec<(String, Machine)>,
    insts: Vec<(String, Vec<Value>)>,
    pending: Vec<Entry>,
    resources: Vec<(String, RState)>,
    route_counters: Vec<(String, u64)>,
    streams: Vec<(String, u64)>,
}

impl Conf {
    fn machine(&self, k: &str) -> Option<&Machine> {
        self.machines.iter().find(|(id, _)| id == k).map(|(_, m)| m)
    }
    fn machine_mut(&mut self, k: &str) -> Option<&mut Machine> {
        self.machines
            .iter_mut()
            .find(|(id, _)| id == k)
            .map(|(_, m)| m)
    }
    fn set_machine(&mut self, k: &str, m: Machine) {
        match self.machine_mut(k) {
            Some(slot) => *slot = m,
            None => self.machines.push((k.to_string(), m)),
        }
    }
    fn insts_of(&self, b: &str) -> Vec<Value> {
        self.insts
            .iter()
            .find(|(k, _)| k == b)
            .map(|(_, v)| v.clone())
            .unwrap_or_default()
    }
    fn resource(&self, r: &str) -> Option<&RState> {
        self.resources.iter().find(|(k, _)| k == r).map(|(_, s)| s)
    }
    fn resource_mut(&mut self, r: &str) -> Option<&mut RState> {
        self.resources
            .iter_mut()
            .find(|(k, _)| k == r)
            .map(|(_, s)| s)
    }
    /// The deep copy of format 1: machine variables and pending payloads get fresh identities.
    fn deep_copy(&self) -> Conf {
        let mut c = self.clone();
        for (_, m) in &mut c.machines {
            m.vars = m.vars.deep_copy();
        }
        for e in &mut c.pending {
            e.payload = e.payload.deep_copy();
        }
        c
    }
}

fn lookup(xs: &[(String, u64)], k: &str) -> u64 {
    xs.iter().find(|(x, _)| x == k).map_or(0, |(_, n)| *n)
}

fn bump(xs: &mut Vec<(String, u64)>, k: &str) {
    match xs.iter_mut().find(|(x, _)| x == k) {
        Some((_, n)) => *n += 1,
        None => xs.push((k.to_string(), 1)),
    }
}

fn insert_entry(q: &mut Vec<Entry>, e: Entry) {
    let mut i = q.len();
    while i > 0 && q[i - 1].time > e.time {
        i -= 1;
    }
    q.insert(i, e);
}

// ---- Resource algebra (formal/Exegra/Resource.lean) -----------------------------------------

fn sum_units(hs: &[Hold], p: impl Fn(&Hold) -> bool) -> u64 {
    hs.iter().filter(|h| p(h)).map(|h| h.units).sum()
}
fn held_c(hs: &[Hold], c: usize) -> u64 {
    sum_units(hs, |h| h.cls == c)
}
fn held_all(hs: &[Hold]) -> u64 {
    sum_units(hs, |_| true)
}
fn held_by(hs: &[Hold], owner: &str, c: usize) -> u64 {
    sum_units(hs, |h| h.owner == owner && h.cls == c && h.req.is_none())
}

fn shortfall(d: &Resource, hs: &[Hold], c: usize) -> u64 {
    (0..d.classes.len())
        .filter(|&k| k != c)
        .map(|k| d.reserved_of(k).saturating_sub(held_c(hs, k)))
        .sum()
}

fn fits(d: &Resource, s: &RState, r: &Req) -> bool {
    let lim_ok = match d.limit_of(r.cls) {
        None => true,
        Some(l) => held_c(&s.holds, r.cls) + r.units <= l,
    };
    lim_ok
        && r.units
            <= s.capacity
                .saturating_sub(held_all(&s.holds))
                .saturating_sub(shortfall(d, &s.holds, r.cls))
}

fn before(d: &Resource, a: &Req, b: &Req) -> bool {
    let older = a.since < b.since || (a.since == b.since && a.id < b.id);
    if d.by_priority {
        let (pa, pb) = (d.priority_of(a.cls), d.priority_of(b.cls));
        pa > pb || (pa == pb && older)
    } else {
        older
    }
}

fn pick(d: &Resource, s: &RState) -> Option<Req> {
    let mut best: Option<&Req> = None;
    for c in 0..d.classes.len() {
        let Some(r) = s.waiting.iter().find(|w| w.cls == c) else {
            continue;
        };
        if !fits(d, s, r) {
            continue;
        }
        best = match best {
            None => Some(r),
            Some(b) => Some(if before(d, r, b) { r } else { b }),
        };
    }
    best.cloned()
}

/// Grant while some class head fits. Returns each grant with its occupancy.
fn grant_loop(d: &Resource, s: &mut RState) -> Vec<(Req, u64)> {
    let mut out = Vec::new();
    for _ in 0..s.waiting.len() {
        let Some(r) = pick(d, s) else { break };
        s.waiting.retain(|w| w.id != r.id);
        s.holds.push(Hold {
            owner: r.owner.clone(),
            cls: r.cls,
            units: r.units,
            req: (r.kind == ReqKind::Use).then_some(r.id),
        });
        let occ = held_all(&s.holds) + s.waiting.len() as u64;
        out.push((r, occ));
    }
    out
}

fn consume(owner: &str, c: usize, mut n: u64, hs: Vec<Hold>) -> Vec<Hold> {
    let mut out = Vec::new();
    for mut h in hs {
        if h.owner == owner && h.cls == c && h.req.is_none() {
            let t = n.min(h.units);
            h.units -= t;
            n -= t;
            if h.units != 0 {
                out.push(h);
            }
        } else {
            out.push(h);
        }
    }
    out
}

fn take_first(ws: &mut Vec<Req>, p: impl Fn(&Req) -> bool) -> Option<Req> {
    let i = ws.iter().position(p)?;
    Some(ws.remove(i))
}

fn take_last(ws: &mut Vec<Req>, p: impl Fn(&Req) -> bool) -> Option<Req> {
    let i = ws.iter().rposition(p)?;
    Some(ws.remove(i))
}

fn lowest_class(d: &Resource, ws: &[Req]) -> Option<usize> {
    let mut acc: Option<usize> = None;
    for c in (0..d.classes.len()).filter(|&c| ws.iter().any(|r| r.cls == c)) {
        acc = match acc {
            None => Some(c),
            Some(b) => Some(if d.priority_of(c) < d.priority_of(b) {
                c
            } else {
                b
            }),
        };
    }
    acc
}

fn choose_all(d: &Resource, ws: &mut Vec<Req>) -> Option<Req> {
    if d.overflow == Overflow::ShedOldest {
        if d.by_priority {
            if let Some(c) = lowest_class(d, ws) {
                if let Some(r) = take_first(ws, |r| r.cls == c) {
                    return Some(r);
                }
            }
        }
        take_first(ws, |_| true)
    } else {
        take_last(ws, |_| true)
    }
}

/// The bounds step: class bounds in declaration order, then the resource bound.
fn bounds(d: &Resource, ws: &mut Vec<Req>) -> Vec<Req> {
    let mut removed = Vec::new();
    for c in 0..d.classes.len() {
        let Some(b) = d.class_at(c).and_then(|k| k.queue_bound) else {
            continue;
        };
        let fuel = ws.len();
        for _ in 0..fuel {
            if ws.iter().filter(|r| r.cls == c).count() as u64 <= b {
                break;
            }
            let r = if d.overflow == Overflow::ShedOldest {
                take_first(ws, |r| r.cls == c)
            } else {
                take_last(ws, |r| r.cls == c)
            };
            match r {
                Some(r) => removed.push(r),
                None => break,
            }
        }
    }
    if let Some(b) = d.queue_bound {
        let fuel = ws.len();
        for _ in 0..fuel {
            if ws.len() as u64 <= b {
                break;
            }
            match choose_all(d, ws) {
                Some(r) => removed.push(r),
                None => break,
            }
        }
    }
    removed
}

// ---- Records --------------------------------------------------------------------------------

#[derive(Clone, Debug)]
struct Draw {
    stream: String,
    index: u64,
    value: u64,
}

#[derive(Clone, Debug)]
struct ResRecord {
    resource: String,
    class: String,
    request: Option<u64>,
    action: &'static str,
    at: u64,
    waited: Option<u64>,
    served: Option<u64>,
    reason: Option<&'static str>,
    units: Option<u64>,
}

fn res_rec(res: &str, d: &Resource, r: &Req, action: &'static str, at: u64) -> ResRecord {
    ResRecord {
        resource: res.to_string(),
        class: d.class_id(r.cls),
        request: Some(r.id),
        action,
        at,
        waited: None,
        served: None,
        reason: None,
        units: None,
    }
}

#[derive(Clone, Debug)]
struct SetRec {
    var: String,
    before: Value,
    after: Value,
}

#[derive(Clone, Debug)]
struct EmitRec {
    event: String,
    time: u64,
    seq: u64,
    payload: Value,
}

#[derive(Clone, Debug)]
struct Fired {
    behavior: String,
    transition: String,
    from: String,
    to: String,
    guard: Option<String>,
    sets: Vec<SetRec>,
    emitted: Vec<EmitRec>,
    inst: Value,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Reason {
    NoTransition,
    GuardFalse,
    Disabled,
}

#[derive(Clone, Debug)]
struct Ignored {
    behavior: String,
    reason: Reason,
    considered: Vec<String>,
    inst: Option<Value>,
}

#[derive(Clone, Debug)]
struct FaultRec {
    fault: String,
    effect: &'static str,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    Deliver,
    Drop,
    Delay,
    ServiceDone,
    WaitTimeout,
}

impl Kind {
    fn name(self) -> &'static str {
        match self {
            Kind::Deliver => "deliver",
            Kind::Drop => "drop",
            Kind::Delay => "delay",
            Kind::ServiceDone => "service-done",
            Kind::WaitTimeout => "wait-timeout",
        }
    }
}

#[derive(Clone, Debug)]
struct StepRec {
    index: u64,
    time: u64,
    kind: Kind,
    head: Entry,
    fired: Vec<Fired>,
    ignored: Vec<Ignored>,
    faults: Vec<FaultRec>,
    responsible: Vec<String>,
    resources: Vec<ResRecord>,
    draws: Vec<Draw>,
    config: Conf,
    error: Option<String>,
}

fn blank(index: u64, head: &Entry, kind: Kind, config: Conf) -> StepRec {
    StepRec {
        index,
        time: head.time,
        kind,
        head: head.clone(),
        fired: Vec::new(),
        ignored: Vec::new(),
        faults: Vec::new(),
        responsible: Vec::new(),
        resources: Vec::new(),
        draws: Vec::new(),
        config,
        error: None,
    }
}

// ---- The simulation -------------------------------------------------------------------------

/// A resource operation recorded in phase 2.
#[derive(Clone, Debug)]
enum Op {
    Req(Req, Option<u64>),
    Release(String, usize, u64),
}

/// The state phases 2 and settling write.
struct Work {
    next: Conf,
    seq: u64,
    draws: Vec<Draw>,
    ops: Vec<(String, Op)>,
    recs: Vec<ResRecord>,
}

struct Sim<'a> {
    input: &'a Input,
    faults: Vec<&'a Fault>,
    fault_ids: Vec<String>,
    compiled: RefCell<HashMap<String, Rc<Ast>>>,
    conf: Conf,
    seq: u64,
    attempts: HashMap<String, u64>,
    delayed_by: HashMap<u64, Vec<String>>,
    steps: Vec<StepRec>,
}

#[allow(clippy::large_enum_variant)]
enum StepResult {
    Committed(Box<StepRec>, Conf, u64, Option<HashMap<String, u64>>),
    Failed(Box<StepRec>),
}

fn draw_next(seed: u64, streams: &mut Vec<(String, u64)>, name: &str) -> (u64, Draw) {
    let i = lookup(streams, name);
    let r = random::draw(seed, name, i);
    bump(streams, name);
    (
        r,
        Draw {
            stream: name.to_string(),
            index: i,
            value: r,
        },
    )
}

fn sample(
    seed: Option<u64>,
    streams: &mut Vec<(String, u64)>,
    name: &str,
    d: &Dist,
    draws: &mut Vec<Draw>,
) -> u64 {
    match (d, seed) {
        (Dist::Fixed(v), _) => *v,
        (Dist::Choice(vs), None) => vs.first().copied().unwrap_or(0),
        (Dist::Choice(vs), Some(s)) => {
            let (r, dr) = draw_next(s, streams, name);
            draws.push(dr);
            vs.get(random::index(r, vs.len())).copied().unwrap_or(0)
        }
        (Dist::Uniform(lo, hi), Some(s)) => {
            let (r, dr) = draw_next(s, streams, name);
            draws.push(dr);
            random::uniform_int(r, *lo, *hi)
        }
        (Dist::Table(pts), Some(s)) => {
            let (r, dr) = draw_next(s, streams, name);
            draws.push(dr);
            random::sample_table(r, pts)
        }
        (_, None) => 0,
    }
}

fn same_json(a: &Value, b: &Value) -> bool {
    a.to_json() == b.to_json()
}

impl<'a> Sim<'a> {
    fn compile(&self, src: &str) -> R<Rc<Ast>> {
        if let Some(ast) = self.compiled.borrow().get(src) {
            return Ok(Rc::clone(ast));
        }
        let ast = Rc::new(parse_expr(src).map_err(|e| format!("Expression \"{src}\": {e}"))?);
        self.compiled
            .borrow_mut()
            .insert(src.to_string(), Rc::clone(&ast));
        Ok(ast)
    }

    #[allow(clippy::too_many_arguments)]
    fn resolve(
        &self,
        view: &Conf,
        start: &Conf,
        mk: &str,
        inst: &Value,
        payload: &Value,
        time: u64,
        path: &[String],
    ) -> R<Value> {
        let p: Vec<&str> = path.iter().map(String::as_str).collect();
        let joined = path.join(".");
        let undef = Ok(Value::Undefined);
        match p.as_slice() {
            ["time"] => Ok(Value::Number(time as f64)),
            ["instance"] => Ok(inst.clone()),
            [name] => Ok(view
                .machine(mk)
                .and_then(|m| m.vars.get(name))
                .cloned()
                .unwrap_or(Value::Undefined)),
            ["event", f] => Ok(payload
                .as_object()
                .and_then(|o| o.get(f))
                .cloned()
                .unwrap_or(Value::Undefined)),
            [r, "inUse"] => Ok(start.resource(r).map_or(Value::Undefined, |s| {
                Value::Number(held_all(&s.holds) as f64)
            })),
            [r, "waiting"] => Ok(start
                .resource(r)
                .map_or(Value::Undefined, |s| Value::Number(s.waiting.len() as f64))),
            [r, what @ ("inUse" | "waiting"), c] => {
                match (start.resource(r), self.input.resource(r)) {
                    (Some(s), Some(d)) => match d.classes.iter().position(|k| k.id == *c) {
                        Some(k) => Ok(Value::Number(if *what == "inUse" {
                            held_c(&s.holds, k) as f64
                        } else {
                            s.waiting.iter().filter(|w| w.cls == k).count() as f64
                        })),
                        None => undef,
                    },
                    _ => undef,
                }
            }
            [b, name] => {
                let Some(bd) = self.input.behavior(b) else {
                    return undef;
                };
                let ks = view.insts_of(b);
                if ks.len() > 1 {
                    return Err(format!(
                        "Reference \"{joined}\" is ambiguous: \"{b}\" has {} instances.",
                        ks.len()
                    ));
                }
                match ks.first().and_then(|v| view.machine(&machine_key(bd, v))) {
                    None => undef,
                    Some(m) => Ok(if *name == "state" {
                        Value::str(m.state.clone())
                    } else {
                        m.vars.get(name).cloned().unwrap_or(Value::Undefined)
                    }),
                }
            }
            [b, "instances", "count"] => match self.input.behavior(b) {
                Some(bd) if !matches!(bd.instances, Instances::Single) => {
                    Ok(Value::Number(view.insts_of(b).len() as f64))
                }
                _ => undef,
            },
            [b, agg, x] => {
                let Some(bd) = self.input.behavior(b) else {
                    return undef;
                };
                if matches!(bd.instances, Instances::Single) {
                    return undef;
                }
                let ms: Vec<&Machine> = view
                    .insts_of(b)
                    .iter()
                    .filter_map(|v| view.machine(&machine_key(bd, v)))
                    .collect();
                match *agg {
                    "count" => Ok(Value::Number(
                        ms.iter().filter(|m| m.state == *x).count() as f64
                    )),
                    "sum" | "min" | "max" => {
                        let mut ns = Vec::new();
                        for m in &ms {
                            match m.vars.get(x).cloned().unwrap_or(Value::Undefined) {
                                Value::Number(n) => ns.push(n),
                                v => {
                                    return Err(format!(
                                        "Aggregate \"{joined}\" needs numbers, got {}.",
                                        v.type_name()
                                    ))
                                }
                            }
                        }
                        Ok(match (*agg, ns.split_first()) {
                            ("sum", _) => Value::Number(ns.iter().fold(0.0, |a, b| a + b)),
                            (_, None) => Value::Null,
                            ("min", Some((n, rest))) => Value::Number(
                                rest.iter().fold(*n, |a, b| if *b < a { *b } else { a }),
                            ),
                            (_, Some((n, rest))) => {
                                Value::Number(
                                    rest.iter().fold(*n, |a, b| if *b > a { *b } else { a }),
                                )
                            }
                        })
                    }
                    _ => undef,
                }
            }
            _ => undef,
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn eval(
        &self,
        src: &str,
        view: &Conf,
        start: &Conf,
        mk: &str,
        inst: &Value,
        payload: &Value,
        time: u64,
    ) -> R<Value> {
        let ast = self.compile(src)?;
        // ORDER: every reference is resolved first, in source order.
        for p in expr_refs(&ast) {
            self.resolve(view, start, mk, inst, payload, time, &p)?;
        }
        eval_expr(&ast, &|path: &[String]| {
            self.resolve(view, start, mk, inst, payload, time, path)
                .unwrap_or(Value::Undefined)
        })
        .map_err(|e| e.message)
    }

    #[allow(clippy::too_many_arguments)]
    fn value_of(
        &self,
        x: Option<&Value>,
        view: &Conf,
        start: &Conf,
        mk: &str,
        inst: &Value,
        payload: &Value,
        time: u64,
    ) -> R<Value> {
        match x {
            None => Err("Effect has no value.".into()),
            Some(Value::String(src)) => self.eval(src, view, start, mk, inst, payload, time),
            Some(v) => Ok(v.deep_copy()),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn eval_entries(
        &self,
        entries: &JsObject,
        view: &Conf,
        start: &Conf,
        mk: &str,
        inst: &Value,
        payload: &Value,
        time: u64,
    ) -> R<JsObject> {
        let mut out = JsObject::new();
        for (k, v) in entries.iter() {
            let x = self.value_of(Some(v), view, start, mk, inst, payload, time)?;
            out.insert(k.clone(), x);
        }
        Ok(out)
    }

    fn responsible_of(&self, event: &str, fired: &[Fired], faults: &[FaultRec]) -> Vec<String> {
        let mut out: Vec<String> = if event.is_empty() {
            Vec::new()
        } else {
            vec![event.to_string()]
        };
        let mut add = |x: &str| {
            if !out.iter().any(|y| y == x) {
                out.push(x.to_string());
            }
        };
        for w in fired {
            add(&w.transition);
            add(&w.behavior);
            if let Some(s) = self
                .input
                .behavior(&w.behavior)
                .and_then(|b| b.subject.as_deref())
            {
                add(s);
            }
        }
        for f in faults {
            add(&f.fault);
        }
        out
    }

    /// Decide the routed instances of an entry first taken as head, creating keyed instances.
    #[allow(clippy::type_complexity)]
    fn decide_routes(&self, c: &mut Conf, head: &Entry) -> R<(Vec<(String, Value)>, Vec<Draw>)> {
        let mut acc = Vec::new();
        let mut drs = Vec::new();
        for b in &self.input.behaviors {
            let Some(r) = self.input.route(&head.event, &b.id) else {
                continue;
            };
            let insts = c.insts_of(&b.id);
            let ckey = format!("{}:{}", r.event, r.behavior);
            let stream = format!("route:{}:{}", r.event, r.behavior);
            match r.by.as_str() {
                "key" => {
                    let f = r.field.clone().unwrap_or_default();
                    let v = head
                        .payload
                        .as_object()
                        .and_then(|o| o.get(&f))
                        .cloned()
                        .unwrap_or(Value::Undefined);
                    if matches!(v, Value::Undefined) {
                        return Err(format!(
                            "Route of \"{}\" to \"{}\" needs payload field \"{f}\".",
                            head.event, b.id
                        ));
                    }
                    if let Instances::Keyed { max, .. } = b.instances {
                        if let Some(k) = insts.iter().find(|k| same_json(k, &v)) {
                            acc.push((b.id.clone(), k.clone()));
                        } else if insts.len() as u64 >= max {
                            return Err(format!(
                                "Behavior \"{}\" would exceed {max} instances.",
                                b.id
                            ));
                        } else {
                            let key = v.deep_copy();
                            if let Some((_, xs)) = c.insts.iter_mut().find(|(k, _)| *k == b.id) {
                                xs.push(key.clone());
                            }
                            c.set_machine(&machine_key(b, &key), initial_machine(b));
                            acc.push((b.id.clone(), key));
                        }
                    } else if !insts.is_empty() {
                        let h = random::fnv1a64(&v.to_json());
                        let i = (h % insts.len() as u64) as usize;
                        acc.push((b.id.clone(), insts[i].clone()));
                    }
                }
                "round-robin" => {
                    if insts.is_empty() {
                        continue;
                    }
                    let n = lookup(&c.route_counters, &ckey);
                    acc.push((
                        b.id.clone(),
                        insts[(n % insts.len() as u64) as usize].clone(),
                    ));
                    bump(&mut c.route_counters, &ckey);
                }
                "least-busy" => {
                    if insts.is_empty() {
                        continue;
                    }
                    let load = |v: &Value| -> u64 {
                        match r.resource.as_deref().and_then(|x| c.resource(x)) {
                            Some(s) => {
                                let mk = machine_key(b, v);
                                sum_units(&s.holds, |h| h.owner == mk)
                                    + s.waiting.iter().filter(|w| w.owner == mk).count() as u64
                            }
                            None => 0,
                        }
                    };
                    let mut best = &insts[0];
                    for v in &insts[1..] {
                        if load(v) < load(best) {
                            best = v;
                        }
                    }
                    acc.push((b.id.clone(), best.clone()));
                }
                _ => {
                    if insts.is_empty() {
                        continue;
                    }
                    match self.input.scenario.seed {
                        None => acc.push((b.id.clone(), insts[0].clone())),
                        Some(seed) => {
                            let (x, dr) = draw_next(seed, &mut c.streams, &stream);
                            drs.push(dr);
                            acc.push((b.id.clone(), insts[random::index(x, insts.len())].clone()));
                        }
                    }
                }
            }
        }
        Ok((acc, drs))
    }

    fn targeting(&self, kind: &str, tid: &str) -> Vec<&'a Fault> {
        self.faults
            .iter()
            .copied()
            .filter(|f| f.is_kind(kind) && f.transition.as_deref() == Some(tid))
            .collect()
    }

    /// Phase 1 for one instance.
    #[allow(clippy::type_complexity)]
    fn choose_inst(
        &self,
        cur: &Conf,
        b: &'a Behavior,
        inst: &Value,
        head: &Entry,
        faults_out: &mut Vec<FaultRec>,
    ) -> R<Result<(&'a Transition, String), Ignored>> {
        let mk = machine_key(b, inst);
        let state = cur.machine(&mk).map(|m| m.state.clone());
        let mut considered = Vec::new();
        let mut dis = false;
        let mut gf = false;
        for t in &b.transitions {
            if Some(&t.from) != state.as_ref() || t.on != head.event {
                continue;
            }
            let enablers = self.targeting("enable-transition", &t.id);
            if t.fault_only && enablers.is_empty() {
                continue;
            }
            considered.push(t.id.clone());
            let disablers = self.targeting("disable-transition", &t.id);
            let holds = match &t.guard {
                None => true,
                Some(g) => match self.eval(g, cur, cur, &mk, inst, &head.payload, head.time)? {
                    Value::Bool(x) => x,
                    _ => {
                        return Err(format!(
                            "Guard \"{g}\" of transition \"{}\" did not evaluate to a boolean.",
                            t.id
                        ))
                    }
                },
            };
            if !holds {
                gf = true;
                continue;
            }
            if !disablers.is_empty() {
                dis = true;
                for d in disablers {
                    faults_out.push(FaultRec {
                        fault: d.id.clone(),
                        effect: "disabled",
                    });
                }
                continue;
            }
            if t.fault_only {
                for e in enablers {
                    faults_out.push(FaultRec {
                        fault: e.id.clone(),
                        effect: "enabled",
                    });
                }
            }
            return Ok(Ok((t, mk)));
        }
        Ok(Err(Ignored {
            behavior: b.id.clone(),
            reason: if dis {
                Reason::Disabled
            } else if gf {
                Reason::GuardFalse
            } else {
                Reason::NoTransition
            },
            considered,
            inst: Some(inst.clone()),
        }))
    }

    /// The instances of `b` an entry addresses; `None` when the behavior is not addressed.
    fn addressed(cur: &Conf, head: &Entry, b: &Behavior) -> Option<Vec<Value>> {
        if let Some(a) = &head.target {
            if a.behavior != b.id {
                return None;
            }
            let found = cur.insts_of(&b.id).iter().any(|v| same_json(v, &a.inst));
            return Some(if found {
                vec![a.inst.clone()]
            } else {
                Vec::new()
            });
        }
        if let Some((_, v)) = head
            .routes
            .as_ref()
            .and_then(|rs| rs.iter().find(|(k, _)| *k == b.id))
        {
            return Some(vec![v.clone()]);
        }
        Some(cur.insts_of(&b.id))
    }

    #[allow(clippy::too_many_arguments)]
    fn run_effects(
        &self,
        start: &Conf,
        head: &Entry,
        b: &Behavior,
        inst: &Value,
        mk: &str,
        t: &Transition,
        w: &mut Work,
        rec: &mut Fired,
    ) -> R<()> {
        let seed = self.input.scenario.seed;
        let time = head.time;
        for (k, e) in t.effects.iter().enumerate() {
            let site = format!("{}:{}:{k}", b.id, t.id);
            match e {
                Effect::Set { var, to } => {
                    if !w.next.machine(mk).is_some_and(|m| m.vars.contains_key(var)) {
                        return Err(format!(
                            "Effect sets \"{var}\", which is not a variable of \"{}\".",
                            b.id
                        ));
                    }
                    let value =
                        self.value_of(to.as_ref(), &w.next, start, mk, inst, &head.payload, time)?;
                    let m = w.next.machine_mut(mk).ok_or("no machine")?;
                    let before = m.vars.get(var).cloned().unwrap_or(Value::Undefined);
                    m.vars.insert(var.clone(), value.clone());
                    rec.sets.push(SetRec {
                        var: var.clone(),
                        before: before.deep_copy(),
                        after: value.deep_copy(),
                    });
                }
                Effect::Sample { var, dist } => {
                    if !w.next.machine(mk).is_some_and(|m| m.vars.contains_key(var)) {
                        return Err(format!(
                            "Effect sets \"{var}\", which is not a variable of \"{}\".",
                            b.id
                        ));
                    }
                    let x = sample(
                        seed,
                        &mut w.next.streams,
                        &format!("sample:{site}"),
                        dist,
                        &mut w.draws,
                    );
                    let value = Value::Number(x as f64);
                    let m = w.next.machine_mut(mk).ok_or("no machine")?;
                    let before = m.vars.get(var).cloned().unwrap_or(Value::Undefined);
                    m.vars.insert(var.clone(), value.clone());
                    rec.sets.push(SetRec {
                        var: var.clone(),
                        before: before.deep_copy(),
                        after: value,
                    });
                }
                Effect::Emit {
                    event,
                    after,
                    payload,
                    reply,
                } => {
                    if !self.input.is_event(event) {
                        return Err(format!("Effect emits \"{event}\", which is not an event."));
                    }
                    // ORDER: the delay is drawn, the time checked, the payload evaluated, then
                    // the requester looked up.
                    let mut streams = w.next.streams.clone();
                    let mut drs = Vec::new();
                    let delay = sample(
                        seed,
                        &mut streams,
                        &format!("after:{site}"),
                        after,
                        &mut drs,
                    );
                    let at = w.next.time + delay;
                    if at >= TWO53 {
                        return Err("Value time exceeds 2^53.".into());
                    }
                    let fs =
                        self.eval_entries(payload, &w.next, start, mk, inst, &head.payload, time)?;
                    let target = if *reply {
                        match &head.sender {
                            Some(a) => Some(a.clone()),
                            None => {
                                return Err(format!(
                                    "Effect replies to \"{}\", which has no requester.",
                                    head.event
                                ))
                            }
                        }
                    } else {
                        None
                    };
                    let pv = Value::object(fs);
                    let s = w.seq;
                    w.seq += 1;
                    insert_entry(
                        &mut w.next.pending,
                        Entry {
                            seq: s,
                            time: at,
                            scheduled_at: at,
                            event: event.clone(),
                            payload: pv.clone(),
                            source: Src::Transition(t.id.clone(), b.id.clone()),
                            kind: EntryKind::Event,
                            target,
                            sender: Some(Addr {
                                behavior: b.id.clone(),
                                inst: inst.clone(),
                                incarnation: 0,
                            }),
                            routes: None,
                        },
                    );
                    w.next.streams = streams;
                    w.draws.extend(drs);
                    rec.emitted.push(EmitRec {
                        event: event.clone(),
                        time: at,
                        seq: s,
                        payload: pv.deep_copy(),
                    });
                }
                Effect::Request {
                    kind,
                    res,
                    class,
                    units,
                    demand,
                    then,
                    refused,
                    payload,
                } => {
                    let d = self.input.resource(res).ok_or_else(|| {
                        format!("Effect uses \"{res}\", which is not a resource.")
                    })?;
                    let ci = d
                        .class_index(class.as_deref())
                        .ok_or_else(|| format!("Effect names no class of \"{res}\"."))?;
                    let fs =
                        self.eval_entries(payload, &w.next, start, mk, inst, &head.payload, time)?;
                    let info = ReqInfo {
                        requester: Addr {
                            behavior: b.id.clone(),
                            inst: inst.clone(),
                            incarnation: 0,
                        },
                        then: then.clone(),
                        refused: refused.clone(),
                        payload: fs,
                        demand: demand.clone(),
                        stream: format!("demand:{site}"),
                    };
                    let r = Req {
                        id: 0,
                        owner: mk.to_string(),
                        cls: ci,
                        units: *units,
                        since: time,
                        kind: *kind,
                        info: Rc::new(info),
                    };
                    let mw = d.class_at(ci).and_then(|c| c.max_wait);
                    w.ops.push((res.clone(), Op::Req(r, mw)));
                }
                Effect::Release { res, class, units } => {
                    let d = self.input.resource(res).ok_or_else(|| {
                        format!("Effect releases \"{res}\", which is not a resource.")
                    })?;
                    let ci = d
                        .class_index(class.as_deref())
                        .ok_or_else(|| format!("Effect names no class of \"{res}\"."))?;
                    w.ops
                        .push((res.clone(), Op::Release(mk.to_string(), ci, *units)));
                }
                Effect::Malformed => {
                    return Err(format!("Malformed effect in transition \"{}\".", t.id));
                }
            }
        }
        Ok(())
    }

    /// The `then` or `refused` entry answering a request, targeted at its requester.
    fn answer(
        w: &mut Work,
        res: &str,
        d: &Resource,
        r: &Req,
        event: &str,
        outcome: &str,
        extra: Vec<(&str, Value)>,
    ) {
        let mut fs = r.info.payload.clone();
        fs.insert("resource", Value::str(res));
        fs.insert("class", Value::str(d.class_id(r.cls)));
        for (k, v) in extra {
            fs.insert(k, v);
        }
        let s = w.seq;
        w.seq += 1;
        let now = w.next.time;
        insert_entry(
            &mut w.next.pending,
            Entry {
                seq: s,
                time: now,
                scheduled_at: now,
                event: event.to_string(),
                payload: Value::object(fs),
                source: Src::Resource(res.to_string(), r.id, outcome.to_string()),
                kind: EntryKind::Event,
                target: Some(r.info.requester.clone()),
                sender: None,
                routes: None,
            },
        );
    }

    fn remove_timeout(q: &mut Vec<Entry>, res: &str, rid: u64) {
        q.retain(|e| {
            !matches!(&e.kind, EntryKind::WaitTimeout { res: r, request } if r == res && *request == rid)
        });
    }

    /// Settle one resource: releases, enqueues, grants, bounds.
    fn settle_one(&self, res: &str, ops: &[&Op], w: &mut Work) -> R<()> {
        let Some(d) = self.input.resource(res) else {
            return Ok(());
        };
        let Some(mut s) = w.next.resource(res).cloned() else {
            return Ok(());
        };
        let now = w.next.time;
        for op in ops {
            if let Op::Release(owner, c, n) = op {
                let held = held_by(&s.holds, owner, *c);
                if held < *n {
                    return Err(format!(
                        "Instance \"{owner}\" releases {n} units of \"{res}\" class \"{}\" but holds {held}.",
                        d.class_id(*c)
                    ));
                }
                s.holds = consume(owner, *c, *n, std::mem::take(&mut s.holds));
                w.recs.push(ResRecord {
                    resource: res.to_string(),
                    class: d.class_id(*c),
                    request: None,
                    action: "released",
                    at: now,
                    waited: None,
                    served: None,
                    reason: None,
                    units: Some(*n),
                });
            }
        }
        for op in ops {
            if let Op::Req(r, mw) = op {
                let mut r = r.clone();
                r.id = w.seq;
                w.seq += 1;
                s.waiting.push(r.clone());
                if let Some(mw) = mw {
                    if now + mw >= TWO53 {
                        return Err("Value time exceeds 2^53.".into());
                    }
                    let seq = w.seq;
                    w.seq += 1;
                    insert_entry(
                        &mut w.next.pending,
                        Entry {
                            seq,
                            time: now + mw,
                            scheduled_at: now + mw,
                            event: String::new(),
                            payload: Value::Null,
                            source: Src::Resource(res.to_string(), r.id, "wait-timeout".into()),
                            kind: EntryKind::WaitTimeout {
                                res: res.to_string(),
                                request: r.id,
                            },
                            target: None,
                            sender: None,
                            routes: None,
                        },
                    );
                }
                w.recs.push(res_rec(res, d, &r, "enqueued", now));
            }
        }
        let grants = grant_loop(d, &mut s);
        *w.next.resource_mut(res).ok_or("no resource")? = s.clone();
        for (r, occ) in grants {
            let waited = now - r.since;
            Self::remove_timeout(&mut w.next.pending, res, r.id);
            match r.kind {
                ReqKind::Use => {
                    let dd = sample(
                        self.input.scenario.seed,
                        &mut w.next.streams,
                        &r.info.stream,
                        &r.info.demand,
                        &mut w.draws,
                    );
                    let served = if dd == 0 {
                        Some(0)
                    } else {
                        d.demand_factor.at(occ).and_then(|(num, den)| {
                            let x = u128::from(dd).checked_mul(num)?;
                            Some(x.div_ceil(den))
                        })
                    };
                    let served = match served {
                        Some(x) if x < u128::from(TWO53) => x as u64,
                        _ => return Err(format!("Value service time of \"{res}\" exceeds 2^53.")),
                    };
                    if now + served >= TWO53 {
                        return Err("Value time exceeds 2^53.".into());
                    }
                    let seq = w.seq;
                    w.seq += 1;
                    insert_entry(
                        &mut w.next.pending,
                        Entry {
                            seq,
                            time: now + served,
                            scheduled_at: now + served,
                            event: String::new(),
                            payload: Value::Null,
                            source: Src::Resource(res.to_string(), r.id, "service-done".into()),
                            kind: EntryKind::ServiceDone {
                                res: res.to_string(),
                                req: r.clone(),
                                waited,
                                served,
                            },
                            target: None,
                            sender: None,
                            routes: None,
                        },
                    );
                }
                ReqKind::Acquire => {
                    Self::answer(
                        w,
                        res,
                        d,
                        &r,
                        &r.info.then,
                        "granted",
                        vec![("waited", Value::Number(waited as f64))],
                    );
                }
            }
            let mut rec = res_rec(res, d, &r, "granted", now);
            rec.waited = Some(waited);
            w.recs.push(rec);
        }
        let mut ws = s.waiting.clone();
        let removed = bounds(d, &mut ws);
        if let Some(st) = w.next.resource_mut(res) {
            st.waiting = ws;
        }
        for r in removed {
            Self::remove_timeout(&mut w.next.pending, res, r.id);
            let waited = now - r.since;
            let (action, reason) = match d.overflow {
                Overflow::Refuse => ("refused", Some("bound")),
                Overflow::Drop => ("dropped", None),
                Overflow::ShedOldest => ("shed", Some("shed")),
            };
            if let (Some(why), Some(ev)) = (reason, &r.info.refused) {
                Self::answer(
                    w,
                    res,
                    d,
                    &r,
                    ev,
                    "refused",
                    vec![
                        ("waited", Value::Number(waited as f64)),
                        ("reason", Value::str(why)),
                    ],
                );
            }
            let mut rec = res_rec(res, d, &r, action, now);
            rec.waited = Some(waited);
            rec.reason = reason;
            w.recs.push(rec);
        }
        Ok(())
    }

    fn settle(&self, touched: &[String], w: &mut Work) -> R<()> {
        let ops = std::mem::take(&mut w.ops);
        for d in &self.input.resources {
            let mine: Vec<&Op> = ops
                .iter()
                .filter(|(r, _)| *r == d.id)
                .map(|(_, o)| o)
                .collect();
            if touched.contains(&d.id) || !mine.is_empty() {
                self.settle_one(&d.id, &mine, w)?;
            }
        }
        Ok(())
    }

    fn fault_matches(f: &Fault, kind: &str, ev: &str, attempt: u64) -> bool {
        f.is_kind(kind)
            && f.event.as_deref() == Some(ev)
            && match f.occurrence {
                Occurrence::Any => true,
                Occurrence::Exactly(n) => n == attempt as f64,
                Occurrence::Never => false,
            }
    }

    /// A step that ends with settling.
    #[allow(clippy::too_many_arguments)]
    fn finish(
        &self,
        head: &Entry,
        kind: Kind,
        fired: Vec<Fired>,
        ignored: Vec<Ignored>,
        faults: Vec<FaultRec>,
        draws: Vec<Draw>,
        touched: &[String],
        mut w: Work,
        attempts: Option<HashMap<String, u64>>,
        pre: Vec<ResRecord>,
    ) -> StepResult {
        let index = self.steps.len() as u64;
        match self.settle(touched, &mut w) {
            Err(msg) => {
                let mut st = blank(index, head, kind, self.conf.clone());
                st.responsible = if head.event.is_empty() {
                    Vec::new()
                } else {
                    vec![head.event.clone()]
                };
                st.error = Some(msg);
                StepResult::Failed(Box::new(st))
            }
            Ok(()) => {
                let mut st = blank(index, head, kind, w.next.clone());
                st.responsible = self.responsible_of(&head.event, &fired, &faults);
                st.fired = fired;
                st.ignored = ignored;
                st.faults = faults;
                st.resources = pre.into_iter().chain(w.recs).collect();
                st.draws = draws.into_iter().chain(w.draws).collect();
                StepResult::Committed(Box::new(st), w.next, w.seq, attempts)
            }
        }
    }

    fn step_head(&mut self, mut next: Conf, head: Entry) -> StepResult {
        let index = self.steps.len() as u64;
        let work = |next: Conf, seq: u64| Work {
            next,
            seq,
            draws: Vec::new(),
            ops: Vec::new(),
            recs: Vec::new(),
        };
        match head.kind.clone() {
            EntryKind::ServiceDone {
                res,
                req,
                waited,
                served,
            } => {
                let (Some(d), Some(s)) = (self.input.resource(&res), next.resource_mut(&res))
                else {
                    return StepResult::Committed(
                        Box::new(blank(index, &head, Kind::ServiceDone, next.clone())),
                        next,
                        self.seq,
                        None,
                    );
                };
                s.holds.retain(|h| h.req != Some(req.id));
                let mut w = work(next, self.seq);
                Self::answer(
                    &mut w,
                    &res,
                    d,
                    &req,
                    &req.info.then,
                    "completed",
                    vec![
                        ("waited", Value::Number(waited as f64)),
                        ("served", Value::Number(served as f64)),
                    ],
                );
                let mut rec = res_rec(&res, d, &req, "completed", w.next.time);
                rec.waited = Some(waited);
                rec.served = Some(served);
                self.finish(
                    &head,
                    Kind::ServiceDone,
                    Vec::new(),
                    Vec::new(),
                    Vec::new(),
                    Vec::new(),
                    std::slice::from_ref(&res),
                    w,
                    None,
                    vec![rec],
                )
            }
            EntryKind::WaitTimeout { res, request } => {
                let found = self.input.resource(&res).zip(
                    next.resource(&res)
                        .and_then(|s| s.waiting.iter().find(|r| r.id == request).cloned()),
                );
                let Some((d, r)) = found else {
                    return StepResult::Committed(
                        Box::new(blank(index, &head, Kind::WaitTimeout, next.clone())),
                        next,
                        self.seq,
                        None,
                    );
                };
                if let Some(s) = next.resource_mut(&res) {
                    s.waiting.retain(|w| w.id != request);
                }
                let waited = next.time - r.since;
                let mut w = work(next, self.seq);
                if let Some(ev) = &r.info.refused {
                    Self::answer(
                        &mut w,
                        &res,
                        d,
                        &r,
                        ev,
                        "refused",
                        vec![
                            ("waited", Value::Number(waited as f64)),
                            ("reason", Value::str("timeout")),
                        ],
                    );
                }
                let mut rec = res_rec(&res, d, &r, "timed-out", w.next.time);
                rec.waited = Some(waited);
                rec.reason = Some("timeout");
                self.finish(
                    &head,
                    Kind::WaitTimeout,
                    Vec::new(),
                    Vec::new(),
                    Vec::new(),
                    Vec::new(),
                    std::slice::from_ref(&res),
                    w,
                    None,
                    vec![rec],
                )
            }
            EntryKind::Event => self.step_event(next, head),
        }
    }

    fn fail(&self, head: &Entry, kind: Kind, msg: String) -> StepResult {
        let mut st = blank(self.steps.len() as u64, head, kind, self.conf.clone());
        st.responsible = vec![head.event.clone()];
        st.error = Some(msg);
        StepResult::Failed(Box::new(st))
    }

    fn step_event(&mut self, mut next: Conf, head: Entry) -> StepResult {
        let index = self.steps.len() as u64;
        let ev = head.event.clone();
        let mut head = head;
        let mut cur = self.conf.clone();
        let mut rdraws = Vec::new();
        // ORDER: routes are decided when the entry is first taken as head, before drop and delay.
        if head.routes.is_none() && head.target.is_none() {
            match self.decide_routes(&mut next, &head) {
                Err(msg) => return self.fail(&head, Kind::Deliver, msg),
                Ok((rs, drs)) => {
                    cur.insts = next.insts.clone();
                    let extra: Vec<(String, Machine)> = next
                        .machines
                        .iter()
                        .filter(|(k, _)| !self.conf.machines.iter().any(|(k2, _)| k2 == k))
                        .cloned()
                        .collect();
                    cur.machines.extend(extra);
                    head.routes = Some(rs);
                    rdraws = drs;
                }
            }
        }
        let attempt = self.attempts.get(&ev).copied().unwrap_or(0) + 1;
        let mut attempts = self.attempts.clone();
        attempts.insert(ev.clone(), attempt);
        let drops: Vec<FaultRec> = self
            .faults
            .iter()
            .filter(|f| Self::fault_matches(f, "drop-event", &ev, attempt))
            .map(|f| FaultRec {
                fault: f.id.clone(),
                effect: "dropped",
            })
            .collect();
        if !drops.is_empty() {
            let mut st = blank(index, &head, Kind::Drop, next.clone());
            st.responsible = self.responsible_of(&ev, &[], &drops);
            st.faults = drops;
            st.draws = rdraws;
            return StepResult::Committed(Box::new(st), next, self.seq, Some(attempts));
        }
        let already = self.delayed_by.get(&head.seq).cloned().unwrap_or_default();
        let delay = self.faults.iter().copied().find(|f| {
            Self::fault_matches(f, "delay-event", &ev, attempt) && !already.contains(&f.id)
        });
        if let Some(d) = delay {
            if head.time + d.by >= TWO53 {
                return self.fail(&head, Kind::Delay, "Value time exceeds 2^53.".into());
            }
            let s = self.seq;
            let mut copy = head.clone();
            copy.seq = s;
            copy.time = head.time + d.by;
            copy.payload = head.payload.deep_copy();
            insert_entry(&mut next.pending, copy);
            let mut applied = already;
            applied.push(d.id.clone());
            self.delayed_by.insert(s, applied);
            let recs = vec![FaultRec {
                fault: d.id.clone(),
                effect: "delayed",
            }];
            let mut st = blank(index, &head, Kind::Delay, next.clone());
            st.responsible = self.responsible_of(&ev, &[], &recs);
            st.faults = recs;
            st.draws = rdraws;
            return StepResult::Committed(Box::new(st), next, s + 1, Some(attempts));
        }
        // Delivery: phase 1 reads `cur`, phase 2 writes `next`.
        let mut faults_out = Vec::new();
        if let Src::Fault(f) = &head.source {
            faults_out.push(FaultRec {
                fault: f.clone(),
                effect: "injected",
            });
        }
        let phase = (|| -> R<(Vec<Fired>, Vec<Ignored>, Work)> {
            let mut winners = Vec::new();
            let mut ignored = Vec::new();
            for b in &self.input.behaviors {
                match Self::addressed(&cur, &head, b) {
                    None => {}
                    Some(insts) if insts.is_empty() => ignored.push(Ignored {
                        behavior: b.id.clone(),
                        reason: Reason::NoTransition,
                        considered: Vec::new(),
                        inst: None,
                    }),
                    Some(insts) => {
                        for inst in insts {
                            match self.choose_inst(&cur, b, &inst, &head, &mut faults_out)? {
                                Ok((t, mk)) => winners.push((b, inst, mk, t)),
                                Err(ig) => ignored.push(ig),
                            }
                        }
                    }
                }
            }
            let mut w = Work {
                next: next.clone(),
                seq: self.seq,
                draws: Vec::new(),
                ops: Vec::new(),
                recs: Vec::new(),
            };
            let mut fired = Vec::new();
            for (b, inst, mk, t) in winners {
                let mut rec = Fired {
                    behavior: b.id.clone(),
                    transition: t.id.clone(),
                    from: t.from.clone(),
                    to: t.to.clone(),
                    guard: t.guard.clone(),
                    sets: Vec::new(),
                    emitted: Vec::new(),
                    inst: inst.clone(),
                };
                self.run_effects(&cur, &head, b, &inst, &mk, t, &mut w, &mut rec)?;
                if let Some(m) = w.next.machine_mut(&mk) {
                    m.state = t.to.clone();
                }
                fired.push(rec);
            }
            Ok((fired, ignored, w))
        })();
        match phase {
            Err(msg) => self.fail(&head, Kind::Deliver, msg),
            Ok((fired, ignored, w)) => {
                let draws: Vec<Draw> = rdraws.into_iter().chain(w.draws.iter().cloned()).collect();
                let w = Work {
                    draws: Vec::new(),
                    ..w
                };
                self.finish(
                    &head,
                    Kind::Deliver,
                    fired,
                    ignored,
                    faults_out,
                    draws,
                    &[],
                    w,
                    Some(attempts),
                    Vec::new(),
                )
            }
        }
    }
}

// ---- Running --------------------------------------------------------------------------------

fn validate(i: &Input) -> R<()> {
    let sid = &i.scenario.id;
    let mut seen = Vec::new();
    for id in &i.scenario.faults {
        if seen.contains(id) {
            continue;
        }
        seen.push(id.clone());
        if i.fault(id).is_none() {
            return Err(format!("\"{id}\" is not a fault in this model."));
        }
    }
    for (k, st) in i.scenario.steps.iter().enumerate() {
        if !i.is_event(&st.event) {
            return Err(format!(
                "Scenario \"{sid}\" step {k} delivers \"{}\", which is not an event.",
                st.event
            ));
        }
    }
    for id in &seen {
        let Some(f) = i.fault(id) else { continue };
        if f.is_kind("inject-event") {
            match &f.event {
                Some(e) if !i.is_event(e) => {
                    return Err(format!(
                        "Fault \"{}\" injects \"{e}\", which is not an event.",
                        f.id
                    ))
                }
                None => {
                    return Err(format!(
                        "Fault \"{}\" injects \"undefined\", which is not an event.",
                        f.id
                    ))
                }
                _ => {}
            }
        }
    }
    let ids: Vec<&String> = i
        .behaviors
        .iter()
        .map(|b| &b.id)
        .chain(i.resources.iter().map(|r| &r.id))
        .collect();
    for x in &ids {
        if ids.iter().filter(|y| *y == x).count() > 1 {
            return Err(format!(
                "Id \"{x}\" is reserved: it names more than one element."
            ));
        }
    }
    for b in &i.behaviors {
        for (name, _) in &b.variables {
            if name == "instance" {
                return Err(format!(
                    "Variable \"instance\" of \"{}\" is reserved.",
                    b.id
                ));
            }
            if !matches!(b.instances, Instances::Single)
                && ["count", "sum", "min", "max", "instances"].contains(&name.as_str())
            {
                return Err(format!("Variable \"{name}\" of \"{}\" is reserved.", b.id));
            }
        }
    }
    for r in &i.routes {
        if !i.is_event(&r.event) {
            return Err(format!(
                "Route names \"{}\", which is not an event.",
                r.event
            ));
        }
        let Some(b) = i.behavior(&r.behavior) else {
            return Err(format!(
                "Route names \"{}\", which is not a behavior.",
                r.behavior
            ));
        };
        if matches!(b.instances, Instances::Keyed { .. }) && r.by != "key" {
            return Err(format!(
                "Route of \"{}\" to keyed \"{}\" must be by key.",
                r.event, b.id
            ));
        }
        if r.by == "key" && r.field.is_none() {
            return Err(format!(
                "Route of \"{}\" to \"{}\" needs a field.",
                r.event, r.behavior
            ));
        }
        if r.by == "least-busy" {
            match &r.resource {
                Some(x) if i.resource(x).is_none() => {
                    return Err(format!("Route names \"{x}\", which is not a resource."))
                }
                None => {
                    return Err(format!(
                        "Route of \"{}\" to \"{}\" needs a resource.",
                        r.event, r.behavior
                    ))
                }
                _ => {}
            }
        }
    }
    for b in &i.behaviors {
        for t in &b.transitions {
            for e in &t.effects {
                match e {
                    Effect::Request {
                        res,
                        class,
                        units,
                        then,
                        refused,
                        ..
                    } => {
                        let Some(d) = i.resource(res) else {
                            return Err(format!("Effect uses \"{res}\", which is not a resource."));
                        };
                        let Some(c) = d.class_index(class.as_deref()) else {
                            return Err(format!("Effect names no class of \"{res}\"."));
                        };
                        let others: u64 = (0..d.classes.len())
                            .filter(|&k| k != c)
                            .map(|k| d.reserved_of(k))
                            .sum();
                        let lim = d.limit_of(c).unwrap_or(d.capacity);
                        if *units > lim.min(d.capacity.saturating_sub(others)) {
                            return Err(format!(
                                "Class \"{}\" of \"{res}\" can never grant {units} units.",
                                d.class_id(c)
                            ));
                        }
                        if !i.is_event(then) {
                            return Err(format!("Effect emits \"{then}\", which is not an event."));
                        }
                        if let Some(ev) = refused {
                            if !i.is_event(ev) {
                                return Err(format!(
                                    "Effect emits \"{ev}\", which is not an event."
                                ));
                            }
                        }
                    }
                    Effect::Release { res, class, .. } => {
                        let Some(d) = i.resource(res) else {
                            return Err(format!(
                                "Effect releases \"{res}\", which is not a resource."
                            ));
                        };
                        if d.class_index(class.as_deref()).is_none() {
                            return Err(format!("Effect names no class of \"{res}\"."));
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    for d in &i.resources {
        let total: u64 = d.classes.iter().map(|c| c.reserved).sum();
        if total > d.capacity {
            return Err(format!(
                "Resource \"{}\" reserves more units than its capacity.",
                d.id
            ));
        }
        for c in &d.classes {
            if let Some(l) = c.limit {
                if c.reserved > l {
                    return Err(format!(
                        "Class \"{}\" of \"{}\" reserves more units than its limit.",
                        c.id, d.id
                    ));
                }
            }
        }
    }
    if i.unit == "tick" && i.per_second.is_some() {
        return Err("Unit tick has no rate.".into());
    }
    if i.scenario.seed.is_none() {
        if let Some(s) = sampled_sites(i).first() {
            return Err(format!("Input samples \"{s}\" but declares no seed."));
        }
    }
    if let (Some(h), Some(w)) = (i.scenario.horizon, i.scenario.warmup) {
        if w >= h {
            return Err("Scenario warmup must be below its horizon.".into());
        }
    }
    if let (Some(h), Some(s)) = (i.scenario.horizon, i.scenario.stop_at) {
        if s < h {
            return Err("Scenario stopAt must be at least its horizon.".into());
        }
    }
    Ok(())
}

fn sampled_sites(i: &Input) -> Vec<String> {
    let mut out = Vec::new();
    for b in &i.behaviors {
        for t in &b.transitions {
            for (k, e) in t.effects.iter().enumerate() {
                let site = format!("{}:{}:{k}", b.id, t.id);
                match e {
                    Effect::Emit { after, .. } if after.draws() => {
                        out.push(format!("after:{site}"))
                    }
                    Effect::Sample { dist, .. } if dist.draws() => {
                        out.push(format!("sample:{site}"))
                    }
                    Effect::Request { demand, .. } if demand.draws() => {
                        out.push(format!("demand:{site}"))
                    }
                    _ => {}
                }
            }
        }
    }
    for r in i.routes.iter().filter(|r| r.by == "random") {
        out.push(format!("route:{}:{}", r.event, r.behavior));
    }
    out
}

fn initial_conf(i: &Input, faults: &[&Fault]) -> (Conf, u64) {
    let mut insts: Vec<(String, Vec<Value>)> = Vec::new();
    for b in &i.behaviors {
        if insts.iter().any(|(k, _)| *k == b.id) {
            continue;
        }
        let vs = match b.instances {
            Instances::Single => vec![Value::Number(0.0)],
            Instances::Count(n) => (0..n).map(|k| Value::Number(k as f64)).collect(),
            Instances::Keyed { .. } => Vec::new(),
        };
        insts.push((b.id.clone(), vs));
    }
    let mut machines = Vec::new();
    for (bid, vs) in &insts {
        if let Some(b) = i.behavior(bid) {
            for v in vs {
                machines.push((machine_key(b, v), initial_machine(b)));
            }
        }
    }
    let mut q = Vec::new();
    let mut n = 0;
    let mk =
        |n: u64, time: u64, event: &str, payload: &Value, source: Src, target: Option<Addr>| {
            Entry {
                seq: n,
                time,
                scheduled_at: time,
                event: event.to_string(),
                payload: payload.clone(),
                source,
                kind: EntryKind::Event,
                target,
                sender: None,
                routes: None,
            }
        };
    for st in &i.scenario.steps {
        let target = st.target.as_ref().map(|(b, v)| Addr {
            behavior: b.clone(),
            inst: v.clone(),
            incarnation: 0,
        });
        insert_entry(
            &mut q,
            mk(n, st.at, &st.event, &st.payload, Src::Scenario(n), target),
        );
        n += 1;
    }
    for f in faults.iter().filter(|f| f.is_kind("inject-event")) {
        insert_entry(
            &mut q,
            mk(
                n,
                f.at,
                f.event.as_deref().unwrap_or(""),
                &f.payload,
                Src::Fault(f.id.clone()),
                None,
            ),
        );
        n += 1;
    }
    (
        Conf {
            time: 0,
            machines,
            insts,
            pending: q,
            resources: i
                .resources
                .iter()
                .map(|d| {
                    (
                        d.id.clone(),
                        RState {
                            capacity: d.capacity,
                            ..RState::default()
                        },
                    )
                })
                .collect(),
            route_counters: Vec::new(),
            streams: Vec::new(),
        },
        n,
    )
}

/// Run a version-2 input: the refusal message, or the trace as JSON text.
pub fn run(root: &JsObject) -> R<String> {
    let input = decode(root)?;
    validate(&input)?;
    let mut fault_ids: Vec<String> = Vec::new();
    for id in &input.scenario.faults {
        if !fault_ids.contains(id) {
            fault_ids.push(id.clone());
        }
    }
    let faults: Vec<&Fault> = fault_ids.iter().filter_map(|id| input.fault(id)).collect();
    let (initial, seq) = initial_conf(&input, &faults);
    let mut sim = Sim {
        input: &input,
        faults,
        fault_ids,
        compiled: RefCell::new(HashMap::new()),
        conf: initial.deep_copy(),
        seq,
        attempts: HashMap::new(),
        delayed_by: HashMap::new(),
        steps: Vec::new(),
    };
    let bound = input.scenario.step_limit;
    let mut outcome = if sim.conf.pending.is_empty() {
        "quiescent"
    } else {
        "running"
    };
    while outcome == "running" {
        let Some(h) = sim.conf.pending.first() else {
            outcome = "quiescent";
            break;
        };
        if input.scenario.stop_at.is_some_and(|s| h.time > s) {
            outcome = "stopped";
            break;
        }
        let mut next = sim.conf.deep_copy();
        let head = next.pending.remove(0);
        next.time = head.time;
        match sim.step_head(next, head) {
            StepResult::Committed(rec, next, seq, attempts) => {
                sim.steps.push(*rec);
                sim.seq = seq;
                if let Some(a) = attempts {
                    sim.attempts = a;
                }
                outcome = if next.pending.is_empty() {
                    "quiescent"
                } else if sim.steps.len() as u64 >= bound {
                    "step-limit"
                } else {
                    "running"
                };
                sim.conf = next;
            }
            StepResult::Failed(rec) => {
                sim.steps.push(*rec);
                outcome = "error";
            }
        }
    }
    Ok(encode_trace(&sim, &initial, outcome).to_json())
}

// ---- Encoding -------------------------------------------------------------------------------

struct Obj(JsObject);

impl Obj {
    fn new() -> Self {
        Obj(JsObject::new())
    }
    fn put(mut self, k: &str, v: Value) -> Self {
        self.0.insert(k, v);
        self
    }
    fn opt(self, k: &str, v: Option<Value>) -> Self {
        match v {
            Some(v) => self.put(k, v),
            None => self,
        }
    }
    fn done(self) -> Value {
        Value::object(self.0)
    }
}

fn s(x: &str) -> Value {
    Value::str(x)
}
fn n(x: u64) -> Value {
    Value::Number(x as f64)
}

fn addr(a: &Addr) -> Value {
    Obj::new()
        .put("behavior", s(&a.behavior))
        .put("instance", a.inst.clone())
        .put("incarnation", n(a.incarnation))
        .done()
}

fn source(src: &Src) -> Value {
    match src {
        Src::Scenario(k) => Obj::new()
            .put("kind", s("scenario"))
            .put("step", n(*k))
            .done(),
        Src::Fault(f) => Obj::new().put("kind", s("fault")).put("fault", s(f)).done(),
        Src::Transition(t, b) => Obj::new()
            .put("kind", s("transition"))
            .put("transition", s(t))
            .put("behavior", s(b))
            .done(),
        Src::Resource(r, q, out) => Obj::new()
            .put("kind", s("resource"))
            .put("resource", s(r))
            .put("request", n(*q))
            .put("outcome", s(out))
            .done(),
    }
}

fn entry_fields(mut o: Obj, e: &Entry) -> Obj {
    match &e.kind {
        EntryKind::Event => {}
        EntryKind::ServiceDone { res, req, .. } => {
            o = o
                .put("kind", s("service-done"))
                .put("resource", s(res))
                .put("request", n(req.id));
        }
        EntryKind::WaitTimeout { res, request } => {
            o = o
                .put("kind", s("wait-timeout"))
                .put("resource", s(res))
                .put("request", n(*request));
        }
    }
    o = o
        .opt("target", e.target.as_ref().map(addr))
        .opt("from", e.sender.as_ref().map(addr));
    if let Some(rs) = &e.routes {
        if !rs.is_empty() {
            let mut ro = JsObject::new();
            for (b, v) in rs {
                ro.insert(b.clone(), v.clone());
            }
            o = o.put("routes", Value::object(ro));
        }
    }
    o
}

fn event_id(e: &Entry) -> Value {
    if e.event.is_empty() {
        Value::Null
    } else {
        s(&e.event)
    }
}

fn pending(e: &Entry) -> Value {
    entry_fields(
        Obj::new()
            .put("seq", n(e.seq))
            .put("time", n(e.time))
            .put("scheduledAt", n(e.scheduled_at))
            .put("event", event_id(e))
            .put("payload", e.payload.clone())
            .put("source", source(&e.source)),
        e,
    )
    .done()
}

fn configuration(i: &Input, c: &Conf) -> Value {
    let mut machines = JsObject::new();
    let mut incarnations = JsObject::new();
    for (id, m) in &c.machines {
        machines.insert(
            id.clone(),
            Obj::new()
                .put("state", s(&m.state))
                .put("vars", Value::object(m.vars.clone()))
                .done(),
        );
        incarnations.insert(id.clone(), n(0));
    }
    let mut resources = JsObject::new();
    for d in &i.resources {
        let v = match c.resource(&d.id) {
            None => Value::Null,
            Some(st) => Obj::new()
                .put("capacity", n(st.capacity))
                .put(
                    "held",
                    Value::array(
                        st.holds
                            .iter()
                            .map(|h| {
                                Obj::new()
                                    .put("instance", s(&h.owner))
                                    .put("class", s(&d.class_id(h.cls)))
                                    .put("units", n(h.units))
                                    .opt("request", h.req.map(n))
                                    .done()
                            })
                            .collect(),
                    ),
                )
                .put(
                    "waiting",
                    Value::array(
                        st.waiting
                            .iter()
                            .map(|r| {
                                Obj::new()
                                    .put("request", n(r.id))
                                    .put("requester", s(&r.owner))
                                    .put("class", s(&d.class_id(r.cls)))
                                    .put("units", n(r.units))
                                    .put("since", n(r.since))
                                    .put("seq", n(r.id))
                                    .done()
                            })
                            .collect(),
                    ),
                )
                .done(),
        };
        resources.insert(d.id.clone(), v);
    }
    let counters = |xs: &[(String, u64)]| {
        let mut o = JsObject::new();
        for (k, v) in xs {
            o.insert(k.clone(), n(*v));
        }
        Value::object(o)
    };
    let empty = || Value::object(JsObject::new());
    Obj::new()
        .put("time", n(c.time))
        .put("machines", Value::object(machines))
        .put(
            "pending",
            Value::array(c.pending.iter().map(pending).collect()),
        )
        .put("resources", Value::object(resources))
        .put("links", empty())
        .put("timers", empty())
        .put("workloads", empty())
        .put("meters", empty())
        .put("routeCounters", counters(&c.route_counters))
        .put("streams", counters(&c.streams))
        .put("down", Value::array(Vec::new()))
        .put("incarnations", Value::object(incarnations))
        .done()
}

fn strings(xs: &[String]) -> Value {
    Value::array(xs.iter().map(|x| s(x)).collect())
}

fn step_value(i: &Input, st: &StepRec) -> Value {
    let e = &st.head;
    let event = entry_fields(
        Obj::new()
            .put("id", event_id(e))
            .put("payload", e.payload.clone())
            .put("seq", n(e.seq))
            .put("source", source(&e.source))
            .put("scheduledAt", n(e.scheduled_at)),
        e,
    )
    .done();
    let fired = st
        .fired
        .iter()
        .map(|f| {
            Obj::new()
                .put("behavior", s(&f.behavior))
                .put("transition", s(&f.transition))
                .put("from", s(&f.from))
                .put("to", s(&f.to))
                .put("guard", f.guard.as_deref().map_or(Value::Null, s))
                .put(
                    "sets",
                    Value::array(
                        f.sets
                            .iter()
                            .map(|r| {
                                Obj::new()
                                    .put("variable", s(&r.var))
                                    .put("before", r.before.clone())
                                    .put("after", r.after.clone())
                                    .done()
                            })
                            .collect(),
                    ),
                )
                .put(
                    "emitted",
                    Value::array(
                        f.emitted
                            .iter()
                            .map(|r| {
                                Obj::new()
                                    .put("event", s(&r.event))
                                    .put("time", n(r.time))
                                    .put("seq", n(r.seq))
                                    .put("payload", r.payload.clone())
                                    .done()
                            })
                            .collect(),
                    ),
                )
                .put("instance", f.inst.clone())
                .done()
        })
        .collect();
    let ignored = st
        .ignored
        .iter()
        .map(|ig| {
            let reason = match (&ig.inst, ig.reason) {
                (None, _) => "no-instance",
                (_, Reason::NoTransition) => "no-transition",
                (_, Reason::GuardFalse) => "guard-false",
                (_, Reason::Disabled) => "disabled",
            };
            Obj::new()
                .put("behavior", s(&ig.behavior))
                .put("reason", s(reason))
                .put("considered", strings(&ig.considered))
                .opt("instance", ig.inst.clone())
                .done()
        })
        .collect();
    let faults = st
        .faults
        .iter()
        .map(|f| {
            Obj::new()
                .put("fault", s(&f.fault))
                .put("effect", s(f.effect))
                .done()
        })
        .collect();
    let resources = st
        .resources
        .iter()
        .map(|r| {
            Obj::new()
                .put("resource", s(&r.resource))
                .put("class", s(&r.class))
                .put("request", r.request.map_or(Value::Null, n))
                .put("action", s(r.action))
                .put("at", n(r.at))
                .opt("waited", r.waited.map(n))
                .opt("served", r.served.map(n))
                .opt("reason", r.reason.map(s))
                .opt("units", r.units.map(n))
                .done()
        })
        .collect();
    let draws = st
        .draws
        .iter()
        .map(|d| {
            Obj::new()
                .put("stream", s(&d.stream))
                .put("index", n(d.index))
                .put("value", s(&d.value.to_string()))
                .done()
        })
        .collect();
    Obj::new()
        .put("index", n(st.index))
        .put("time", n(st.time))
        .put("kind", s(st.kind.name()))
        .put("event", event)
        .put("fired", Value::array(fired))
        .put("ignored", Value::array(ignored))
        .put("faults", Value::array(faults))
        .put("responsible", strings(&st.responsible))
        .put("resources", Value::array(resources))
        .put("draws", Value::array(draws))
        .put("config", configuration(i, &st.config))
        .opt(
            "error",
            st.error
                .as_ref()
                .map(|m| Obj::new().put("message", s(m)).done()),
        )
        .done()
}

fn encode_trace(sim: &Sim, initial: &Conf, outcome: &str) -> Value {
    let i = sim.input;
    let mut o = Obj::new()
        .put("version", n(2))
        .put("timeUnit", s(&i.unit))
        .put(
            "seed",
            i.scenario.seed.map_or(Value::Null, |x| s(&x.to_string())),
        )
        .put("scenarioId", s(&i.scenario.id))
        .put("faults", strings(&sim.fault_ids))
        .put("initialDraws", Value::array(Vec::new()));
    if i.scenario.output != "metrics" {
        o = o.put("initial", configuration(i, initial)).put(
            "steps",
            Value::array(sim.steps.iter().map(|st| step_value(i, st)).collect()),
        );
    }
    o.put("stepsTaken", n(sim.steps.len() as u64))
        .put("outcome", s(outcome))
        .put(
            "truncated",
            Value::Bool(outcome == "step-limit" || outcome == "error"),
        )
        .put("final", configuration(i, &sim.conf))
        .done()
}
