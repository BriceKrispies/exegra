//! Format 2 of the engine input and trace, the WG-4664 part: integer time in a declared unit,
//! counted and keyed instances with routes, resources (`use`, `acquire`, `release`, class queues,
//! bounds, overflow, demand factors) and seeded SplitMix64 streams.
//!
//! This is a port of `formal/Exegra/Format2.lean` and `formal/Exegra/Resource.lean`, which define
//! it; the differential check (`tools/differential.js`) compares the two. Comments marked ORDER
//! note where an order decides an observable result. Not here yet (refused when present): links,
//! workloads, timers, meters, request classes, prices, windowed and resource faults and
//! `crash-instance`.

// Clippy asks for `const` on a thread-local initializer that already is one.
#![allow(clippy::missing_const_for_thread_local)]

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::expr::{eval_expr, expr_refs, parse_expr, Ast};
use crate::random;
use crate::value::{JsObject, Value};
use crate::workload::{self as work, Cursor, Phase, Rate};
use num_bigint::BigUint;

type R<T> = Result<T, String>;

const TWO53: u64 = 1 << 53;
const TWO32: u64 = 1 << 32;

/// A shared immutable string: identifiers are cloned by the step, so cloning must not allocate.
#[derive(Clone, Eq)]
pub struct Id(Rc<str>);

// Whether the run keeps its steps: the records only a trace reads are built then.
static KEEP: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(true);

/// A shared property name: the few names the engine itself puts in payloads are built once.
fn skey(name: &str) -> Rc<str> {
    thread_local! {
        static KEYS: RefCell<Vec<Rc<str>>> = const { RefCell::new(Vec::new()) };
    }
    KEYS.with(|ks| {
        let mut ks = ks.borrow_mut();
        if let Some(k) = ks.iter().find(|k| &***k == name) {
            return Rc::clone(k);
        }
        let k: Rc<str> = Rc::from(name);
        ks.push(Rc::clone(&k));
        k
    })
}

fn keep() -> bool {
    KEEP.load(std::sync::atomic::Ordering::Relaxed)
}

fn set_keep(on: bool) {
    KEEP.store(on, std::sync::atomic::Ordering::Relaxed);
}

impl std::hash::Hash for Id {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        (*self.0).hash(h)
    }
}

impl Id {
    pub fn as_str(&self) -> &str {
        &self.0
    }
}
impl std::ops::Deref for Id {
    type Target = str;
    fn deref(&self) -> &str {
        &self.0
    }
}
impl std::fmt::Debug for Id {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&*self.0, f)
    }
}
impl std::fmt::Display for Id {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&*self.0, f)
    }
}
impl From<&str> for Id {
    fn from(s: &str) -> Id {
        Id(Rc::from(s))
    }
}
impl From<String> for Id {
    fn from(s: String) -> Id {
        Id(Rc::from(s))
    }
}
impl From<&Id> for Id {
    fn from(s: &Id) -> Id {
        s.clone()
    }
}
impl From<&String> for Id {
    fn from(s: &String) -> Id {
        Id(Rc::from(s.as_str()))
    }
}
thread_local! {
    static EMPTY_ID: Id = Id(Rc::from(""));
}
impl Default for Id {
    /// The empty identifier, shared.
    fn default() -> Id {
        EMPTY_ID.with(Id::clone)
    }
}
impl std::borrow::Borrow<str> for Id {
    fn borrow(&self) -> &str {
        &self.0
    }
}
impl AsRef<str> for Id {
    fn as_ref(&self) -> &str {
        &self.0
    }
}
impl PartialEq for Id {
    fn eq(&self, o: &Id) -> bool {
        Rc::ptr_eq(&self.0, &o.0) || *self.0 == *o.0
    }
}
impl PartialEq<str> for Id {
    fn eq(&self, o: &str) -> bool {
        &*self.0 == o
    }
}
impl PartialEq<&str> for Id {
    fn eq(&self, o: &&str) -> bool {
        &*self.0 == *o
    }
}
impl PartialEq<String> for Id {
    fn eq(&self, o: &String) -> bool {
        &*self.0 == o.as_str()
    }
}
impl PartialEq<&String> for Id {
    fn eq(&self, o: &&String) -> bool {
        &*self.0 == o.as_str()
    }
}
impl PartialEq<Id> for String {
    fn eq(&self, o: &Id) -> bool {
        self.as_str() == &*o.0
    }
}
impl PartialEq<Id> for str {
    fn eq(&self, o: &Id) -> bool {
        self == &*o.0
    }
}
impl PartialEq<Id> for &str {
    fn eq(&self, o: &Id) -> bool {
        *self == &*o.0
    }
}
impl PartialEq<Id> for &String {
    fn eq(&self, o: &Id) -> bool {
        self.as_str() == &*o.0
    }
}

// ---- Input ----------------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub enum Dist {
    Fixed(u64),
    Uniform(u64, u64),
    Table(Rc<[(u64, u64)]>),
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
        res: Id,
        class: Option<String>,
        units: u64,
        demand: Dist,
        then: Id,
        refused: Option<Id>,
        payload: JsObject,
    },
    Release {
        res: Id,
        class: Option<String>,
        units: u64,
    },
    /// An emit sent over a link.
    Send {
        event: String,
        size: SizeIn,
        payload: JsObject,
        reply: bool,
        via: String,
        fanout: bool,
    },
    Timer {
        name: String,
        after: Dist,
        event: String,
        payload: JsObject,
    },
    Cancel(String),
    Malformed,
}

/// The size of a message sent over a link.
#[derive(Clone, Debug)]
pub enum SizeIn {
    None,
    Expr(String),
    Dist(Dist),
}

/// A link (WG-4729).
#[derive(Clone, Debug)]
pub struct Link {
    pub id: Id,
    pub from: String,
    pub to: String,
    pub latency: Dist,
    pub bandwidth: Option<u64>,
    pub queue_bound: Option<u64>,
    pub ordered: bool,
    pub fanout: bool,
}

#[derive(Clone, Debug)]
pub struct Transition {
    pub id: Id,
    pub from: Id,
    pub to: Id,
    pub on: Id,
    pub guard: Option<Id>,
    pub effects: Vec<Effect>,
    pub fault_only: bool,
    /// The random-stream names of each effect, in effect order (filled when the behavior is decoded).
    pub sites: Vec<Site>,
}

/// The stream names of one effect site `<behavior>:<transition>:<k>`.
#[derive(Clone, Debug)]
pub struct Site {
    pub sample: Id,
    pub after: Id,
    pub demand: Id,
    pub size: Id,
}

#[derive(Clone, Debug)]
pub struct Behavior {
    pub id: Id,
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
    pub id: Id,
    pub kind: Option<String>,
    pub event: Option<String>,
    pub transition: Option<String>,
    pub occurrence: Occurrence,
    pub by: u64,
    pub at: u64,
    pub payload: Value,
    pub window: Option<(u64, Option<u64>)>,
    pub resource: Option<String>,
    pub class: Option<String>,
    pub capacity: u64,
    pub limit: u64,
    pub num: u64,
    pub den: u64,
    pub behavior: Option<String>,
    pub effect: u64,
    pub demand: Dist,
}

const RESOURCE_KINDS: [&str; 5] = [
    "set-capacity",
    "set-class-limit",
    "collapse-classes",
    "scale-demand",
    "replace-demand",
];

impl Fault {
    fn is_kind(&self, k: &str) -> bool {
        self.kind.as_deref() == Some(k)
    }
    /// A format-1 fault kind with a window acts only on heads whose time lies in it.
    fn acts_at(&self, t: u64) -> bool {
        match self.window {
            None => true,
            Some((a, u)) => a <= t && u.is_none_or(|u| t < u),
        }
    }
    fn is_resource_kind(&self) -> bool {
        self.kind
            .as_deref()
            .is_some_and(|k| RESOURCE_KINDS.contains(&k))
    }
}

fn active_faults<'a, 'f>(
    faults: &'a [&'f Fault],
    active: &'a [Id],
) -> impl DoubleEndedIterator<Item = &'f Fault> + 'a {
    faults
        .iter()
        .copied()
        .filter(move |f| f.window.is_none() || active.contains(&f.id))
}

fn eff_capacity(faults: &[&Fault], active: &[Id], d: &Resource) -> u64 {
    active_faults(faults, active)
        .rfind(|f| f.is_kind("set-capacity") && f.resource.as_deref() == Some(d.id.as_str()))
        .map_or(d.capacity, |f| f.capacity)
}

/// The resource as the acting faults leave it (Format2.lean, `effDecl`): the declaration itself
/// unless a fault changes it.
fn eff_decl<'d>(
    faults: &[&Fault],
    active: &[Id],
    d: &'d Resource,
) -> std::borrow::Cow<'d, Resource> {
    let touches = |f: &Fault| {
        (f.is_kind("set-class-limit") || f.is_kind("collapse-classes"))
            && f.resource.as_deref() == Some(d.id.as_str())
    };
    if !active_faults(faults, active).any(touches) {
        return std::borrow::Cow::Borrowed(d);
    }
    let mut e = d.clone();
    for cl in &mut e.classes {
        if let Some(f) = active_faults(faults, active).rfind(|f| {
            f.is_kind("set-class-limit")
                && f.resource.as_deref() == Some(d.id.as_str())
                && f.class.as_deref() == Some(cl.id.as_str())
        }) {
            cl.limit = Some(f.limit);
        }
    }
    if active_faults(faults, active)
        .any(|f| f.is_kind("collapse-classes") && f.resource.as_deref() == Some(d.id.as_str()))
    {
        e.by_priority = false;
        e.strict = true;
        for cl in &mut e.classes {
            cl.reserved = 0;
            cl.limit = None;
            cl.queue_bound = None;
        }
    }
    std::borrow::Cow::Owned(e)
}

/// The combined `scale-demand` factor of a resource, in lowest terms.
fn eff_scale(faults: &[&Fault], active: &[Id], res: &str) -> R<(u64, u64)> {
    if !active_faults(faults, active)
        .any(|f| f.is_kind("scale-demand") && f.resource.as_deref() == Some(res))
    {
        return Ok((1, 1));
    }
    let mut n = BigUint::from(1u32);
    let mut m = BigUint::from(1u32);
    for f in active_faults(faults, active) {
        if f.is_kind("scale-demand") && f.resource.as_deref() == Some(res) {
            n *= f.num;
            m *= f.den;
        }
    }
    let g = {
        let (mut a, mut b) = (n.clone(), m.clone());
        while b != BigUint::from(0u32) {
            let r = &a % &b;
            a = b;
            b = r;
        }
        a
    };
    let n = n / &g;
    let m = m / &g;
    let lim = BigUint::from(TWO32);
    if n >= lim || m >= lim {
        return Err(format!("Value demand scale of \"{res}\" exceeds 2^32."));
    }
    Ok((u64::try_from(n).unwrap_or(0), u64::try_from(m).unwrap_or(1)))
}

/// The demand a `use` draws from (Format2.lean, `effDemand`).
fn eff_demand<'d>(faults: &[&'d Fault], active: &[Id], stream: &str, d: &'d Dist) -> &'d Dist {
    active_faults(faults, active)
        .rfind(|f| {
            f.is_kind("replace-demand")
                && format!(
                    "demand:{}:{}:{}",
                    f.behavior.as_deref().unwrap_or(""),
                    f.transition.as_deref().unwrap_or(""),
                    f.effect
                ) == stream
        })
        .map_or(d, |f| &f.demand)
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
    pub id: Id,
    pub priority: i64,
    pub reserved: u64,
    pub limit: Option<u64>,
    pub queue_bound: Option<u64>,
    pub max_wait: Option<u64>,
}

#[derive(Clone, Debug)]
pub struct Resource {
    pub id: Id,
    pub kind: String,
    pub capacity: u64,
    pub by_priority: bool,
    pub queue_bound: Option<u64>,
    pub overflow: Overflow,
    pub demand_factor: DemandFactor,
    pub classes: Vec<Class>,
    /// One strict FIFO queue (a `collapse-classes` fault).
    pub strict: bool,
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

/// A generated payload field of a workload.
#[derive(Clone, Debug)]
pub enum PField {
    Lit(Value),
    Sample(Dist),
    Choose(Vec<Value>, Vec<u64>),
    Counter,
}

#[derive(Clone, Debug)]
pub struct Clients {
    pub count: u64,
    pub round_robin: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WKind {
    Open,
    Closed,
    Population,
}

/// A workload (WG-4715): open, closed or a population. A population's `event` is its start event.
#[derive(Clone, Debug)]
pub struct Workload {
    pub id: Id,
    pub event: String,
    pub poisson: bool,
    pub phases: Vec<Phase>,
    pub period: Option<u64>,
    pub batch: Dist,
    pub clients: Option<Clients>,
    pub legitimate: bool,
    pub max_arrivals: Option<u64>,
    pub payload: Vec<(Rc<str>, PField)>,
    pub request_field: Rc<str>,
    pub client_field: Rc<str>,
    pub address_field: Rc<str>,
    pub kind: WKind,
    /// Closed: the number of clients; population: the number of client instances.
    pub population: u64,
    pub think: Dist,
    /// Closed: the start offset of each client; population: `start.at`.
    pub start: Dist,
    pub reply: String,
    pub timeout: Option<u64>,
    /// Population: the client behavior.
    pub behavior: String,
    /// `clients.addresses.groupSize`.
    pub group_size: Option<Dist>,
    /// The random-stream names of this workload (filled after decoding).
    pub names: WNames,
}

/// The random-stream names of a workload.
#[derive(Clone, Debug, Default)]
pub struct WNames {
    pub arrival: Id,
    pub batch: Id,
    pub client: Id,
    pub think: Id,
    pub groups: Id,
    pub start: Id,
    /// One per payload field, in order.
    pub payload: Vec<Id>,
}

impl WNames {
    fn of(w: &Workload) -> WNames {
        WNames {
            arrival: format!("arrival:{}", w.id).into(),
            batch: format!("batch:{}", w.id).into(),
            client: format!("client:{}", w.id).into(),
            think: format!("think:{}", w.id).into(),
            groups: format!("groups:{}", w.id).into(),
            start: format!("start:{}", w.id).into(),
            payload: w
                .payload
                .iter()
                .map(|(f, _)| format!("payload:{}:{f}", w.id).into())
                .collect(),
        }
    }
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
    pub links: Vec<Link>,
    pub workloads: Vec<Workload>,
    pub unit_exp: Vec<(u64, u128)>,
    /// Quantiles of the measured outputs as `(key, num, den)`; `None` when none are asked.
    pub metrics: Option<Vec<(String, u64, u64)>>,
    /// `metrics.series.bucket`.
    pub series: Option<u64>,
    pub requests: Vec<ReqClass>,
}

/// A request class.
#[derive(Clone, Debug)]
pub struct ReqClass {
    pub id: String,
    pub start_event: String,
    pub start_workload: Option<String>,
    pub key: String,
    pub ends: Vec<(String, &'static str)>,
}

impl Input {
    /// Whether the run reports measured outputs.
    fn measures(&self) -> bool {
        self.metrics.is_some() || self.scenario.output == "metrics" || !self.requests.is_empty()
    }
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
                Ok(Dist::Table(pts.into()))
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
    if fx.contains_key("emit") && fx.contains_key("via") {
        let event = string(fx, "emit", what)?;
        let via = string(fx, "via", what)?;
        if !field(fx, "after").is_nullish() {
            return Err(format!(
                "{what}: \"via\" cannot be combined with \"after\"."
            ));
        }
        let size = match field(fx, "size") {
            Value::Undefined | Value::Null => SizeIn::None,
            Value::String(src) => SizeIn::Expr(src.clone()),
            x => SizeIn::Dist(decode_dist(x, &format!("{what}.size"))?),
        };
        let payload = payload_obj(fx, what)?;
        let reply = match field(fx, "target") {
            Value::Undefined | Value::Null => false,
            Value::String(s) if s == "reply" => true,
            _ => return Err(format!("{what}: \"target\" must be \"reply\".")),
        };
        let fanout = matches!(field(fx, "fanout"), Value::Bool(true));
        return Ok(Effect::Send {
            event,
            size,
            payload,
            reply,
            via,
            fanout,
        });
    }
    if fx.contains_key("timer") {
        let name = string(fx, "timer", what)?;
        let after = decode_dist(field(fx, "after"), &format!("{what}.after"))?;
        let event = string(fx, "emit", what)?;
        let payload = payload_obj(fx, what)?;
        return Ok(Effect::Timer {
            name,
            after,
            event,
            payload,
        });
    }
    if fx.contains_key("cancel") {
        return Ok(Effect::Cancel(string(fx, "cancel", what)?));
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
            res: res.into(),
            class,
            units,
            demand,
            then: then.into(),
            refused: refused.map(Id::from),
            payload,
        });
    }
    if fx.contains_key("release") {
        let res = string(fx, "release", what)?;
        let class = opt_str(fx, "class", what)?;
        let units = int_or(fx, "units", &format!("{what}.units"), 1, TWO32 - 1, 1)?;
        return Ok(Effect::Release {
            res: res.into(),
            class,
            units,
        });
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
        id: string(t, "id", what)?.into(),
        from: string(t, "from", what)?.into(),
        to: string(t, "to", what)?.into(),
        on: string(t, "on", what)?.into(),
        guard: field(t, "guard").as_str().map(Id::from),
        effects,
        fault_only: matches!(field(t, "faultOnly"), Value::Bool(true)),
        sites: Vec::new(),
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
        let mut t = decode_transition(t, &format!("{what}.transitions[{j}]"))?;
        t.sites = (0..t.effects.len())
            .map(|k| {
                let site = format!("{id}:{}:{k}", t.id);
                Site {
                    sample: format!("sample:{site}").into(),
                    after: format!("after:{site}").into(),
                    demand: format!("demand:{site}").into(),
                    size: format!("size:{site}").into(),
                }
            })
            .collect();
        transitions.push(t);
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
        id: id.into(),
        subject,
        initial,
        variables,
        transitions,
        instances,
    })
}

fn decode_fault(v: &Value, i: usize) -> R<Fault> {
    let what = format!("faults[{i}]");
    let f = object(v, &what)?;
    let kind = opt_str(f, "kind", &what)?;
    if kind.as_deref() == Some("crash-instance") {
        return Err(format!(
            "{what}: fault kind \"crash-instance\" is not implemented (WG-4664)."
        ));
    }
    let window = match field(f, "window") {
        Value::Undefined | Value::Null => None,
        w => {
            let wo = object(w, &format!("{what}.window"))?;
            let a = int_in(field(wo, "at"), &format!("{what}.window.at"), 0, TWO53 - 1)?;
            let u = opt_int(wo, "until", &format!("{what}.window.until"), 0, TWO53 - 1)?;
            Some((a, u))
        }
    };
    let occurrence = match field(f, "occurrence") {
        Value::Undefined => Occurrence::Any,
        Value::Number(n) => Occurrence::Exactly(*n),
        _ => Occurrence::Never,
    };
    // `by` of a delay, of a retry (computed by the shell from the retry policy) and of a
    // duplicate's second delivery (0 when left out); Format2.lean, `Decode.fault`.
    let by = match kind.as_deref() {
        Some("delay-event" | "retry-event") => {
            int_in(field(f, "by"), &format!("{what}.by"), 0, TWO53 - 1)?
        }
        Some("duplicate-event") => match field(f, "by") {
            Value::Undefined | Value::Null => 0,
            v => int_in(v, &format!("{what}.by"), 0, TWO53 - 1)?,
        },
        _ => 0,
    };
    let at = if kind.as_deref() == Some("inject-event") {
        int_in(field(f, "at"), &format!("{what}.at"), 0, TWO53 - 1)?
    } else {
        0
    };
    let k = kind.as_deref();
    let resource = opt_str(f, "resource", &what)?;
    let class = opt_str(f, "class", &what)?;
    let capacity = if k == Some("set-capacity") {
        int_in(
            field(f, "capacity"),
            &format!("{what}.capacity"),
            1,
            TWO32 - 1,
        )?
    } else {
        0
    };
    let limit = if k == Some("set-class-limit") {
        int_in(field(f, "limit"), &format!("{what}.limit"), 1, TWO32 - 1)?
    } else {
        0
    };
    let num = if k == Some("scale-demand") {
        int_in(field(f, "num"), &format!("{what}.num"), 0, TWO32 - 1)?
    } else {
        1
    };
    let den = if k == Some("scale-demand") {
        int_in(field(f, "den"), &format!("{what}.den"), 1, TWO32 - 1)?
    } else {
        1
    };
    let behavior = opt_str(f, "behavior", &what)?;
    let effect = if k == Some("replace-demand") {
        int_in(field(f, "effect"), &format!("{what}.effect"), 0, TWO32 - 1)?
    } else {
        0
    };
    let demand = if k == Some("replace-demand") {
        decode_dist(field(f, "demand"), &format!("{what}.demand"))?
    } else {
        Dist::Fixed(0)
    };
    Ok(Fault {
        window,
        resource,
        class,
        capacity,
        limit,
        num,
        den,
        behavior,
        effect,
        demand,
        id: string(f, "id", &what)?.into(),
        event: opt_str(f, "event", &what)?,
        transition: opt_str(f, "transition", &what)?,
        kind,
        occurrence,
        by,
        at,
        payload: payload_or_empty(field(f, "payload")),
    })
}

fn decode_link(v: &Value, i: usize) -> R<Link> {
    let what = format!("links[{i}]");
    let o = object(v, &what)?;
    let id = string(o, "id", &what)?;
    let from = field(o, "from").as_str().unwrap_or("").to_string();
    let to = field(o, "to").as_str().unwrap_or("").to_string();
    let latency = match field(o, "latency") {
        Value::Undefined | Value::Null => Dist::Fixed(0),
        x => decode_dist(x, &format!("{what}.latency"))?,
    };
    let bandwidth = opt_int(
        o,
        "bandwidth",
        &format!("{what}.bandwidth"),
        1,
        (1 << 40) - 1,
    )?;
    let queue_bound = opt_int(o, "queueBound", &format!("{what}.queueBound"), 0, TWO32 - 1)?;
    Ok(Link {
        id: id.into(),
        from,
        to,
        latency,
        bandwidth,
        queue_bound,
        ordered: matches!(field(o, "ordered"), Value::Bool(true)),
        fanout: matches!(field(o, "fanout"), Value::Bool(true)),
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
                    id: cid.into(),
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
        id: id.into(),
        kind,
        capacity,
        by_priority,
        queue_bound,
        overflow,
        demand_factor,
        classes,
        strict: false,
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
/// A natural number written as a JSON number or as a decimal string, in `[0, hi]`.
fn big_nat(v: &Value, path: &str, hi: u128) -> R<u128> {
    let err = || format!("Field \"{path}\" must be an integer in [0, {hi}].");
    match v {
        Value::Number(_) => {
            let h = u64::try_from(hi.min(u128::from(TWO53 - 1))).unwrap_or(TWO53 - 1);
            int_in(v, path, 0, h).map(u128::from)
        }
        Value::String(s) => {
            let bs = s.as_bytes();
            if bs.is_empty()
                || !bs.iter().all(u8::is_ascii_digit)
                || (bs.len() > 1 && bs[0] == b'0')
            {
                return Err(err());
            }
            match s.parse::<u128>() {
                Ok(n) if n <= hi => Ok(n),
                _ => Err(err()),
            }
        }
        _ => Err(err()),
    }
}

fn decode_unit_exp(v: &Value) -> R<Vec<(u64, u128)>> {
    let malformed = || "Distribution \"unitExponential\" has a malformed table.".to_string();
    match v {
        Value::Undefined | Value::Null => Ok(Vec::new()),
        Value::Array(xs) => {
            let mut pts = Vec::new();
            for (i, p) in xs.iter().enumerate() {
                match p {
                    Value::Array(ux) if ux.len() == 2 => {
                        let u = big_nat(&ux[0], &format!("unitExponential[{i}][0]"), 1u128 << 32)?;
                        let x = big_nat(
                            &ux[1],
                            &format!("unitExponential[{i}][1]"),
                            (1u128 << 72) - 1,
                        )?;
                        pts.push((u as u64, x));
                    }
                    _ => return Err(malformed()),
                }
            }
            let ok = pts.first().map(|p| p.0) == Some(0)
                && pts.last().map(|p| p.0) == Some(TWO32)
                && pts.windows(2).all(|w| w[0].0 < w[1].0 && w[0].1 <= w[1].1);
            if ok {
                Ok(pts)
            } else {
                Err(malformed())
            }
        }
        _ => Err(malformed()),
    }
}

fn decode_rate(v: &Value, path: &str) -> R<(u64, u64)> {
    let o = object(v, path)?;
    let num = int_in(field(o, "num"), &format!("{path}.num"), 0, TWO32 - 1)?;
    let den = int_in(field(o, "den"), &format!("{path}.den"), 1, TWO32 - 1)?;
    Ok((num, den))
}

fn decode_pfield(what: &str, k: &str, x: &Value) -> R<PField> {
    let pw = format!("{what}.payload.{k}");
    let Value::Object(xo) = x else {
        return Ok(PField::Lit(x.clone()));
    };
    if xo.get("sample").is_some() {
        return Ok(PField::Sample(decode_dist(
            field(xo, "sample"),
            &format!("{pw}.sample"),
        )?));
    }
    if xo.get("choose").is_some() {
        let vs = array(xo, "choose", &pw)?.to_vec();
        let mut ws = Vec::new();
        for (j, w) in array(xo, "weights", &pw)?.iter().enumerate() {
            ws.push(int_in(w, &format!("{pw}.weights[{j}]"), 0, TWO32 - 1)?);
        }
        let total: u64 = ws.iter().sum();
        if vs.len() != ws.len() || total == 0 || total >= TWO53 {
            return Err(format!(
                "Field \"{pw}\" must have one weight per value, with a sum in [1, 2^53)."
            ));
        }
        return Ok(PField::Choose(vs, ws));
    }
    if matches!(field(xo, "counter"), Value::Bool(true)) {
        return Ok(PField::Counter);
    }
    Ok(PField::Lit(x.clone()))
}

fn decode_clients(
    o: &JsObject,
    what: &str,
    count: Option<u64>,
) -> R<(Option<Clients>, Option<Dist>)> {
    let c = field(o, "clients");
    if c.is_nullish() {
        return Ok((None, None));
    }
    let co = object(c, &format!("{what}.clients"))?;
    let count = match count {
        Some(n) => n,
        None => int_in(
            field(co, "count"),
            &format!("{what}.clients.count"),
            1,
            TWO32 - 1,
        )?,
    };
    let round_robin = match field(co, "pick") {
        Value::Undefined | Value::Null => false,
        Value::String(p) if p == "uniform" => false,
        Value::String(p) if p == "round-robin" => true,
        _ => {
            return Err(format!(
                "{what}.clients: \"pick\" must be uniform or round-robin."
            ))
        }
    };
    let group_size = match field(co, "addresses") {
        Value::Undefined | Value::Null => None,
        a => {
            let ao = object(a, &format!("{what}.clients.addresses"))?;
            Some(decode_dist(
                field(ao, "groupSize"),
                &format!("{what}.clients.addresses.groupSize"),
            )?)
        }
    };
    Ok((Some(Clients { count, round_robin }), group_size))
}

fn opt_dist(o: &JsObject, key: &str, path: &str) -> R<Dist> {
    match field(o, key) {
        Value::Undefined | Value::Null => Ok(Dist::Fixed(0)),
        x => decode_dist(x, path),
    }
}

fn decode_workload(v: &Value, i: usize) -> R<Workload> {
    let what = format!("workloads[{i}]");
    let o = object(v, &what)?;
    let id = string(o, "id", &what)?;
    let kind = string(o, "kind", &what)?;
    let legitimate = !matches!(field(o, "legitimate"), Value::Bool(false));
    let payload = match field(o, "payload") {
        Value::Object(fs) => {
            let mut out = Vec::new();
            for (k, x) in fs.iter() {
                out.push((k.clone(), decode_pfield(&what, k, x)?));
            }
            out
        }
        x if x.is_nullish() => Vec::new(),
        _ => return Err(format!("{what}: \"payload\" must be an object.")),
    };
    let fname = |k: &str, d: &str| -> Rc<str> { Rc::from(field(o, k).as_str().unwrap_or(d)) };
    let base = Workload {
        id: id.as_str().into(),
        event: String::new(),
        poisson: false,
        phases: Vec::new(),
        period: None,
        batch: Dist::Fixed(1),
        clients: None,
        legitimate,
        max_arrivals: None,
        payload,
        request_field: fname("requestField", "request"),
        client_field: fname("clientField", "client"),
        address_field: fname("addressField", "address"),
        kind: WKind::Open,
        population: 0,
        think: Dist::Fixed(0),
        start: Dist::Fixed(0),
        reply: String::new(),
        timeout: None,
        behavior: String::new(),
        group_size: None,
        names: WNames::default(),
    };
    if kind == "closed" {
        let event = string(o, "event", &what)?;
        let population = int_in(
            field(o, "population"),
            &format!("{what}.population"),
            0,
            TWO32 - 1,
        )?;
        let think = opt_dist(o, "think", &format!("{what}.think"))?;
        let start = opt_dist(o, "start", &format!("{what}.start"))?;
        let reply = string(o, "reply", &what)?;
        let timeout = opt_int(o, "timeout", &format!("{what}.timeout"), 1, TWO53 - 1)?;
        return Ok(Workload {
            kind: WKind::Closed,
            event,
            population,
            think,
            start,
            reply,
            timeout,
            clients: Some(Clients {
                count: population,
                round_robin: true,
            }),
            ..base
        });
    }
    if kind == "population" {
        let behavior = string(o, "behavior", &what)?;
        let count = int_in(field(o, "count"), &format!("{what}.count"), 0, TWO32 - 1)?;
        let so = object(field(o, "start"), &format!("{what}.start"))?;
        let event = string(so, "event", &format!("{what}.start"))?;
        let start = opt_dist(so, "at", &format!("{what}.start.at"))?;
        let (_, group_size) = decode_clients(o, &what, Some(count))?;
        return Ok(Workload {
            kind: WKind::Population,
            event,
            population: count,
            start,
            behavior,
            group_size,
            clients: Some(Clients {
                count,
                round_robin: true,
            }),
            ..base
        });
    }
    if kind != "open" {
        return Err(format!(
            "{what}: \"kind\" must be open, closed or population."
        ));
    }
    let event = string(o, "event", &what)?;
    let poisson = match field(o, "process").as_str() {
        Some("poisson") => true,
        Some("constant") => false,
        _ => return Err(format!("{what}: \"process\" must be poisson or constant.")),
    };
    let mut phases = Vec::new();
    for (k, p) in array(o, "phases", &what)?.iter().enumerate() {
        let pw = format!("{what}.phases[{k}]");
        let po = object(p, &pw)?;
        let start = int_in(field(po, "from"), &format!("{pw}.from"), 0, TWO53 - 1)?;
        let stop = int_in(field(po, "until"), &format!("{pw}.until"), 0, TWO53 - 1)?;
        let ro = object(field(po, "rate"), &format!("{pw}.rate"))?;
        let rate = match (field(ro, "from"), field(ro, "to")) {
            (Value::Undefined, Value::Undefined) => {
                let (a, b) = decode_rate(field(po, "rate"), &format!("{pw}.rate"))?;
                Rate::Const(a, b)
            }
            (f, t) => {
                let (a0, b0) = decode_rate(f, &format!("{pw}.rate.from"))?;
                let (a1, b1) = decode_rate(t, &format!("{pw}.rate.to"))?;
                Rate::Ramp(a0, b0, a1, b1)
            }
        };
        phases.push(Phase { start, stop, rate });
    }
    let period = opt_int(o, "repeat", &format!("{what}.repeat"), 1, TWO53 - 1)?;
    let batch = match field(o, "batch") {
        Value::Undefined | Value::Null => Dist::Fixed(1),
        b => decode_dist(b, &format!("{what}.batch"))?,
    };
    let (clients, group_size) = decode_clients(o, &what, None)?;
    let max_arrivals = opt_int(
        o,
        "maxArrivals",
        &format!("{what}.maxArrivals"),
        0,
        TWO32 - 1,
    )?;
    Ok(Workload {
        event,
        poisson,
        phases,
        period,
        batch,
        clients,
        max_arrivals,
        group_size,
        ..base
    })
}

/// An exact decimal in (0, 1]: `"1"` or `"0.<digits>"`.
fn decode_quantile(v: &Value, path: &str) -> R<(String, u64, u64)> {
    let err = || format!("Field \"{path}\" must be an exact decimal in (0, 1].");
    match v {
        Value::String(q) if q == "1" => Ok(("1".into(), 1, 1)),
        Value::String(q) => {
            let Some(ds) = q.strip_prefix("0.") else {
                return Err(err());
            };
            if ds.is_empty() || ds.len() > 18 || !ds.bytes().all(|c| c.is_ascii_digit()) {
                return Err(err());
            }
            let n: u64 = ds.parse().map_err(|_| err())?;
            if n == 0 {
                return Err(err());
            }
            Ok((q.clone(), n, 10u64.pow(ds.len() as u32)))
        }
        _ => Err(err()),
    }
}

fn default_quantiles() -> Vec<(String, u64, u64)> {
    vec![
        ("0.5".into(), 1, 2),
        ("0.9".into(), 9, 10),
        ("0.99".into(), 99, 100),
    ]
}

fn decode_req_class(v: &Value, i: usize) -> R<ReqClass> {
    let what = format!("requests[{i}]");
    let o = object(v, &what)?;
    let id = string(o, "id", &what)?;
    let so = object(field(o, "start"), &format!("{what}.start"))?;
    let start_event = string(so, "event", &format!("{what}.start"))?;
    let start_workload = opt_str(so, "workload", &format!("{what}.start"))?;
    let key = string(o, "key", &what)?;
    let mut ends = Vec::new();
    for (j, e) in array_or_empty(o, "ends").iter().enumerate() {
        let ew = format!("{what}.ends[{j}]");
        let eo = object(e, &ew)?;
        let ev = string(eo, "event", &ew)?;
        let out = string(eo, "outcome", &ew)?;
        let out: &'static str = match out.as_str() {
            "ok" => "ok",
            "refused" => "refused",
            "timeout" => "timeout",
            "error" => "error",
            _ => {
                return Err(format!(
                    "Request class \"{id}\": outcome must be ok, refused, timeout or error."
                ))
            }
        };
        ends.push((ev, out));
    }
    Ok(ReqClass {
        id,
        start_event,
        start_workload,
        key,
        ends,
    })
}

fn decode_series(v: &Value) -> R<Option<u64>> {
    let Value::Object(o) = v else { return Ok(None) };
    match field(o, "series") {
        Value::Undefined | Value::Null => Ok(None),
        s => {
            let so = object(s, "metrics.series")?;
            Ok(Some(int_in(
                field(so, "bucket"),
                "metrics.series.bucket",
                1,
                TWO53 - 1,
            )?))
        }
    }
}

fn decode_metrics(v: &Value) -> R<Option<Vec<(String, u64, u64)>>> {
    match v {
        Value::Undefined | Value::Null => Ok(None),
        Value::Object(o) => match field(o, "quantiles") {
            Value::Undefined | Value::Null => Ok(Some(default_quantiles())),
            Value::Array(qs) => {
                let mut out = Vec::new();
                for (i, q) in qs.iter().enumerate() {
                    out.push(decode_quantile(q, &format!("metrics.quantiles[{i}]"))?);
                }
                Ok(Some(out))
            }
            _ => Err("Field \"metrics.quantiles\" must be an array.".into()),
        },
        _ => Err("Field \"metrics\" must be an object.".into()),
    }
}

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
    for k in ["meters", "prices"] {
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
    let mut links = Vec::new();
    for (i, l) in array_or_empty(root, "links").iter().enumerate() {
        links.push(decode_link(l, i)?);
    }
    let mut workloads = Vec::new();
    for (i, w) in array_or_empty(root, "workloads").iter().enumerate() {
        let mut wl = decode_workload(w, i)?;
        wl.names = WNames::of(&wl);
        workloads.push(wl);
    }
    let unit_exp = decode_unit_exp(field(root, "unitExponential"))?;
    let metrics = decode_metrics(field(root, "metrics"))?;
    let series = decode_series(field(root, "metrics"))?;
    let mut requests = Vec::new();
    for (i, r) in array_or_empty(root, "requests").iter().enumerate() {
        requests.push(decode_req_class(r, i)?);
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
        links,
        workloads,
        unit_exp,
        metrics,
        series,
        requests,
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
    fn class_id(&self, i: usize) -> Id {
        thread_local! {
            static DEFAULT_CLASS: Id = Id::from("default");
        }
        self.class_at(i)
            .map_or_else(|| DEFAULT_CLASS.with(Id::clone), |c| c.id.clone())
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

fn machine_key(b: &Behavior, inst: &Value) -> Id {
    match b.instances {
        Instances::Single => b.id.clone(),
        _ => format!("{}#{}", b.id, inst.to_json()).into(),
    }
}

fn initial_machine(b: &Behavior) -> Machine {
    let mut vars = JsObject::new();
    for (name, v) in &b.variables {
        vars.insert(name.clone(), v.clone());
    }
    Machine {
        state: b.initial.as_str().into(),
        vars,
    }
}

// ---- Arrivals (Format2.lean, makeInstant) ---------------------------------------------------

/// The address index of user `k`: users fill address 0, then 1, and so on.
fn group_of(groups: &[u64], mut k: u64) -> u64 {
    let mut a = 0;
    for &g in groups {
        if k < g {
            return a;
        }
        k -= g;
        a += 1;
    }
    a
}

/// The address of client `k`: `<w>@<a>` with address groups, else the client.
fn address_of(w: &Workload, st: &WState, k: u64) -> String {
    match w.group_size {
        Some(_) => format!("{}@{}", w.id, group_of(&st.groups, k)),
        None => format!("{}:{k}", w.id),
    }
}

/// The generated payload of entry `n` for `client`: payload fields in declaration order, then
/// the request id, client and address.
fn gen_payload(
    i: &Input,
    w: &Workload,
    st: &WState,
    n_: u64,
    client: Option<u64>,
    streams: &mut Vec<(Rc<str>, u64)>,
    draws: &mut Vec<Draw>,
) -> JsObject {
    let seed = i.scenario.seed.unwrap_or(0);
    let mut fs = JsObject::new();
    for (fi, (f, pf)) in w.payload.iter().enumerate() {
        let pname = &w.names.payload[fi];
        match pf {
            PField::Lit(v) => fs.insert(f.clone(), v.deep_copy()),
            PField::Counter => fs.insert(f.clone(), Value::Number(n_ as f64)),
            PField::Sample(d) => {
                let x = sample(i.scenario.seed, streams, pname, d, draws);
                fs.insert(f.clone(), Value::Number(x as f64));
            }
            PField::Choose(vs, ws) => {
                let (r, dr) = draw_next(seed, streams, pname);
                draws.push(dr);
                let v = vs
                    .get(random::categorical(r, ws))
                    .cloned()
                    .unwrap_or(Value::Null);
                fs.insert(f.clone(), v.deep_copy());
            }
        }
    }
    fs.insert(
        w.request_field.clone(),
        Value::str(format!("{}#{n_}", w.id)),
    );
    if let Some(c) = client {
        fs.insert(w.client_field.clone(), Value::str(format!("{}:{c}", w.id)));
        fs.insert(w.address_field.clone(), Value::str(address_of(w, st, c)));
    }
    fs
}

/// Create the next arrival instant of an open workload, if any; returns the draws in order and
/// advances `seq`.
fn make_instant(
    i: &Input,
    w: &Workload,
    st: &mut WState,
    streams: &mut Vec<(Rc<str>, u64)>,
    seq: &mut u64,
    q: &mut Vec<Sh<Entry>>,
) -> Vec<Draw> {
    let full = w.max_arrivals.is_some_and(|m| st.arrivals >= m);
    if st.cursor.done || full {
        st.cursor.done = true;
        return Vec::new();
    }
    let seed = i.scenario.seed.unwrap_or(0);
    let aname = &w.names.arrival;
    let base = lookup(streams, aname);
    let ex = |k: u64| -> u128 {
        random::sample_table_wide(random::draw(seed, aname, base + k), &i.unit_exp)
    };
    let horizon = i.scenario.horizon.unwrap_or(0);
    let (t, cur, used) = work::next_time(
        i.per_second.unwrap_or(1),
        horizon,
        &w.phases,
        w.period,
        w.poisson,
        &ex,
        work::fuel_for(horizon, &w.phases),
        st.cursor.clone(),
    );
    let mut draws: Vec<Draw> = (0..if keep() { used } else { 0 })
        .map(|k| Draw {
            stream: aname.clone(),
            index: base + k,
            value: random::draw(seed, aname, base + k),
        })
        .collect();
    for _ in 0..used {
        bump(streams, aname);
    }
    let Some(t) = t else {
        st.cursor = cur;
        return draws;
    };
    let b = sample(
        i.scenario.seed,
        streams,
        &w.names.batch,
        &w.batch,
        &mut draws,
    )
    .max(1);
    let b = match w.max_arrivals {
        Some(m) => b.min(m - st.arrivals),
        None => b,
    };
    for k in 0..b {
        let n_ = st.arrivals + k;
        let client = match &w.clients {
            None => None,
            Some(cl) if cl.round_robin => Some(n_ % cl.count),
            Some(cl) => {
                let (r, dr) = draw_next(seed, streams, &w.names.client);
                draws.push(dr);
                Some(random::index(r, cl.count as usize) as u64)
            }
        };
        let fs = gen_payload(i, w, st, n_, client, streams, &mut draws);
        let cname: Option<Id> = client.map(|c| format!("{}:{c}", w.id).into());
        insert_entry(
            q,
            Entry {
                seq: *seq,
                time: t,
                scheduled_at: t,
                event: w.event.as_str().into(),
                payload: Value::object(fs),
                source: Src::Arrival(w.id.clone(), n_, cname),
                kind: EntryKind::Event,
                target: None,
                sender: None,
                routes: None,
                first: if k == 0 { Some(st.instants) } else { None },
                timer: None,
                copy_of: None,
            },
        );
        *seq += 1;
    }
    st.instants += 1;
    st.arrivals += b;
    st.cursor = cur;
    if w.max_arrivals.is_some_and(|m| st.arrivals >= m) {
        st.cursor.done = true;
    }
    draws
}

/// A closed client `c` issues its next request at `t`, unless `t` is at or after the horizon:
/// the arrival entry, then its `client-timeout` entry when the workload has a `timeout`.
#[allow(clippy::too_many_arguments)]
fn issue(
    i: &Input,
    w: &Workload,
    st: &mut WState,
    c: u64,
    t: u64,
    streams: &mut Vec<(Rc<str>, u64)>,
    seq: &mut u64,
    q: &mut Vec<Sh<Entry>>,
    draws: &mut Vec<Draw>,
) {
    if t >= i.scenario.horizon.unwrap_or(0) {
        st.clients[c as usize] = None;
        return;
    }
    let n_ = st.arrivals;
    let fs = gen_payload(i, w, st, n_, Some(c), streams, draws);
    let cname: Id = format!("{}:{c}", w.id).into();
    insert_entry(
        q,
        Entry {
            seq: *seq,
            time: t,
            scheduled_at: t,
            event: w.event.as_str().into(),
            payload: Value::object(fs),
            source: Src::Arrival(w.id.clone(), n_, Some(cname.clone())),
            kind: EntryKind::Event,
            target: None,
            sender: None,
            routes: None,
            first: None,
            timer: None,
            copy_of: None,
        },
    );
    *seq += 1;
    if let Some(to) = w.timeout {
        insert_entry(
            q,
            Entry {
                seq: *seq,
                time: t + to,
                scheduled_at: t + to,
                event: Id::default(),
                payload: Value::Null,
                source: Src::ClientTimeout(w.id.clone(), n_, cname),
                kind: EntryKind::ClientTimeout {
                    workload: w.id.clone(),
                    client: c,
                    n: n_,
                },
                target: None,
                sender: None,
                routes: None,
                first: None,
                timer: None,
                copy_of: None,
            },
        );
        *seq += 1;
    }
    st.arrivals = n_ + 1;
    st.clients[c as usize] = Some(n_);
}

/// A closed client `c` got its reply or gave up at `now`: it thinks (`think:<w>`) and issues again.
#[allow(clippy::too_many_arguments)]
fn rethink(
    i: &Input,
    w: &Workload,
    st: &mut WState,
    c: u64,
    now: u64,
    streams: &mut Vec<(Rc<str>, u64)>,
    seq: &mut u64,
    q: &mut Vec<Sh<Entry>>,
    draws: &mut Vec<Draw>,
) {
    let d = sample(i.scenario.seed, streams, &w.names.think, &w.think, draws);
    st.clients[c as usize] = None;
    issue(i, w, st, c, now + d, streams, seq, q, draws);
}

/// The initial entries of a workload, after its address groups (Format2.lean, initialWorkload).
fn initial_workload(
    i: &Input,
    c: &mut Conf,
    w: &Workload,
    st: &mut WState,
    seq: &mut u64,
) -> Vec<Draw> {
    let mut draws = Vec::new();
    if let Some(d) = &w.group_size {
        let mut left = w.clients.as_ref().map_or(0, |cl| cl.count);
        let name = &w.names.groups;
        while left > 0 {
            let g = sample(i.scenario.seed, &mut c.streams, name, d, &mut draws).max(1);
            st.groups.push(g);
            left -= g.min(left);
        }
    }
    match w.kind {
        WKind::Open => {
            draws.extend(make_instant(i, w, st, &mut c.streams, seq, &mut c.pending));
        }
        WKind::Closed => {
            st.clients = vec![None; w.population as usize];
            let sname = &w.names.start;
            for k in 0..w.population {
                let t = sample(i.scenario.seed, &mut c.streams, sname, &w.start, &mut draws);
                issue(
                    i,
                    w,
                    st,
                    k,
                    t,
                    &mut c.streams,
                    seq,
                    &mut c.pending,
                    &mut draws,
                );
            }
        }
        WKind::Population => {
            let Some(b) = i.behavior(&w.behavior) else {
                return draws;
            };
            let keys: Vec<Value> = (0..w.population)
                .map(|k| Value::str(format!("{}:{k}", w.id)))
                .collect();
            if let Some((_, xs)) = c.insts.iter_mut().find(|(k, _)| **k == *b.id) {
                xs.extend(keys.iter().cloned());
            }
            for v in &keys {
                c.set_machine(&machine_key(b, v), initial_machine(b));
            }
            let sname = &w.names.start;
            for k in 0..w.population {
                let t = sample(i.scenario.seed, &mut c.streams, sname, &w.start, &mut draws);
                if t >= i.scenario.horizon.unwrap_or(0) {
                    continue;
                }
                let cname: Id = format!("{}:{k}", w.id).into();
                let mut fs = JsObject::new();
                fs.insert(w.client_field.clone(), Value::str(cname.as_str()));
                fs.insert(w.address_field.clone(), Value::str(address_of(w, st, k)));
                insert_entry(
                    &mut c.pending,
                    Entry {
                        seq: *seq,
                        time: t,
                        scheduled_at: t,
                        event: w.event.as_str().into(),
                        payload: Value::object(fs),
                        source: Src::Arrival(w.id.clone(), k, Some(cname.clone())),
                        kind: EntryKind::Event,
                        target: Some(Addr {
                            behavior: b.id.clone(),
                            inst: Value::str(cname.as_str()),
                            incarnation: 0,
                        }),
                        sender: None,
                        routes: None,
                        first: None,
                        timer: None,
                        copy_of: None,
                    },
                );
                *seq += 1;
            }
        }
    }
    draws
}

// ---- Configuration --------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct Machine {
    pub state: Id,
    pub vars: JsObject,
}

#[derive(Clone, Debug)]
pub struct Addr {
    pub behavior: Id,
    pub inst: Value,
    pub incarnation: u64,
}

#[derive(Clone, Debug)]
pub enum Src {
    Scenario(u64),
    Fault(Id),
    Transition(Id, Id),
    Resource(Id, u64, &'static str),
    Arrival(Id, u64, Option<Id>),
    /// A closed client's timeout: workload, request number, client.
    ClientTimeout(Id, u64, Id),
    Timer(Id, Value, Id),
    Link(Id, u64),
}

#[derive(Clone, Debug)]
pub struct ReqInfo {
    requester: Addr,
    then: Id,
    refused: Option<Id>,
    payload: JsObject,
    demand: Dist,
    stream: Id,
}

#[derive(Clone, Debug)]
pub struct Req {
    id: u64,
    owner: Rc<str>,
    cls: usize,
    units: u64,
    since: u64,
    kind: ReqKind,
    info: Rc<ReqInfo>,
}

#[derive(Clone, Debug)]
pub struct Hold {
    owner: Rc<str>,
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
        res: Id,
        req: Req,
        waited: u64,
        served: u64,
    },
    WaitTimeout {
        res: Id,
        request: u64,
    },
    ClientTimeout {
        workload: Id,
        client: u64,
        n: u64,
    },
    LinkDone {
        link: Id,
        key: Id,
        msg: u64,
    },
    FaultEdge {
        fault: Id,
        on: bool,
    },
}

#[derive(Clone, Debug)]
pub struct Entry {
    seq: u64,
    time: u64,
    scheduled_at: u64,
    event: Id,
    payload: Value,
    source: Src,
    kind: EntryKind,
    target: Option<Addr>,
    sender: Option<Addr>,
    routes: Option<Vec<(Id, Value)>>,
    /// The instant number, on the original first entry of an arrival instant only.
    first: Option<u64>,
    /// The timer id of a timer firing.
    timer: Option<String>,
    /// On a delayed copy: the sequence number of the original entry.
    copy_of: Option<u64>,
}

/// A message on a link.
#[derive(Clone, Debug)]
pub struct Msg {
    id: u64,
    event: String,
    payload: Value,
    size: u64,
    sent_at: u64,
    target: Option<Addr>,
    sender: Option<Addr>,
}

/// A link's transfer queue.
#[derive(Clone, Debug, Default)]
pub struct LQueue {
    in_transfer: Option<Msg>,
    waiting: Vec<Msg>,
    last_delivery: Option<u64>,
}

/// The state of an open workload.
#[derive(Clone, Debug, Default)]
pub struct WState {
    instants: u64,
    arrivals: u64,
    cursor: Cursor,
    /// Closed: per client, the number of its outstanding request.
    clients: Vec<Option<u64>>,
    /// With `addresses`: the group size of each address.
    groups: Vec<u64>,
}

/// A shared value with copy-on-write: cloning is a reference-count bump, and the first write
/// through `DerefMut` after a clone copies the value.
#[derive(Debug)]
pub struct Sh<T>(Rc<T>);

impl<T> Clone for Sh<T> {
    fn clone(&self) -> Self {
        Sh(Rc::clone(&self.0))
    }
}

impl<T: Default> Default for Sh<T> {
    fn default() -> Self {
        Sh(Rc::new(T::default()))
    }
}

impl<T> Sh<T> {
    fn new(v: T) -> Self {
        Sh(Rc::new(v))
    }
}

impl<T: Clone> Sh<Vec<T>> {
    /// Make this a copy of `src`: into the existing buffer when this is its only owner, else shared.
    fn copy_from(&mut self, src: &Sh<Vec<T>>) {
        match Rc::get_mut(&mut self.0) {
            Some(v) => v.clone_from(&src.0),
            None => self.0 = Rc::clone(&src.0),
        }
    }
}

impl<T> From<T> for Sh<T> {
    fn from(v: T) -> Self {
        Sh(Rc::new(v))
    }
}

impl<T> std::ops::Deref for Sh<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0
    }
}

impl<T: Clone> std::ops::DerefMut for Sh<T> {
    fn deref_mut(&mut self) -> &mut T {
        Rc::make_mut(&mut self.0)
    }
}

#[derive(Clone, Debug, Default)]
pub struct Conf {
    time: u64,
    machines: Sh<Vec<(Rc<str>, Sh<Machine>)>>,
    insts: Sh<Vec<(Rc<str>, Vec<Value>)>>,
    pending: Sh<Vec<Sh<Entry>>>,
    resources: Sh<Vec<(Rc<str>, Sh<RState>)>>,
    route_counters: Sh<Vec<(Rc<str>, u64)>>,
    streams: Sh<Vec<(Rc<str>, u64)>>,
    workloads: Sh<Vec<(Rc<str>, Sh<WState>)>>,
    /// Link queues by (link, key), in creation order.
    lqueues: Sh<Vec<((String, String), LQueue)>>,
    /// The windowed faults acting now, in `faults` order.
    active: Vec<Id>,
}

impl Conf {
    fn machine(&self, k: &str) -> Option<&Machine> {
        self.machines
            .iter()
            .find(|(id, _)| &**id == k)
            .map(|(_, m)| &**m)
    }
    fn machine_mut(&mut self, k: &str) -> Option<&mut Machine> {
        self.machines
            .iter_mut()
            .find(|(id, _)| &**id == k)
            .map(|(_, m)| &mut **m)
    }
    fn set_machine(&mut self, k: &str, m: Machine) {
        match self.machine_mut(k) {
            Some(slot) => *slot = m,
            None => self.machines.push((Rc::from(k), Sh::new(m))),
        }
    }
    fn insts_of(&self, b: &str) -> &[Value] {
        self.insts
            .iter()
            .find(|(k, _)| &**k == b)
            .map_or(&[], |(_, v)| v.as_slice())
    }
    fn lqueue(&self, l: &str, k: &str) -> LQueue {
        self.lqueues
            .iter()
            .find(|((a, b), _)| a == l && b == k)
            .map(|(_, q)| q.clone())
            .unwrap_or_default()
    }
    fn set_lqueue(&mut self, l: &str, k: &str, q: LQueue) {
        match self.lqueues.iter_mut().find(|((a, b), _)| a == l && b == k) {
            Some((_, slot)) => *slot = q,
            None => self.lqueues.push(((l.to_string(), k.to_string()), q)),
        }
    }
    fn resource(&self, r: &str) -> Option<&RState> {
        self.resources
            .iter()
            .find(|(k, _)| &**k == r)
            .map(|(_, s)| &**s)
    }
    fn resource_mut(&mut self, r: &str) -> Option<&mut RState> {
        self.resources
            .iter_mut()
            .find(|(k, _)| &**k == r)
            .map(|(_, s)| &mut **s)
    }
    /// The deep copy of format 1, written into `dst` (whose buffers are reused when it owns
    /// them): machine variables get fresh identities (pending payloads do too, but only the
    /// head's is ever observed, so `run` copies that one when it takes it). Only values that
    /// have an identity (arrays and objects) are copied; everything else is shared until written.
    fn deep_copy(&self) -> Conf {
        let mut c = Conf::default();
        self.deep_copy_into(&mut c);
        c
    }

    fn deep_copy_into(&self, dst: &mut Conf) {
        dst.time = self.time;
        dst.machines.copy_from(&self.machines);
        dst.insts.copy_from(&self.insts);
        dst.pending.copy_from(&self.pending);
        dst.resources.copy_from(&self.resources);
        dst.route_counters.copy_from(&self.route_counters);
        dst.streams.copy_from(&self.streams);
        dst.workloads.copy_from(&self.workloads);
        dst.lqueues.copy_from(&self.lqueues);
        dst.active.clone_from(&self.active);
        for i in 0..dst.machines.len() {
            if dst.machines[i].1.vars.iter().any(|(_, v)| v.has_identity()) {
                let m = &mut dst.machines[i].1;
                m.vars = m.vars.deep_copy();
            }
        }
    }
}

fn lookup(xs: &[(Rc<str>, u64)], k: &str) -> u64 {
    xs.iter().find(|(x, _)| &**x == k).map_or(0, |(_, n)| *n)
}

fn bump(xs: &mut Vec<(Rc<str>, u64)>, k: &str) {
    match xs.iter_mut().find(|(x, _)| &**x == k) {
        Some((_, n)) => *n += 1,
        None => xs.push((Rc::from(k), 1)),
    }
}

fn insert_entry(q: &mut Vec<Sh<Entry>>, e: Entry) {
    // The queue is ordered by time and keeps insertion order within a time: an entry goes after
    // every entry at its time or earlier (the queue is sorted, so a binary search finds it).
    let i = q.partition_point(|x| x.time <= e.time);
    q.insert(i, Sh::new(e));
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
    sum_units(hs, |h| &*h.owner == owner && h.cls == c && h.req.is_none())
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
        if !d.strict && !fits(d, s, r) {
            continue;
        }
        best = match best {
            None => Some(r),
            Some(b) => Some(if before(d, r, b) { r } else { b }),
        };
    }
    if d.strict && best.is_some_and(|r| !fits(d, s, r)) {
        return None;
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
        if &*h.owner == owner && h.cls == c && h.req.is_none() {
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
    stream: Id,
    index: u64,
    value: u64,
}

#[derive(Clone, Debug)]
struct ResRecord {
    resource: Id,
    class: Id,
    request: Option<u64>,
    action: &'static str,
    at: u64,
    waited: Option<u64>,
    served: Option<u64>,
    reason: Option<&'static str>,
    units: Option<u64>,
}

fn res_rec(res: &Id, d: &Resource, r: &Req, action: &'static str, at: u64) -> ResRecord {
    ResRecord {
        resource: res.clone(),
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
    behavior: Id,
    transition: Id,
    from: Id,
    to: Id,
    guard: Option<Id>,
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
    behavior: Id,
    reason: Reason,
    considered: Vec<Id>,
    inst: Option<Value>,
}

#[derive(Clone, Debug)]
struct FaultRec {
    fault: Id,
    effect: &'static str,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    Deliver,
    Drop,
    Delay,
    ServiceDone,
    WaitTimeout,
    ClientTimeout,
    LinkDone,
    FaultEdge,
}

impl Kind {
    fn name(self) -> &'static str {
        match self {
            Kind::Deliver => "deliver",
            Kind::Drop => "drop",
            Kind::Delay => "delay",
            Kind::ServiceDone => "service-done",
            Kind::WaitTimeout => "wait-timeout",
            Kind::ClientTimeout => "client-timeout",
            Kind::LinkDone => "link-done",
            Kind::FaultEdge => "fault-edge",
        }
    }
}

#[derive(Clone, Debug)]
struct StepRec {
    index: u64,
    time: u64,
    kind: Kind,
    head: Sh<Entry>,
    fired: Vec<Fired>,
    ignored: Vec<Ignored>,
    faults: Vec<FaultRec>,
    responsible: Vec<String>,
    resources: Vec<ResRecord>,
    draws: Vec<Draw>,
    config: Option<Conf>,
    error: Option<String>,
    links: Vec<LinkRec>,
}

fn blank(index: u64, head: &Sh<Entry>, kind: Kind, config: Option<Conf>) -> StepRec {
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
        links: Vec::new(),
    }
}

// ---- The simulation -------------------------------------------------------------------------

/// A resource operation recorded in phase 2.
#[derive(Clone, Debug)]
enum Op {
    Req(Req, Option<u64>),
    Release(Id, usize, u64),
}

/// The state phases 2 and settling write.
struct Work {
    next: Conf,
    seq: u64,
    draws: Vec<Draw>,
    ops: Vec<(Id, Op)>,
    recs: Vec<ResRecord>,
    lrecs: Vec<LinkRec>,
}

#[derive(Clone, Debug)]
struct LinkRec {
    link: String,
    queue: String,
    message: u64,
    action: &'static str,
    at: u64,
    size: u64,
}

fn link_rec(l: &str, k: &str, m: &Msg, action: &'static str, now: u64) -> LinkRec {
    LinkRec {
        link: l.to_string(),
        queue: k.to_string(),
        message: m.id,
        action,
        at: now,
        size: m.size,
    }
}

/// Propagation of message `m` at `now` (Format2.lean, `propagate`).
fn propagate(i: &Input, l: &Link, k: &str, m: &Msg, now: u64, w: &mut Work) -> R<()> {
    let mut drs = Vec::new();
    let mut streams = w.next.streams.clone();
    let lat = sample(
        i.scenario.seed,
        &mut streams,
        &format!("latency:{}", l.id),
        &l.latency,
        &mut drs,
    );
    let mut q = w.next.lqueue(&l.id, k);
    let t = if l.ordered {
        (now + lat).max(q.last_delivery.unwrap_or(0))
    } else {
        now + lat
    };
    if t >= TWO53 {
        return Err("Value time exceeds 2^53.".into());
    }
    insert_entry(
        &mut w.next.pending,
        Entry {
            seq: w.seq,
            time: t,
            scheduled_at: t,
            event: m.event.as_str().into(),
            payload: m.payload.clone(),
            source: Src::Link(l.id.clone(), m.id),
            kind: EntryKind::Event,
            target: m.target.clone(),
            sender: m.sender.clone(),
            routes: None,
            first: None,
            timer: None,
            copy_of: None,
        },
    );
    w.next.streams = streams;
    if l.ordered {
        q.last_delivery = Some(t);
        w.next.set_lqueue(&l.id, k, q);
    }
    w.seq += 1;
    w.draws.extend(drs);
    w.lrecs.push(link_rec(&l.id, k, m, "propagated", now));
    Ok(())
}

/// Message `m` starts its transfer at `now` (Format2.lean, `startTransfer`).
fn start_transfer(i: &Input, l: &Link, k: &str, m: Msg, now: u64, w: &mut Work) -> R<()> {
    let bw = u128::from(l.bandwidth.unwrap_or(1));
    let tt = (u128::from(m.size) * u128::from(i.per_second.unwrap_or(1))).div_ceil(bw);
    if u128::from(now) + tt >= u128::from(TWO53) {
        return Err("Value time exceeds 2^53.".into());
    }
    let at = now + tt as u64;
    insert_entry(
        &mut w.next.pending,
        Entry {
            seq: w.seq,
            time: at,
            scheduled_at: at,
            event: Id::default(),
            payload: Value::Null,
            source: Src::Link(l.id.clone(), m.id),
            kind: EntryKind::LinkDone {
                link: l.id.clone(),
                key: k.into(),
                msg: m.id,
            },
            target: None,
            sender: None,
            routes: None,
            first: None,
            timer: None,
            copy_of: None,
        },
    );
    w.seq += 1;
    w.lrecs.push(link_rec(&l.id, k, &m, "started", now));
    let mut q = w.next.lqueue(&l.id, k);
    q.in_transfer = Some(m);
    w.next.set_lqueue(&l.id, k, q);
    Ok(())
}

/// Send message `m` on queue `k` of link `l` (Format2.lean, `sendMsg`).
fn send_msg(i: &Input, l: &Link, fan: bool, k: &str, m: Msg, now: u64, w: &mut Work) -> R<()> {
    if l.bandwidth.is_none() || (!l.ordered && m.size == 0) {
        return propagate(i, l, k, &m, now, w);
    }
    let mut q = w.next.lqueue(&l.id, k);
    if q.in_transfer.is_none() {
        return start_transfer(i, l, k, m, now, w);
    }
    w.lrecs.push(link_rec(&l.id, k, &m, "queued", now));
    q.waiting.push(m);
    if let Some(b) = l.queue_bound {
        if q.waiting.len() as u64 > b {
            let lost = if fan {
                q.waiting.remove(0)
            } else {
                q.waiting.pop().expect("non-empty")
            };
            w.lrecs.push(link_rec(&l.id, k, &lost, "lost", now));
        }
    }
    w.next.set_lqueue(&l.id, k, q);
    Ok(())
}

/// The size of a message: an integer in `[0, 2^40)`.
fn size_of(event: &str, v: &Value) -> R<u64> {
    match v {
        Value::Number(x) if x.fract() == 0.0 && *x >= 0.0 && *x < 1099511627776.0 => Ok(*x as u64),
        Value::Number(_) => Err(format!(
            "Size of emit \"{event}\" must be an integer in [0, 2^40), got {}.",
            v.to_json()
        )),
        _ => Err(format!(
            "Size of emit \"{event}\" must be an integer in [0, 2^40), got {}.",
            v.type_name()
        )),
    }
}

/// The machine keys already made for one behavior: by string and by number bits.
#[derive(Default)]
struct MKeys {
    strings: HashMap<String, Id>,
    numbers: HashMap<u64, Id>,
}

/// A parsed expression with its reference paths.
struct Compiled {
    ast: Ast,
    refs: Vec<Vec<String>>,
}

struct Sim<'a> {
    input: &'a Input,
    faults: Vec<&'a Fault>,
    fault_ids: Vec<String>,
    compiled: RefCell<HashMap<String, Rc<Compiled>>>,
    /// Machine keys of keyed instances by behavior and instance value (strings and numbers).
    mkeys: RefCell<HashMap<Id, MKeys>>,
    conf: Conf,
    seq: u64,
    attempts: HashMap<Id, u64>,
    delayed_by: HashMap<u64, Vec<Id>>,
    steps: Vec<StepRec>,
    initial_draws: Vec<Draw>,
    /// Steps taken (the steps themselves are kept only for a trace).
    taken: u64,
    meter: Measure,
    /// Whether steps are kept for the trace; without, step records carry no configuration.
    keep_steps: bool,
}

#[allow(clippy::large_enum_variant)]
enum StepResult {
    Committed(Box<StepRec>, Conf, u64, Option<(Id, u64)>),
    Failed(Box<StepRec>),
}

fn draw_next(seed: u64, streams: &mut Vec<(Rc<str>, u64)>, name: &str) -> (u64, Draw) {
    let i = lookup(streams, name);
    let r = random::draw(seed, name, i);
    bump(streams, name);
    (
        r,
        Draw {
            stream: if keep() { name.into() } else { Id::default() },
            index: i,
            value: r,
        },
    )
}

fn sample(
    seed: Option<u64>,
    streams: &mut Vec<(Rc<str>, u64)>,
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
    // Primitives of one kind compare directly; everything else by its serialization.
    match (a, b) {
        (Value::Null, Value::Null) => return true,
        (Value::Bool(x), Value::Bool(y)) => return x == y,
        (Value::String(x), Value::String(y)) => return x == y,
        (Value::Number(x), Value::Number(y)) if x.is_finite() && y.is_finite() => return x == y,
        _ => {}
    }
    a.to_json() == b.to_json()
}

impl<'a> Sim<'a> {
    /// The configuration a step record keeps: none when only metrics are output.
    fn snap(&self, c: &Conf) -> Option<Conf> {
        if self.keep_steps {
            Some(c.clone())
        } else {
            None
        }
    }

    /// `machine_key`, remembered for instances that are strings or finite numbers.
    fn mkey(&self, b: &Behavior, inst: &Value) -> Id {
        if matches!(b.instances, Instances::Single) {
            return b.id.clone();
        }
        let mut all = self.mkeys.borrow_mut();
        let cache = match all.get_mut(&*b.id) {
            Some(c) => c,
            None => all.entry(b.id.clone()).or_default(),
        };
        match inst {
            Value::String(x) => {
                if let Some(k) = cache.strings.get(x.as_str()) {
                    return k.clone();
                }
                let k = machine_key(b, inst);
                cache.strings.insert(x.clone(), k.clone());
                k
            }
            Value::Number(x) if x.is_finite() => {
                if let Some(k) = cache.numbers.get(&x.to_bits()) {
                    return k.clone();
                }
                let k = machine_key(b, inst);
                cache.numbers.insert(x.to_bits(), k.clone());
                k
            }
            _ => machine_key(b, inst),
        }
    }

    fn compile(&self, src: &str) -> R<Rc<Compiled>> {
        if let Some(c) = self.compiled.borrow().get(src) {
            return Ok(Rc::clone(c));
        }
        let ast = parse_expr(src).map_err(|e| format!("Expression \"{src}\": {e}"))?;
        let refs = expr_refs(&ast);
        let c = Rc::new(Compiled { ast, refs });
        self.compiled
            .borrow_mut()
            .insert(src.to_string(), Rc::clone(&c));
        Ok(c)
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
        // Paths have at most a few segments: no allocation for them.
        let mut arr = [""; 4];
        let long: Vec<&str>;
        let p: &[&str] = if path.len() <= arr.len() {
            for (slot, seg) in arr.iter_mut().zip(path) {
                *slot = seg;
            }
            &arr[..path.len()]
        } else {
            long = path.iter().map(String::as_str).collect();
            &long
        };
        let joined = || path.join(".");
        let undef = Ok(Value::Undefined);
        match p {
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
                        "Reference \"{}\" is ambiguous: \"{b}\" has {} instances.",
                        joined(),
                        ks.len()
                    ));
                }
                match ks.first().and_then(|v| view.machine(&self.mkey(bd, v))) {
                    None => undef,
                    Some(m) => Ok(if *name == "state" {
                        Value::str(m.state.as_str())
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
                    .filter_map(|v| view.machine(&self.mkey(bd, v)))
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
                                        "Aggregate \"{}\" needs numbers, got {}.",
                                        joined(),
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
        let compiled = self.compile(src)?;
        // ORDER: every reference is resolved first, in source order.
        for p in &compiled.refs {
            self.resolve(view, start, mk, inst, payload, time, p)?;
        }
        eval_expr(&compiled.ast, &|path: &[String]| {
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
        // Only the trace output reads the responsible set.
        if !self.keep_steps {
            return Vec::new();
        }
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
    fn decide_routes(&self, c: &mut Conf, head: &Entry) -> R<(Vec<(Id, Value)>, Vec<Draw>)> {
        let mut acc = Vec::new();
        let mut drs = Vec::new();
        for b in &self.input.behaviors {
            let Some(r) = self.input.route(&head.event, &b.id) else {
                continue;
            };
            let n_insts = c.insts_of(&b.id).len();
            match r.by.as_str() {
                "key" => {
                    let f = r.field.as_deref().unwrap_or("");
                    let v = head
                        .payload
                        .as_object()
                        .and_then(|o| o.get(f))
                        .cloned()
                        .unwrap_or(Value::Undefined);
                    if matches!(v, Value::Undefined) {
                        return Err(format!(
                            "Route of \"{}\" to \"{}\" needs payload field \"{f}\".",
                            head.event, b.id
                        ));
                    }
                    if let Instances::Keyed { max, .. } = b.instances {
                        let found = c.insts_of(&b.id).iter().find(|k| same_json(k, &v)).cloned();
                        if let Some(k) = found {
                            acc.push((b.id.clone(), k));
                        } else if n_insts as u64 >= max {
                            return Err(format!(
                                "Behavior \"{}\" would exceed {max} instances.",
                                b.id
                            ));
                        } else {
                            let key = v.deep_copy();
                            if let Some((_, xs)) = c.insts.iter_mut().find(|(k, _)| **k == *b.id) {
                                xs.push(key.clone());
                            }
                            c.set_machine(&machine_key(b, &key), initial_machine(b));
                            acc.push((b.id.clone(), key));
                        }
                    } else if n_insts > 0 {
                        let h = random::fnv1a64(&v.to_json());
                        let i = (h % n_insts as u64) as usize;
                        acc.push((b.id.clone(), c.insts_of(&b.id)[i].clone()));
                    }
                }
                "round-robin" => {
                    if n_insts == 0 {
                        continue;
                    }
                    let ckey = format!("{}:{}", r.event, r.behavior);
                    let n = lookup(&c.route_counters, &ckey);
                    acc.push((
                        b.id.clone(),
                        c.insts_of(&b.id)[(n % n_insts as u64) as usize].clone(),
                    ));
                    bump(&mut c.route_counters, &ckey);
                }
                "least-busy" => {
                    if n_insts == 0 {
                        continue;
                    }
                    let insts = c.insts_of(&b.id);
                    let load = |v: &Value| -> u64 {
                        match r.resource.as_deref().and_then(|x| c.resource(x)) {
                            Some(s) => {
                                let mk = self.mkey(b, v);
                                sum_units(&s.holds, |h| *h.owner == *mk)
                                    + s.waiting.iter().filter(|w| *w.owner == *mk).count() as u64
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
                    if n_insts == 0 {
                        continue;
                    }
                    match self.input.scenario.seed {
                        None => acc.push((b.id.clone(), c.insts_of(&b.id)[0].clone())),
                        Some(seed) => {
                            let stream = format!("route:{}:{}", r.event, r.behavior);
                            let (x, dr) = draw_next(seed, &mut c.streams, &stream);
                            drs.push(dr);
                            acc.push((
                                b.id.clone(),
                                c.insts_of(&b.id)[random::index(x, n_insts)].clone(),
                            ));
                        }
                    }
                }
            }
        }
        Ok((acc, drs))
    }

    fn targeting(&self, kind: &str, tid: &str, time: u64) -> Vec<&'a Fault> {
        self.faults
            .iter()
            .copied()
            .filter(|f| f.is_kind(kind) && f.transition.as_deref() == Some(tid) && f.acts_at(time))
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
    ) -> R<Result<(&'a Transition, Id), Ignored>> {
        let mk = self.mkey(b, inst);
        let state = cur.machine(&mk).map(|m| m.state.clone());
        let mut considered = Vec::new();
        let mut dis = false;
        let mut gf = false;
        for t in &b.transitions {
            if Some(&t.from) != state.as_ref() || t.on != head.event {
                continue;
            }
            let enablers = self.targeting("enable-transition", &t.id, head.time);
            if t.fault_only && enablers.is_empty() {
                continue;
            }
            if keep() {
                considered.push(t.id.clone());
            }
            let disablers = self.targeting("disable-transition", &t.id, head.time);
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
    fn addressed<'c>(
        cur: &'c Conf,
        head: &Entry,
        b: &Behavior,
    ) -> Option<std::borrow::Cow<'c, [Value]>> {
        use std::borrow::Cow;
        if let Some(a) = &head.target {
            if a.behavior != b.id {
                return None;
            }
            let found = cur.insts_of(&b.id).iter().any(|v| same_json(v, &a.inst));
            return Some(if found {
                Cow::Owned(vec![a.inst.clone()])
            } else {
                Cow::Borrowed(&[])
            });
        }
        if let Some((_, v)) = head
            .routes
            .as_ref()
            .and_then(|rs| rs.iter().find(|(k, _)| *k == b.id))
        {
            return Some(Cow::Owned(vec![v.clone()]));
        }
        Some(Cow::Borrowed(cur.insts_of(&b.id)))
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
            let site = &t.sites[k];
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
                    if keep() {
                        rec.sets.push(SetRec {
                            var: var.clone(),
                            before: before.deep_copy(),
                            after: value.deep_copy(),
                        });
                    }
                }
                Effect::Sample { var, dist } => {
                    if !w.next.machine(mk).is_some_and(|m| m.vars.contains_key(var)) {
                        return Err(format!(
                            "Effect sets \"{var}\", which is not a variable of \"{}\".",
                            b.id
                        ));
                    }
                    let x = sample(seed, &mut w.next.streams, &site.sample, dist, &mut w.draws);
                    let value = Value::Number(x as f64);
                    let m = w.next.machine_mut(mk).ok_or("no machine")?;
                    let before = m.vars.get(var).cloned().unwrap_or(Value::Undefined);
                    m.vars.insert(var.clone(), value.clone());
                    if keep() {
                        rec.sets.push(SetRec {
                            var: var.clone(),
                            before: before.deep_copy(),
                            after: value,
                        });
                    }
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
                    let delay = sample(seed, &mut streams, &site.after, after, &mut drs);
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
                            event: event.as_str().into(),
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
                            first: None,
                            timer: None,
                            copy_of: None,
                        },
                    );
                    w.next.streams = streams;
                    w.draws.extend(drs);
                    if keep() {
                        rec.emitted.push(EmitRec {
                            event: event.clone(),
                            time: at,
                            seq: s,
                            payload: pv.deep_copy(),
                        });
                    }
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
                        stream: site.demand.clone(),
                    };
                    let r = Req {
                        id: 0,
                        owner: Rc::from(mk),
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
                        .push((res.clone(), Op::Release(mk.into(), ci, *units)));
                }
                Effect::Send {
                    event,
                    size,
                    payload,
                    reply,
                    via,
                    fanout,
                } => {
                    if !self.input.is_event(event) {
                        return Err(format!("Effect emits \"{event}\", which is not an event."));
                    }
                    let l = self
                        .input
                        .links
                        .iter()
                        .find(|l| l.id == *via)
                        .ok_or_else(|| {
                            format!("Effect sends over \"{via}\", which is not a link.")
                        })?;
                    let fan = *fanout || l.fanout;
                    let mut streams = w.next.streams.clone();
                    let mut drs = Vec::new();
                    let sz = match size {
                        SizeIn::None => 0,
                        SizeIn::Dist(d) => sample(seed, &mut streams, &site.size, d, &mut drs),
                        SizeIn::Expr(src) => {
                            let v =
                                self.eval(src, &w.next, start, mk, inst, &head.payload, time)?;
                            size_of(event, &v)?
                        }
                    };
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
                    let receivers: Vec<(Id, Option<Addr>)> = if fan {
                        let mut out = Vec::new();
                        for rb in &self.input.behaviors {
                            if rb.subject.as_deref() == Some(l.to.as_str()) {
                                for v in w.next.insts_of(&rb.id).iter().cloned() {
                                    out.push((
                                        machine_key(rb, &v),
                                        Some(Addr {
                                            behavior: rb.id.clone(),
                                            inst: v,
                                            incarnation: 0,
                                        }),
                                    ));
                                }
                            }
                        }
                        out
                    } else {
                        vec![(Id::default(), target)]
                    };
                    w.next.streams = streams;
                    w.draws.extend(drs);
                    let sender = Some(Addr {
                        behavior: b.id.clone(),
                        inst: inst.clone(),
                        incarnation: 0,
                    });
                    for (key, tg) in receivers {
                        let m = Msg {
                            id: w.seq,
                            event: event.clone(),
                            payload: Value::object(fs.deep_copy()),
                            size: sz,
                            sent_at: time,
                            target: tg,
                            sender: sender.clone(),
                        };
                        w.seq += 1;
                        if keep() {
                            rec.emitted.push(EmitRec {
                                event: event.clone(),
                                time,
                                seq: m.id,
                                payload: m.payload.deep_copy(),
                            });
                        }
                        send_msg(self.input, l, fan, &key, m, time, w)?;
                    }
                }
                Effect::Timer {
                    name,
                    after,
                    event,
                    payload,
                } => {
                    if !self.input.is_event(event) {
                        return Err(format!("Effect emits \"{event}\", which is not an event."));
                    }
                    let mut streams = w.next.streams.clone();
                    let mut drs = Vec::new();
                    let delay = sample(seed, &mut streams, &site.after, after, &mut drs);
                    let at = w.next.time + delay;
                    if at >= TWO53 {
                        return Err("Value time exceeds 2^53.".into());
                    }
                    let fs =
                        self.eval_entries(payload, &w.next, start, mk, inst, &head.payload, time)?;
                    let tid = format!("{mk}/{name}");
                    let pv = Value::object(fs);
                    let sq = w.seq;
                    w.seq += 1;
                    w.next
                        .pending
                        .retain(|e| e.timer.as_deref() != Some(tid.as_str()));
                    insert_entry(
                        &mut w.next.pending,
                        Entry {
                            seq: sq,
                            time: at,
                            scheduled_at: at,
                            event: event.as_str().into(),
                            payload: pv.clone(),
                            source: Src::Timer(b.id.clone(), inst.clone(), name.as_str().into()),
                            kind: EntryKind::Event,
                            target: Some(Addr {
                                behavior: b.id.clone(),
                                inst: inst.clone(),
                                incarnation: 0,
                            }),
                            sender: None,
                            routes: None,
                            first: None,
                            timer: Some(tid),
                            copy_of: None,
                        },
                    );
                    w.next.streams = streams;
                    w.draws.extend(drs);
                    if keep() {
                        rec.emitted.push(EmitRec {
                            event: event.clone(),
                            time: at,
                            seq: sq,
                            payload: pv.deep_copy(),
                        });
                    }
                }
                Effect::Cancel(name) => {
                    let tid = format!("{mk}/{name}");
                    w.next
                        .pending
                        .retain(|e| e.timer.as_deref() != Some(tid.as_str()));
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
        res: &Id,
        d: &Resource,
        r: &Req,
        event: &str,
        outcome: &'static str,
        extra: Vec<(&str, Value)>,
    ) {
        let mut fs = r.info.payload.clone();
        fs.insert(skey("resource"), Value::str(res.as_str()));
        fs.insert(skey("class"), Value::str(d.class_id(r.cls).as_str()));
        for (k, v) in extra {
            fs.insert(skey(k), v);
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
                event: event.into(),
                payload: Value::object(fs),
                source: Src::Resource(res.into(), r.id, outcome),
                kind: EntryKind::Event,
                target: Some(r.info.requester.clone()),
                sender: None,
                routes: None,
                first: None,
                timer: None,
                copy_of: None,
            },
        );
    }

    fn remove_timeout(q: &mut Vec<Sh<Entry>>, res: &str, rid: u64) {
        q.retain(|e| {
            !matches!(&e.kind, EntryKind::WaitTimeout { res: r, request } if r == res && *request == rid)
        });
    }

    /// Settle one resource: releases, enqueues, grants, bounds.
    fn settle_one(&self, res: &Id, ops: &[&Op], w: &mut Work) -> R<()> {
        let Some(d) = self.input.resource(res) else {
            return Ok(());
        };
        let Some(mut s) = w.next.resource_mut(res).map(std::mem::take) else {
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
                    resource: res.into(),
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
                            event: Id::default(),
                            payload: Value::Null,
                            source: Src::Resource(res.into(), r.id, "wait-timeout"),
                            kind: EntryKind::WaitTimeout {
                                res: res.into(),
                                request: r.id,
                            },
                            target: None,
                            sender: None,
                            routes: None,
                            first: None,
                            timer: None,
                            copy_of: None,
                        },
                    );
                }
                w.recs.push(res_rec(res, d, &r, "enqueued", now));
            }
        }
        let de = eff_decl(&self.faults, &w.next.active, d);
        let grants = grant_loop(&de, &mut s);
        // The state is written once, after the grants and bounds below.
        w.next.resource(res).ok_or("no resource")?;
        for (r, occ) in grants {
            let waited = now - r.since;
            Self::remove_timeout(&mut w.next.pending, res, r.id);
            match r.kind {
                ReqKind::Use => {
                    let (sn, sd) = eff_scale(&self.faults, &w.next.active, res)?;
                    let demand =
                        eff_demand(&self.faults, &w.next.active, &r.info.stream, &r.info.demand);
                    let dd = sample(
                        self.input.scenario.seed,
                        &mut w.next.streams,
                        &r.info.stream,
                        demand,
                        &mut w.draws,
                    );
                    let served = if dd == 0 || sn == 0 {
                        Some(0)
                    } else {
                        d.demand_factor.at(occ).and_then(|(num, den)| {
                            // The ceiling of dd * num * sn / (den * sd), in machine integers when
                            // they do not overflow, else in big integers.
                            let fast = (|| {
                                let x = u128::from(dd)
                                    .checked_mul(num)?
                                    .checked_mul(u128::from(sn))?;
                                let y = den.checked_mul(u128::from(sd))?;
                                if y == 0 {
                                    return None;
                                }
                                Some(x.checked_add(y - 1)? / y)
                            })();
                            if fast.is_some() {
                                return fast;
                            }
                            let x = BigUint::from(dd) * BigUint::from(num) * BigUint::from(sn);
                            let y = BigUint::from(den) * BigUint::from(sd);
                            let q = (x + &y - 1u32) / y;
                            u128::try_from(q).ok()
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
                            event: Id::default(),
                            payload: Value::Null,
                            source: Src::Resource(res.into(), r.id, "service-done"),
                            kind: EntryKind::ServiceDone {
                                res: res.into(),
                                req: r.clone(),
                                waited,
                                served,
                            },
                            target: None,
                            sender: None,
                            routes: None,
                            first: None,
                            timer: None,
                            copy_of: None,
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
        let removed = bounds(&de, &mut s.waiting);
        if let Some(st) = w.next.resource_mut(res) {
            *st = s;
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

    fn settle(&self, touched: &[&str], w: &mut Work) -> R<()> {
        let ops = std::mem::take(&mut w.ops);
        for d in &self.input.resources {
            let mine: Vec<&Op> = ops
                .iter()
                .filter(|(r, _)| *r == d.id)
                .map(|(_, o)| o)
                .collect();
            if touched.iter().any(|t| *t == d.id) || !mine.is_empty() {
                self.settle_one(&d.id, &mine, w)?;
            }
        }
        Ok(())
    }

    fn fault_matches(f: &Fault, kind: &str, ev: &str, attempt: u64, time: u64) -> bool {
        f.is_kind(kind)
            && f.acts_at(time)
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
        head: &Sh<Entry>,
        kind: Kind,
        fired: Vec<Fired>,
        ignored: Vec<Ignored>,
        faults: Vec<FaultRec>,
        draws: Vec<Draw>,
        touched: &[&str],
        mut w: Work,
        attempts: Option<(Id, u64)>,
        pre: Vec<ResRecord>,
    ) -> StepResult {
        let index = self.taken;
        match self.settle(touched, &mut w) {
            Err(msg) => {
                let mut st = blank(index, head, kind, self.snap(&self.conf));
                st.responsible = if head.event.is_empty() {
                    Vec::new()
                } else {
                    vec![head.event.to_string()]
                };
                st.error = Some(msg);
                StepResult::Failed(Box::new(st))
            }
            Ok(()) => {
                let mut st = blank(index, head, kind, self.snap(&w.next));
                st.links = std::mem::take(&mut w.lrecs);
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

    fn step_head(&mut self, mut next: Conf, head: Sh<Entry>) -> StepResult {
        let index = self.taken;
        let work = |next: Conf, seq: u64| Work {
            next,
            seq,
            draws: Vec::new(),
            ops: Vec::new(),
            recs: Vec::new(),
            lrecs: Vec::new(),
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
                        Box::new(blank(index, &head, Kind::ServiceDone, self.snap(&next))),
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
                    &[res.as_str()],
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
                        Box::new(blank(index, &head, Kind::WaitTimeout, self.snap(&next))),
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
                    &[res.as_str()],
                    w,
                    None,
                    vec![rec],
                )
            }
            EntryKind::FaultEdge { fault, on } => {
                next.active = self
                    .faults
                    .iter()
                    .filter(|f| {
                        f.window.is_some()
                            && ((f.id == fault && on)
                                || (f.id != fault && next.active.contains(&f.id)))
                    })
                    .map(|f| f.id.clone())
                    .collect();
                let Some(f) = self.faults.iter().copied().find(|f| f.id == fault) else {
                    return StepResult::Committed(
                        Box::new(blank(index, &head, Kind::FaultEdge, self.snap(&next))),
                        next,
                        self.seq,
                        None,
                    );
                };
                let name = match f.kind.as_deref() {
                    Some("set-capacity") => "capacity",
                    Some("set-class-limit") => "limit",
                    Some("collapse-classes") => "collapsed",
                    Some("scale-demand") => "scaled",
                    _ => "replaced",
                };
                let recs = vec![FaultRec {
                    fault: fault.clone(),
                    effect: name,
                }];
                match f.resource.as_deref().and_then(|r| self.input.resource(r)) {
                    Some(d) => {
                        let cap = eff_capacity(&self.faults, &next.active, d);
                        if let Some(s) = next.resource_mut(&d.id) {
                            s.capacity = cap;
                        }
                        let w = work(next, self.seq);
                        self.finish(
                            &head,
                            Kind::FaultEdge,
                            Vec::new(),
                            Vec::new(),
                            recs,
                            Vec::new(),
                            &[d.id.as_str()],
                            w,
                            None,
                            Vec::new(),
                        )
                    }
                    None => {
                        let mut rec = blank(index, &head, Kind::FaultEdge, self.snap(&next));
                        rec.faults = recs;
                        rec.responsible = vec![fault.to_string()];
                        StepResult::Committed(Box::new(rec), next, self.seq, None)
                    }
                }
            }
            EntryKind::LinkDone { link, key, .. } => {
                let l = self.input.links.iter().find(|l| l.id == link);
                let q = next.lqueue(&link, &key);
                let (Some(l), Some(m)) = (l, q.in_transfer.clone()) else {
                    return StepResult::Committed(
                        Box::new(blank(index, &head, Kind::LinkDone, self.snap(&next))),
                        next,
                        self.seq,
                        None,
                    );
                };
                let now = next.time;
                let mut q0 = q;
                q0.in_transfer = None;
                next.set_lqueue(&link, &key, q0);
                let mut w = work(next, self.seq);
                w.lrecs.push(link_rec(&link, &key, &m, "transferred", now));
                let r = (|| -> R<()> {
                    propagate(self.input, l, &key, &m, now, &mut w)?;
                    let mut q = w.next.lqueue(&link, &key);
                    if !q.waiting.is_empty() {
                        let m2 = q.waiting.remove(0);
                        w.next.set_lqueue(&link, &key, q);
                        start_transfer(self.input, l, &key, m2, now, &mut w)?;
                    }
                    Ok(())
                })();
                if let Err(msg) = r {
                    let mut st = blank(index, &head, Kind::LinkDone, self.snap(&self.conf));
                    st.error = Some(msg);
                    return StepResult::Failed(Box::new(st));
                }
                let mut rec = blank(index, &head, Kind::LinkDone, self.snap(&w.next));
                rec.draws = w.draws;
                rec.links = w.lrecs;
                StepResult::Committed(Box::new(rec), w.next, w.seq, None)
            }
            EntryKind::ClientTimeout {
                workload,
                client,
                n: k,
            } => {
                let mut draws = Vec::new();
                let mut seq = self.seq;
                if let (Some(w), Some(pos)) = (
                    self.input.workloads.iter().find(|w| w.id == workload),
                    next.workloads.iter().position(|(id, _)| **id == *workload),
                ) {
                    let mut st = next.workloads[pos].1.clone();
                    if st.clients.get(client as usize).copied().flatten() == Some(k) {
                        let now = next.time;
                        rethink(
                            self.input,
                            w,
                            &mut st,
                            client,
                            now,
                            &mut next.streams,
                            &mut seq,
                            &mut next.pending,
                            &mut draws,
                        );
                        next.workloads[pos].1 = st;
                    }
                }
                let mut rec = blank(index, &head, Kind::ClientTimeout, self.snap(&next));
                rec.draws = draws;
                StepResult::Committed(Box::new(rec), next, seq, None)
            }
            EntryKind::Event => {
                let attempt = self.attempts.get(&head.event).copied().unwrap_or(0) + 1;
                let already = self.delayed_by.get(&head.seq).cloned().unwrap_or_default();
                let r = self.step_event(next, head.clone());
                let r = self.after_deliver(&head, r);
                self.duplicate_after(attempt, already, r)
            }
        }
    }

    /// After a delivery that did not fail: closed clients receive their replies
    /// (Format2.lean, `replies`).
    fn after_deliver(&self, head: &Entry, r: StepResult) -> StepResult {
        let StepResult::Committed(mut rec, mut next, mut seq, attempts) = r else {
            return r;
        };
        if rec.kind != Kind::Deliver {
            return StepResult::Committed(rec, next, seq, attempts);
        }
        let mut draws = Vec::new();
        for w in &self.input.workloads {
            if w.kind != WKind::Closed || w.reply != head.event {
                continue;
            }
            let Some(Value::String(r)) = head
                .payload
                .as_object()
                .and_then(|o| o.get(&w.request_field))
            else {
                continue;
            };
            let Some(pos) = next.workloads.iter().position(|(id, _)| **id == *w.id) else {
                continue;
            };
            let mut st = next.workloads[pos].1.clone();
            let Some(k) = st
                .clients
                .iter()
                .position(|o| o.is_some_and(|m| format!("{}#{m}", w.id) == **r))
            else {
                continue;
            };
            let n_ = st.clients[k].unwrap_or(0);
            next.pending.retain(|e| {
                !matches!(&e.kind, EntryKind::ClientTimeout { workload, client, n: m }
                    if *workload == w.id && *client == k as u64 && *m == n_)
            });
            let now = next.time;
            rethink(
                self.input,
                w,
                &mut st,
                k as u64,
                now,
                &mut next.streams,
                &mut seq,
                &mut next.pending,
                &mut draws,
            );
            next.workloads[pos].1 = st;
        }
        rec.config = self.snap(&next);
        rec.draws.extend(draws);
        StepResult::Committed(rec, next, seq, attempts)
    }

    fn fail(&self, head: &Sh<Entry>, kind: Kind, msg: String) -> StepResult {
        let mut st = blank(self.taken, head, kind, self.snap(&self.conf));
        st.responsible = vec![head.event.to_string()];
        st.error = Some(msg);
        StepResult::Failed(Box::new(st))
    }

    fn step_event(&mut self, mut next: Conf, head: Sh<Entry>) -> StepResult {
        let index = self.taken;
        let ev = head.event.clone();
        let mut head = head;
        // The start-of-step view: the configuration before the step, copied only when routes
        // create keyed instances.
        let mut cur: std::borrow::Cow<Conf> = std::borrow::Cow::Borrowed(&self.conf);
        let mut rdraws = Vec::new();
        // ORDER: routes are decided when the entry is first taken as head, before drop and delay.
        if head.routes.is_none() && head.target.is_none() {
            match self.decide_routes(&mut next, &head) {
                Err(msg) => return self.fail(&head, Kind::Deliver, msg),
                Ok((rs, drs)) => {
                    let extra: Vec<(Rc<str>, Sh<Machine>)> = next
                        .machines
                        .iter()
                        .filter(|(k, _)| !self.conf.machines.iter().any(|(k2, _)| k2 == k))
                        .cloned()
                        .collect();
                    if !extra.is_empty() {
                        let c = cur.to_mut();
                        c.insts = next.insts.clone();
                        c.machines.extend(extra);
                    }
                    head.routes = Some(rs);
                    rdraws = drs;
                }
            }
        }
        let attempt = self.attempts.get(&ev).copied().unwrap_or(0) + 1;
        let attempts = (ev.clone(), attempt);
        let drops: Vec<FaultRec> = self
            .faults
            .iter()
            .filter(|f| {
                Self::fault_matches(f, "drop-event", &ev, attempt, head.time)
                    || Self::fault_matches(f, "lose-event", &ev, attempt, head.time)
            })
            .map(|f| FaultRec {
                fault: f.id.clone(),
                effect: if f.is_kind("lose-event") {
                    "lost"
                } else {
                    "dropped"
                },
            })
            .collect();
        if !drops.is_empty() {
            let mut st = blank(index, &head, Kind::Drop, self.snap(&next));
            st.responsible = self.responsible_of(&ev, &[], &drops);
            st.faults = drops;
            st.draws = rdraws;
            return StepResult::Committed(Box::new(st), next, self.seq, Some(attempts));
        }
        let already = self.delayed_by.get(&head.seq).cloned().unwrap_or_default();
        let delay = self.faults.iter().copied().find(|f| {
            (Self::fault_matches(f, "delay-event", &ev, attempt, head.time)
                || Self::fault_matches(f, "retry-event", &ev, attempt, head.time))
                && !already.contains(&f.id)
        });
        if let Some(d) = delay {
            if head.time + d.by >= TWO53 {
                return self.fail(&head, Kind::Delay, "Value time exceeds 2^53.".into());
            }
            let s = self.seq;
            let mut copy: Entry = (*head).clone();
            copy.seq = s;
            copy.first = None;
            copy.copy_of = Some(head.copy_of.unwrap_or(head.seq));
            copy.time = head.time + d.by;
            copy.payload = head.payload.deep_copy();
            insert_entry(&mut next.pending, copy);
            let mut applied = already;
            applied.push(d.id.clone());
            self.delayed_by.insert(s, applied);
            let recs = vec![FaultRec {
                fault: d.id.clone(),
                effect: if d.is_kind("retry-event") {
                    "retried"
                } else {
                    "delayed"
                },
            }];
            let mut st = blank(index, &head, Kind::Delay, self.snap(&next));
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
        let phase = (|next: Conf| -> R<(Vec<Fired>, Vec<Ignored>, Work)> {
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
                        for inst in insts.iter().cloned() {
                            match self.choose_inst(&cur, b, &inst, &head, &mut faults_out)? {
                                Ok((t, mk)) => winners.push((b, inst, mk, t)),
                                Err(ig) => ignored.push(ig),
                            }
                        }
                    }
                }
            }
            let mut w = Work {
                next,
                seq: self.seq,
                draws: Vec::new(),
                ops: Vec::new(),
                recs: Vec::new(),
                lrecs: Vec::new(),
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
                if w.next.machine(&mk).is_some_and(|m| m.state != t.to) {
                    if let Some(m) = w.next.machine_mut(&mk) {
                        m.state = t.to.clone();
                    }
                }
                fired.push(rec);
            }
            Ok((fired, ignored, w))
        })(next);
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

    /// After a delivery that committed (and its replies), a matching `duplicate-event` fault that
    /// has not acted on this entry yet queues a copy of the head (as routed, from the step record)
    /// `by` later, with the next sequence number after the step's own entries (Format2.lean,
    /// `duplicateAfter`). `attempt` and `already` are those of the head before the step.
    fn duplicate_after(&mut self, attempt: u64, already: Vec<Id>, r: StepResult) -> StepResult {
        let StepResult::Committed(mut rec, mut next, seq, attempts) = r else {
            return r;
        };
        if rec.kind != Kind::Deliver {
            return StepResult::Committed(rec, next, seq, attempts);
        }
        let head = rec.head.clone();
        let head = &head;
        let dup = self.faults.iter().copied().find(|f| {
            Self::fault_matches(f, "duplicate-event", &head.event, attempt, head.time)
                && !already.contains(&f.id)
        });
        let Some(d) = dup else {
            return StepResult::Committed(rec, next, seq, attempts);
        };
        if head.time + d.by >= TWO53 {
            return self.fail(head, Kind::Deliver, "Value time exceeds 2^53.".into());
        }
        let mut copy: Entry = (**head).clone();
        copy.seq = seq;
        copy.first = None;
        copy.copy_of = Some(head.copy_of.unwrap_or(head.seq));
        copy.time = head.time + d.by;
        copy.payload = head.payload.deep_copy();
        insert_entry(&mut next.pending, copy);
        let mut applied = already;
        applied.push(d.id.clone());
        self.delayed_by.insert(seq, applied);
        rec.faults.push(FaultRec {
            fault: d.id.clone(),
            effect: "duplicated",
        });
        if !rec.responsible.iter().any(|r| **r == *d.id) {
            rec.responsible.push(d.id.to_string());
        }
        rec.config = self.snap(&next);
        StepResult::Committed(rec, next, seq + 1, attempts)
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
    let ids: Vec<&str> = i
        .behaviors
        .iter()
        .map(|b| b.id.as_str())
        .chain(i.resources.iter().map(|r| r.id.as_str()))
        .chain(i.workloads.iter().map(|w| w.id.as_str()))
        .chain(i.links.iter().map(|l| l.id.as_str()))
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
                    Effect::Send { via, .. } if !i.links.iter().any(|l| l.id == *via) => {
                        return Err(format!("Effect sends over \"{via}\", which is not a link."));
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
    // Format-2 faults.
    let sfaults: Vec<&Fault> = seen.iter().filter_map(|id| i.fault(id)).collect();
    for f in &sfaults {
        if f.is_kind("inject-event") && f.window.is_some() {
            return Err(format!("Fault \"{}\": inject-event takes no window.", f.id));
        }
        if let Some((a, Some(u))) = f.window {
            if u <= a {
                return Err(format!("Fault \"{}\" has an empty window.", f.id));
            }
        }
        if f.is_kind("replace-demand") {
            let ok = f
                .behavior
                .as_deref()
                .and_then(|b| i.behavior(b))
                .and_then(|b| {
                    b.transitions
                        .iter()
                        .find(|t| Some(t.id.as_str()) == f.transition.as_deref())
                })
                .and_then(|t| t.effects.get(f.effect as usize))
                .is_some_and(|e| {
                    matches!(
                        e,
                        Effect::Request {
                            kind: ReqKind::Use,
                            ..
                        }
                    )
                });
            if !ok {
                return Err(format!("Fault \"{}\" names no use effect.", f.id));
            }
        } else if f.is_resource_kind() {
            match f.resource.as_deref().and_then(|r| i.resource(r)) {
                None => {
                    return Err(format!(
                        "Fault \"{}\" names \"{}\", which is not a resource.",
                        f.id,
                        f.resource.as_deref().unwrap_or("")
                    ))
                }
                Some(d) => {
                    if f.is_kind("set-class-limit")
                        && !d
                            .classes
                            .iter()
                            .any(|c| Some(c.id.as_str()) == f.class.as_deref())
                    {
                        return Err(format!(
                            "Fault \"{}\" names no class of \"{}\".",
                            f.id, d.id
                        ));
                    }
                }
            }
        }
    }
    for d in &i.resources {
        let cap = eff_capacity(&sfaults, &[], d);
        let total: u64 = d.classes.iter().map(|c| c.reserved).sum();
        if total > cap {
            let f = sfaults
                .iter()
                .rfind(|f| {
                    f.window.is_none()
                        && f.is_kind("set-capacity")
                        && f.resource.as_deref() == Some(d.id.as_str())
                })
                .map_or("", |f| f.id.as_str());
            return Err(format!(
                "Fault \"{f}\" leaves \"{}\" with reserved units above capacity.",
                d.id
            ));
        }
        let de = eff_decl(&sfaults, &[], d);
        for c in &de.classes {
            if let Some(l) = c.limit {
                if c.reserved > l {
                    let f = sfaults
                        .iter()
                        .rfind(|f| {
                            f.window.is_none()
                                && f.is_kind("set-class-limit")
                                && f.resource.as_deref() == Some(d.id.as_str())
                                && f.class.as_deref() == Some(c.id.as_str())
                        })
                        .map_or("", |f| f.id.as_str());
                    return Err(format!(
                        "Fault \"{f}\" leaves \"{}\" with reserved units above a class limit.",
                        d.id
                    ));
                }
            }
        }
    }
    if i.unit == "tick" && i.per_second.is_some() {
        return Err("Unit tick has no rate.".into());
    }
    for (li, l) in i.links.iter().enumerate() {
        if i.per_second.is_none() && l.bandwidth.is_some() {
            return Err(format!("Unit tick has no rate; \"links[{li}]\" needs one."));
        }
    }
    for (wi, w) in i.workloads.iter().enumerate() {
        if !i.is_event(&w.event) {
            return Err(format!(
                "Workload \"{}\" generates \"{}\", which is not an event.",
                w.id, w.event
            ));
        }
        if w.kind == WKind::Closed {
            if !i.is_event(&w.reply) {
                return Err(format!(
                    "Workload \"{}\" waits for \"{}\", which is not an event.",
                    w.id, w.reply
                ));
            }
            if let Some(to) = w.timeout {
                if i.scenario.horizon.unwrap_or(0) + to >= TWO53 {
                    return Err(format!(
                        "Workload \"{}\" has a timeout that reaches 2^53 after the horizon.",
                        w.id
                    ));
                }
            }
        }
        if w.kind == WKind::Population {
            match i.behavior(&w.behavior).map(|b| &b.instances) {
                Some(Instances::Keyed { max, .. }) => {
                    let total: u64 = i
                        .workloads
                        .iter()
                        .filter(|x| x.kind == WKind::Population && x.behavior == w.behavior)
                        .map(|x| x.population)
                        .sum();
                    if total > *max {
                        return Err(format!(
                            "Population of \"{}\" exceeds its max of {max} instances.",
                            w.behavior
                        ));
                    }
                }
                _ => {
                    return Err(format!(
                        "Workload \"{}\" names \"{}\", which is not a keyed behavior.",
                        w.id, w.behavior
                    ))
                }
            }
        }
        if w.kind != WKind::Open {
            continue;
        }
        let Some(ps) = i.per_second else {
            return Err(format!(
                "Unit tick has no rate; \"workloads[{wi}]\" needs one."
            ));
        };
        let ok = w.phases.iter().all(|ph| ph.start < ph.stop)
            && w.phases.windows(2).all(|x| x[0].stop <= x[1].start)
            && w.period
                .is_none_or(|p| p >= w.phases.last().map_or(0, |ph| ph.stop))
            && (w.poisson || w.phases.iter().all(|ph| matches!(ph.rate, Rate::Const(..))));
        if !ok {
            return Err(format!("Workload \"{}\" has malformed phases.", w.id));
        }
        for (pi, ph) in w.phases.iter().enumerate() {
            let ((a0, b0), (a1, b1)) = ph.rate.ends();
            let low = |a: u64, b: u64| u128::from(ps) * u128::from(b) < 100 * u128::from(a);
            if low(a0, b0) || low(a1, b1) {
                return Err(format!(
                    "Phase {pi} of workload \"{}\" has a mean interarrival below 100 base units; use a finer unit.",
                    w.id
                ));
            }
        }
        if matches!(w.batch, Dist::Fixed(0)) {
            return Err(format!("Workload \"{}\" has a batch below 1.", w.id));
        }
        if w.poisson && i.unit_exp.is_empty() {
            return Err(
                "Input field \"unitExponential\" is required by a Poisson workload.".into(),
            );
        }
    }
    if i.scenario.seed.is_none() {
        if let Some(s) = sampled_sites(i).first() {
            return Err(format!("Input samples \"{s}\" but declares no seed."));
        }
    }
    if !i.workloads.is_empty() && i.scenario.horizon.is_none() {
        return Err(format!(
            "Scenario \"{}\" has workloads but no horizon.",
            i.scenario.id
        ));
    }
    for c in &i.requests {
        if !i.is_event(&c.start_event) {
            return Err(format!(
                "Request class \"{}\" starts on \"{}\", which is not an event.",
                c.id, c.start_event
            ));
        }
        for (e, _) in &c.ends {
            if !i.is_event(e) {
                return Err(format!(
                    "Request class \"{}\" ends on \"{e}\", which is not an event.",
                    c.id
                ));
            }
        }
        if let Some(w) = &c.start_workload {
            if !i.workloads.iter().any(|x| x.id == *w) {
                return Err(format!(
                    "Request class \"{}\" names \"{w}\", which is not a workload.",
                    c.id
                ));
            }
        }
    }
    if i.measures() && i.scenario.horizon.is_none() {
        return Err(format!(
            "Scenario \"{}\" measures outputs but has no horizon.",
            i.scenario.id
        ));
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
    if let (Some(b), Some(h)) = (i.series, i.scenario.horizon) {
        if h.saturating_sub(i.scenario.warmup.unwrap_or(0)) % b != 0 {
            return Err("Metrics series bucket must divide the window.".into());
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
                    Effect::Send {
                        size: SizeIn::Dist(d),
                        ..
                    } if d.draws() => out.push(format!("size:{site}")),
                    Effect::Timer { after, .. } if after.draws() => {
                        out.push(format!("after:{site}"))
                    }
                    _ => {}
                }
            }
        }
    }
    for l in &i.links {
        if l.latency.draws() {
            out.push(format!("latency:{}", l.id));
        }
    }
    for r in i.routes.iter().filter(|r| r.by == "random") {
        out.push(format!("route:{}:{}", r.event, r.behavior));
    }
    for w in &i.workloads {
        if w.group_size.as_ref().is_some_and(|d| d.draws()) {
            out.push(format!("groups:{}", w.id));
        }
        if w.kind != WKind::Open && w.start.draws() {
            out.push(format!("start:{}", w.id));
        }
        if w.kind == WKind::Closed && w.think.draws() {
            out.push(format!("think:{}", w.id));
        }
        if w.poisson {
            out.push(format!("arrival:{}", w.id));
        }
        if w.batch.draws() {
            out.push(format!("batch:{}", w.id));
        }
        if w.kind == WKind::Open && w.clients.as_ref().is_some_and(|c| !c.round_robin) {
            out.push(format!("client:{}", w.id));
        }
        for (f, pf) in &w.payload {
            match pf {
                PField::Sample(d) if d.draws() => out.push(format!("payload:{}:{f}", w.id)),
                PField::Choose(..) => out.push(format!("payload:{}:{f}", w.id)),
                _ => {}
            }
        }
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
        insts.push((b.id.to_string(), vs));
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
                event: event.into(),
                payload: payload.clone(),
                source,
                kind: EntryKind::Event,
                target,
                sender: None,
                routes: None,
                first: None,
                timer: None,
                copy_of: None,
            }
        };
    for st in &i.scenario.steps {
        let target = st.target.as_ref().map(|(b, v)| Addr {
            behavior: b.as_str().into(),
            inst: v.clone(),
            incarnation: 0,
        });
        insert_entry(
            &mut q,
            mk(n, st.at, &st.event, &st.payload, Src::Scenario(n), target),
        );
        n += 1;
    }
    let inject: Vec<&&Fault> = faults
        .iter()
        .filter(|f| f.is_kind("inject-event"))
        .collect();
    for f in inject {
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
    // The edges of windowed resource faults, in `faults` order: `at`, then `until`.
    for f in faults.iter().filter(|f| f.is_resource_kind()) {
        let Some((a, u)) = f.window else { continue };
        let mut edges = vec![(a, true)];
        if let Some(u) = u {
            edges.push((u, false));
        }
        for (t, on) in edges {
            insert_entry(
                &mut q,
                Entry {
                    seq: n,
                    time: t,
                    scheduled_at: t,
                    event: Id::default(),
                    payload: Value::Null,
                    source: Src::Fault(f.id.clone()),
                    kind: EntryKind::FaultEdge {
                        fault: f.id.clone(),
                        on,
                    },
                    target: None,
                    sender: None,
                    routes: None,
                    first: None,
                    timer: None,
                    copy_of: None,
                },
            );
            n += 1;
        }
    }
    (
        Conf {
            time: 0,
            machines: machines
                .into_iter()
                .map(|(k, m)| (Rc::from(&*k), Sh::new(m)))
                .collect::<Vec<_>>()
                .into(),
            insts: insts
                .into_iter()
                .map(|(k, v)| (Rc::from(k), v))
                .collect::<Vec<_>>()
                .into(),
            pending: q.into(),
            resources: i
                .resources
                .iter()
                .map(|d| {
                    (
                        Rc::from(d.id.as_str()),
                        RState {
                            capacity: eff_capacity(faults, &[], d),
                            ..RState::default()
                        }
                        .into(),
                    )
                })
                .collect::<Vec<_>>()
                .into(),
            route_counters: Vec::new().into(),
            streams: Vec::new().into(),
            workloads: i
                .workloads
                .iter()
                .map(|w| (Rc::from(w.id.as_str()), WState::default().into()))
                .collect::<Vec<_>>()
                .into(),
            lqueues: Vec::new().into(),
            active: Vec::new(),
        },
        n,
    )
}

/// Each workload's initial entries, in input order: the initial draws.
fn initial_instants(i: &Input, c: &mut Conf, seq: &mut u64) -> Vec<Draw> {
    let mut drs = Vec::new();
    for w in &i.workloads {
        if let Some(pos) = c.workloads.iter().position(|(id, _)| **id == *w.id) {
            let mut st = c.workloads[pos].1.clone();
            drs.extend(initial_workload(i, c, w, &mut st, seq));
            c.workloads[pos].1 = st;
        }
    }
    drs
}

/// Run a version-2 input: the refusal message, or the trace as JSON text.
pub fn run(root: &JsObject) -> R<String> {
    let input = decode(root)?;
    validate(&input)?;
    set_keep(true);
    let mut fault_ids: Vec<String> = Vec::new();
    for id in &input.scenario.faults {
        if !fault_ids.contains(id) {
            fault_ids.push(id.clone());
        }
    }
    let faults: Vec<&Fault> = fault_ids.iter().filter_map(|id| input.fault(id)).collect();
    let (mut initial, mut seq) = initial_conf(&input, &faults);
    let initial_draws = initial_instants(&input, &mut initial, &mut seq);
    let mut sim = Sim {
        input: &input,
        faults,
        fault_ids,
        compiled: RefCell::new(HashMap::new()),
        mkeys: RefCell::new(HashMap::new()),
        conf: initial.deep_copy(),
        seq,
        attempts: HashMap::new(),
        delayed_by: HashMap::new(),
        steps: Vec::new(),
        initial_draws,
        taken: 0,
        meter: Measure::new(&input, &initial),
        keep_steps: input.scenario.output != "metrics",
    };
    let keep_steps = sim.keep_steps;
    let bound = input.scenario.step_limit;
    let mut outcome = if sim.conf.pending.is_empty() {
        "quiescent"
    } else {
        "running"
    };
    let mut spare: Option<Conf> = None;
    // The initial draws are output whatever the mode; the steps' records only when kept.
    set_keep(keep_steps);
    while outcome == "running" {
        let Some(h) = sim.conf.pending.first() else {
            outcome = "quiescent";
            break;
        };
        if input.scenario.stop_at.is_some_and(|s| h.time > s) {
            outcome = "stopped";
            break;
        }
        let mut next = spare.take().unwrap_or_default();
        sim.conf.deep_copy_into(&mut next);
        let mut head = next.pending.remove(0);
        // The payload object itself is never observed, only the values in it: copy when one of
        // them has an identity.
        if head.payload.has_nested_identity() {
            head.payload = head.payload.deep_copy();
        }
        next.time = head.time;
        // ORDER: the next arrival instant is created before anything else happens in the step.
        let mut adraws = Vec::new();
        if let (Some(k), Src::Arrival(wid, _, _)) = (head.first, &head.source) {
            if let Some(w) = input.workloads.iter().find(|w| &w.id == wid) {
                if let Some(pos) = next.workloads.iter().position(|(id, _)| **id == **wid) {
                    if next.workloads[pos].1.instants == k + 1 {
                        let mut st = next.workloads[pos].1.clone();
                        let mut seq = sim.seq;
                        adraws = make_instant(
                            &input,
                            w,
                            &mut st,
                            &mut next.streams,
                            &mut seq,
                            &mut next.pending,
                        );
                        next.workloads[pos].1 = st;
                        sim.seq = seq;
                    }
                }
            }
        }
        let with_draws = |mut rec: Box<StepRec>| {
            let mut ds = adraws.clone();
            ds.append(&mut rec.draws);
            rec.draws = ds;
            rec
        };
        match sim.step_head(next, head) {
            StepResult::Committed(rec, next, seq, attempts) => {
                let rec = with_draws(rec);
                sim.meter.observe(&input, &rec, &next);
                sim.taken += 1;
                if keep_steps {
                    sim.steps.push(*rec);
                }
                sim.seq = seq;
                if let Some((ev, n)) = attempts {
                    sim.attempts.insert(ev, n);
                }
                outcome = if next.pending.is_empty() {
                    "quiescent"
                } else if sim.taken >= bound {
                    "step-limit"
                } else {
                    "running"
                };
                spare = Some(std::mem::replace(&mut sim.conf, next));
            }
            StepResult::Failed(rec) => {
                let rec = with_draws(rec);
                sim.meter.observe(&input, &rec, &sim.conf);
                sim.taken += 1;
                if keep_steps {
                    sim.steps.push(*rec);
                }
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
        Src::Arrival(w, k, cl) => Obj::new()
            .put("kind", s("arrival"))
            .put("workload", s(w))
            .put("n", n(*k))
            .put("client", cl.as_deref().map_or(Value::Null, s))
            .done(),
        Src::ClientTimeout(w, k, cl) => Obj::new()
            .put("kind", s("client-timeout"))
            .put("workload", s(w))
            .put("n", n(*k))
            .put("client", s(cl))
            .done(),
        Src::Timer(b, v, t) => Obj::new()
            .put("kind", s("timer"))
            .put("behavior", s(b))
            .put("instance", v.clone())
            .put("timer", s(t))
            .done(),
        Src::Link(l, m) => Obj::new()
            .put("kind", s("link"))
            .put("link", s(l))
            .put("message", n(*m))
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
        EntryKind::ClientTimeout {
            workload,
            client,
            n: k,
        } => {
            o = o
                .put("kind", s("client-timeout"))
                .put("workload", s(workload))
                .put("client", n(*client))
                .put("request", n(*k));
        }
        EntryKind::LinkDone { link, key, msg } => {
            o = o
                .put("kind", s("link-done"))
                .put("link", s(link))
                .put("queue", s(key))
                .put("message", n(*msg));
        }
        EntryKind::FaultEdge { fault, on } => {
            o = o
                .put("kind", s("fault-edge"))
                .put("fault", s(fault))
                .put("edge", s(if *on { "at" } else { "until" }));
        }
    }
    o = o
        .opt("target", e.target.as_ref().map(addr))
        .opt("from", e.sender.as_ref().map(addr));
    if let Some(rs) = &e.routes {
        if !rs.is_empty() {
            let mut ro = JsObject::new();
            for (b, v) in rs {
                ro.insert(&**b, v.clone());
            }
            o = o.put("routes", Value::object(ro));
        }
    }
    if e.first.is_some() {
        o = o.put("first", Value::Bool(true));
    }
    o.opt("timer", e.timer.as_deref().map(s))
        .opt("copyOf", e.copy_of.map(n))
}

fn msg_value(m: &Msg) -> Value {
    Obj::new()
        .put("message", n(m.id))
        .put("event", s(&m.event))
        .put("size", n(m.size))
        .put("sentAt", n(m.sent_at))
        .put("payload", m.payload.clone())
        .opt("target", m.target.as_ref().map(addr))
        .opt("from", m.sender.as_ref().map(addr))
        .done()
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
    for (id, m) in c.machines.iter() {
        machines.insert(
            &**id,
            Obj::new()
                .put("state", s(&m.state))
                .put("vars", Value::object(m.vars.clone()))
                .done(),
        );
        incarnations.insert(&**id, n(0));
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
        resources.insert(d.id.to_string(), v);
    }
    let counters = |xs: &[(Rc<str>, u64)]| {
        let mut o = JsObject::new();
        for (k, v) in xs {
            o.insert(&**k, n(*v));
        }
        Value::object(o)
    };
    let empty = || Value::object(JsObject::new());
    Obj::new()
        .put("time", n(c.time))
        .put("machines", Value::object(machines))
        .put(
            "pending",
            Value::array(c.pending.iter().map(|e| pending(e)).collect()),
        )
        .put("resources", Value::object(resources))
        .put("links", {
            let mut lo = JsObject::new();
            for l in &i.links {
                let mut qo = JsObject::new();
                for ((ln, k), q) in c.lqueues.iter() {
                    if *ln == l.id {
                        qo.insert(
                            k.clone(),
                            Obj::new()
                                .put(
                                    "inTransfer",
                                    q.in_transfer.as_ref().map_or(Value::Null, msg_value),
                                )
                                .put(
                                    "waiting",
                                    Value::array(q.waiting.iter().map(msg_value).collect()),
                                )
                                .put("lastDelivery", q.last_delivery.map_or(Value::Null, n))
                                .done(),
                        );
                    }
                }
                lo.insert(&*l.id, Value::object(qo));
            }
            Value::object(lo)
        })
        .put("timers", {
            let mut to = JsObject::new();
            for e in c.pending.iter() {
                if let Some(t) = &e.timer {
                    to.insert(t.clone(), n(e.seq));
                }
            }
            Value::object(to)
        })
        .put("workloads", {
            let mut wo = JsObject::new();
            for (id, w) in c.workloads.iter() {
                wo.insert(
                    &**id,
                    Obj::new()
                        .put("instants", n(w.instants))
                        .put("arrivals", n(w.arrivals))
                        .put("repetition", n(w.cursor.rep))
                        .put("phase", n(w.cursor.phase))
                        .put("j", n(w.cursor.j))
                        .put("last", w.cursor.last.map_or(Value::Null, n))
                        .put("done", Value::Bool(w.cursor.done))
                        .opt(
                            "clients",
                            i.workloads
                                .iter()
                                .find(|x| *x.id == **id && x.kind == WKind::Closed)
                                .map(|_| {
                                    Value::array(
                                        w.clients
                                            .iter()
                                            .map(|x| x.map_or(Value::Null, n))
                                            .collect(),
                                    )
                                }),
                        )
                        .opt(
                            "groups",
                            (!w.groups.is_empty())
                                .then(|| Value::array(w.groups.iter().map(|g| n(*g)).collect())),
                        )
                        .done(),
                );
            }
            Value::object(wo)
        })
        .put("meters", empty())
        .put("routeCounters", counters(&c.route_counters))
        .put("streams", counters(&c.streams))
        .put("down", Value::array(Vec::new()))
        .put(
            "activeFaults",
            Value::array(c.active.iter().map(|x| s(x)).collect()),
        )
        .put("incarnations", Value::object(incarnations))
        .done()
}

fn draw_value(d: &Draw) -> Value {
    Obj::new()
        .put("stream", s(&d.stream))
        .put("index", n(d.index))
        .put("value", s(&d.value.to_string()))
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
                .put(
                    "considered",
                    Value::array(ig.considered.iter().map(|x| s(x)).collect()),
                )
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
    let draws = st.draws.iter().map(draw_value).collect();
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
        .put(
            "links",
            Value::array(
                st.links
                    .iter()
                    .map(|r| {
                        Obj::new()
                            .put("link", s(&r.link))
                            .put("queue", s(&r.queue))
                            .put("message", n(r.message))
                            .put("action", s(r.action))
                            .put("at", n(r.at))
                            .put("size", n(r.size))
                            .done()
                    })
                    .collect(),
            ),
        )
        .put("draws", Value::array(draws))
        .put(
            "config",
            configuration(
                i,
                st.config
                    .as_ref()
                    .expect("a kept step has its configuration"),
            ),
        )
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
        .put(
            "initialDraws",
            Value::array(sim.initial_draws.iter().map(draw_value).collect()),
        );
    if i.scenario.output != "metrics" {
        o = o.put("initial", configuration(i, initial)).put(
            "steps",
            Value::array(sim.steps.iter().map(|st| step_value(i, st)).collect()),
        );
    }
    let o = o.put("stepsTaken", n(sim.taken));
    let measured = i.measures();
    let o = o
        .put("outcome", s(outcome))
        .put(
            "truncated",
            Value::Bool(outcome == "step-limit" || outcome == "error"),
        )
        .put("final", configuration(i, &sim.conf));
    if measured {
        o.put("metrics", sim.meter.encode(i)).done()
    } else {
        o.done()
    }
}

// ---- The request lifecycle (Format2.lean, "The request lifecycle") -------------------------

#[derive(Clone, Debug)]
struct Rq {
    start: u64,
    orig: u64,
    legit: Option<bool>,
    outcome: Option<(&'static str, u64)>,
}

impl Rq {
    fn sample(&self) -> Option<u64> {
        match self.outcome {
            Some(("ok", t)) => Some(t - self.start),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, Default)]
struct ClassAcc {
    reqs: Vec<Rq>,
    /// Unended requests by key and by the sequence number of their original start entry.
    open: HashMap<String, usize>,
    by_orig: HashMap<u64, usize>,
    keys: Vec<String>,
    /// Keys that ever started a request.
    seen: std::collections::HashSet<String>,
    unkeyed: u64,
    duplicate: u64,
    late_ends: u64,
}

impl ClassAcc {
    fn end(&mut self, idx: usize, o: &'static str, t: u64) {
        self.reqs[idx].outcome = Some((o, t));
        let k = self.keys[idx].clone();
        self.open.remove(&k);
        self.by_orig.remove(&self.reqs[idx].orig);
    }
    fn end_key(&mut self, k: &str, o: &'static str, t: u64) {
        if let Some(&idx) = self.open.get(k) {
            self.end(idx, o, t);
        }
    }
}

fn payload_key(p: &Value, k: &str) -> Option<String> {
    match p.as_object().and_then(|o| o.get(k)) {
        None | Some(Value::Undefined) => None,
        Some(v) => Some(v.to_json()),
    }
}

fn starts_class(c: &ReqClass, h: &Entry) -> bool {
    h.event == c.start_event
        && matches!(h.kind, EntryKind::Event)
        && match &c.start_workload {
            None => true,
            Some(w) => matches!(&h.source, Src::Arrival(w2, _, _) if w2 == w),
        }
}

fn legit_of(i: &Input, h: &Entry) -> Option<bool> {
    match &h.source {
        Src::Arrival(w, _, _) => i
            .workloads
            .iter()
            .find(|x| x.id == *w)
            .map(|x| x.legitimate),
        Src::Transition(_, b) => match &h.sender {
            Some(Addr {
                inst: Value::String(s),
                ..
            }) => i
                .workloads
                .iter()
                .find(|w| {
                    w.kind == WKind::Population
                        && w.behavior == *b
                        && s.starts_with(&format!("{}:", w.id))
                })
                .map(|w| w.legitimate),
            _ => None,
        },
        _ => None,
    }
}

fn life_step(i: &Input, c: &ReqClass, acc: &mut ClassAcc, st: &StepRec) {
    let h = &st.head;
    let failed = st.error.is_some();
    let is_start = starts_class(c, h);
    if is_start && h.copy_of.is_none() {
        match payload_key(&h.payload, &c.key) {
            None => acc.unkeyed += 1,
            Some(k) => {
                if acc.open.contains_key(&k) {
                    acc.duplicate += 1;
                } else {
                    let idx = acc.reqs.len();
                    acc.reqs.push(Rq {
                        start: h.scheduled_at,
                        orig: h.seq,
                        legit: legit_of(i, h),
                        outcome: None,
                    });
                    acc.keys.push(k.clone());
                    acc.open.insert(k.clone(), idx);
                    acc.by_orig.insert(h.seq, idx);
                    acc.seen.insert(k);
                }
            }
        }
    }
    if is_start
        && !failed
        && (st.kind == Kind::Drop || (st.kind == Kind::Deliver && st.fired.is_empty()))
    {
        let orig = h.copy_of.unwrap_or(h.seq);
        if let Some(&idx) = acc.by_orig.get(&orig) {
            acc.end(idx, "error", st.time);
        }
    }
    if st.kind == Kind::Deliver && !failed {
        if let (Some((_, o)), Some(k)) = (
            c.ends.iter().find(|(e, _)| *e == h.event),
            payload_key(&h.payload, &c.key),
        ) {
            if acc.open.contains_key(&k) {
                acc.end_key(&k, o, st.time);
            } else if acc.seen.contains(&k) {
                acc.late_ends += 1;
            }
        }
    }
    if let EntryKind::ClientTimeout { workload, n: k, .. } = &h.kind {
        if let Some(wl) = i.workloads.iter().find(|x| x.id == *workload) {
            if wl.event == c.start_event && c.start_workload.as_ref().is_none_or(|x| x == workload)
            {
                let key = Value::str(format!("{workload}#{k}")).to_json();
                acc.end_key(&key, "timeout", st.time);
            }
        }
    }
}

fn samples_value(samples: &[Option<u64>], qs: &[(String, u64, u64)]) -> Value {
    let mut fin: Vec<u64> = samples.iter().filter_map(|x| *x).collect();
    let count = samples.len() as u64;
    let sum: u128 = fin.iter().map(|&x| u128::from(x)).sum();
    let max = fin.iter().max().copied();
    fin.sort_unstable();
    let mut qo = JsObject::new();
    for (key, qa, qb) in qs {
        let v = if count == 0 {
            Obj::new()
                .put("value", Value::Null)
                .put("empty", Value::Bool(true))
        } else {
            let rank = (u128::from(*qa) * u128::from(count))
                .div_ceil(u128::from(*qb))
                .max(1) as usize;
            match fin.get(rank - 1) {
                Some(x) => Obj::new().put("value", n(*x)),
                None => Obj::new()
                    .put("value", Value::Null)
                    .put("infinite", Value::Bool(true)),
            }
        };
        qo.insert(key.clone(), v.done());
    }
    Obj::new()
        .put("count", n(count))
        .put("finite", n(fin.len() as u64))
        .put("infinite", n(count - fin.len() as u64))
        .put("sum", Value::Number(sum as f64))
        .put("max", max.map_or(Value::Null, n))
        .put("quantiles", Value::object(qo))
        .done()
}

fn class_value(qs: &[(String, u64, u64)], acc: &ClassAcc, lo: u64, hi: u64) -> Obj {
    let ms: Vec<&Rq> = acc
        .reqs
        .iter()
        .filter(|r| lo <= r.start && r.start < hi)
        .collect();
    let cnt = |rs: &[&Rq], x: &str| {
        rs.iter()
            .filter(|r| r.outcome.is_some_and(|(o, _)| o == x))
            .count() as u64
    };
    let leg: Vec<&Rq> = ms
        .iter()
        .copied()
        .filter(|r| r.legit == Some(true))
        .collect();
    let samples: Vec<Option<u64>> = ms.iter().map(|r| r.sample()).collect();
    Obj::new()
        .put("measured", n(ms.len() as u64))
        .put(
            "outcomes",
            Obj::new()
                .put("ok", n(cnt(&ms, "ok")))
                .put("refused", n(cnt(&ms, "refused")))
                .put("timeout", n(cnt(&ms, "timeout")))
                .put("error", n(cnt(&ms, "error")))
                .put(
                    "censored",
                    n(ms.iter().filter(|r| r.outcome.is_none()).count() as u64),
                )
                .done(),
        )
        .put("responseTime", samples_value(&samples, qs))
        .put(
            "legitimate",
            Obj::new()
                .put("measured", n(leg.len() as u64))
                .put("refused", n(cnt(&leg, "refused")))
                .done(),
        )
}

// ---- Measured outputs (Format2.lean, "Measured outputs") ----------------------------------

#[derive(Clone, Debug, Default)]
struct ResSignals {
    busy: u128,
    cap_time: u128,
    max_held: u64,
    queue_int: u128,
    max_waiting: u64,
}

/// The measured outputs, accumulated step by step: the same function of the run as the Lean
/// definition over the whole step list.
struct Measure {
    w: u64,
    h: u64,
    /// Per resource: the last point (time, held, waiting, capacity) and the integrals.
    last: Vec<(u64, u64, u64, u64)>,
    sig: Vec<ResSignals>,
    /// Per resource: requests enqueued in the window, in order, and the first outcome of each.
    enq: Vec<Vec<u64>>,
    outcome: Vec<HashMap<u64, Option<u64>>>,
    /// Per request class, its requests.
    classes: Vec<ClassAcc>,
    /// Firings in the window: (time, behavior index, transition index).
    fired: Vec<(u64, usize, usize)>,
}

fn signals_at(d: &Resource, c: &Conf) -> (u64, u64, u64) {
    match c.resource(&d.id) {
        Some(s) => (held_all(&s.holds), s.waiting.len() as u64, s.capacity),
        None => (0, 0, 0),
    }
}

impl Measure {
    fn new(i: &Input, initial: &Conf) -> Measure {
        Measure {
            w: i.scenario.warmup.unwrap_or(0),
            h: i.scenario.horizon.unwrap_or(0),
            last: i
                .resources
                .iter()
                .map(|d| {
                    let (a, b, c) = signals_at(d, initial);
                    (0, a, b, c)
                })
                .collect(),
            sig: vec![ResSignals::default(); i.resources.len()],
            enq: vec![Vec::new(); i.resources.len()],
            outcome: vec![HashMap::new(); i.resources.len()],
            classes: vec![ClassAcc::default(); i.requests.len()],
            fired: Vec::new(),
        }
    }

    fn segment(&mut self, k: usize, b: u64) {
        let (a, held, waiting, cap) = self.last[k];
        let len = b.min(self.h).saturating_sub(a.max(self.w));
        if len == 0 {
            return;
        }
        let g = &mut self.sig[k];
        let len = u128::from(len);
        g.busy += u128::from(held) * len;
        g.cap_time += u128::from(cap) * len;
        g.max_held = g.max_held.max(held);
        g.queue_int += u128::from(waiting) * len;
        g.max_waiting = g.max_waiting.max(waiting);
    }

    fn observe(&mut self, i: &Input, st: &StepRec, conf: &Conf) {
        for (k, c) in i.requests.iter().enumerate() {
            life_step(i, c, &mut self.classes[k], st);
        }
        if self.w <= st.time && st.time < self.h {
            for f in &st.fired {
                if let Some(bi) = i.behaviors.iter().position(|b| b.id == f.behavior) {
                    if let Some(ti) = i.behaviors[bi]
                        .transitions
                        .iter()
                        .position(|t| t.id == f.transition)
                    {
                        self.fired.push((st.time, bi, ti));
                    }
                }
            }
        }
        for (k, d) in i.resources.iter().enumerate() {
            self.segment(k, st.time);
            let (a, b, c) = signals_at(d, conf);
            self.last[k] = (st.time, a, b, c);
        }
        for r in &st.resources {
            let Some(k) = i.resources.iter().position(|d| d.id == r.resource) else {
                continue;
            };
            let Some(id) = r.request else { continue };
            match r.action {
                "enqueued" => {
                    if self.w <= r.at && r.at < self.h {
                        self.enq[k].push(id);
                    }
                }
                "granted" | "refused" | "shed" | "dropped" | "timed-out" => {
                    let v = if r.action == "granted" {
                        Some(r.waited.unwrap_or(0))
                    } else {
                        None
                    };
                    self.outcome[k].entry(id).or_insert(v);
                }
                _ => {}
            }
        }
    }

    fn encode(&self, i: &Input) -> Value {
        let qs = i.metrics.clone().unwrap_or_else(default_quantiles);
        let big = |x: u128| Value::Number(x as f64);
        let mut res = JsObject::new();
        for (k, d) in i.resources.iter().enumerate() {
            let mut g = self.sig[k].clone();
            let (a, held, waiting, cap) = self.last[k];
            let len = a.max(self.h).min(self.h).saturating_sub(a.max(self.w));
            if len > 0 {
                let len = u128::from(len);
                g.busy += u128::from(held) * len;
                g.cap_time += u128::from(cap) * len;
                g.max_held = g.max_held.max(held);
                g.queue_int += u128::from(waiting) * len;
                g.max_waiting = g.max_waiting.max(waiting);
            }
            let samples: Vec<Option<u64>> = self.enq[k]
                .iter()
                .map(|id| self.outcome[k].get(id).copied().flatten())
                .collect();
            let mut fin: Vec<u64> = samples.iter().filter_map(|x| *x).collect();
            let count = samples.len() as u64;
            let sum: u128 = fin.iter().map(|&x| u128::from(x)).sum();
            let max = fin.iter().max().copied();
            fin.sort_unstable();
            let mut qo = JsObject::new();
            for (key, qa, qb) in &qs {
                let v = if count == 0 {
                    Obj::new()
                        .put("value", Value::Null)
                        .put("empty", Value::Bool(true))
                } else {
                    let rank = (u128::from(*qa) * u128::from(count))
                        .div_ceil(u128::from(*qb))
                        .max(1) as usize;
                    match fin.get(rank - 1) {
                        Some(x) => Obj::new().put("value", n(*x)),
                        None => Obj::new()
                            .put("value", Value::Null)
                            .put("infinite", Value::Bool(true)),
                    }
                };
                qo.insert(key.clone(), v.done());
            }
            res.insert(
                d.id.to_string(),
                Obj::new()
                    .put(
                        "utilisation",
                        Obj::new()
                            .put("busy", big(g.busy))
                            .put("capacityTime", big(g.cap_time))
                            .put("max", n(g.max_held))
                            .done(),
                    )
                    .put(
                        "queueLength",
                        Obj::new()
                            .put("integral", big(g.queue_int))
                            .put("window", n(self.h.saturating_sub(self.w)))
                            .put("max", n(g.max_waiting))
                            .done(),
                    )
                    .put(
                        "waitingTime",
                        Obj::new()
                            .put("count", n(count))
                            .put("finite", n(fin.len() as u64))
                            .put("infinite", n(count - fin.len() as u64))
                            .put("sum", big(sum))
                            .put("max", max.map_or(Value::Null, n))
                            .put("quantiles", Value::object(qo))
                            .done(),
                    )
                    .done(),
            );
        }
        let mut reqs = JsObject::new();
        for (k, c) in i.requests.iter().enumerate() {
            let acc = &self.classes[k];
            reqs.insert(
                c.id.clone(),
                class_value(&qs, acc, self.w, self.h)
                    .put("unkeyed", n(acc.unkeyed))
                    .put("duplicate", n(acc.duplicate))
                    .put("lateEnds", n(acc.late_ends))
                    .put("window", n(self.h.saturating_sub(self.w)))
                    .done(),
            );
        }
        let transitions = |lo: u64, hi: u64| {
            let mut to = JsObject::new();
            for (bi, b) in i.behaviors.iter().enumerate() {
                for (ti, t) in b.transitions.iter().enumerate() {
                    let c = self
                        .fired
                        .iter()
                        .filter(|(tm, x, y)| *x == bi && *y == ti && lo <= *tm && *tm < hi)
                        .count();
                    to.insert(format!("{}.{}", b.id, t.id), n(c as u64));
                }
            }
            Value::object(to)
        };
        let mut o = Obj::new()
            .put(
                "window",
                Obj::new()
                    .put("from", n(self.w))
                    .put("until", n(self.h))
                    .done(),
            )
            .put("requests", Value::object(reqs))
            .put("transitions", transitions(self.w, self.h))
            .put("resources", Value::object(res));
        if let Some(b) = i.series {
            let mut buckets = Vec::new();
            for k in 0..self.h.saturating_sub(self.w) / b {
                let lo = self.w + k * b;
                let mut rq = JsObject::new();
                for (ci, c) in i.requests.iter().enumerate() {
                    rq.insert(
                        c.id.clone(),
                        class_value(&qs, &self.classes[ci], lo, lo + b).done(),
                    );
                }
                buckets.push(
                    Obj::new()
                        .put("from", n(lo))
                        .put("until", n(lo + b))
                        .put("requests", Value::object(rq))
                        .put("transitions", transitions(lo, lo + b))
                        .done(),
                );
            }
            o = o.put(
                "series",
                Obj::new()
                    .put("bucket", n(b))
                    .put("buckets", Value::array(buckets))
                    .done(),
            );
        }
        o.done()
    }
}
