//! The trace (format version 1): configurations, steps and the run's outcome, as
//! `docs/simulation.md` ("Trace") documents them, and their JSON form.
//!
//! Every record holds its own values: the engine builds a record from the state of the moment
//! and never changes it afterwards. Arrays and objects inside values are immutable once
//! created, so a record may share them with the live configuration without ever observing a
//! later change.

use crate::value::{write_json_object, JsObject, Value};

/// Where a queue entry came from.
#[derive(Clone, Debug, PartialEq)]
pub enum Source {
    /// Input step `step` of `scenario.steps`.
    Scenario { step: usize },
    /// An `inject-event` fault.
    Fault { fault: String },
    /// An `emit` effect.
    Transition {
        transition: String,
        behavior: String,
    },
}

/// One queue entry.
#[derive(Clone, Debug)]
pub struct Pending {
    pub seq: u64,
    pub time: f64,
    pub event: String,
    pub payload: Value,
    pub source: Source,
}

impl Pending {
    /// The reference engine's `deepCopy` of an entry.
    pub fn deep_copy(&self) -> Pending {
        Pending {
            payload: self.payload.deep_copy(),
            ..self.clone()
        }
    }
}

/// One machine: a behavior's state and variables.
#[derive(Clone, Debug)]
pub struct Machine {
    pub state: String,
    pub vars: JsObject,
}

/// A configuration: logical time, one machine per behavior, and the pending queue ordered by
/// `(time, seq)`.
#[derive(Clone, Debug, Default)]
pub struct Configuration {
    pub time: f64,
    /// Machines by behavior id, in the order they were created.
    pub machines: Vec<(String, Machine)>,
    pub pending: Vec<Pending>,
}

impl Configuration {
    pub fn machine(&self, id: &str) -> Option<&Machine> {
        self.machines.iter().find(|(k, _)| k == id).map(|(_, m)| m)
    }

    pub fn machine_mut(&mut self, id: &str) -> Option<&mut Machine> {
        self.machines
            .iter_mut()
            .find(|(k, _)| k == id)
            .map(|(_, m)| m)
    }

    /// `machines[id] = m`: an existing machine keeps its position.
    pub fn set_machine(&mut self, id: &str, m: Machine) {
        match self.machine_mut(id) {
            Some(slot) => *slot = m,
            None => self.machines.push((id.to_string(), m)),
        }
    }

    /// The reference engine's `deepCopy`: every array and object inside a value is fresh.
    pub fn deep_copy(&self) -> Configuration {
        Configuration {
            time: self.time,
            machines: self
                .machines
                .iter()
                .map(|(id, m)| {
                    (
                        id.clone(),
                        Machine {
                            state: m.state.clone(),
                            vars: m.vars.deep_copy(),
                        },
                    )
                })
                .collect(),
            pending: self.pending.iter().map(Pending::deep_copy).collect(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StepKind {
    Deliver,
    Drop,
    Delay,
}

impl StepKind {
    pub fn as_str(self) -> &'static str {
        match self {
            StepKind::Deliver => "deliver",
            StepKind::Drop => "drop",
            StepKind::Delay => "delay",
        }
    }
}

/// The head of the queue as a step records it: `{id, payload, seq, source}`.
#[derive(Clone, Debug)]
pub struct EventRecord {
    pub id: String,
    pub payload: Value,
    pub seq: u64,
    pub source: Source,
}

#[derive(Clone, Debug)]
pub struct SetRecord {
    pub variable: String,
    /// [`Value::Undefined`] (left out of the JSON) when the variable had no value.
    pub before: Value,
    pub after: Value,
}

#[derive(Clone, Debug)]
pub struct EmitRecord {
    pub event: String,
    pub time: f64,
    pub seq: u64,
    pub payload: Value,
}

#[derive(Clone, Debug)]
pub struct Fired {
    pub behavior: String,
    pub transition: String,
    pub from: String,
    pub to: String,
    pub guard: Option<String>,
    pub sets: Vec<SetRecord>,
    pub emitted: Vec<EmitRecord>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IgnoredReason {
    NoTransition,
    GuardFalse,
    Disabled,
}

impl IgnoredReason {
    pub fn as_str(self) -> &'static str {
        match self {
            IgnoredReason::NoTransition => "no-transition",
            IgnoredReason::GuardFalse => "guard-false",
            IgnoredReason::Disabled => "disabled",
        }
    }
}

#[derive(Clone, Debug)]
pub struct Ignored {
    pub behavior: String,
    pub reason: IgnoredReason,
    pub considered: Vec<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FaultEffect {
    Dropped,
    Delayed,
    Enabled,
    Disabled,
    Injected,
}

impl FaultEffect {
    pub fn as_str(self) -> &'static str {
        match self {
            FaultEffect::Dropped => "dropped",
            FaultEffect::Delayed => "delayed",
            FaultEffect::Enabled => "enabled",
            FaultEffect::Disabled => "disabled",
            FaultEffect::Injected => "injected",
        }
    }
}

#[derive(Clone, Debug)]
pub struct FaultRecord {
    pub fault: String,
    pub effect: FaultEffect,
}

/// One step of a run.
#[derive(Clone, Debug)]
pub struct TraceStep {
    pub index: usize,
    pub time: f64,
    pub kind: StepKind,
    pub event: EventRecord,
    pub fired: Vec<Fired>,
    pub ignored: Vec<Ignored>,
    pub faults: Vec<FaultRecord>,
    pub responsible: Vec<String>,
    pub config: Configuration,
    /// The message of a failed step.
    pub error: Option<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Outcome {
    Running,
    Quiescent,
    StepLimit,
    Error,
}

impl Outcome {
    pub fn as_str(self) -> &'static str {
        match self {
            Outcome::Running => "running",
            Outcome::Quiescent => "quiescent",
            Outcome::StepLimit => "step-limit",
            Outcome::Error => "error",
        }
    }
}

/// A run: what `runInput` returns.
#[derive(Clone, Debug)]
pub struct Trace {
    pub scenario_id: String,
    pub faults: Vec<String>,
    pub initial: Configuration,
    pub steps: Vec<TraceStep>,
    pub outcome: Outcome,
    pub final_config: Configuration,
}

// ---- JSON -----------------------------------------------------------------------------------

/// Builds a JSON object field by field.
struct Obj(JsObject);

impl Obj {
    fn new() -> Self {
        Obj(JsObject::new())
    }

    fn put(mut self, key: &str, v: Value) -> Self {
        self.0.insert(key, v);
        self
    }

    fn done(self) -> Value {
        Value::object(self.0)
    }
}

fn s(x: &str) -> Value {
    Value::str(x)
}

fn n(x: f64) -> Value {
    Value::Number(x)
}

fn seq(x: u64) -> Value {
    Value::Number(x as f64)
}

fn strings(xs: &[String]) -> Value {
    Value::array(xs.iter().map(|x| s(x)).collect())
}

impl Source {
    pub fn to_value(&self) -> Value {
        match self {
            Source::Scenario { step } => Obj::new()
                .put("kind", s("scenario"))
                .put("step", n(*step as f64))
                .done(),
            Source::Fault { fault } => Obj::new()
                .put("kind", s("fault"))
                .put("fault", s(fault))
                .done(),
            Source::Transition {
                transition,
                behavior,
            } => Obj::new()
                .put("kind", s("transition"))
                .put("transition", s(transition))
                .put("behavior", s(behavior))
                .done(),
        }
    }
}

impl Pending {
    pub fn to_value(&self) -> Value {
        Obj::new()
            .put("seq", seq(self.seq))
            .put("time", n(self.time))
            .put("event", s(&self.event))
            .put("payload", self.payload.clone())
            .put("source", self.source.to_value())
            .done()
    }
}

impl Configuration {
    pub fn to_value(&self) -> Value {
        let mut machines = JsObject::new();
        for (id, m) in &self.machines {
            machines.insert(
                id.clone(),
                Obj::new()
                    .put("state", s(&m.state))
                    .put("vars", Value::object(m.vars.clone()))
                    .done(),
            );
        }
        Obj::new()
            .put("time", n(self.time))
            .put("machines", Value::object(machines))
            .put(
                "pending",
                Value::array(self.pending.iter().map(Pending::to_value).collect()),
            )
            .done()
    }
}

impl Fired {
    pub fn to_value(&self) -> Value {
        let sets = self
            .sets
            .iter()
            .map(|r| {
                Obj::new()
                    .put("variable", s(&r.variable))
                    .put("before", r.before.clone())
                    .put("after", r.after.clone())
                    .done()
            })
            .collect();
        let emitted = self
            .emitted
            .iter()
            .map(|e| {
                Obj::new()
                    .put("event", s(&e.event))
                    .put("time", n(e.time))
                    .put("seq", seq(e.seq))
                    .put("payload", e.payload.clone())
                    .done()
            })
            .collect();
        Obj::new()
            .put("behavior", s(&self.behavior))
            .put("transition", s(&self.transition))
            .put("from", s(&self.from))
            .put("to", s(&self.to))
            .put("guard", self.guard.as_deref().map_or(Value::Null, s))
            .put("sets", Value::array(sets))
            .put("emitted", Value::array(emitted))
            .done()
    }
}

impl TraceStep {
    pub fn to_value(&self) -> Value {
        let event = Obj::new()
            .put("id", s(&self.event.id))
            .put("payload", self.event.payload.clone())
            .put("seq", seq(self.event.seq))
            .put("source", self.event.source.to_value())
            .done();
        let ignored = self
            .ignored
            .iter()
            .map(|i| {
                Obj::new()
                    .put("behavior", s(&i.behavior))
                    .put("reason", s(i.reason.as_str()))
                    .put("considered", strings(&i.considered))
                    .done()
            })
            .collect();
        let faults = self
            .faults
            .iter()
            .map(|f| {
                Obj::new()
                    .put("fault", s(&f.fault))
                    .put("effect", s(f.effect.as_str()))
                    .done()
            })
            .collect();
        let mut o = Obj::new()
            .put("index", n(self.index as f64))
            .put("time", n(self.time))
            .put("kind", s(self.kind.as_str()))
            .put("event", event)
            .put(
                "fired",
                Value::array(self.fired.iter().map(Fired::to_value).collect()),
            )
            .put("ignored", Value::array(ignored))
            .put("faults", Value::array(faults))
            .put("responsible", strings(&self.responsible))
            .put("config", self.config.to_value());
        if let Some(message) = &self.error {
            o = o.put("error", Obj::new().put("message", s(message)).done());
        }
        o.done()
    }
}

impl Trace {
    pub fn to_value(&self) -> Value {
        Obj::new()
            .put("scenarioId", s(&self.scenario_id))
            .put("faults", strings(&self.faults))
            .put("initial", self.initial.to_value())
            .put(
                "steps",
                Value::array(self.steps.iter().map(TraceStep::to_value).collect()),
            )
            .put("outcome", s(self.outcome.as_str()))
            .put("final", self.final_config.to_value())
            .done()
    }

    /// The trace as compact JSON text.
    pub fn to_json(&self) -> String {
        let mut out = String::new();
        match self.to_value() {
            Value::Object(o) => write_json_object(&o, &mut out),
            other => other.write_json(&mut out),
        }
        out
    }
}
