//! The engine input (format `exegra-sim-input`, version 1), as `src/core/sim-input.js` writes it
//! and `docs/simulation.md` ("Engine input") documents it.
//!
//! Conversion from JSON checks the format and version first, with the reference engine's
//! messages, then the shape of every field the engine reads. A field of the wrong JSON type is a
//! refusal here, where the reference engine would go on with JavaScript coercions; a validated
//! model never produces one. Literal values (variable initials, payloads, literal `to` and
//! payload entries) are kept as [`Value`]s, untouched.
//!
//! Later input sections (instances, resources, a random seed, aspect hooks) belong here as new
//! fields of [`SimInput`] and their own types.

use crate::value::{js_display, JsObject, Value};

pub const SIM_INPUT_FORMAT: &str = "exegra-sim-input";
pub const SIM_INPUT_VERSION: f64 = 1.0;

/// One scenario run: everything the engine reads, and nothing else.
#[derive(Clone, Debug)]
pub struct SimInput {
    pub scenario: ScenarioInput,
    pub behaviors: Vec<BehaviorInput>,
    pub events: Vec<String>,
    pub faults: Vec<FaultInput>,
}

#[derive(Clone, Debug)]
pub struct ScenarioInput {
    pub id: String,
    pub steps: Vec<StepInput>,
    /// The active fault ids as listed (`faults ?? []`); the engine removes repeats.
    pub faults: Vec<String>,
    /// `stepLimit ?? 1000`.
    pub step_limit: f64,
}

#[derive(Clone, Debug)]
pub struct StepInput {
    pub at: f64,
    pub event: String,
    /// `payload ?? {}`.
    pub payload: Value,
}

#[derive(Clone, Debug)]
pub struct BehaviorInput {
    pub id: String,
    /// Used only for `responsible`, and only when it is a string.
    pub subject: Option<String>,
    pub initial: String,
    pub variables: Vec<VariableInput>,
    pub transitions: Vec<TransitionInput>,
}

#[derive(Clone, Debug)]
pub struct VariableInput {
    pub name: String,
    /// [`Value::Undefined`] when the input has no `initial`.
    pub initial: Value,
}

#[derive(Clone, Debug)]
pub struct TransitionInput {
    pub id: String,
    pub from: String,
    pub to: String,
    pub on: String,
    /// The guard when it is a string; anything else means no guard.
    pub guard: Option<String>,
    pub effects: Vec<Effect>,
    /// `faultOnly === true`.
    pub fault_only: bool,
}

#[derive(Clone, Debug)]
pub enum Effect {
    /// `{set, to}`; `to` is `None` when absent (an error when the effect runs).
    Set { variable: String, to: Option<Value> },
    /// `{emit, after, payload}`, with `after ?? 0` and `payload ?? {}` applied.
    Emit {
        event: String,
        after: f64,
        payload: JsObject,
    },
    /// Neither `set` nor `emit` (an error when the effect runs).
    Malformed,
}

/// How a fault's `occurrence` matches an attempt number.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Occurrence {
    /// No `occurrence`: every attempt.
    Any,
    /// A number: that attempt only.
    Exactly(f64),
    /// Present but not a number (`null`, ...): `occurrence === attempt` never holds.
    Never,
}

impl Occurrence {
    pub fn matches(self, attempt: u64) -> bool {
        match self {
            Occurrence::Any => true,
            Occurrence::Exactly(n) => n == attempt as f64,
            Occurrence::Never => false,
        }
    }
}

#[derive(Clone, Debug)]
pub struct FaultInput {
    pub id: String,
    pub kind: Option<String>,
    pub event: Option<String>,
    pub transition: Option<String>,
    pub occurrence: Occurrence,
    /// `by` of a `delay-event` fault (required for that kind).
    pub by: f64,
    /// `at` of an `inject-event` fault (required for that kind).
    pub at: f64,
    /// `payload ?? {}` of an `inject-event` fault.
    pub payload: Value,
}

impl FaultInput {
    pub fn is_kind(&self, kind: &str) -> bool {
        self.kind.as_deref() == Some(kind)
    }
}

// ---- conversion -----------------------------------------------------------------------------

type R<T> = Result<T, String>;

fn field<'a>(o: &'a JsObject, key: &str) -> &'a Value {
    o.get(key).unwrap_or(&Value::Undefined)
}

fn object<'a>(v: &'a Value, what: &str) -> R<&'a JsObject> {
    v.as_object()
        .ok_or_else(|| format!("{what} must be an object."))
}

fn string(o: &JsObject, key: &str, what: &str) -> R<String> {
    field(o, key)
        .as_str()
        .map(str::to_string)
        .ok_or_else(|| format!("{what}: \"{key}\" must be a string."))
}

fn number(o: &JsObject, key: &str, what: &str) -> R<f64> {
    field(o, key)
        .as_number()
        .ok_or_else(|| format!("{what}: \"{key}\" must be a number."))
}

fn array<'a>(o: &'a JsObject, key: &str, what: &str) -> R<&'a [Value]> {
    match field(o, key) {
        Value::Array(items) => Ok(items.as_slice()),
        _ => Err(format!("{what}: \"{key}\" must be an array.")),
    }
}

/// An array where the reference engine applies `Array.isArray(x) ? x : []`.
fn array_or_empty<'a>(o: &'a JsObject, key: &str) -> &'a [Value] {
    match field(o, key) {
        Value::Array(items) => items.as_slice(),
        _ => &[],
    }
}

/// `x ?? {}`.
fn payload_or_empty(v: &Value) -> Value {
    if v.is_nullish() {
        Value::object(JsObject::new())
    } else {
        v.clone()
    }
}

impl SimInput {
    /// Convert a parsed engine input. Errors are refusals, not traces.
    pub fn from_value(input: &Value) -> R<SimInput> {
        let format_error =
            || format!("Not an engine input: \"format\" must be \"{SIM_INPUT_FORMAT}\".");
        let root = input.as_object().ok_or_else(format_error)?;
        if field(root, "format").as_str() != Some(SIM_INPUT_FORMAT) {
            return Err(format_error());
        }
        let version = field(root, "version");
        if version.as_number() != Some(SIM_INPUT_VERSION) {
            return Err(format!(
                "Unsupported engine input version {}; this engine reads version 1.",
                js_display(version)
            ));
        }

        let events = array(root, "events", "input")?
            .iter()
            .enumerate()
            .map(|(i, e)| {
                string(
                    object(e, &format!("events[{i}]"))?,
                    "id",
                    &format!("events[{i}]"),
                )
            })
            .collect::<R<Vec<_>>>()?;

        let behaviors = array(root, "behaviors", "input")?
            .iter()
            .enumerate()
            .map(|(i, b)| behavior(b, i))
            .collect::<R<Vec<_>>>()?;

        let faults = array(root, "faults", "input")?
            .iter()
            .enumerate()
            .map(|(i, f)| fault(f, i))
            .collect::<R<Vec<_>>>()?;

        let sc = object(field(root, "scenario"), "scenario")?;
        let id = string(sc, "id", "scenario")?;
        let steps = array(sc, "steps", "scenario")?
            .iter()
            .enumerate()
            .map(|(i, st)| {
                let what = format!("scenario.steps[{i}]");
                let st = object(st, &what)?;
                Ok(StepInput {
                    at: number(st, "at", &what)?,
                    event: string(st, "event", &what)?,
                    payload: payload_or_empty(field(st, "payload")),
                })
            })
            .collect::<R<Vec<_>>>()?;
        let fault_ids = match field(sc, "faults") {
            v if v.is_nullish() => Vec::new(),
            Value::Array(items) => items
                .iter()
                .map(|v| {
                    v.as_str()
                        .map(str::to_string)
                        .ok_or_else(|| "scenario.faults must hold strings.".to_string())
                })
                .collect::<R<Vec<_>>>()?,
            _ => return Err("scenario: \"faults\" must be an array.".to_string()),
        };
        let step_limit = match field(sc, "stepLimit") {
            v if v.is_nullish() => 1000.0,
            Value::Number(n) => *n,
            _ => return Err("scenario: \"stepLimit\" must be a number.".to_string()),
        };

        Ok(SimInput {
            scenario: ScenarioInput {
                id,
                steps,
                faults: fault_ids,
                step_limit,
            },
            behaviors,
            events,
            faults,
        })
    }
}

fn behavior(v: &Value, i: usize) -> R<BehaviorInput> {
    let what = format!("behaviors[{i}]");
    let b = object(v, &what)?;
    let id = string(b, "id", &what)?;
    let variables = array_or_empty(b, "variables")
        .iter()
        .enumerate()
        .map(|(j, var)| {
            let vw = format!("{what}.variables[{j}]");
            let var = object(var, &vw)?;
            Ok(VariableInput {
                name: string(var, "name", &vw)?,
                initial: field(var, "initial").clone(),
            })
        })
        .collect::<R<Vec<_>>>()?;
    let transitions = array_or_empty(b, "transitions")
        .iter()
        .enumerate()
        .map(|(j, t)| transition(t, &format!("{what}.transitions[{j}]")))
        .collect::<R<Vec<_>>>()?;
    Ok(BehaviorInput {
        id,
        subject: field(b, "subject").as_str().map(str::to_string),
        initial: string(b, "initial", &what)?,
        variables,
        transitions,
    })
}

fn transition(v: &Value, what: &str) -> R<TransitionInput> {
    let t = object(v, what)?;
    let effects = array_or_empty(t, "effects")
        .iter()
        .enumerate()
        .map(|(k, fx)| effect(fx, &format!("{what}.effects[{k}]")))
        .collect::<R<Vec<_>>>()?;
    Ok(TransitionInput {
        id: string(t, "id", what)?,
        from: string(t, "from", what)?,
        to: string(t, "to", what)?,
        on: string(t, "on", what)?,
        guard: field(t, "guard").as_str().map(str::to_string),
        effects,
        fault_only: matches!(field(t, "faultOnly"), Value::Bool(true)),
    })
}

fn effect(v: &Value, what: &str) -> R<Effect> {
    let Some(fx) = v.as_object() else {
        return Ok(Effect::Malformed);
    };
    if fx.contains_key("set") {
        let to = match field(fx, "to") {
            Value::Undefined => None,
            other => Some(other.clone()),
        };
        return Ok(Effect::Set {
            variable: string(fx, "set", what)?,
            to,
        });
    }
    if fx.contains_key("emit") {
        let after = match field(fx, "after") {
            v if v.is_nullish() => 0.0,
            Value::Number(n) => *n,
            _ => return Err(format!("{what}: \"after\" must be a number.")),
        };
        let payload = match field(fx, "payload") {
            v if v.is_nullish() => JsObject::new(),
            Value::Object(o) => (**o).clone(),
            _ => return Err(format!("{what}: \"payload\" must be an object.")),
        };
        return Ok(Effect::Emit {
            event: string(fx, "emit", what)?,
            after,
            payload,
        });
    }
    Ok(Effect::Malformed)
}

fn fault(v: &Value, i: usize) -> R<FaultInput> {
    let what = format!("faults[{i}]");
    let f = object(v, &what)?;
    let opt_string = |key: &str| -> R<Option<String>> {
        match field(f, key) {
            Value::Undefined => Ok(None),
            Value::String(s) => Ok(Some(s.clone())),
            _ => Err(format!("{what}: \"{key}\" must be a string.")),
        }
    };
    let kind = opt_string("kind")?;
    let occurrence = match field(f, "occurrence") {
        Value::Undefined => Occurrence::Any,
        Value::Number(n) => Occurrence::Exactly(*n),
        _ => Occurrence::Never,
    };
    let by = match kind.as_deref() {
        Some("delay-event") => number(f, "by", &what)?,
        _ => 0.0,
    };
    let at = match kind.as_deref() {
        Some("inject-event") => number(f, "at", &what)?,
        _ => 0.0,
    };
    Ok(FaultInput {
        id: string(f, "id", &what)?,
        kind,
        event: opt_string("event")?,
        transition: opt_string("transition")?,
        occurrence,
        by,
        at,
        payload: payload_or_empty(field(f, "payload")),
    })
}
