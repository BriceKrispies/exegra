//! The discrete-event simulation, ported from `createSimulation` in the former `src/core/sim.js`.
//!
//! [`EngineSource`] is the narrow view of the input the engine reads (entities by id and each
//! behavior's transitions), as `sourceOf` builds it in `src/core/sim-input.js`. [`Simulation`]
//! holds the run state and steps it; [`Simulation::step`] is one event delivery.
//!
//! Homes for later features: per-instance machines extend [`Configuration`] and the machine
//! lookup in [`resolve`]; resources and a seeded random generator become fields of the run state
//! next to `seq`, `attempts` and `delayed_by` (reset by [`Simulation::reset`]); aspect hooks are
//! calls at the step boundaries of [`Simulation::step`] (before the head is handled, after
//! phase 1, after phase 2).

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::expr::{eval_expr, parse_expr, Ast};
use crate::input::{BehaviorInput, Effect, FaultInput, SimInput, TransitionInput};
use crate::trace::{
    Configuration, EmitRecord, EventRecord, FaultEffect, FaultRecord, Fired, Ignored,
    IgnoredReason, Machine, Outcome, Pending, SetRecord, Source, StepKind, Trace, TraceStep,
};
use crate::value::{JsObject, Value};

/// What an id names in the engine source.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Entity {
    Event,
    Behavior(usize),
    Fault(usize),
    Scenario,
}

/// The engine's view of an input: entities by id (a later declaration with the same id replaces
/// an earlier one, in the order events, behaviors, faults, scenario) and the transitions.
pub struct EngineSource<'a> {
    input: &'a SimInput,
    entities: HashMap<&'a str, Entity>,
}

impl<'a> EngineSource<'a> {
    pub fn new(input: &'a SimInput) -> Self {
        let mut entities = HashMap::new();
        for e in &input.events {
            entities.insert(e.as_str(), Entity::Event);
        }
        for (i, b) in input.behaviors.iter().enumerate() {
            entities.insert(b.id.as_str(), Entity::Behavior(i));
        }
        for (i, f) in input.faults.iter().enumerate() {
            entities.insert(f.id.as_str(), Entity::Fault(i));
        }
        entities.insert(input.scenario.id.as_str(), Entity::Scenario);
        EngineSource { input, entities }
    }

    fn is_event(&self, id: &str) -> bool {
        self.entities.get(id) == Some(&Entity::Event)
    }

    fn behavior(&self, id: &str) -> Option<&'a BehaviorInput> {
        match self.entities.get(id) {
            Some(Entity::Behavior(i)) => Some(&self.input.behaviors[*i]),
            _ => None,
        }
    }

    fn fault(&self, id: &str) -> Option<&'a FaultInput> {
        match self.entities.get(id) {
            Some(Entity::Fault(i)) => Some(&self.input.faults[*i]),
            _ => None,
        }
    }

    /// Transitions owned by a behavior id, in declaration order.
    fn transitions_of(&self, bid: &str) -> Vec<&'a TransitionInput> {
        self.input
            .behaviors
            .iter()
            .filter(|b| b.id == bid)
            .flat_map(|b| b.transitions.iter())
            .collect()
    }
}

/// Reference resolver for one behavior's scope (`resolverFor` in sim.js).
fn resolve(view: &Configuration, bid: &str, payload: &Value, time: f64, path: &[String]) -> Value {
    if path.len() == 1 {
        if path[0] == "time" {
            return Value::Number(time);
        }
        return view
            .machine(bid)
            .and_then(|m| m.vars.get(&path[0]))
            .cloned()
            .unwrap_or(Value::Undefined);
    }
    if path.len() != 2 {
        return Value::Undefined;
    }
    if path[0] == "event" {
        return payload
            .as_object()
            .and_then(|o| o.get(&path[1]))
            .cloned()
            .unwrap_or(Value::Undefined);
    }
    let Some(m) = view.machine(&path[0]) else {
        return Value::Undefined;
    };
    if path[1] == "state" {
        return Value::String(m.state.clone());
    }
    m.vars.get(&path[1]).cloned().unwrap_or(Value::Undefined)
}

/// Keep the queue ordered by (time, seq): a new entry goes after every entry with an equal or
/// earlier time.
fn insert_pending(queue: &mut Vec<Pending>, entry: Pending) {
    let mut i = queue.len();
    while i > 0 && queue[i - 1].time > entry.time {
        i -= 1;
    }
    queue.insert(i, entry);
}

/// A simulation of one scenario, ready to step.
pub struct Simulation<'a> {
    source: EngineSource<'a>,
    scenario_id: String,
    behavior_ids: Vec<String>,
    /// Transitions per entry of `behavior_ids`.
    transitions: Vec<Vec<&'a TransitionInput>>,
    fault_ids: Vec<String>,
    faults: Vec<&'a FaultInput>,
    limit: f64,
    initial: Configuration,
    initial_seq: u64,
    compiled: RefCell<HashMap<String, Rc<Ast>>>,

    // run state
    config: Configuration,
    steps: Vec<TraceStep>,
    outcome: Outcome,
    seq: u64,
    /// Event id -> delivery attempts so far.
    attempts: HashMap<String, u64>,
    /// Queue entry seq -> ids of the delay faults that already delayed it or its ancestors.
    delayed_by: HashMap<u64, HashSet<String>>,
}

impl<'a> Simulation<'a> {
    /// Create a simulation of the input's scenario with its active faults. Errors are the
    /// reference engine's creation refusals.
    pub fn new(input: &'a SimInput) -> Result<Self, String> {
        let source = EngineSource::new(input);
        let scenario_id = input.scenario.id.clone();
        let behavior_ids: Vec<String> = input.behaviors.iter().map(|b| b.id.clone()).collect();

        // `behaviors` map of sim.js: first occurrence's position, last declaration's data.
        let mut behaviors: Vec<(&str, &'a BehaviorInput)> = Vec::new();
        for bid in &behavior_ids {
            let Some(b) = source.behavior(bid) else {
                return Err(format!(
                    "Scenario \"{scenario_id}\" lists \"{bid}\", which is not a behavior."
                ));
            };
            match behaviors.iter_mut().find(|(k, _)| *k == bid.as_str()) {
                Some(slot) => slot.1 = b,
                None => behaviors.push((bid.as_str(), b)),
            }
        }
        let transitions = behavior_ids
            .iter()
            .map(|bid| source.transitions_of(bid))
            .collect();

        let mut fault_ids: Vec<String> = Vec::new();
        for id in &input.scenario.faults {
            if !fault_ids.contains(id) {
                fault_ids.push(id.clone());
            }
        }
        let mut faults = Vec::new();
        for id in &fault_ids {
            match source.fault(id) {
                Some(f) => faults.push(f),
                None => return Err(format!("\"{id}\" is not a fault in this model.")),
            }
        }

        // Initial configuration.
        let mut initial = Configuration::default();
        for (bid, b) in &behaviors {
            let mut vars = JsObject::new();
            for v in &b.variables {
                vars.insert(v.name.clone(), v.initial.deep_copy());
            }
            initial.set_machine(
                bid,
                Machine {
                    state: b.initial.clone(),
                    vars,
                },
            );
        }
        let mut seq = 0u64;
        for (i, st) in input.scenario.steps.iter().enumerate() {
            if !source.is_event(&st.event) {
                return Err(format!(
                    "Scenario \"{scenario_id}\" step {i} delivers \"{}\", which is not an event.",
                    st.event
                ));
            }
            insert_pending(
                &mut initial.pending,
                Pending {
                    seq,
                    time: st.at,
                    event: st.event.clone(),
                    payload: st.payload.deep_copy(),
                    source: Source::Scenario { step: i },
                },
            );
            seq += 1;
        }
        for f in &faults {
            if !f.is_kind("inject-event") {
                continue;
            }
            let event = f.event.clone().unwrap_or_default();
            if f.event.is_none() || !source.is_event(&event) {
                let shown = f.event.as_deref().unwrap_or("undefined");
                return Err(format!(
                    "Fault \"{}\" injects \"{shown}\", which is not an event.",
                    f.id
                ));
            }
            insert_pending(
                &mut initial.pending,
                Pending {
                    seq,
                    time: f.at,
                    event,
                    payload: f.payload.deep_copy(),
                    source: Source::Fault {
                        fault: f.id.clone(),
                    },
                },
            );
            seq += 1;
        }
        let initial = initial.deep_copy();
        let outcome = if initial.pending.is_empty() {
            Outcome::Quiescent
        } else {
            Outcome::Running
        };

        Ok(Simulation {
            source,
            scenario_id,
            behavior_ids,
            transitions,
            fault_ids,
            faults,
            limit: input.scenario.step_limit,
            config: initial.deep_copy(),
            initial,
            initial_seq: seq,
            compiled: RefCell::new(HashMap::new()),
            steps: Vec::new(),
            outcome,
            seq,
            attempts: HashMap::new(),
            delayed_by: HashMap::new(),
        })
    }

    pub fn outcome(&self) -> Outcome {
        self.outcome
    }

    pub fn steps(&self) -> &[TraceStep] {
        &self.steps
    }

    pub fn config(&self) -> &Configuration {
        &self.config
    }

    /// Parse an expression once and keep it.
    fn compile(&self, src: &str) -> Result<Rc<Ast>, String> {
        if let Some(ast) = self.compiled.borrow().get(src) {
            return Ok(Rc::clone(ast));
        }
        let ast = Rc::new(parse_expr(src).map_err(|e| format!("Expression \"{src}\": {e}"))?);
        self.compiled
            .borrow_mut()
            .insert(src.to_string(), Rc::clone(&ast));
        Ok(ast)
    }

    /// Evaluate an expression in one behavior's scope.
    fn eval(
        &self,
        src: &str,
        view: &Configuration,
        bid: &str,
        payload: &Value,
        time: f64,
    ) -> Result<Value, String> {
        let ast = self.compile(src)?;
        eval_expr(&ast, &|path: &[String]| {
            resolve(view, bid, payload, time, path)
        })
        .map_err(|e| e.message)
    }

    /// The value of an effect `to` or payload entry: a string is an expression, anything else
    /// a literal, copied.
    fn value_of(
        &self,
        x: Option<&Value>,
        view: &Configuration,
        bid: &str,
        payload: &Value,
        time: f64,
    ) -> Result<Value, String> {
        match x {
            None => Err("Effect has no value.".to_string()),
            Some(Value::String(src)) => self.eval(src, view, bid, payload, time),
            Some(v) => Ok(v.deep_copy()),
        }
    }

    fn guard_holds(
        &self,
        t: &TransitionInput,
        view: &Configuration,
        bid: &str,
        payload: &Value,
        time: f64,
    ) -> Result<bool, String> {
        let Some(guard) = &t.guard else {
            return Ok(true);
        };
        match self.eval(guard, view, bid, payload, time)? {
            Value::Bool(b) => Ok(b),
            _ => Err(format!(
                "Guard \"{guard}\" of transition \"{}\" did not evaluate to a boolean.",
                t.id
            )),
        }
    }

    /// Ids that explain a step, without repeats: the event, each fired transition with its
    /// behavior and subject, then the faults.
    fn responsible_of(
        &self,
        event_id: &str,
        fired: &[Fired],
        faults: &[FaultRecord],
    ) -> Vec<String> {
        let mut out: Vec<String> = vec![event_id.to_string()];
        let mut add = |id: &str| {
            if !out.iter().any(|x| x == id) {
                out.push(id.to_string());
            }
        };
        for w in fired {
            add(&w.transition);
            add(&w.behavior);
            if let Some(subject) = self
                .source
                .behavior(&w.behavior)
                .and_then(|b| b.subject.as_deref())
            {
                add(subject);
            }
        }
        for f in faults {
            add(&f.fault);
        }
        out
    }

    /// Record a finished step and advance the outcome.
    fn commit(&mut self, mut step: TraceStep, next: Configuration) -> &TraceStep {
        step.config = next.clone();
        self.steps.push(step);
        self.outcome = if next.pending.is_empty() {
            Outcome::Quiescent
        } else if self.steps.len() as f64 >= self.limit {
            Outcome::StepLimit
        } else {
            Outcome::Running
        };
        self.config = next;
        let last = self.steps.len() - 1;
        &self.steps[last]
    }

    /// Execute one event delivery. Returns `None` when the run is not running.
    pub fn step(&mut self) -> Option<&TraceStep> {
        if self.outcome != Outcome::Running {
            return None;
        }
        let cur = std::mem::take(&mut self.config);
        let mut next = cur.deep_copy();
        let head = next.pending.remove(0);
        next.time = head.time;
        let index = self.steps.len();
        let event_id = head.event.clone();
        let attempt = self.attempts.get(&event_id).copied().unwrap_or(0) + 1;
        self.attempts.insert(event_id.clone(), attempt);
        let event = EventRecord {
            id: event_id.clone(),
            payload: head.payload.deep_copy(),
            seq: head.seq,
            source: head.source.clone(),
        };
        let mut faults_out: Vec<FaultRecord> = Vec::new();
        let matches = |f: &FaultInput, kind: &str| {
            f.is_kind(kind)
                && f.event.as_deref() == Some(event_id.as_str())
                && f.occurrence.matches(attempt)
        };
        let record = |kind: StepKind, faults: Vec<FaultRecord>| TraceStep {
            index,
            time: head.time,
            kind,
            event: event.clone(),
            fired: Vec::new(),
            ignored: Vec::new(),
            faults,
            responsible: Vec::new(),
            config: Configuration::default(),
            error: None,
        };

        // Drop faults act first; every matching drop fault is recorded.
        let drops: Vec<&FaultInput> = self
            .faults
            .iter()
            .copied()
            .filter(|f| matches(f, "drop-event"))
            .collect();
        if !drops.is_empty() {
            for f in drops {
                faults_out.push(FaultRecord {
                    fault: f.id.clone(),
                    effect: FaultEffect::Dropped,
                });
            }
            let mut step = record(StepKind::Drop, Vec::new());
            step.responsible = self.responsible_of(&event_id, &[], &faults_out);
            step.faults = faults_out;
            return Some(self.commit(step, next));
        }

        // Delay faults: the first matching one not already applied to this queue entry.
        let already = self.delayed_by.get(&head.seq);
        let delay = self
            .faults
            .iter()
            .copied()
            .find(|f| matches(f, "delay-event") && !already.is_some_and(|s| s.contains(&f.id)));
        if let Some(delay) = delay {
            let new_seq = self.seq;
            self.seq += 1;
            insert_pending(
                &mut next.pending,
                Pending {
                    seq: new_seq,
                    time: head.time + delay.by,
                    event: event_id.clone(),
                    payload: head.payload.deep_copy(),
                    source: head.source.clone(),
                },
            );
            let mut applied = already.cloned().unwrap_or_default();
            applied.insert(delay.id.clone());
            self.delayed_by.insert(new_seq, applied);
            faults_out.push(FaultRecord {
                fault: delay.id.clone(),
                effect: FaultEffect::Delayed,
            });
            let mut step = record(StepKind::Delay, Vec::new());
            step.responsible = self.responsible_of(&event_id, &[], &faults_out);
            step.faults = faults_out;
            return Some(self.commit(step, next));
        }

        // Delivery.
        if let Source::Fault { fault } = &head.source {
            faults_out.push(FaultRecord {
                fault: fault.clone(),
                effect: FaultEffect::Injected,
            });
        }
        match self.deliver(&cur, &mut next, &head, &mut faults_out) {
            Ok((fired, ignored)) => {
                let mut step = record(StepKind::Deliver, Vec::new());
                step.responsible = self.responsible_of(&event_id, &fired, &faults_out);
                step.fired = fired;
                step.ignored = ignored;
                step.faults = faults_out;
                Some(self.commit(step, next))
            }
            Err(message) => {
                // The failing step is not committed: the configuration stays as it was before it.
                let mut step = record(StepKind::Deliver, Vec::new());
                step.responsible = vec![event_id.clone()];
                step.config = cur.clone();
                step.error = Some(message);
                self.steps.push(step);
                self.config = cur;
                self.outcome = Outcome::Error;
                self.steps.last()
            }
        }
    }

    /// Both phases of a delivery. On error nothing of `next` is kept by the caller.
    fn deliver(
        &mut self,
        cur: &Configuration,
        next: &mut Configuration,
        head: &Pending,
        faults_out: &mut Vec<FaultRecord>,
    ) -> Result<(Vec<Fired>, Vec<Ignored>), String> {
        let event_id = head.event.as_str();
        let payload = &head.payload;
        let time = head.time;

        // Phase 1: choose the transition of each behavior, reading the configuration as it was
        // at the start of the step.
        let mut winners: Vec<(String, &'a TransitionInput)> = Vec::new();
        let mut ignored: Vec<Ignored> = Vec::new();
        for (bi, bid) in self.behavior_ids.iter().enumerate() {
            let state = cur.machine(bid).map(|m| m.state.as_str());
            let mut considered: Vec<String> = Vec::new();
            let mut winner: Option<(&'a TransitionInput, Vec<&'a FaultInput>)> = None;
            let mut disabled_would_fire = false;
            let mut guard_false = false;
            for &t in &self.transitions[bi] {
                if Some(t.from.as_str()) != state || t.on != event_id {
                    continue;
                }
                let targets = |kind: &str| -> Vec<&'a FaultInput> {
                    self.faults
                        .iter()
                        .copied()
                        .filter(|f| {
                            f.is_kind(kind) && f.transition.as_deref() == Some(t.id.as_str())
                        })
                        .collect()
                };
                let enablers = targets("enable-transition");
                if t.fault_only && enablers.is_empty() {
                    continue;
                }
                considered.push(t.id.clone());
                let disablers = targets("disable-transition");
                if !self.guard_holds(t, cur, bid, payload, time)? {
                    guard_false = true;
                    continue;
                }
                if !disablers.is_empty() {
                    disabled_would_fire = true;
                    for d in disablers {
                        faults_out.push(FaultRecord {
                            fault: d.id.clone(),
                            effect: FaultEffect::Disabled,
                        });
                    }
                    continue;
                }
                winner = Some((t, if t.fault_only { enablers } else { Vec::new() }));
                break;
            }
            match winner {
                Some((t, enablers)) => {
                    for e in enablers {
                        faults_out.push(FaultRecord {
                            fault: e.id.clone(),
                            effect: FaultEffect::Enabled,
                        });
                    }
                    winners.push((bid.clone(), t));
                }
                None => ignored.push(Ignored {
                    behavior: bid.clone(),
                    reason: if disabled_would_fire {
                        IgnoredReason::Disabled
                    } else if guard_false {
                        IgnoredReason::GuardFalse
                    } else {
                        IgnoredReason::NoTransition
                    },
                    considered,
                }),
            }
        }

        // Phase 2: effects, behavior by behavior, in scenario order, on the next configuration.
        let mut fired: Vec<Fired> = Vec::new();
        for (bid, t) in winners {
            let bid = bid.as_str();
            let mut rec = Fired {
                behavior: bid.to_string(),
                transition: t.id.clone(),
                from: t.from.clone(),
                to: t.to.clone(),
                guard: t.guard.clone(),
                sets: Vec::new(),
                emitted: Vec::new(),
            };
            for fx in &t.effects {
                match fx {
                    Effect::Set { variable, to } => {
                        let has = next
                            .machine(bid)
                            .is_some_and(|m| m.vars.contains_key(variable));
                        if !has {
                            return Err(format!(
                                "Effect sets \"{variable}\", which is not a variable of \"{bid}\"."
                            ));
                        }
                        let value = self.value_of(to.as_ref(), next, bid, payload, time)?;
                        let machine = next
                            .machine_mut(bid)
                            .ok_or_else(|| format!("No machine for \"{bid}\"."))?;
                        let slot = machine
                            .vars
                            .get_mut(variable)
                            .ok_or_else(|| format!("No variable \"{variable}\"."))?;
                        let before = std::mem::replace(slot, value.clone());
                        rec.sets.push(SetRecord {
                            variable: variable.clone(),
                            before: before.deep_copy(),
                            after: value.deep_copy(),
                        });
                    }
                    Effect::Emit {
                        event,
                        after,
                        payload: entries,
                    } => {
                        if !self.source.is_event(event) {
                            return Err(format!(
                                "Effect emits \"{event}\", which is not an event."
                            ));
                        }
                        let at = next.time + after;
                        let mut emit_payload = JsObject::new();
                        for (k, v) in entries.iter() {
                            let value = self.value_of(Some(v), next, bid, payload, time)?;
                            emit_payload.insert(k.clone(), value);
                        }
                        let s = self.seq;
                        self.seq += 1;
                        let emit_payload = Value::object(emit_payload);
                        insert_pending(
                            &mut next.pending,
                            Pending {
                                seq: s,
                                time: at,
                                event: event.clone(),
                                payload: emit_payload.clone(),
                                source: Source::Transition {
                                    transition: t.id.clone(),
                                    behavior: bid.to_string(),
                                },
                            },
                        );
                        rec.emitted.push(EmitRecord {
                            event: event.clone(),
                            time: at,
                            seq: s,
                            payload: emit_payload.deep_copy(),
                        });
                    }
                    Effect::Malformed => {
                        return Err(format!("Malformed effect in transition \"{}\".", t.id));
                    }
                }
            }
            if let Some(m) = next.machine_mut(bid) {
                m.state = t.to.clone();
            }
            fired.push(rec);
        }
        Ok((fired, ignored))
    }

    /// Step until the run is no longer running.
    pub fn run(&mut self) -> Trace {
        while self.outcome == Outcome::Running {
            self.step();
        }
        self.trace()
    }

    /// Return to the initial configuration with no steps.
    pub fn reset(&mut self) {
        self.config = self.initial.deep_copy();
        self.steps.clear();
        self.outcome = if self.initial.pending.is_empty() {
            Outcome::Quiescent
        } else {
            Outcome::Running
        };
        self.attempts.clear();
        self.delayed_by.clear();
        self.seq = self.initial_seq;
    }

    pub fn trace(&self) -> Trace {
        Trace {
            scenario_id: self.scenario_id.clone(),
            faults: self.fault_ids.clone(),
            initial: self.initial.deep_copy(),
            steps: self.steps.clone(),
            outcome: self.outcome,
            final_config: self.config.deep_copy(),
        }
    }
}

/// Create a simulation of an input and run it to completion.
pub fn run(input: &SimInput) -> Result<Trace, String> {
    Ok(Simulation::new(input)?.run())
}
