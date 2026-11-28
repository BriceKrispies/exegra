import Exegra.Model
import Exegra.Lower.Families

/-!
# The engine input of a scenario

`Exegra.Lower.engineInput m sc faults`: the version-2 engine input (format `exegra-sim-input`) of
scenario `sc` of the model `m`, formerly computed in JavaScript by `src/core/sim-input.js` and
`src/core/pools.js` (WG-5683). It reads the entities of the model and nothing else, and refuses,
with the message the JavaScript lowering gave, a scenario, behavior, event, fault, workload or quota
pool that does not exist and a malformed unit, rate, size, bandwidth or distribution.

A scenario that uses a construct only the timed form has (workloads, a seed or horizon, instances,
resource, timer or link effects, a duplicate, lose or retry fault) counts time in whole base units
of its `timeUnit` (default `us`), with durations, rates and distributions lowered to integers and
tables (`Exegra.Lower.Dist`); every other scenario counts time in logical ticks, every number as the
scenario gives it (docs/simulation.md, "Engine input and trace format").

The input is built as the JSON value the engine decodes; `jsonNormal` gives it the form a JSON round
trip gives (no `undefined` member, `undefined` items as `null`).
-/

namespace Exegra.Lower

open Exegra
open Exegra.Model (Model Entity)
open Exegra.Lower.Dist (mem hasMem itemsOf isArr numV jsText decimalOf? lowerDistribution unitExponentialTable)

abbrev L := Except String

/-! ## The model as the lowering reads it -/

/-- The entity with an id: the last one declared, as the JavaScript model's map holds it. -/
def ent? (m : Model) (id : String) : Option Entity := m.entities.reverse.find? (·.id == id)

/-- The entity a JSON value names, if it is a string. -/
def entV? (m : Model) : Value → Option Entity
  | .str id => ent? m id
  | _ => none

/-- The entities of a kind, in declaration order. -/
def byKind (m : Model) (k : String) : List Entity := m.entities.filter (·.kind == k)

def ownedBy (m : Model) (k owner : String) : List Entity :=
  m.entities.filter fun e => e.kind == k && e.owner == some owner

def strOf? : Value → Option String
  | .str s => some s
  | _ => none

/-- `x ?? d`. -/
def orElse (x d : Value) : Value := if x.isNullish then d else x

def isObj : Value → Bool
  | .obj .. => true
  | _ => false

/-- JavaScript truthiness of a JSON value. -/
def truthy : Value → Bool
  | .undef | .null => false
  | .bool b => b
  | .num x => !(x == 0)
  | .str s => !s.isEmpty
  | _ => true

/-- `Number.isInteger(v)`. -/
def isInteger : Value → Bool
  | .num x => Num.isInteger x
  | _ => false

def intOf? : Value → Option Int
  | .num x => Num.safeInteger? x
  | _ => none

/-- An object value with its `undefined` members left out. -/
def obj (fs : List (String × Value)) : Value := .obj 0 (fs.filter fun (_, v) => !(v matches .undef))

/-- The form a JSON round trip gives a value: no `undefined` member, `undefined` items as `null`. -/
partial def jsonNormal : Value → Value
  | .obj _ fs => .obj 0 ((fs.filter fun (_, v) => !(v matches .undef)).map fun (k, v) => (k, jsonNormal v))
  | .arr _ xs => .arr 0 (xs.map fun v => match v with
    | .undef => .null
    | v => jsonNormal v)
  | v => v

/-- `{...o, k: v}` (a present key keeps its place). -/
def setMem (o : Value) (k : String) (v : Value) : Value :=
  match o with
  | .obj n fs => .obj n (objInsert fs k v)
  | _ => o

def delMem (o : Value) (k : String) : Value :=
  match o with
  | .obj n fs => .obj n (fs.filter (·.1 != k))
  | _ => o

/-- Distinct elements, first occurrence first (`[...new Set(xs)]`, for JSON scalars). -/
def dedupV (xs : List Value) : List Value :=
  xs.foldl (fun acc x => if acc.any (fun y => Dist.jsText y == Dist.jsText x && sameKind y x) then acc else acc ++ [x]) []
where
  sameKind : Value → Value → Bool
    | .str _, .str _ | .num _, .num _ | .bool _, .bool _ | .null, .null | .undef, .undef => true
    | _, _ => false

/-! ## Units -/

def isSpace (c : Char) : Bool := c.isWhitespace

/-- `/^(\S+)\s*<sep>\s*(<units>)$/` on `t`, with the backtracking of a JavaScript regular
expression: the longest prefix without white space after which the rest (white space, the
separator if any, white space) is one of the units. Returns the prefix and the unit. -/
def matchUnit (t : String) (units : List String) (sep : Option Char) : Option (String × String) :=
  let cs := t.toList
  let n := cs.length
  let try_ (k : Nat) : Option (String × String) :=
    let pre := cs.take k
    if pre.isEmpty || pre.any isSpace then none else
    let rest := (cs.drop k).dropWhile isSpace
    let rest := match sep with
      | none => some rest
      | some c => match rest with
        | c' :: r => if c' == c then some (r.dropWhile isSpace) else none
        | [] => none
    match rest with
    | none => none
    | some r =>
      let u := String.ofList r
      if units.contains u then some (String.ofList pre, u) else none
  ((List.range n).reverse.map (· + 1)).findSome? try_

def trimJs (s : String) : String := s.trimAscii.toString

/-- `decimal(s, what)`: an exact non-negative decimal as `(num, den)`. -/
def decimal (s what : String) : L (Int × Int) :=
  match decimalOf? s with
  | some p => .ok p
  | none => .error s!"{what}: \"{s}\" is not an exact non-negative decimal."

def nsPer : String → Int
  | "ns" => 1 | "us" => 1000 | "ms" => 1000000 | "s" => 1000000000
  | "min" => 60000000000 | "h" => 3600000000000 | _ => 1

def durationUnits : List String := ["ns", "us", "ms", "s", "min", "h"]

/-- Base units per second of a scenario time unit (`none` for `tick`); `unknown` for any other. -/
def perSecond? : String → Option (Option Int)
  | "tick" => some none | "s" => some (some 1) | "ms" => some (some 1000)
  | "us" => some (some 1000000) | "ns" => some (some 1000000000)
  | _ => none

/-- A duration `"<decimal> <unit>"` in whole base units of `unit`; a bare non-negative integer is
already in base units. -/
def durationIn (v : Value) (unit what : String) : L Int := do
  if isInteger v then
    if let some n := intOf? v then
      if n ≥ 0 then return n
  let m := match v with
    | .str s => matchUnit (trimJs s) durationUnits none
    | _ => none
  let some (num, u) := m
    | throw s!"{what}: \"{jsText v}\" is not a duration (\"<decimal> <unit>\", unit ns, us, ms, s, min or h)."
  let (n, d) ← decimal num what
  if unit == "tick" then throw s!"{what}: unit tick has no duration; \"{jsText v}\" needs a time unit."
  let a := n * nsPer u
  let b := d * nsPer unit
  if a % b != 0 then throw s!"{what}: \"{jsText v}\" is not a whole number of {unit}."
  let x := a / b
  if x ≥ 2 ^ 53 then throw s!"{what}: \"{jsText v}\" is 2^53 base units or more."
  return x

def ratePer : String → Int
  | "min" => 60 | "h" => 3600 | _ => 1

/-- A rate `"<decimal>/<s|min|h>"` as an exact `{num, den}` per second (an object with `num` is
taken as it is). -/
def rateOf (v : Value) (what : String) : L Value := do
  if isObj v && hasMem v "num" then return v
  let m := match v with
    | .str s => matchUnit (trimJs s) ["s", "min", "h"] (some '/')
    | _ => none
  let some (num, u) := m
    | throw s!"{what}: \"{jsText v}\" is not a rate (\"<decimal>/s\", \"/min\" or \"/h\")."
  let (n, d) ← decimal num what
  let den := d * ratePer u
  let g := Int.ofNat (Int.gcd n den)
  let g := if g == 0 then 1 else g
  return obj [("num", numV (n / g)), ("den", numV (den / g))]

def sizeUnits : List String := ["B", "kB", "MB", "GB", "KiB", "MiB", "GiB"]

def bytesPer : String → Int
  | "kB" => 1000 | "MB" => 1000000 | "GB" => 1000000000
  | "KiB" => 1024 | "MiB" => 1048576 | "GiB" => 1073741824 | _ => 1

/-- A size `"<decimal> <unit>"` in bytes (a number as it is). -/
def sizeOf (v : Value) (what : String) : L Value := do
  if v matches .num _ then return v
  let m := match v with
    | .str s => matchUnit (trimJs s) sizeUnits none
    | _ => none
  let some (num, u) := m | throw s!"{what}: \"{jsText v}\" is not a size."
  let (n, d) ← decimal num what
  let x := n * bytesPer u
  if x % d != 0 then throw s!"{what}: \"{jsText v}\" is not a whole number of bytes."
  return numV (x / d)

def bandwidthUnits : List String :=
  ["bit/s", "kbit/s", "Mbit/s", "Gbit/s", "B/s", "kB/s", "MB/s", "GB/s"]

def bandwidthPer : String → Int × Int
  | "bit/s" => (1, 8) | "kbit/s" => (1000, 8) | "Mbit/s" => (1000000, 8) | "Gbit/s" => (1000000000, 8)
  | "kB/s" => (1000, 1) | "MB/s" => (1000000, 1) | "GB/s" => (1000000000, 1) | _ => (1, 1)

/-- A bandwidth `"<decimal> <unit>"` in whole bytes per second, rounded down (a number as it is). -/
def bandwidthOf (v : Value) (what : String) : L Value := do
  if v matches .num _ then return v
  let m := match v with
    | .str s => matchUnit (trimJs s) bandwidthUnits none
    | _ => none
  let some (num, u) := m | throw s!"{what}: \"{jsText v}\" is not a bandwidth."
  let (n, d) ← decimal num what
  let (a, b) := bandwidthPer u
  return numV ((n * a) / (d * b))

/-- A distribution as a specification writes it, lowered to the engine's integer form: a duration
(fixed), `{constant}`, `{uniform}`, `{exponential}`, `{lognormal}`, `{empirical}` with durations in
any unit, or an engine distribution (`{kind}`) as it is. `none` for an absent one. -/
def lowerSpecDistribution (d : Value) (unit what : String) : L (Option Value) := do
  if d.isNullish then return none
  match d with
  | .num _ | .str _ => return some (obj [("kind", .str "fixed"), ("value", numV (← durationIn d unit what))])
  | .obj .. =>
    if hasMem d "kind" then return some d
    let dur (x : Value) : L Value := do pure (.str (toString (← durationIn x unit what)))
    if hasMem d "constant" then
      return some (← lowerDistribution (obj [("constant", ← dur (mem d "constant"))]) what)
    if hasMem d "uniform" then
      let u := mem d "uniform"
      let lo ← dur (mem u "lo")
      let hi ← dur (mem u "hi")
      return some (← lowerDistribution (obj [("uniform", obj [("lo", lo), ("hi", hi)])]) what)
    if hasMem d "exponential" then
      return some (← lowerDistribution (obj [("exponential", obj [("mean", ← dur (mem (mem d "exponential") "mean"))])]) what)
    if hasMem d "lognormal" then
      let l := mem d "lognormal"
      let median ← dur (mem l "median")
      let second ← match mem l "p99" with
        | .undef => pure ("sigma", mem l "sigma")
        | p => do pure ("p99", ← dur p)
      return some (← lowerDistribution (obj [("lognormal", obj [("median", median), second])]) what)
    if hasMem d "empirical" then
      let e := mem d "empirical"
      let inner ← if truthy (mem e "samples") then do
          pure (obj [("samples", .arr 0 (← (itemsOf (mem e "samples")).mapM dur))])
        else do
          let qs ← (itemsOf (mem e "quantiles")).mapM fun q => do
            let p := match q with | .arr _ (p :: _) => p | _ => .undef
            let x := match q with | .arr _ (_ :: x :: _) => x | _ => .undef
            pure (.arr 0 [p, ← dur x])
          pure (obj [("quantiles", .arr 0 qs)])
      return some (← lowerDistribution (obj [("empirical", inner)]) what)
    throw s!"{what}: unknown distribution."
  | _ => return some d

/-! ## Declared types -/

def intTypes : List String := ["u8", "u16", "u32", "u64", "i32", "i64"]

/-- `unsharedText`: a type name without its `shared<...>` wrappers. -/
partial def unsharedText (name : String) : String :=
  let t := trimJs name
  if t.startsWith "shared<" && t.endsWith ">" && t.length > 8 then
    unsharedText ((t.drop 7).dropEnd 1).toString
  else t

/-- The type a declared type name stands for in evaluation: an integer type name, `option`, or
the name itself; a timestamp is an `i64`, a duration a `u64`, a declared id or scalar type its
representation. -/
def evalTypeOf (m : Model) : Nat → Value → Option String
  | depth, .str name =>
    let t := unsharedText name
    if intTypes.contains t then some t
    else if t == "timestamp" then some "i64"
    else if t == "duration" then some "u64"
    else if t.startsWith "option" && ((t.drop 6).toString.trimAsciiStart.toString.startsWith "<") then some "option"
    else match depth, ent? m t with
      | depth + 1, some decl =>
        if decl.kind == "type" then
          let k := mem decl.data "kind"
          let repr := mem decl.data "repr"
          if (k matches .str "id" || k matches .str "scalar") && (repr matches .str _) then
            evalTypeOf m depth repr
          else some t
        else some t
      | _, _ => some t
  | _, _ => none

/-- The declared types of the references an implementation-level behavior's expressions read
(`types` of a behavior in the engine input): `time`, each variable with a `repr`, and
`event.<field>` of the events it receives; a field two events type differently is left out. -/
def behaviorTypes (m : Model) (bid : String) : List (String × String) := Id.run do
  let some b := ent? m bid | return []
  if b.kind != "behavior" || !(mem b.data "level" matches .str "implementation") then return []
  let ev := evalTypeOf m 8
  let mut out : List (String × String) := [("time", "i64")]
  let put (o : List (String × String)) (k v : String) : List (String × String) :=
    if o.any (·.1 == k) then o.map fun (k', v') => if k' == k then (k', v) else (k', v') else o ++ [(k, v)]
  for v in itemsOf (mem b.data "variables") do
    if let (.str name, some t) := (mem v "name", ev (mem v "repr")) then out := put out name t
  let mut conflicting : List String := []
  let received := dedupV ((ownedBy m "transition" bid).map fun t => mem t.data "on")
  for eid in received do
    let payload := match entV? m eid with
      | some e => if e.kind == "event" then itemsOf (mem e.data "payload") else []
      | none => []
    for f in payload do
      let .str name := mem f "name" | continue
      let t := if mem f "optional" matches .bool true then some "option" else ev (mem f "type")
      let some t := t | continue
      let key := s!"event.{name}"
      match out.find? (·.1 == key) with
      | some (_, t') => if t' != t then conflicting := conflicting ++ [key] else out := put out key t
      | none => out := put out key t
  return out.filter fun (k, _) => !conflicting.contains k

/-! ## Quota pools (formerly `src/core/pools.js`) -/

def poolVariables : List String :=
  ["usage", "day", "overDays", "underDays", "throttledOn", "burstSetOn", "burstFrom", "admitted", "refused"]

def posInt (v : Value) : Bool := isInteger v && match v with | .num x => x ≥ 1 | _ => false

/-- The number of members the model of a pool runs: `modelMembers` when 1 to 4, else 2. -/
def modelMembers (pool : Entity) : Nat :=
  let n := mem pool.data "modelMembers"
  match intOf? n with
  | some k => if posInt n && k ≤ 4 then k.toNat else 2
  | none => 2

def limitName (s : String) : Bool :=
  match s.toList with
  | c :: cs => c.isLower && c.isAlpha && cs.all fun d => (d.isLower && d.isAlpha) || d.isDigit
  | [] => false

/-- The pooled limits of a pool that have a usable name. -/
def limitsOf (pool : Entity) : List Value :=
  (itemsOf (mem pool.data "limits")).filter fun l => isObj l && match mem l "name" with
    | .str s => limitName s
    | _ => false

def positiveNum? : Value → Option Rat
  | .num x => if x > 0 then some x else none
  | _ => none

/-- What one member contributes to a pooled limit (its fair share). -/
def contributionOf (m : Model) (limit : Value) : Option Rat :=
  match positiveNum? (mem limit "perMember") with
  | some x => some x
  | none => match entV? m (mem limit "quota") with
    | some q => if q.kind == "quota" then positiveNum? (mem q.data "limit") else none
    | none => none

/-- The event that uses a pooled limit: its own, or the event its quota counts. -/
def usageEventOf (m : Model) (limit : Value) : Option String :=
  match mem limit "usage" with
  | .str s => some s
  | _ => match entV? m (mem limit "quota") with
    | some q => if q.kind == "quota" then strOf? (mem q.data "event") else none
    | none => none

def poolMachineId (poolId limit : String) (k : Nat) : String := s!"{poolId}-{limit}-m{k}"

def jsNum (x : Rat) : String := Num.jsNumberToString x

/-- The machines a pool runs as, in the engine input's behavior form, one per pooled limit and
modelled member (docs/model-and-format.md, "Pooled quotas"). -/
def poolMachines (m : Model) (poolId : String) : L (List Value) := do
  let some pool := ent? m poolId | throw s!"\"{poolId}\" is not a quota pool in this model."
  if pool.kind != "quotaPool" then throw s!"\"{poolId}\" is not a quota pool in this model."
  let d := pool.data
  let n := modelMembers pool
  let bigN := mem (mem d "overShare") "consecutive"
  let release := mem (mem d "throttle") "release"
  let to := mem (mem d "throttle") "to"
  let windowEnd := mem d "windowEnd"
  if !posInt bigN then throw s!"Quota pool \"{poolId}\" has no over-share window count."
  if !(posInt release || release matches .str "never") then
    throw s!"Quota pool \"{poolId}\" does not say when a throttle is released."
  let ex := if isObj (mem d "exemption") && (mem (mem d "exemption") "event" matches .str _) then some (mem d "exemption") else none
  let offset := match ex with
    | some e => (mem e "effective" matches .str "next-window")
    | none => false
  let subject := match mem d "heldBy" with
    | .str s => s
    | _ => poolId
  let mut out : List Value := []
  for l in limitsOf pool do
    let name := (strOf? (mem l "name")).getD ""
    let some share := contributionOf m l
      | throw s!"Pooled limit \"{name}\" of \"{poolId}\" states no contribution."
    let some usageEvent := usageEventOf m l
      | throw s!"Pooled limit \"{name}\" of \"{poolId}\" has no usage event."
    let capacity := share * (n : Rat)
    let ids := (List.range n).map fun i => poolMachineId poolId name (i + 1)
    let total := "(" ++ " + ".intercalate (ids.map (· ++ ".usage")) ++ ")"
    let rate := !(mem l "kind" matches .str "level")
    for k in (List.range n).map (· + 1) do
      let id := ids.getD (k - 1) ""
      let me := s!"event.member == 'm{k}'"
      let over := s!"usage > {jsNum share}"
      let exempt := if ex.isSome then "(burstFrom >= 0 && burstFrom <= day)" else "false"
      let set (v : String) (value : Value) : Value := obj [("set", .str v), ("to", value)]
      let e (s : String) : Value := .str s
      let tail := (if rate then [set "usage" (numV 0)] else []) ++ [set "day" (e "day + 1")]
      let t (nm from_ toState : String) (on : Value) (guard : Option String) (effects : List Value) : Value :=
        obj [("id", .str s!"{id}-{nm}"), ("from", .str from_), ("to", .str toState), ("on", on),
             ("guard", match guard with | some g => .str g | none => .null),
             ("effects", .arr 0 effects), ("faultOnly", .bool false)]
      let ue : Value := .str usageEvent
      let admitFx := [set "usage" (e "usage + event.amount"), set "admitted" (e "admitted + 1")]
      let refuse := [set "refused" (e "refused + 1")]
      let cap := jsNum capacity
      let sh := jsNum share
      let mut transitions : List Value := [
        t "use" "normal" "normal" ue (some s!"{me} && (event.amount <= 0 || {total} + event.amount <= {cap})") admitFx,
        t "refuse" "normal" "normal" ue (some me) refuse,
        t "use-throttled" "throttled" "throttled" ue
          (some (if to matches .str "refuse" then s!"{me} && event.amount <= 0"
            else s!"{me} && (event.amount <= 0 || (usage + event.amount <= {sh} && {total} + event.amount <= {cap}))")) admitFx,
        t "refuse-throttled" "throttled" "throttled" ue (some me) refuse,
        t "throttle" "normal" "throttled" windowEnd (some s!"{over} && overDays + 1 >= {jsText bigN} && !{exempt}")
          ([set "overDays" (e "overDays + 1"), set "underDays" (numV 0), set "throttledOn" (e "day")] ++ tail),
        t "over" "normal" "normal" windowEnd (some over) ([set "overDays" (e "overDays + 1"), set "underDays" (numV 0)] ++ tail),
        t "under" "normal" "normal" windowEnd none ([set "overDays" (numV 0), set "underDays" (e "underDays + 1")] ++ tail)]
      if posInt release then
        transitions := transitions ++ [t "release" "throttled" "normal" windowEnd
          (some s!"!({over}) && underDays + 1 >= {jsText release}")
          ([set "overDays" (numV 0), set "underDays" (numV 0), set "throttledOn" (numV (-1))] ++ tail)]
      transitions := transitions ++ [
        t "over-throttled" "throttled" "throttled" windowEnd (some over) ([set "overDays" (e "overDays + 1"), set "underDays" (numV 0)] ++ tail),
        t "under-throttled" "throttled" "throttled" windowEnd none ([set "overDays" (numV 0), set "underDays" (e "underDays + 1")] ++ tail)]
      if let some exv := ex then
        let mark := [set "burstSetOn" (e "day"), set "burstFrom" (e (if offset then "day + 1" else "day"))]
        let xe := mem exv "event"
        transitions := transitions ++ [t "exempt" "normal" "normal" xe (some s!"{me} && burstSetOn < 0") mark]
        transitions := transitions ++ [if mem exv "retroactive" matches .bool true
          then t "exempt-lifts" "throttled" "normal" xe (some s!"{me} && burstSetOn < 0")
            (mark ++ [set "overDays" (numV 0), set "throttledOn" (numV (-1))])
          else t "exempt-throttled" "throttled" "throttled" xe (some s!"{me} && burstSetOn < 0") mark]
      out := out ++ [obj [
        ("id", .str id), ("subject", .str subject), ("initial", .str "normal"),
        ("variables", .arr 0 (poolVariables.map fun nm =>
          obj [("name", .str nm), ("initial", numV (if ["throttledOn", "burstSetOn", "burstFrom"].contains nm then -1 else 0))])),
        ("states", .arr 0 [.str "normal", .str "throttled"]),
        ("transitions", .arr 0 transitions)]]
  return out

/-! ## The retry backoff (formerly `retryDelay` of `src/core/fault-model.js`) -/

/-- The delay after which an at-least-once message is delivered when its first `attempts`
dispatches failed: the sum of the waits, the k-th being `min(first · factor^(k-1), max)`, under
`system.generation.retry` over the runtime's default (1 s, factor 2, at most 300 s). -/
def retryDelay (m : Model) (attempts : Value) (unit : String) : L Int := do
  let sys := (byKind m "system").head?
  let r := match sys with
    | some s => mem (mem s.data "generation") "retry"
    | none => .undef
  let o := if isObj r then r else .obj 0 []
  let firstV := orElse (mem o "first") (.str "1 s")
  let maxV := orElse (mem o "max") (.str "300 s")
  let factor : Int := match intOf? (mem o "factor") with
    | some f => if isInteger (mem o "factor") && f ≥ 1 then f else 2
    | none => 2
  let first ← durationIn firstV unit "system.generation.retry.first"
  let mx ← durationIn maxV unit "system.generation.retry.max"
  let att : Nat := match attempts with
    | .num x => if x ≥ 1 then x.floor.toNat else 0
    | _ => 0
  let mut wait := first
  let mut total : Int := 0
  for k in (List.range att).map (· + 1) do
    if k > 1 then wait := min (wait * factor) mx
    total := total + min wait mx
  return total

/-! ## The engine input -/

def effectKeys : List String := ["set", "to", "emit", "after", "payload"]
def faultKeys : List String := ["kind", "event", "transition", "occurrence", "by", "at", "payload"]
def format2Faults : List String := ["duplicate-event", "lose-event", "retry-event"]
def v2Effects : List String := ["use", "acquire", "release", "timer", "cancel", "via"]

/-- An effect of the tick-counted input: the fields the engine reads (an emit's `to` names a
receiver outside the model and is left out). -/
def inputEffect (fx : Value) : Value :=
  match fx with
  | .obj _ fs => obj (effectKeys.filterMap fun k =>
      if k == "to" && objHas fs "emit" then none else (objGet? fs k).map (k, ·))
  | v => v

/-- Whether a scenario needs the timed input: it names workloads, a seed or a horizon, one of its
faults is a duplicate, lose or retry fault, or one of its behaviors has instances or an effect only
the timed input has. -/
def needsTimedInput (m : Model) (sdata : Value) : Bool :=
  (isArr (mem sdata "workloads") && !(itemsOf (mem sdata "workloads")).isEmpty) ||
  hasMem sdata "seed" || hasMem sdata "horizon" ||
  (itemsOf (mem sdata "faults")).any (fun fid => match entV? m fid with
    | some f => match mem f.data "kind" with
      | .str k => format2Faults.contains k
      | _ => false
    | none => false) ||
  (itemsOf (mem sdata "behaviors")).any fun bid =>
    (match entV? m bid with
     | some b => truthy (mem b.data "instances")
     | none => false) ||
    (match bid with
     | .str bid => (ownedBy m "transition" bid).any fun t =>
        (itemsOf (mem t.data "effects")).any fun fx => isObj fx && v2Effects.any (hasMem fx ·)
     | _ => false)

/-- An effect of the timed input: distributions lowered, sizes in bytes, notes left out. -/
def effectV2 (fx : Value) (unit what : String) : L Value := do
  if !isObj fx then return fx
  let mut out := fx
  for k in ["source", "note", "description"] do out := delMem out k
  let isEmit := hasMem out "emit"
  let isTimer := hasMem out "timer"
  if isEmit && !isTimer then out := delMem out "to"
  let low (k : String) (v : Value) (o : Value) : L Value := do
    pure (setMem o k ((← lowerSpecDistribution v unit s!"{what}.{k}").getD .undef))
  if hasMem out "demand" then out ← low "demand" (mem out "demand") out
  if isEmit && !isTimer && hasMem out "after" then out ← low "after" (mem out "after") out
  if isTimer && hasMem out "after" then
    let a := mem out "after"
    out ← low "after" (if isObj a && hasMem a "expr" then mem a "simulate" else a) out
  if hasMem out "size" then
    match mem out "size" with
    | .obj .. | .arr .. | .null => out ← low "size" (mem out "size") out
    | .str s =>
      if (matchUnit s sizeUnits none).isSome then out := setMem out "size" (← sizeOf (.str s) s!"{what}.size")
    | _ => pure ()
  if hasMem out "to" then
    let to := mem out "to"
    if isObj to && hasMem to "sample" then
      out := setMem out "to" (obj [("sample", (← lowerSpecDistribution (mem to "sample") unit s!"{what}.to.sample").getD .undef)])
  return out

/-- A USL parameter as `[num, den]` from an exact decimal or a pair. -/
def ratPair (v : Value) : L Value := do
  if isArr v then return v
  let (n, d) ← decimal (jsText v) "demandFactor"
  let g := Int.ofNat (Int.gcd n d)
  let g := if g == 0 then 1 else g
  return .arr 0 [numV (n / g), numV (d / g)]

/-- The engine's view of `instances` (`storedIn` is implementation-level and declarative). -/
def engineInstances (inst : Value) : Value := delMem inst "storedIn"

def nullOr (v : Value) : Value := orElse v .null

/-- The timed (version-2) form of an input whose shared fields `v1` are given. -/
def engineInputV2 (m : Model) (sc : String) (sdata : Value) (v1behaviors : List Value)
    (v1faults : List Value) (scenarioFields : List (String × Value)) (events : List Value)
    (steps : List Value) : L Value := do
  let unit := match mem sdata "timeUnit" with
    | .str u => u
    | _ => "us"
  let some ps := perSecond? unit | throw s!"Scenario \"{sc}\": unknown time unit \"{unit}\"."
  let dur (v : Value) (what : String) : L Int := durationIn v unit what
  let opt (v : Value) (what : String) : L Value := do
    if v.isNullish then pure .null else pure (numV (← dur v what))
  let behaviors ← v1behaviors.mapM fun b => do
    let bid := (strOf? (mem b "id")).getD ""
    let some e := ent? m bid
      | throw s!"Cannot read properties of undefined (reading 'data')"
    let b := if truthy (mem e.data "instances") then setMem b "instances" (engineInstances (mem e.data "instances")) else b
    let ts ← (itemsOf (mem b "transitions")).mapM fun t => do
      let tid := (strOf? (mem t "id")).getD ""
      let fxs := match ent? m tid with
        | some te => itemsOf (mem te.data "effects")
        | none => []
      let effs ← fxs.zipIdx.mapM fun (fx, k) => effectV2 fx unit s!"{tid}.effects[{k}]"
      pure (setMem t "effects" (.arr 0 effs))
    pure (setMem b "transitions" (.arr 0 ts))
  let horizon ← opt (mem sdata "horizon") s!"{sc}.horizon"
  let resources ← (byKind m "resource").mapM fun r => do
    let d := r.data
    let df := mem d "demandFactor"
    let usl := mem df "usl"
    let demandFactor ← if truthy usl then do
        pure (obj [("usl", obj [("alpha", ← ratPair (mem usl "alpha")), ("beta", ← ratPair (mem usl "beta"))])])
      else pure (nullOr df)
    let classes ← (itemsOf (mem d "classes")).mapM fun c => do
      pure (obj [("id", mem c "id"), ("priority", orElse (mem c "priority") (numV 0)),
        ("reserved", orElse (mem c "reserved") (numV 0)), ("limit", nullOr (mem c "limit")),
        ("queueBound", nullOr (mem c "queueBound")),
        ("maxWait", ← opt (mem c "maxWait") s!"{r.id}.{jsText (mem c "id")}.maxWait")])
    pure (obj [("id", .str r.id), ("kind", orElse (mem d "kind") (.str "pool")), ("capacity", mem d "capacity"),
      ("discipline", orElse (mem d "discipline") (.str "fifo")), ("queueBound", nullOr (mem d "queueBound")),
      ("overflow", orElse (mem d "overflow") (.str "refuse")), ("demandFactor", demandFactor),
      ("classes", .arr 0 classes)])
  let links ← (byKind m "link").mapM fun l => do
    let d := l.data
    let latency ← lowerSpecDistribution (mem d "latency") unit s!"{l.id}.latency"
    let bandwidth ← match mem d "bandwidth" with
      | .undef => pure .null
      | bw => bandwidthOf bw s!"{l.id}.bandwidth"
    pure (obj [("id", .str l.id), ("from", mem d "from"), ("to", mem d "to"),
      ("latency", latency.getD (obj [("kind", .str "fixed"), ("value", numV 0)])),
      ("bandwidth", bandwidth), ("queueBound", nullOr (mem d "queueBound")),
      ("ordered", .bool (mem d "ordered" matches .bool true)), ("fanout", .bool (mem d "fanout" matches .bool true))])
  let workloads ← (itemsOf (mem sdata "workloads")).mapM fun widV => do
    let wid := jsText widV
    let some w := entV? m widV | throw s!"Scenario \"{sc}\" names \"{wid}\", which is not a workload."
    if w.kind != "workload" then throw s!"Scenario \"{sc}\" names \"{wid}\", which is not a workload."
    let d := w.data
    let kind := orElse (mem d "kind") (.str "open")
    let mut out : List (String × Value) := [("id", widV), ("kind", kind)]
    for k in ["event", "legitimate", "maxArrivals", "requestField", "clientField", "addressField", "reply",
              "population", "behavior", "count"] do
      if hasMem d k then out := out ++ [(k, mem d k)]
    if truthy (mem d "payload") then
      let fs ← (match mem d "payload" with | .obj _ fs => fs | _ => []).mapM fun (k, v) => do
        if isObj v && hasMem v "sample" then
          pure (k, obj [("sample", (← lowerSpecDistribution (mem v "sample") unit s!"{wid}.payload.{k}").getD .undef)])
        else pure (k, v)
      out := out ++ [("payload", .obj 0 fs)]
    match kind with
    | .str "open" =>
      out := out ++ [("process", orElse (mem d "process") (.str "poisson"))]
      let phases ← if isArr (mem d "phases") then
          (itemsOf (mem d "phases")).zipIdx.mapM fun (p, i) => do
            let f ← dur (mem p "from") s!"{wid}.phases[{i}].from"
            let u ← dur (mem p "until") s!"{wid}.phases[{i}].until"
            let r := mem p "rate"
            let rate ← if isObj r && hasMem r "from" then do
                pure (obj [("from", ← rateOf (mem r "from") wid), ("to", ← rateOf (mem r "to") wid)])
              else rateOf r wid
            pure (obj [("from", numV f), ("until", numV u), ("rate", rate)])
        else do
          pure [obj [("from", numV 0), ("until", orElse horizon (numV 0)), ("rate", ← rateOf (mem d "rate") s!"{wid}.rate")]]
      out := out ++ [("phases", .arr 0 phases)]
      if hasMem d "repeat" then out := out ++ [("repeat", numV (← dur (mem d "repeat") s!"{wid}.repeat"))]
      if hasMem d "batch" then
        out := out ++ [("batch", (← lowerSpecDistribution (mem d "batch") "tick" s!"{wid}.batch").getD .undef)]
      let cl := mem d "clients"
      if truthy cl then
        let mut c : List (String × Value) := [("count", mem cl "count")]
        if truthy (mem cl "pick") then c := c ++ [("pick", mem cl "pick")]
        if truthy (mem cl "addresses") then
          c := c ++ [("addresses", obj [("groupSize",
            (← lowerSpecDistribution (mem (mem cl "addresses") "groupSize") "tick" s!"{wid}.groupSize").getD .undef)])]
        out := out ++ [("clients", obj c)]
    | .str "closed" =>
      if hasMem d "think" then out := out ++ [("think", (← lowerSpecDistribution (mem d "think") unit s!"{wid}.think").getD .undef)]
      if hasMem d "start" then out := out ++ [("start", (← lowerSpecDistribution (mem d "start") unit s!"{wid}.start").getD .undef)]
      if hasMem d "timeout" then out := out ++ [("timeout", numV (← dur (mem d "timeout") s!"{wid}.timeout"))]
    | .str "population" =>
      let st := mem d "start"
      let atF ← if hasMem st "at" then do
          pure [("at", (← lowerSpecDistribution (mem st "at") unit s!"{wid}.start.at").getD .undef)]
        else pure []
      out := out ++ [("start", obj ([("event", mem st "event")] ++ atF))]
    | _ => pure ()
    pure (obj out)
  let requests := (byKind m "requestClass").map fun c =>
    obj [("id", .str c.id), ("start", mem c.data "start"), ("key", mem c.data "key"),
         ("ends", orElse (mem c.data "ends") (.arr 0 []))]
  let faults ← v1faults.mapM fun f => do
    let fid := (strOf? (mem f "id")).getD ""
    let e := match ent? m fid with
      | some x => x.data
      | none => .undef
    let mut out := f
    if hasMem out "by" then out := setMem out "by" (numV (← dur (mem out "by") s!"{fid}.by"))
    if mem out "kind" matches .str "duplicate-event" && !hasMem out "by" then out := setMem out "by" (numV 0)
    if mem out "kind" matches .str "retry-event" then
      out := setMem out "by" (numV (← retryDelay m (mem e "attempts") unit))
    if hasMem out "at" then out := setMem out "at" (numV (← dur (mem out "at") s!"{fid}.at"))
    for k in ["resource", "class", "capacity", "limit", "num", "den", "behavior", "effect"] do
      if hasMem e k then out := setMem out k (mem e k)
    if hasMem e "demand" then
      out := setMem out "demand" ((← lowerSpecDistribution (mem e "demand") unit s!"{fid}.demand").getD .undef)
    if truthy (mem e "window") then
      let wv := mem e "window"
      let a ← dur (mem wv "at") s!"{fid}.window.at"
      let u ← if hasMem wv "until" then do pure [("until", numV (← dur (mem wv "until") s!"{fid}.window.until"))] else pure []
      out := setMem out "window" (obj ([("at", numV a)] ++ u))
    pure out
  let steps2 ← steps.zipIdx.mapM fun (st, i) => do
    pure (setMem st "at" (numV (← dur (mem st "at") s!"{sc}.steps[{i}].at")))
  let seed := match mem sdata "seed" with
    | .undef => Value.null
    | v => .str (jsText v)
  let scenario := obj (scenarioFields.map (fun (k, v) => if k == "steps" then (k, .arr 0 steps2) else (k, v)) ++
    [("seed", seed), ("horizon", horizon), ("warmup", ← opt (mem sdata "warmup") s!"{sc}.warmup"),
     ("stopAt", ← opt (mem sdata "stopAt") s!"{sc}.stopAt"), ("output", orElse (mem sdata "output") (.str "trace"))])
  let mut input : List (String × Value) := [
    ("format", .str "exegra-sim-input"), ("version", numV 2),
    ("time", obj [("unit", .str unit), ("perSecond", match ps with | some p => numV p | none => .null)]),
    ("scenario", scenario), ("behaviors", .arr 0 behaviors), ("events", .arr 0 events),
    ("faults", .arr 0 faults),
    ("routes", if isArr (mem sdata "routes") then mem sdata "routes" else .arr 0 []),
    ("resources", .arr 0 resources), ("links", .arr 0 links), ("workloads", .arr 0 workloads),
    ("requests", .arr 0 requests)]
  if truthy (mem sdata "metrics") then input := input ++ [("metrics", mem sdata "metrics")]
  if workloads.any (fun w => mem w "process" matches .str "poisson") then
    input := input ++ [("unitExponential", unitExponentialTable)]
  return obj input

/-- **The engine input of a scenario** (format `exegra-sim-input`, version 2). `faults`, when
given, replaces the scenario's own fault list. -/
def engineInput (m : Model) (sc : String) (faultsOverride : Option (List Value)) : L Value := do
  let some s := ent? m sc | throw s!"\"{sc}\" is not a scenario in this model."
  if s.kind != "scenario" then throw s!"\"{sc}\" is not a scenario in this model."
  let sdata := s.data
  let mut behaviors : List Value := []
  for bidV in itemsOf (mem sdata "behaviors") do
    let bid := jsText bidV
    let some b := entV? m bidV | throw s!"Scenario \"{sc}\" lists \"{bid}\", which is not a behavior."
    if b.kind != "behavior" then throw s!"Scenario \"{sc}\" lists \"{bid}\", which is not a behavior."
    let types := behaviorTypes m bid
    let variables := (itemsOf (mem b.data "variables")).map fun v =>
      obj [("name", mem v "name"), ("initial", mem v "initial")]
    let states := (ownedBy m "state" bid).map fun x => Value.str x.id
    let transitions := (ownedBy m "transition" bid).map fun t =>
      obj [("id", .str t.id), ("from", mem t.data "from"), ("to", mem t.data "to"), ("on", mem t.data "on"),
        ("guard", match mem t.data "guard" with | .str g => .str g | _ => .null),
        ("effects", .arr 0 ((itemsOf (mem t.data "effects")).map inputEffect)),
        ("faultOnly", .bool (mem t.data "faultOnly" matches .bool true))]
    behaviors := behaviors ++ [obj ([("id", bidV), ("subject", mem b.data "subject"), ("initial", mem b.data "initial")] ++
      (if types.isEmpty then [] else [("types", .obj 0 (types.map fun (k, t) => (k, .str t)))]) ++
      [("variables", .arr 0 variables), ("states", .arr 0 states), ("transitions", .arr 0 transitions)])]
  for pidV in itemsOf (mem sdata "pools") do
    let pid := jsText pidV
    match entV? m pidV with
    | some p => if p.kind != "quotaPool" then throw s!"Scenario \"{sc}\" lists \"{pid}\", which is not a quota pool."
    | none => throw s!"Scenario \"{sc}\" lists \"{pid}\", which is not a quota pool."
    behaviors := behaviors ++ (← poolMachines m pid)
  let faultIds := dedupV (faultsOverride.getD (itemsOf (mem sdata "faults")))
  let faultDecls ← faultIds.mapM fun id => do
    let some f := entV? m id | throw s!"\"{jsText id}\" is not a fault in this model."
    if f.kind != "fault" then throw s!"\"{jsText id}\" is not a fault in this model."
    pure (obj ([("id", id)] ++ faultKeys.filterMap fun k => if hasMem f.data k then some (k, mem f.data k) else none))
  let steps ← (itemsOf (mem sdata "steps")).zipIdx.mapM fun (st, i) => do
    let ev := mem st "event"
    match entV? m ev with
    | some e => if e.kind != "event" then throw s!"Scenario \"{sc}\" step {i} delivers \"{jsText ev}\", which is not an event."
    | none => throw s!"Scenario \"{sc}\" step {i} delivers \"{jsText ev}\", which is not an event."
    pure (obj [("at", mem st "at"), ("event", ev), ("payload", orElse (mem st "payload") (.obj 0 []))])
  for f in faultDecls do
    if mem f "kind" matches .str "inject-event" then
      let ev := mem f "event"
      let ok := match entV? m ev with
        | some e => e.kind == "event"
        | none => false
      if !ok then throw s!"Fault \"{jsText (mem f "id")}\" injects \"{jsText ev}\", which is not an event."
  let events := (byKind m "event").map fun e => obj [("id", .str e.id)]
  let scenarioFields : List (String × Value) :=
    [("id", .str sc), ("steps", .arr 0 steps), ("faults", .arr 0 faultIds),
     ("stepLimit", orElse (mem sdata "maxSteps") (numV 1000))]
  let timed := needsTimedInput m sdata || faultDecls.any fun f => match mem f "kind" with
    | .str k => format2Faults.contains k
    | _ => false
  if timed then
    return jsonNormal (← engineInputV2 m sc sdata behaviors faultDecls scenarioFields events steps)
  return jsonNormal (obj [("format", .str "exegra-sim-input"), ("version", numV 2),
    ("scenario", obj scenarioFields), ("behaviors", .arr 0 behaviors), ("events", .arr 0 events),
    ("faults", .arr 0 faultDecls), ("time", obj [("unit", .str "tick"), ("perSecond", .null)])])

end Exegra.Lower
