import Std.Data.HashMap
import Exegra.Hash

/-!
# Model derivation

The specification's JSON value to the semantic model: the effective meta-model (the built-in
meta-model plus the specification's `vocabulary`), the entities by kind with their data, every
reference and expression with its JSON path, and the structural diagnostics, with the codes and
messages `src/core/parse.js` reported before the port.

**The boundary with the JavaScript text layer.** The JSONC text (comments, trailing commas,
syntax errors, line and column positions) stays in `src/core/parse.js`. It hands over the
document as written: every object as `{"o": [[key, value], ...]}` with its members in source
order and repeated keys kept (`decode`), arrays and scalars as they are. Every place the
derivation reports or records is a *raw path* (`at`): the indices of the object members and
array items from the root, with a `Part` saying whether the node, the key of the last member or
the first character of the node is meant. JavaScript maps raw paths to source locations. The one
message that quotes a line number (`id.duplicate`) leaves the number to JavaScript too
(`Diag.lineOf`).

**Faithfulness.** The derivation follows parse.js statement by statement, including its
observable JavaScript semantics: a `Map` of members per object (first position, last value, a
`property.duplicate` diagnostic every time an object's members are read), `getNodeValue` for
entity data and the vocabulary (`plain`: assignment order into objects without a prototype), template strings and `String(...)` of arbitrary JSON values (`jsString`), and the
seven names an object inherits that `ent.properties[name]` sees (`inheritedNames`). It differs
only where Lean strings cannot follow: a lone surrogate (JavaScript replaces it with U+FFFD
before the call) and `toLowerCase` of non-ASCII letters in a declared entity kind's label.

**Totality.** Every function here is total. Recursion over the document is bounded by `fuel`,
set to twice the depth of the document plus a margin (`deriveFuel`); each step descends one level
of the document at most every second call, so the bound is never what ends a walk.
-/

namespace Exegra.Model

open Exegra

/-! ## JavaScript operations on JSON values -/

/-- `v[k]` for an own property; `undefined` otherwise. -/
def get (v : Value) (k : String) : Value :=
  match v with
  | .obj _ fs => (objGet? fs k).getD .undef
  | _ => .undef

/-- `Object.hasOwn(v, k)`. -/
def has (v : Value) (k : String) : Bool :=
  match v with
  | .obj _ fs => objHas fs k
  | _ => false

def isObject : Value → Bool
  | .obj .. => true
  | _ => false

def isArray : Value → Bool
  | .arr .. => true
  | _ => false

def isString : Value → Bool
  | .str _ => true
  | _ => false

def isUndef : Value → Bool
  | .undef => true
  | _ => false

/-- `x ?? y` is `y` exactly when `x` is one of these. -/
def isNullish : Value → Bool
  | .undef => true
  | .null => true
  | _ => false

/-- JavaScript truthiness. -/
def truthy : Value → Bool
  | .undef => false
  | .null => false
  | .bool b => b
  | .num x => !(x == 0)
  | .str s => !s.isEmpty
  | _ => true

def fieldsOf : Value → List (String × Value)
  | .obj _ fs => fs
  | _ => []

def itemsOf : Value → List Value
  | .arr _ xs => xs
  | _ => []

def keysOf (v : Value) : List String := (fieldsOf v).map (·.1)

/-- `Array.prototype.includes` element test (SameValueZero); arrays and objects from different
places are different objects. -/
def sameValue : Value → Value → Bool
  | .undef, .undef => true
  | .null, .null => true
  | .bool a, .bool b => a == b
  | .num a, .num b => a == b
  | .str a, .str b => a == b
  | _, _ => false

def includes (xs : Value) (x : Value) : Bool := (itemsOf xs).any (sameValue · x)

def isStr (v : Value) (s : String) : Bool := sameValue v (.str s)

mutual
/-- `String(v)`, which template strings use. -/
def jsString : Value → String
  | .undef => "undefined"
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .num x => Num.jsNumberToString x
  | .str s => s
  | .arr _ xs => ",".intercalate (joinItems xs)
  | .obj .. => "[object Object]"

/-- The strings `Array.prototype.join` joins: `null` and `undefined` give the empty string. -/
def joinItems : List Value → List String
  | [] => []
  | x :: xs => (match x with
    | .undef => ""
    | .null => ""
    | _ => jsString x) :: joinItems xs
end

/-- `xs.join(sep)`. -/
def join (xs : Value) (sep : String) : String := sep.intercalate (joinItems (itemsOf xs))

/-- `JSON.stringify(node.value)` of a jsonc-parser node: arrays and objects have no `value`. -/
def nodeValueText : Value → String
  | .arr .. => "undefined"
  | .obj .. => "undefined"
  | v => Json.write v

/-- A string as a value. -/
abbrev s (x : String) : Value := .str x

/-- `o[k] = x`. -/
def setKey (o : Value) (k : String) (x : Value) : Value := .obj 0 (objInsert (fieldsOf o) k x)

/-- `o[k] = f(o[k])`, for an existing `k`. -/
def updateKey (o : Value) (k : String) (f : Value → Value) : Value :=
  setKey o k (f (get o k))

/-- The names `ent.properties[name]` finds on any object without an own property: the
alphanumeric names of `Object.prototype`. -/
def inheritedNames : List String :=
  ["constructor", "hasOwnProperty", "isPrototypeOf", "propertyIsEnumerable", "toLocaleString",
   "toString", "valueOf"]

/-! ## Identifier patterns -/

def isLowerC (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'
def isUpperC (c : Char) : Bool := 'A' ≤ c && c ≤ 'Z'

def doubleHyphen : List Char → Bool
  | a :: b :: r => (a == '-' && b == '-') || doubleHyphen (b :: r)
  | _ => false

/-- The meta-model's `idPattern`, `^[a-z][a-z0-9_]*(-[a-z0-9_]+)*$`: a lower-case letter first,
then lower-case letters, digits, `_` and single hyphens, not ending in a hyphen. -/
def idOk (id : String) : Bool :=
  let cs := id.toList
  match cs with
  | [] => false
  | c :: _ =>
    isLowerC c && cs.all (fun c => isLowerC c || c.isDigit || c == '_' || c == '-') &&
      cs.getLast? != some '-' && !doubleHyphen cs

/-- `^[a-z][a-zA-Z0-9]*$`. -/
def kindIdOk (x : String) : Bool :=
  match x.toList with
  | [] => false
  | c :: cs => isLowerC c && cs.all (fun c => isLowerC c || isUpperC c || c.isDigit)

/-- `^[a-zA-Z][a-zA-Z0-9]*$`. -/
def propNameOk (x : String) : Bool :=
  match x.toList with
  | [] => false
  | c :: cs => (isLowerC c || isUpperC c) && cs.all (fun c => isLowerC c || isUpperC c || c.isDigit)

/-! ## The document -/

mutual
/-- The document as written, from its encoding: an object is `{"o": [[key, value], ...]}`, with
its members in source order and repeated keys kept. Any other value reads as itself (an
unencoded object as its members). -/
def decode : Value → Value
  | .obj _ [("o", .arr _ ps)] => .obj 0 (decodePairs ps)
  | .obj _ fs => .obj 0 (decodeFields fs)
  | .arr _ xs => .arr 0 (decodeItems xs)
  | v => v

def decodePairs : List Value → List (String × Value)
  | [] => []
  | .arr _ [.str k, v] :: ps => (k, decode v) :: decodePairs ps
  | _ :: ps => decodePairs ps

def decodeFields : List (String × Value) → List (String × Value)
  | [] => []
  | (k, v) :: fs => (k, decode v) :: decodeFields fs

def decodeItems : List Value → List Value
  | [] => []
  | x :: xs => decode x :: decodeItems xs
end

mutual
/-- jsonc-parser's `getNodeValue`: each member assigned, in source order, to an object without a
prototype (a repeated key keeps its first position and takes the last value, canonical array
indices go first; `__proto__` is an ordinary key). -/
def plain : Value → Value
  | .obj _ fs => .obj 0 (plainFields fs [])
  | .arr _ xs => .arr 0 (plainItems xs)
  | v => v

def plainFields : List (String × Value) → List (String × Value) → List (String × Value)
  | [], acc => acc
  | (k, v) :: fs, acc =>
    plainFields fs (objInsert acc k (plain v))

def plainItems : List Value → List Value
  | [] => []
  | x :: xs => plain x :: plainItems xs
end

mutual
/-- The nesting depth of a value. -/
def depth : Value → Nat
  | .obj _ fs => depthFields fs + 1
  | .arr _ xs => depthItems xs + 1
  | _ => 0

def depthFields : List (String × Value) → Nat
  | [] => 0
  | (_, v) :: fs => max (depth v) (depthFields fs)

def depthItems : List Value → Nat
  | [] => 0
  | x :: xs => max (depth x) (depthItems xs)
end

/-! ## Results -/

/-- Which part of the node at a raw path a diagnostic points at: the node, the key of the member
the path ends in, or the node's first character. -/
inductive Part where
  | node
  | key
  | start
  deriving Inhabited, BEq

structure Diag where
  code : String
  message : String
  /-- Raw path, innermost index first. -/
  raw : List Nat
  part : Part := .node
  path : Option (List Value) := none
  entityId : Option String := none
  /-- The message continues with the line of the node at this raw path, then `messageAfter`. -/
  lineOf : Option (List Nat) := none
  messageAfter : String := ""
  deriving Inhabited

structure Entity where
  id : String
  kind : String
  data : Value
  owner : Option String
  path : List Value
  raw : List Nat
  deriving Inhabited

structure Ref where
  src : String
  path : List Value
  target : String
  /-- The kinds the target may have (an array of strings; `"*"` for any kind). -/
  allowed : Value
  raw : List Nat
  deriving Inhabited

structure ExprRef where
  owner : String
  path : List Value
  src : String
  raw : List Nat
  deriving Inhabited

structure St where
  diags : Array Diag := #[]
  entities : Array Entity := #[]
  /-- id ↦ (kind, raw path) of the entities so far, for the duplicate check. -/
  ids : Std.HashMap String (String × List Nat) := {}
  refs : Array Ref := #[]
  exprs : Array ExprRef := #[]

abbrev M := StateM St

def push (d : Diag) : M Unit := modify fun st => { st with diags := st.diags.push d }

def addRef (r : Ref) : M Unit := modify fun st => { st with refs := st.refs.push r }

def addExpr (e : ExprRef) : M Unit := modify fun st => { st with exprs := st.exprs.push e }

/-- A node of the document with its raw path (innermost index first). -/
structure Node where
  v : Value
  raw : List Nat

/-- A member of an object node: its key and value node (the key is at the value's raw path,
part `key`). -/
structure Member where
  key : String
  val : Node

/-- The members of an object node as parse.js's `members` reads them into a `Map`: the first
position and the last occurrence of every key, with a `property.duplicate` diagnostic for every
repeated key, every time. -/
def members (n : Node) : M (List (String × Member)) := do
  match n.v with
  | .obj _ fs =>
    let mut m : List (String × Member) := []
    let mut i := 0
    for (k, v) in fs do
      let mem : Member := ⟨k, ⟨v, i :: n.raw⟩⟩
      if m.any (·.1 == k) then
        push { code := "property.duplicate", message := s!"Property \"{k}\" is declared twice.",
               raw := i :: n.raw, part := .key }
        m := m.map fun e => if e.1 == k then (k, mem) else e
      else
        m := m ++ [(k, mem)]
      i := i + 1
    return m
  | _ => return []

def lookup (ms : List (String × Member)) (k : String) : Option Member :=
  (ms.find? (·.1 == k)).map (·.2)

/-- `String(seg)` for a path segment. -/
def segKey : Value → String
  | .str x => x
  | v => jsString v

/-- `Number(seg)` as an array index, when it is one. -/
def segIndex : Value → Option Nat
  | .num x => if x ≥ 0 && Num.isInteger x && x < 9007199254740992 then some x.floor.toNat else none
  | .str x => if x.isEmpty then some 0 else if x.all Char.isDigit then some (Num.digitsToNat x.toList) else none
  | _ => none

/-- parse.js's `nodeAt`: the node at a JSON path, reading the members of every object on the way. -/
def nodeAt (n : Node) : List Value → M (Option Node)
  | [] => return some n
  | seg :: rest => do
    match n.v with
    | .obj .. =>
      let ms ← members n
      match lookup ms (segKey seg) with
      | some m => nodeAt m.val rest
      | none => return none
    | .arr _ xs =>
      match segIndex seg with
      | some i =>
        match xs[i]? with
        | some x => nodeAt ⟨x, i :: n.raw⟩ rest
        | none => return none
      | none => return none
    | _ => return none

/-! ## The effective meta-model -/

abbrev Report := String → String → List Value → M Unit

def scalarTypes : List String := ["string", "text", "boolean", "number"]

def propFields : List String := ["type", "label", "values", "doc", "expected", "required", "ref", "items"]

def allStrings (v : Value) : Bool := isArray v && !(itemsOf v).isEmpty && (itemsOf v).all isString

/-- The type part of a declared property (`typed` in parse.js), for a list's items. -/
def typedItem (entities x : Value) (p : List Value) (report : Report) : M (Option Value) := do
  let t := get x "type"
  if (itemsOf (.arr 0 (scalarTypes.map s))).any (sameValue · t) then
    return some (.obj 0 [("type", t)])
  if isStr t "enum" then
    let vs := get x "values"
    if !allStrings vs then
      report "vocabulary.type" "An enum property needs a non-empty string array \"values\"." p
      return none
    return some (.obj 0 [("type", s "enum"), ("values", vs)])
  if isStr t "ref" then
    let r := get x "ref"
    let kinds := if isString r then .arr 0 [r] else r
    if !allStrings kinds then
      report "vocabulary.type" "A ref property needs \"ref\": the entity kind(s) it may point to." p
      return none
    let unknown := (itemsOf kinds).filter fun k => !isStr k "*" && !has entities (segKey k)
    if !unknown.isEmpty then
      report "vocabulary.entity" s!"Unknown entity kind(s) in \"ref\": {", ".intercalate (joinItems unknown)}." p
      return none
    return some (.obj 0 [("type", s "ref"), ("ref", kinds)])
  report "vocabulary.type" "Property type must be one of: string, text, boolean, number, enum, ref, list (lists cannot nest)." p
  return none

/-- The type part of a declared property (`typed(x, false)`). -/
def typed (entities x : Value) (p : List Value) (report : Report) : M (Option Value) := do
  let t := get x "type"
  if isStr t "list" then
    if !isObject (get x "items") then
      report "vocabulary.type" "A list property needs \"items\": {\"type\": ...}." p
      return none
    match ← typedItem entities (get x "items") p report with
    | some it => return some (.obj 0 [("type", s "list"), ("items", it)])
    | none => return none
  if (itemsOf (.arr 0 ((scalarTypes ++ ["enum", "ref"]).map s))).any (sameValue · t) then
    typedItem entities x p report
  else
    report "vocabulary.type" "Property type must be one of: string, text, boolean, number, enum, ref, list." p
    return none

/-- `propertyDef` of parse.js: a declared property as a meta-model property definition. -/
def propertyDef (entities d : Value) (p : List Value) (report : Report) : M (Option Value) := do
  match ← typed entities d p report with
  | none => return none
  | some base =>
    let label := get d "label"
    let doc := get d "doc"
    return some (.obj 0 (fieldsOf base ++ [
      ("label", if isString label then label else .undef),
      ("doc", if isString doc then doc else .undef),
      ("required", if sameValue (get d "required") (.bool true) then .bool true else .undef),
      ("expected", if sameValue (get d "expected") (.bool true) then .bool true else .undef),
      ("extension", .bool true)]))

/-- `x ?? y`. -/
def orElse (x y : Value) : Value := if isNullish x then y else x

/-- The effective meta-model (`effectiveMeta` in parse.js): the built-in meta-model `mm` plus the
vocabulary `vocab` (its plain value, `undefined` when absent). `methods` is the claim method
registry. -/
def effectiveMeta (mm methods vocab : Value) (report : Report) : M Value := do
  let V := get mm "vocabulary"
  let shapes := get V "shapes"
  let colors := get V "colors"
  let lines := get V "lines"
  let mut entities := get mm "entities"
  let mut categories := get V "categories"
  let mut relKinds := get V "relationshipKinds"
  let projections := get V "projections"
  let mut sections := get mm "sections"
  let mut vmethods : Value := .obj 0 []
  if isUndef vocab then
    return .obj 0 [("entities", entities), ("categories", categories), ("relationshipKinds", relKinds),
      ("projections", projections), ("sections", sections), ("verificationMethods", vmethods)]
  if !isObject vocab then
    report "vocabulary.type" "\"vocabulary\" must be an object." [s "vocabulary"]
    return .obj 0 [("entities", entities), ("categories", categories), ("relationshipKinds", relKinds),
      ("projections", projections), ("sections", sections), ("verificationMethods", vmethods)]
  for key in keysOf vocab do
    if !["categories", "relationshipKinds", "properties", "entityKinds", "verificationMethods"].contains key then
      report "vocabulary.unknown" s!"Unsupported vocabulary section \"{key}\"." [s "vocabulary", s key]
  -- categories
  let cats := get vocab "categories"
  if !isUndef cats then
    if !isObject cats then
      report "vocabulary.type" "\"vocabulary.categories\" must be an object keyed by category id." [s "vocabulary", s "categories"]
    else
      for (id, d) in fieldsOf cats do
        let p := [s "vocabulary", s "categories", s id]
        if !isObject d then
          report "vocabulary.type" s!"Category \"{id}\" must be an object." p
          continue
        for k in keysOf d do
          if !["label", "shape", "color", "description"].contains k then
            report "vocabulary.unknown" s!"Unsupported category field \"{k}\"." (p ++ [s k])
        if !isString (get d "label") then
          report "vocabulary.type" s!"Category \"{id}\" needs a string \"label\"." p
        if !includes shapes (get d "shape") then
          report "vocabulary.shape" s!"Category \"{id}\" needs \"shape\" to be one of: {join shapes ", "}." p
        if !includes colors (get d "color") then
          report "vocabulary.color" s!"Category \"{id}\" needs \"color\" to be one of: {join colors ", "}." p
        let desc := get d "description"
        categories := setKey categories id (.obj 0 [
          ("label", s (jsString (orElse (get d "label") (s id)))),
          ("shape", if includes shapes (get d "shape") then get d "shape" else s "box"),
          ("color", if includes colors (get d "color") then get d "color" else s "slate"),
          ("description", if isString desc then desc else s ""),
          ("declared", .bool true)])
  -- relationship kinds
  let rks := get vocab "relationshipKinds"
  if !isUndef rks then
    if !isObject rks then
      report "vocabulary.type" "\"vocabulary.relationshipKinds\" must be an object keyed by kind id." [s "vocabulary", s "relationshipKinds"]
    else
      for (id, d) in fieldsOf rks do
        let p := [s "vocabulary", s "relationshipKinds", s id]
        if !isObject d then
          report "vocabulary.type" s!"Relationship kind \"{id}\" must be an object." p
          continue
        for k in keysOf d do
          if !["label", "line", "color", "dependency", "description", "class", "direction", "parent"].contains k then
            report "vocabulary.unknown" s!"Unsupported relationship kind field \"{k}\"." (p ++ [s k])
        if !isString (get d "label") then
          report "vocabulary.type" s!"Relationship kind \"{id}\" needs a string \"label\"." p
        if !includes lines (get d "line") then
          report "vocabulary.line" s!"Relationship kind \"{id}\" needs \"line\" to be one of: {join lines ", "}." p
        if !includes colors (get d "color") then
          report "vocabulary.color" s!"Relationship kind \"{id}\" needs \"color\" to be one of: {join colors ", "}." p
        -- The taxonomy (class, direction, parent) is checked by the JS validator (interactions.js); the
        -- kernel passes it on. A kind that states a class needs no `dependency`: it is derived from the class.
        let cls := get d "class"
        let dep := get d "dependency"
        if isUndef cls && !(match dep with | .bool _ => true | _ => false) then
          report "vocabulary.type" s!"Relationship kind \"{id}\" needs a boolean \"dependency\"." p
        let depFlag := if isUndef cls then sameValue dep (.bool true) else !(sameValue cls (s "none"))
        let taxonomy := ["class", "direction", "parent"].filterMap (fun k =>
          let v := get d k
          if isUndef v then none else some (k, v))
        let desc := get d "description"
        relKinds := setKey relKinds id (.obj 0 ([
          ("label", s (jsString (orElse (get d "label") (s id)))),
          ("line", if includes lines (get d "line") then get d "line" else s "solid"),
          ("color", if includes colors (get d "color") then get d "color" else s "neutral"),
          ("dependency", .bool depFlag),
          ("description", if isString desc then desc else s "")] ++ taxonomy ++ [
          ("declared", .bool true)]))
  -- entity kinds
  let eks := get vocab "entityKinds"
  if !isUndef eks then
    if !isObject eks then
      report "vocabulary.type" "\"vocabulary.entityKinds\" must be an object keyed by kind id." [s "vocabulary", s "entityKinds"]
    else
      let mut declared : List (String × Value × List Value) := []
      for (id, d) in fieldsOf eks do
        let p := [s "vocabulary", s "entityKinds", s id]
        if !isObject d then
          report "vocabulary.type" s!"Entity kind \"{id}\" must be an object." p
          continue
        for k in keysOf d do
          if !["label", "section", "doc", "shape", "color", "properties"].contains k then
            report "vocabulary.unknown" s!"Unsupported entity kind field \"{k}\"." (p ++ [s k])
        if !kindIdOk id then
          report "vocabulary.type" s!"Entity kind id \"{id}\" must be alphanumeric and start with a lower-case letter." p
          continue
        if has entities id then
          report "vocabulary.duplicate" s!"Entity kind \"{id}\" already exists." p
          continue
        let label := get d "label"
        if !(isString label && !isStr label "") then
          report "vocabulary.type" s!"Entity kind \"{id}\" needs a string \"label\"." p
          continue
        let sec := get d "section"
        if !(match sec with | .str x => kindIdOk x | _ => false) then
          report "vocabulary.type" s!"Entity kind \"{id}\" needs an alphanumeric \"section\" (the top-level key its entities are declared under)." p
          continue
        if has sections (segKey sec) then
          report "vocabulary.duplicate" s!"Section \"{segKey sec}\" is already in use." p
          continue
        let shape := get d "shape"
        let color := get d "color"
        if !isUndef shape && !includes shapes shape then
          report "vocabulary.shape" s!"Entity kind \"{id}\": \"shape\" must be one of: {join shapes ", "}." p
        if !isUndef color && !includes colors color then
          report "vocabulary.color" s!"Entity kind \"{id}\": \"color\" must be one of: {join colors ", "}." p
        let doc := get d "doc"
        entities := setKey entities id (.obj 0 [
          ("label", label),
          ("doc", if isString doc then doc else s ""),
          ("declared", .bool true),
          ("shape", if includes shapes shape then shape else s "box"),
          ("color", if includes colors color then color else s "neutral"),
          ("properties", .obj 0 [("id", .obj 0 [("type", s "id"), ("required", .bool true)])])])
        sections := setKey sections (segKey sec) (.obj 0 [("entity", s id), ("declared", .bool true)])
        declared := declared ++ [(id, d, p)]
      -- Properties second, so that kinds may refer to each other in any order.
      for (id, d, p) in declared do
        let props := get d "properties"
        if isUndef props then continue
        if !isObject props then
          report "vocabulary.type" s!"Entity kind \"{id}\": \"properties\" must be an object keyed by property name." p
          continue
        for (name, pd) in fieldsOf props do
          let pp := p ++ [s "properties", s name]
          if !isObject pd then
            report "vocabulary.type" s!"Property \"{name}\" must be an object." pp
            continue
          if !propNameOk name || name == "id" then
            report "vocabulary.type" s!"Property name \"{name}\" must be alphanumeric and not \"id\"." pp
            continue
          for k in keysOf pd do
            if !propFields.contains k then
              report "vocabulary.unknown" s!"Unsupported property definition field \"{k}\"." (pp ++ [s k])
          match ← propertyDef entities pd pp report with
          | none => pure ()
          | some built =>
            let built := setKey built "label" (orElse (get built "label") (s name))
            let built := setKey built "extension" .undef
            entities := updateKey entities id fun ent =>
              updateKey ent "properties" fun ps => setKey ps name built
  -- properties added to existing kinds
  let props := get vocab "properties"
  if !isUndef props then
    if !isArray props then
      report "vocabulary.type" "\"vocabulary.properties\" must be an array." [s "vocabulary", s "properties"]
    else
      let mut i := 0
      for d in itemsOf props do
        let p := [s "vocabulary", s "properties", .num (↑i : Rat)]
        i := i + 1
        if !isObject d then
          report "vocabulary.type" "A property definition must be an object." p
          continue
        for k in keysOf d do
          if !(["entity", "name"] ++ propFields).contains k then
            report "vocabulary.unknown" s!"Unsupported property definition field \"{k}\"." (p ++ [s k])
        let ent := get d "entity"
        let entDef := match ent with
          | .str e => objGet? (fieldsOf entities) e
          | _ => none
        match entDef with
        | none =>
          report "vocabulary.entity" s!"Unknown entity kind \"{jsString ent}\" in property definition." p
          continue
        | some entDef =>
          let name := get d "name"
          match name with
          | .str nm =>
            if !propNameOk nm then
              report "vocabulary.type" "A property definition needs an alphanumeric \"name\"." p
              continue
            if has (get entDef "properties") nm || inheritedNames.contains nm then
              report "vocabulary.duplicate" s!"Property \"{nm}\" already exists on {jsString ent}." p
              continue
            match ← propertyDef entities d p report with
            | none => pure ()
            | some built =>
              let built := setKey built "label" (orElse (get built "label") (s nm))
              entities := updateKey entities (segKey ent) fun e =>
                updateKey e "properties" fun ps => setKey ps nm built
          | _ =>
            report "vocabulary.type" "A property definition needs an alphanumeric \"name\"." p
            continue
  -- verification methods carried out outside Exegra
  let vms := get vocab "verificationMethods"
  if !isUndef vms then
    if !isObject vms then
      report "vocabulary.type" "\"vocabulary.verificationMethods\" must be an object keyed by method id." [s "vocabulary", s "verificationMethods"]
    else
      for (id, d) in fieldsOf vms do
        let p := [s "vocabulary", s "verificationMethods", s id]
        if !isObject d || !isString (get d "label") then
          report "vocabulary.type" s!"Verification method \"{id}\" must be an object with a string \"label\"." p
          continue
        for k in keysOf d do
          if !["label", "description"].contains k then
            report "vocabulary.unknown" s!"Unsupported verification method field \"{k}\"." (p ++ [s k])
        if has methods id then
          report "vocabulary.duplicate" s!"\"{id}\" is a built-in evaluation method." p
          continue
        let desc := get d "description"
        vmethods := setKey vmethods id (.obj 0 [("label", get d "label"),
          ("description", if isString desc then desc else s "")])
  return .obj 0 [("entities", entities), ("categories", categories), ("relationshipKinds", relKinds),
    ("projections", projections), ("sections", sections), ("verificationMethods", vmethods)]

/-! ## Structure, types and references -/

/-- What every check needs: the effective meta-model and the claim method registry. -/
structure Ctx where
  mmeta : Value
  methods : Value

/-- `idRef`: a reference from a string node. -/
def idRef (owner : String) (n : Node) (p : List Value) (allowed : List String) : M Unit :=
  match n.v with
  | .str t => addRef { src := owner, path := p, target := t, allowed := .arr 0 (allowed.map s), raw := n.raw }
  | _ => pure ()

/-- `idRefs`: a reference from a string node, or one from each item of an array node. -/
def idRefs (owner : String) (n : Node) (p : List Value) (allowed : List String) : M Unit := do
  match n.v with
  | .str _ => idRef owner n p allowed
  | .arr _ xs =>
    let mut i := 0
    for x in xs do
      idRef owner ⟨x, i :: n.raw⟩ (p ++ [.num (↑i : Rat)]) allowed
      i := i + 1
  | _ => pure ()

/-- References and expressions inside an `effect` value (its shape is validate.js's). -/
def checkEffect (owner : String) (node : Node) (path : List Value) : M Unit := do
  let m ← members node
  if let some e := lookup m "emit" then
    if let .str t := e.val.v then
      addRef { src := owner, path := path ++ [s "emit"], target := t, allowed := .arr 0 [s "event"], raw := e.val.raw }
  if let some e := lookup m "to" then
    if let .str x := e.val.v then
      addExpr { owner, path := path ++ [s "to"], src := x, raw := e.val.raw }
  if let some e := lookup m "payload" then
    if isObject e.val.v then
      let pm ← members e.val
      for (k, pe) in pm do
        if let .str x := pe.val.v then
          addExpr { owner, path := path ++ [s "payload", s k], src := x, raw := pe.val.raw }

/-- References and expressions inside a claim's `evaluate`, by the parameter types of its method. -/
def checkEvaluation (ctx : Ctx) (owner : String) (node : Node) (path : List Value) : M Unit := do
  let m ← members node
  let mdef := match lookup m "method" with
    | some e => match e.val.v with
      | .str x => objGet? (fieldsOf ctx.methods) x
      | _ => none
    | none => none
  let some mdef := mdef | return
  for (key, pdef) in fieldsOf (get mdef "params") do
    let some entry := lookup m key | continue
    let type := segKey (get pdef "type")
    let p := path ++ [s key]
    if type == "selector" then
      if isObject entry.val.v then
        let sm ← members entry.val
        if let some ids := lookup sm "ids" then idRefs owner ids.val (p ++ [s "ids"]) ["component"]
        if let some w := lookup sm "within" then idRef owner w.val (p ++ [s "within"]) ["component"]
      else idRefs owner entry.val p ["component"]
    else if type.startsWith "ids:" then
      idRefs owner entry.val p [type.drop 4 |>.toString]
    else if type == "matcher" && isObject entry.val.v then
      let mm ← members entry.val
      if let some ev := lookup mm "event" then idRef owner ev.val (p ++ [s "event"]) ["event"]
      if let some tr := lookup mm "transition" then idRef owner tr.val (p ++ [s "transition"]) ["transition"]
    else if type == "negatives" && isArray entry.val.v then
      let mut i := 0
      for neg in itemsOf entry.val.v do
        let nn : Node := ⟨neg, i :: entry.val.raw⟩
        if isObject neg then
          let nm ← members nn
          if let some sc := lookup nm "scenario" then idRef owner sc.val (p ++ [.num (↑i : Rat), s "scenario"]) ["scenario"]
          if let some fs := lookup nm "faults" then idRefs owner fs.val (p ++ [.num (↑i : Rat), s "faults"]) ["fault"]
        i := i + 1
    else if type == "expr" then
      if let .str x := entry.val.v then
        addExpr { owner, path := p, src := x, raw := entry.val.raw }

/-- The values an enum property allows. -/
def enumValues (mmeta pd : Value) : Value :=
  let vs := get pd "values"
  if !isNullish vs then vs
  else if isStr (get pd "valuesFrom") "projections" then get mmeta "projections"
  else match get pd "valuesFrom" with
    | .str k => .arr 0 ((keysOf (get mmeta k)).map s)
    | _ => .arr 0 []

mutual
/-- `checkValue`: one property value against its definition. -/
def checkValue (ctx : Ctx) : Nat → Value → Node → List Value → String → String → M Unit
  | 0, _, _, _, _, _ => pure ()
  | fuel + 1, pd, node, path, owner, label => do
    let bad (code message : String) : M Unit :=
      push { code, message, raw := node.raw, path := some path, entityId := some owner }
    let t := get pd "type"
    match segKey t, node.v with
    | "id", v | "string", v | "text", v =>
      if !isString v then bad "property.type" s!"{label} must be a string."
    | "expr", v =>
      match v with
      | .str x => addExpr { owner, path, src := x, raw := node.raw }
      | _ => bad "property.type" s!"{label} must be an expression string."
    | "boolean", v =>
      if !(match v with | .bool _ => true | _ => false) then bad "property.type" s!"{label} must be true or false."
    | "number", v =>
      if !(match v with | .num _ => true | _ => false) then bad "property.type" s!"{label} must be a number."
    | "enum", v =>
      let values := enumValues ctx.mmeta pd
      if !(isString v && includes values v) then
        bad "property.enum" s!"{label} must be one of: {join values ", "}."
    | "ref", v =>
      match v with
      | .str x =>
        let lits := get pd "literals"
        if isArray lits && includes lits v then pure ()
        else addRef { src := owner, path, target := x, allowed := get pd "ref", raw := node.raw }
      | _ => bad "property.type" s!"{label} must be an entity id."
    | "list", v =>
      match v with
      | .arr _ xs =>
        let mut i := 0
        for x in xs do
          checkValue ctx fuel (get pd "items") ⟨x, i :: node.raw⟩ (path ++ [.num (↑i : Rat)]) owner s!"{label}[{i}]"
          i := i + 1
      | _ => bad "property.type" s!"{label} must be an array."
    | "object", v =>
      if isObject v then checkFields ctx fuel (get pd "fields") node path owner label
      else bad "property.type" s!"{label} must be an object."
    | "map", v =>
      if !isObject v then bad "property.type" s!"{label} must be an object."
    | "effect", v =>
      if isObject v then checkEffect owner node path
      else bad "property.type" s!"{label} must be an object."
    | "evaluation", v =>
      if isObject v then checkEvaluation ctx owner node path
      else bad "property.type" s!"{label} must be an object."
    | "any", _ => pure ()
    | _, _ => bad "metamodel.type" s!"{label} has an unsupported meta-model type \"{jsString t}\"."

/-- `checkFields`: the members of an object node against field definitions. -/
def checkFields (ctx : Ctx) : Nat → Value → Node → List Value → String → String → M Unit
  | 0, _, _, _, _, _ => pure ()
  | fuel + 1, fields, node, path, owner, label => do
    let m ← members node
    for (key, e) in m do
      match objGet? (fieldsOf fields) key with
      | none =>
        push { code := "property.unknown", message := s!"Unsupported property \"{key}\" on {label}.",
               raw := e.val.raw, part := .key, path := some (path ++ [s key]), entityId := some owner }
      | some d =>
        if isStr (get d "type") "entities" then continue
        checkValue ctx fuel d e.val (path ++ [s key]) owner s!"\"{key}\""
    for (key, d) in fieldsOf fields do
      if truthy (get d "required") && !m.any (·.1 == key) then
        push { code := "property.required", message := s!"Missing required property \"{key}\" on {label}.",
               raw := node.raw, part := .start, path := some path, entityId := some owner }
end

/-- `parseEntity`: an entity declaration, its properties and the entities nested in it. -/
def parseEntity (ctx : Ctx) (idPattern : String) : Nat → String → Node → List Value → Option String → M Unit
  | 0, _, _, _, _ => pure ()
  | fuel + 1, kind, node, path, owner => do
    let edef := get (get ctx.mmeta "entities") kind
    let lower := (jsString (get edef "label")).toLower
    if !isObject node.v then
      push { code := "entity.type", message := s!"A {lower} must be an object.", raw := node.raw, path := some path }
      return
    let m ← members node
    let idNode := lookup m "id"
    let some (id, idAt) := (match idNode with
      | some e => match e.val.v with
        | .str x => some (x, e.val.raw)
        | _ => none
      | none => none) | do
        push { code := "id.missing", message := s!"This {lower} has no string \"id\".", raw := node.raw,
               part := .start, path := some path }
        return
    if !idOk id then
      push { code := "id.format",
             message := s!"Id \"{id}\" must be lower-case words joined by hyphens (pattern {idPattern}).",
             raw := idAt, path := some (path ++ [s "id"]), entityId := some id }
    if let some (exKind, exAt) := (← getThe St).ids[id]? then
      push { code := "id.duplicate", message := s!"Id \"{id}\" is already used by a {exKind} declared on line ",
             lineOf := some exAt, messageAfter := ".", raw := idAt, path := some (path ++ [s "id"]),
             entityId := some id }
      return
    let entity : Entity := { id, kind, data := plain node.v, owner, path, raw := node.raw }
    modify fun st => { st with entities := st.entities.push entity, ids := st.ids.insert id (kind, node.raw) }
    checkFields ctx fuel (get edef "properties") node path id s!"{kind} \"{id}\""
    for (key, pdef) in fieldsOf (get edef "properties") do
      if !isStr (get pdef "type") "entities" then continue
      let some entry := lookup m key | continue
      match entry.val.v with
      | .arr _ xs =>
        let mut i := 0
        for x in xs do
          parseEntity ctx idPattern fuel (segKey (get pdef "entity")) ⟨x, i :: entry.val.raw⟩
            (path ++ [s key, .num (↑i : Rat)]) (some id)
          i := i + 1
      | _ =>
        push { code := "property.type", message := s!"\"{key}\" must be an array.", raw := entry.val.raw,
               path := some (path ++ [s key]), entityId := some id }

/-! ## The model -/

structure Model where
  schemaVersion : Value
  mmeta : Value
  vocabulary : Value
  /-- The entity kinds, in the order of the effective meta-model (`byKind`'s keys). -/
  kinds : List String
  /-- In declaration order. -/
  entities : List Entity
  refs : List Ref
  exprs : List ExprRef

/-- The top-level declarations, the content of the semantic hash. -/
def Model.top (m : Model) : List Hash.Decl :=
  (m.entities.filter (·.owner.isNone)).map fun e => (e.id, e.kind, e.data)

/-- The semantic hash of a model. -/
def Model.semanticHash (m : Model) : String :=
  Hash.semanticHash m.schemaVersion m.vocabulary m.top

def deriveFuel (doc : Value) : Nat := 2 * depth doc + 8

/-- Everything but reference resolution: the diagnostics so far and the model, if the root is an
object. -/
def build (mm methods doc : Value) : M (Option Model) := do
  let root : Node := ⟨doc, []⟩
  if !isObject doc then
    push { code := "spec.root", message := "The specification must be a JSON object.", raw := [] }
    return none
  let fuel := deriveFuel doc
  let sv := get mm "schemaVersion"
  let top ← members root
  match lookup top "exegra" with
  | none =>
    push { code := "schema.missing", message := s!"Missing \"exegra\" schema version (current: \"{jsString sv}\").",
           raw := [], part := .start }
  | some m =>
    if !sameValue m.val.v sv then
      push { code := "schema.version",
             message := s!"Unsupported schema version {nodeValueText m.val.v}; this build reads \"{jsString sv}\". Run \"exegra migrate\" if a migration exists.",
             raw := m.val.raw }
  let vocabM := lookup top "vocabulary"
  let report : Report := fun code message path => do
    let n ← nodeAt root path
    let n := (n <|> vocabM.map (·.val)).getD root
    push { code, message, raw := n.raw, path := some path }
  let mmeta ← effectiveMeta mm methods (match vocabM with | some m => plain m.val.v | none => .undef) report
  for (key, m) in top do
    if !has (get mmeta "sections") key then
      push { code := "spec.unknown-section", message := s!"Unsupported top-level section \"{key}\".",
             raw := m.val.raw, part := .key, path := some [s key] }
  let ctx : Ctx := { mmeta, methods }
  let idPattern := jsString (get mm "idPattern")
  for (sec, sdef) in fieldsOf (get mmeta "sections") do
    let ent := get sdef "entity"
    if !truthy ent then continue
    match lookup top sec with
    | none =>
      if truthy (get sdef "single") then
        push { code := "spec.system-missing", message := "Missing \"system\" section.", raw := [], part := .start }
    | some entry =>
      if truthy (get sdef "single") then
        parseEntity ctx idPattern fuel (segKey ent) entry.val [s sec] none
      else match entry.val.v with
        | .arr _ xs =>
          let mut i := 0
          for x in xs do
            parseEntity ctx idPattern fuel (segKey ent) ⟨x, i :: entry.val.raw⟩ [s sec, .num (↑i : Rat)] none
            i := i + 1
        | _ =>
          push { code := "spec.section-type", message := s!"Section \"{sec}\" must be an array.",
                 raw := entry.val.raw, path := some [s sec] }
  let st ← getThe St
  return some {
    schemaVersion := sv, mmeta,
    vocabulary := match vocabM with | some m => plain m.val.v | none => .obj 0 [],
    kinds := keysOf (get mmeta "entities"),
    entities := st.entities.toList, refs := st.refs.toList, exprs := st.exprs.toList }

/-- The entity a reference names, if any. -/
def target? (es : List Entity) (id : String) : Option Entity := es.find? (·.id == id)

/-- Whether a reference may point to an entity of this kind. -/
def allowedKind (allowed : Value) (kind : String) : Bool :=
  includes allowed (s "*") || includes allowed (s kind)

/-- The diagnostic of one reference: none when it resolves to an entity of an allowed kind. -/
def resolveRef (es : List Entity) (r : Ref) : Option Diag :=
  match target? es r.target with
  | none =>
    let expected := if includes r.allowed (s "*") then "any entity" else "a " ++ join r.allowed " or "
    some ({ code := "ref.unresolved",
            message := s!"\"{r.target}\" does not identify any entity (expected {expected}).",
            raw := r.raw, path := some r.path, entityId := some r.src } : Diag)
  | some e =>
    if allowedKind r.allowed e.kind then none
    else some ({ code := "ref.kind", message := s!"\"{r.target}\" is a {e.kind}; expected a {join r.allowed " or "}.",
                 raw := r.raw, path := some r.path, entityId := some r.src } : Diag)

/-- The diagnostics of reference resolution, in the order of the references. -/
def resolveRefs (es : List Entity) (refs : List Ref) : List Diag := refs.filterMap (resolveRef es)

structure Result where
  diagnostics : List Diag
  model : Option Model

/-- **Model derivation**: the meta-model `mm`, the claim method registry `methods` and the
document (decoded) to the diagnostics and the model. -/
def derive (mm methods doc : Value) : Result :=
  let (model, st) := (build mm methods doc).run {}
  match model with
  | none => { diagnostics := st.diags.toList, model := none }
  | some m => { diagnostics := st.diags.toList ++ resolveRefs m.entities m.refs, model := some m }

/-! ## As JSON for the shell -/

/-- A raw path as text, outermost index first, separated by dots (`""` for the root): one string
instead of an array of numbers, which the shell splits. -/
def natsJson (raw : List Nat) : Value := .str (".".intercalate (raw.reverse.map toString))

def Part.name : Part → String
  | .node => "node"
  | .key => "key"
  | .start => "start"

def Diag.toJson (d : Diag) : Value :=
  .obj 0 ([("code", s d.code), ("severity", s "error"), ("message", s d.message),
    ("at", natsJson d.raw), ("part", s d.part.name)] ++
    (match d.path with | some p => [("path", .arr 0 p)] | none => []) ++
    (match d.entityId with | some e => [("entityId", s e)] | none => []) ++
    (match d.lineOf with | some l => [("lineOf", natsJson l), ("messageAfter", s d.messageAfter)] | none => []))

def Entity.toJson (e : Entity) : Value :=
  .obj 0 [("id", s e.id), ("kind", s e.kind), ("data", e.data),
    ("owner", match e.owner with | some o => s o | none => .null),
    ("path", .arr 0 e.path), ("at", natsJson e.raw)]

def Ref.toJson (r : Ref) : Value :=
  .obj 0 [("from", s r.src), ("path", .arr 0 r.path), ("target", s r.target),
    ("allowed", r.allowed), ("at", natsJson r.raw)]

def ExprRef.toJson (x : ExprRef) : Value :=
  .obj 0 [("owner", s x.owner), ("path", .arr 0 x.path), ("src", s x.src), ("at", natsJson x.raw)]

/-- The model as JSON, with its semantic hash (computed by the implementation `semanticHash'`,
equal to the definition by `Hash.semanticHash'_eq`). -/
def Model.toJson (m : Model) : Value :=
  .obj 0 [("schemaVersion", m.schemaVersion), ("meta", m.mmeta), ("vocabulary", m.vocabulary),
    ("kinds", .arr 0 (m.kinds.map s)),
    ("entities", .arr 0 (m.entities.map Entity.toJson)),
    ("refs", .arr 0 (m.refs.map Ref.toJson)),
    ("exprs", .arr 0 (m.exprs.map ExprRef.toJson)),
    ("semanticHash", s (Hash.semanticHash' m.schemaVersion m.vocabulary m.top))]

def Result.toJson (r : Result) : Value :=
  .obj 0 [("diagnostics", .arr 0 (r.diagnostics.map Diag.toJson)),
    ("model", match r.model with | some m => m.toJson | none => .null)]

/-- The boundary function: `{spec, metamodel, methods}` (the document encoded as `decode` reads
it) to the JSON text of the result. Never refuses: missing arguments read as `undefined`. -/
def deriveValue (args : Value) : Except String String :=
  .ok (Impl.JsonOut.write' (derive (get args "metamodel") (get args "methods") (decode (get args "spec"))).toJson)

end Exegra.Model
