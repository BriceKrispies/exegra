import Exegra.ProveLive

/-
Kernel-checked invariants of a scenario (WG-5682, criterion 5).

The proof files of `exegra prove` establish their results by compiled evaluation (`native_decide`),
which adds an axiom per statement. `kernelModule` writes a Lean module that the kernel checks with
the standard axioms only: the elaborated calculus system of the scenario written out as a Lean term
(`sysLean`; elaboration parses JSON, which the kernel does not evaluate), the
claim expression elaborated into the calculus (`claimExpr`, evaluated by `Expr.eval` on the
configuration, `claimTrue`), the list of reachable states the explorer visited, and

* `checkClosed (Exec.enum sys) visited (fun s => s.ok && claimTrue e s) = true`, by `decide`;
* the invariant `(Sys.lts sys).Invariant (fun s => s.ok = true ∧ claimTrue e s = true)`, by
  `checkClosed_sound`.

The statement is about the written system; `exegra prove --module` writes it from the elaboration of
the scenario's engine input and the build checks it.
-/

namespace Exegra.Core.Behav

/-- A claim expression of machine `me` evaluated on a configuration: the snapshot is the
configuration, the machine's own state is its own, and no entry is being delivered. -/
def claimEval {S : Sig} {me : Fin S.machines} (c : Cfg) (e : Expr S me) : Except Err Val :=
  e.eval { snap := c.machines, time := c.time, own := c.machines.getD me.val { ctrl := 0, vars := [] }, payload := [] }

/-- The claim expression is true in the state's configuration (an error or a non-Boolean is not). -/
def claimTrue {S : Sig} {me : Fin S.machines} (e : Expr S me) (s : State) : Bool :=
  match claimEval s.cfg e with
  | .ok (.bool true) => true
  | _ => false

/-- **The invariant of a kernel-checked certificate**, in the form `s.ok = true ∧ P s`. -/
theorem invariant_of_kernel_certificate {sys : Sys} {S : Sig} {me : Fin S.machines} {e : Expr S me}
    {L : List State} (h : LTS.checkClosed (Exec.enum sys) L (fun s => s.ok && claimTrue e s) = true) :
    (Sys.lts sys).Invariant (fun s => s.ok = true ∧ claimTrue e s = true) := by
  intro s hs
  have := LTS.checkClosed_sound _ L _ h s hs
  simpa only [Bool.and_eq_true] using this

end Exegra.Core.Behav

namespace Exegra.V2.ProveKernel

open Exegra
open Exegra.V2.B
open Exegra.V2.ProveB
open Exegra.V2.ProveLive

/-! ### Writing a system as Lean -/

def intLean (n : Int) : String := if n < 0 then s!"({n})" else s!"{n}"

def tyLean : Core.Behav.Ty → String
  | .int lo hi => s!"(.int {intLean lo} {intLean hi})"
  | .bool => ".bool"
  | .str => ".str"
  | .lit => ".lit"
  | .num => ".num"

def atyLean : Core.Behav.ATy → String
  | .untyped => ".untyped"
  | .int lo hi => s!"(.int {intLean lo} {intLean hi})"

def aopLean : Core.Behav.AOp → String
  | .add => ".add" | .sub => ".sub" | .mul => ".mul" | .div => ".div" | .mod => ".mod"

def bopLean : Core.Behav.BOp → String
  | .arith op τ => s!"(.arith {aopLean op} {atyLean τ})"
  | .lt => ".lt" | .le => ".le" | .eq => ".eq" | .ne => ".ne"
  | .and => ".and" | .or => ".or" | .imp => ".imp" | .concat => ".concat"

def uopLean : Core.Behav.UOp → String
  | .neg τ => s!"(.neg {atyLean τ})"
  | .not => ".not"

def aggLean : Core.Behav.AggOp → String
  | .sum => ".sum" | .min => ".min" | .max => ".max"

/-- A `Fin` literal whose bound the kernel computes. -/
def finLean (i : Nat) : String := s!"⟨{i}, by decide⟩"

def rqLean : Core.Behav.RQuery → String
  | .inUse => ".inUse" | .waiting => ".waiting"
  | .inUseC c => s!"(.inUseC {c})" | .waitingC c => s!"(.waitingC {c})"

def reqKindLean : Res.ReqKind → String
  | .use => ".use" | .acquire => ".acquire"

def distLean0 : Core.Behav.Dist → String
  | .fixed v => s!"(.fixed {v})"
  | .choice vs => s!"(.choice {listLean toString vs})"
  | .uniform lo hi => s!"(.uniform {lo} {hi})"
  | .table pts => s!"(.table {listLean (fun (p : Nat × Nat) => s!"({p.1}, {p.2})") pts})"

/-- The group of a `Ref.one` or `Ref.uniq`. -/
def oneLean {S : Core.Behav.Sig} (g : List ((m : Fin S.machines) × Option (Fin (S.vars m).length))) : String :=
  listLean (fun (p : (m : Fin S.machines) × Option (Fin (S.vars m).length)) =>
    s!"⟨{finLean p.1.val}, {match p.2 with | some v => s!"some {finLean v.val}" | none => "none"}⟩") g

def refLean {S : Core.Behav.Sig} {me : Fin S.machines} : Core.Behav.Ref S me → String
  | .own v => s!"(.own {finLean v.val})"
  | .other m v => s!"(.other {finLean m.val} {finLean v.val})"
  | .state m => s!"(.state {finLean m.val})"
  | .field f τ => s!"(.field {f} {tyLean τ})"
  | .time => ".time"
  | .count g name => s!"(.count {listLean (fun (m : Fin S.machines) => finLean m.val) g} {name.quote})"
  | .agg op g => s!"(.agg {aggLean op} {listLean (fun (p : (m : Fin S.machines) × Fin (S.vars m).length) => s!"⟨{finLean p.1.val}, {finLean p.2.val}⟩") g})"
  | .absent τ => s!"(.absent {tyLean τ})"
  | .res r q => s!"(.res {r} {rqLean q})"
  | .one g τ => s!"(.one {oneLean g} {tyLean τ})"
  | .uniq g => s!"(.uniq {oneLean g})"
  | .key τ => s!"(.key {tyLean τ})"

def exprLean {S : Core.Behav.Sig} {me : Fin S.machines} : Core.Behav.Expr S me → String
  | .val v => s!"(.val {valLean v})"
  | .ref r => s!"(.ref {refLean r})"
  | .un op a => s!"(.un {uopLean op} {exprLean a})"
  | .bin op a b => s!"(.bin {bopLean op} {exprLean a} {exprLean b})"

def payloadLean {S : Core.Behav.Sig} {me : Fin S.machines} (pl : List (Nat × Core.Behav.Expr S me)) : String :=
  listLean (fun (p : Nat × Core.Behav.Expr S me) => s!"({p.1}, {exprLean p.2})") pl

def effectLean {S : Core.Behav.Sig} {me : Fin S.machines} : Core.Behav.Effect S me → String
  | .set v rhs => s!"(.set {finLean v.val} {exprLean rhs})"
  | .emit ev a pl => s!"(.emit {ev} {a} {payloadLean pl})"
  | .timer n a ev pl => s!"(.timer {n} {a} {ev} {payloadLean pl})"
  | .cancel n => s!"(.cancel {n})"
  | .reply ev a pl => s!"(.reply {ev} {a} {payloadLean pl})"
  | .request r cl u k th rf d st pl =>
    s!"(.request {r} {cl} {u} {reqKindLean k} {th} {optLean rf} {distLean0 d} ({st.1}, {st.2}) {payloadLean pl})"
  | .release r cl u => s!"(.release {r} {cl} {u})"

def transLean {S : Core.Behav.Sig} {me : Fin S.machines} (t : Core.Behav.Trans S me) : String :=
  s!"\{ src := {finLean t.src.val}, dst := {finLean t.dst.val}, event := {t.event}, guard := {exprLean t.guard}, " ++
  s!"effects := {listLean effectLean t.effects}, faultOnly := {t.faultOnly} }"

def fkindLean : Core.Behav.FKind → String
  | .drop => ".drop" | .lose => ".lose" | .delay => ".delay" | .retry => ".retry"
  | .duplicate => ".duplicate" | .enable => ".enable" | .disable => ".disable" | .inject => ".inject"
  | .setCapacity => ".setCapacity" | .setClassLimit => ".setClassLimit" | .collapse => ".collapse"
  | .scaleDemand => ".scaleDemand" | .replaceDemand => ".replaceDemand"

def occLean : Core.Behav.Occ → String
  | .any => ".any" | .exactly n => s!"(.exactly {n})" | .never => ".never"

def faultLean (f : Core.Behav.Fault) : String :=
  let window := match f.window with
    | none => "none"
    | some (a, u) => s!"(some ({a}, {optLean u}))"
  s!"\{ kind := {fkindLean f.kind}, event := {f.event}, targets := {listLean (fun (p : Nat × Nat) => s!"({p.1}, {p.2})") f.targets}, " ++
  s!"occ := {occLean f.occ}, by_ := {f.by_}, window := {window}, at_ := {f.at_}, " ++
  s!"payload := {listLean (fun (p : Nat × Core.Behav.Val) => s!"({p.1}, {valLean p.2})") f.payload}, " ++
  s!"res := {f.res}, cls := {f.cls}, capacity := {f.capacity}, limit := {f.limit}, num := {f.num}, " ++
  s!"den := {f.den}, effect := {f.effect}, demand := {distLeanW f.demand} }"

def classLean (c : Res.ClassDecl) : String :=
  s!"\{ id := {c.id.quote}, priority := {intLean c.priority}, reserved := {c.reserved}, limit := {optLean c.limit}, " ++
  s!"queueBound := {optLean c.queueBound}, maxWait := {optLean c.maxWait} }"

def overflowLean : Res.Overflow → String
  | .refuse => ".refuse" | .drop => ".drop" | .shedOldest => ".shedOldest"

def demandFactorLean : Res.DemandFactor → String
  | .none => ".none"
  | .table rows => s!"(.table {listLean (fun (r : Nat × Nat × Nat) => s!"({r.1}, {r.2.1}, {r.2.2})") rows})"
  | .usl an ad bn bd => s!"(.usl {an} {ad} {bn} {bd})"

/-- A resource declaration as a Lean term (WG-5683). -/
def resourceLean (d : Res.ResourceDecl) : String :=
  s!"\{ id := {d.id.quote}, kind := {d.kind.quote}, capacity := {d.capacity}, byPriority := {d.byPriority}, " ++
  s!"queueBound := {optLean d.queueBound}, overflow := {overflowLean d.overflow}, " ++
  s!"demandFactor := {demandFactorLean d.demandFactor}, classes := {listLean classLean d.classes}, strict := {d.strict} }"

def distLean : Core.Behav.Dist → String
  | .fixed v => s!"(.fixed {v})"
  | .choice vs => s!"(.choice {listLean toString vs})"
  | .uniform lo hi => s!"(.uniform {lo} {hi})"
  | .table pts => s!"(.table {listLean (fun (p : Nat × Nat) => s!"({p.1}, {p.2})") pts})"

/-- The claim expression of a system, elaborated as an expression of machine 0. -/
def claimExpr (i : Input) (sys : Core.Behav.Sys) (h : 0 < sys.sig.machines) (src : String) :
    Except String (Core.Behav.Expr sys.sig ⟨0, h⟩) :=
  let behs := i.behaviors
  let cx : Elab.Ctx := { input := i, behs, b := behs.getD 0 default, bi := 0, inst := 0 }
  match Elab.elabSrc ⟨0, h⟩ cx .bool src "the claim" with
  | .ok e => if e.ty? == some .bool then .ok e else .error "the claim expression is not Boolean in the calculus"
  | .error r => .error r.message

/-- A Lean module stating, with the kernel and the standard axioms only, the invariant of each
claim of a scenario whose reachable states the explorer closes. -/
def kernelModule (modName sysName : String) (i : Input) (sys : Core.Behav.Sys)
    (claims : List (String × String)) (bound cap : Nat) : Except String String := do
  let some L := Core.Behav.reachable (Core.Behav.Exec.gen sys) bound cap
    | throw "the explorer did not close the reachable states within the bound and the state budget"
  if h : 0 < sys.sig.machines then
    let n := sys.sig.machines
    let fins := Core.Behav.finList n
    let me : Fin sys.sig.machines := ⟨0, h⟩
    let mut out : Array String := #[]
    out := out.push s!"-- Generated by `exegra prove --module`. Do not edit; rewrite it with that command."
    out := out.push "import Exegra.ProveKernel"
    out := out.push ""
    out := out.push "/-!"
    out := out.push s!"The calculus system of scenario `{i.scenario.id}`, written out from the elaboration of its engine"
    out := out.push "input, and the invariants of its claims, checked by the kernel with the standard axioms only:"
    out := out.push "a closed-set certificate over the reachable states, checked by `decide`, and `checkClosed_sound`."
    out := out.push "-/"
    out := out.push ""
    out := out.push s!"namespace {modName}"
    out := out.push ""
    out := out.push "open Exegra.Core.Behav Exegra.Core.LTS"
    out := out.push ""
    out := out.push s!"def sig : Sig :=\n  \{ machines := {n},\n    vars := fun m => ({listLean (fun (m : Fin n) => listLean tyLean (sys.sig.vars m)) fins} : List (List Ty)).getD m.val [],\n    states := fun m => ({listLean (fun (m : Fin n) => listLean String.quote (sys.sig.states m)) fins} : List (List String)).getD m.val [] }"
    out := out.push ""
    for m in fins do
      let ts := sys.trans m
      out := out.push s!"def t{m.val} : List (Trans sig {finLean m.val}) :=\n  {listLean transLean ts}"
      out := out.push ""
    out := out.push s!"def tarr : List ((m : Fin sig.machines) × List (Trans sig m)) :=\n  {listLean (fun (m : Fin n) => s!"⟨{finLean m.val}, t{m.val}⟩") fins}"
    out := out.push ""
    out := out.push "def trans (m : Fin sig.machines) : List (Trans sig m) :=\n  match tarr[m.val]? with\n  | some p => if h : p.1 = m then h ▸ p.2 else []\n  | none => []"
    out := out.push ""
    out := out.push s!"/-- The calculus system of scenario `{i.scenario.id}`. -/"
    out := out.push s!"def {sysName} : Sys :=\n  \{ sig, trans, init := {cfgLean sys.init},\n    faults := {listLean faultLean sys.faults}, stopAt := {optLean sys.stopAt},\n    samples := {listLean (fun (p : Nat × Nat × Nat × Core.Behav.Dist) => s!"({p.1}, {p.2.1}, {p.2.2.1}, {distLean p.2.2.2})") sys.samples},\n    resources := {listLean resourceLean sys.resources} }"
    out := out.push ""
    out := out.push "/-- Its reachable states, as the explorer visited them. -/"
    out := out.push s!"def visited : List State :=\n  {listLean stateLean L}"
    out := out.push ""
    for (name, src) in claims do
      let e ← claimExpr i sys h src
      let _ := me
      let base := name.replace "-" "_"
      out := out.push s!"/-- The claim expression `{src}`, elaborated in the calculus. -/"
      out := out.push s!"def {base}_expr : Expr sig {finLean 0} := {exprLean e}"
      out := out.push ""
      out := out.push s!"theorem {base}_certificate :\n    checkClosed (Exec.enum {sysName}) visited (fun s => s.ok && claimTrue {base}_expr s) = true := by decide"
      out := out.push ""
      out := out.push s!"/-- **`{src}`** holds in every reachable state of scenario `{i.scenario.id}`, and no run fails. -/"
      out := out.push s!"theorem {base} :\n    (Sys.lts {sysName}).Invariant (fun s => s.ok = true ∧ claimTrue {base}_expr s = true) :=\n  invariant_of_kernel_certificate {base}_certificate"
      out := out.push ""
      out := out.push s!"/-- info: '{modName}.{base}' depends on axioms: [propext, Classical.choice, Quot.sound] -/\n#guard_msgs (whitespace := lax) in\n#print axioms {base}"
      out := out.push ""
    out := out.push s!"end {modName}"
    pure ("\n".intercalate out.toList ++ "\n")
  else throw "the scenario has no machine"

/-- `{input, module, sysName, claims: [{id, expr}], bound, maxStates}`: the text of the module. -/
def kernelModuleValue (req : Value) : Except String String := do
  let root ← match req with
    | .obj _ fs => pure fs
    | _ => throw "module: the request must be an object"
  let (i, sys, _) ← prepare (fieldOr root "input")
  let bound ← natField root "bound" "module"
  let cap ← natField root "maxStates" "module"
  let modName ← match fieldOr root "module" with | .str s => pure s | _ => throw "module: \"module\" must be a string"
  let sysName ← match fieldOr root "sysName" with | .str s => pure s | _ => throw "module: \"sysName\" must be a string"
  let claims ← match fieldOr root "claims" with
    | .arr _ xs => xs.mapM fun c => match c with
      | .obj _ fs => match fieldOr fs "id", fieldOr fs "expr" with
        | .str id, .str e => pure (id, e)
        | _, _ => throw "module: a claim needs \"id\" and \"expr\" strings"
      | _ => throw "module: a claim must be an object"
    | _ => throw "module: \"claims\" must be an array"
  let text ← kernelModule modName sysName i sys claims bound cap
  pure (Json.write (Encode.o [("text", .str text)]))

def runKernelModule (text : String) : Except String String := do kernelModuleValue (← Json.parse text)

end Exegra.V2.ProveKernel

/-- info: 'Exegra.Core.Behav.invariant_of_kernel_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.invariant_of_kernel_certificate
