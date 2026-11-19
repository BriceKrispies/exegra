import Exegra.Semantics

/-!
# Evaluating expressions fast

The definition's evaluator (`Exegra.eval`) builds an `Except` and a `Value` at every node of
the syntax tree, and resolves every reference from scratch. On an arithmetic expression of 8192
terms that is about 40,000 allocations per evaluation.

`evalFast` evaluates an expression the way the definition does, with one fast path: when every
node is a number literal, a reference to a number without a declared type, a negation or a `+`,
`-` or `*` (`numeric`), the value is computed on unboxed floats (`evalNum`), with no allocation,
and the result is the one the definition gives (`eval_numeric`). Typed (integer) arithmetic is
checked, so it always takes the definition's path. Any other expression is evaluated by the definition
itself. References are resolved by `resolveFast`, which looks the behavior's machine up once per
evaluation instead of once per reference (`resolveFast_eq`).
-/

namespace Exegra.Impl

/-- Is the expression arithmetic on untyped numbers only, under `res` and `tys`? -/
@[specialize] def numeric (res : List String → Value) (tys : TyEnv) : Ast → Bool
  | .lit (.num _) => true
  | .ref p =>
    match tys p, res p with
    | .none, .num _ => true
    | _, _ => false
  | .un .neg a => numeric res tys a
  | .bin .add a b => numeric res tys a && numeric res tys b
  | .bin .sub a b => numeric res tys a && numeric res tys b
  | .bin .mul a b => numeric res tys a && numeric res tys b
  | _ => false

/-- The value of a `numeric` expression, on unboxed floats. -/
@[specialize] def evalNum (res : List String → Value) : Ast → Float
  | .lit (.num x) => x
  | .ref p =>
    match res p with
    | .num x => x
    | _ => 0
  | .un .neg a => -(evalNum res a)
  | .bin .add a b => evalNum res a + evalNum res b
  | .bin .sub a b => evalNum res a - evalNum res b
  | .bin .mul a b => evalNum res a * evalNum res b
  | _ => 0

/-- The definition's evaluator, with the fast path for numeric expressions. -/
@[inline] def evalFast (res : List String → Value) (tys : TyEnv) (a : Ast) : Except String Value :=
  if numeric res tys a then .ok (.num (evalNum res a)) else eval res tys a

/-- `(objGet? fs key).getD .undef`, without building the options. -/
def varOf (fs : List (String × Value)) (key : String) : Value :=
  match fs with
  | [] => .undef
  | (k, v) :: rest => if k == key then v else varOf rest key

theorem varOf_eq (fs : List (String × Value)) (key : String) :
    varOf fs key = (objGet? fs key).getD .undef := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    obtain ⟨k, v⟩ := p
    simp only [varOf, objGet?, List.find?_cons]
    cases h : k == key <;> simp_all [objGet?]

/-- `resolve`, with the behavior's machine `m?` looked up once. -/
def resolveFast (m? : Option Machine) (view : Configuration) (bid : String) (payload : Value)
    (time : Float) : List String → Value
  | [name] =>
    if name = "time" then .num time
    else match m? with
      | some m => varOf m.vars name
      | none => .undef
  | path => resolve view bid payload time path

/-! ## Agreement with the definition -/

/-- A numeric expression has no declared type. -/
theorem staticTy_numeric (res : List String → Value) (tys : TyEnv) :
    ∀ a, numeric res tys a = true → staticTy tys a = .none
  | .lit v, _ => by simp [staticTy]
  | .ref p, h => by
    simp only [numeric] at h
    simp only [staticTy]
    split at h <;> simp_all
  | .un op a, h => by
    cases op with
    | not => simp [numeric] at h
    | neg =>
      simp only [numeric] at h
      simp [staticTy, staticTy_numeric res tys a h]
  | .bin op a b, h => by
    cases op <;> simp only [numeric, Bool.and_eq_true, Bool.false_eq_true] at h <;>
      (obtain ⟨ha, hb⟩ := h
       simp [staticTy, BinOp.isArith, staticTy_numeric res tys a ha, staticTy_numeric res tys b hb])

/-- **The fast path computes the definition's value.** -/
theorem eval_numeric (res : List String → Value) (tys : TyEnv) :
    ∀ a, numeric res tys a = true → eval res tys a = .ok (.num (evalNum res a))
  | .lit v, h => by
    cases v <;> simp_all [numeric, evalNum, eval]
  | .ref p, h => by
    simp only [numeric] at h
    simp only [eval, evalNum]
    split at h <;> simp_all
  | .un op a, h => by
    cases op with
    | not => simp [numeric] at h
    | neg =>
      simp only [numeric] at h
      have ha := eval_numeric res tys a h
      simp [eval, evalNum, ha, requireType, Value.typeName, numOf, bind, Except.bind,
        staticTy_numeric res tys a h, intResult]
  | .bin op a b, h => by
    have hs := staticTy_numeric res tys (.bin op a b) h
    cases op <;> simp only [numeric, Bool.and_eq_true, Bool.false_eq_true] at h <;>
      (obtain ⟨ha, hb⟩ := h
       simp [eval, evalNum, eval_numeric res tys a ha, eval_numeric res tys b hb, requireType,
         Value.typeName, numOf, bind, Except.bind, pure, Except.pure, hs, intResult]
       rfl)

theorem evalFast_eq (res : List String → Value) (tys : TyEnv) (a : Ast) :
    evalFast res tys a = eval res tys a := by
  unfold evalFast
  split
  · exact (eval_numeric res tys a ‹_›).symm
  · rfl

theorem resolveFast_eq (view : Configuration) (bid : String) (payload : Value) (time : Float) :
    resolveFast (view.machine? bid) view bid payload time = resolve view bid payload time := by
  funext path
  match path with
  | [name] =>
    simp only [resolveFast]
    by_cases h : name = "time"
    · subst h; simp [resolve]
    · simp only [h, ite_false, varOf_eq]
      unfold resolve
      split <;> simp_all
  | [] => rfl
  | [_, _] => rfl
  | _ :: _ :: _ :: _ => rfl

end Exegra.Impl
