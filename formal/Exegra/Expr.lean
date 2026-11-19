import Exegra.Value

/-
The expression language (`engine/exegra-engine/src/expr.rs`, which mirrors `src/core/expr.js`).

Grammar, lowest precedence first:

    implies :  a => b            (right associative)
    or      :  a || b
    and     :  a && b
    equality:  a == b, a != b
    compare :  a < b, a <= b, a > b, a >= b
    additive:  a + b, a - b
    multiply:  a * b, a / b, a % b
    unary   :  !a, -a
    primary :  number | 'string' | "string" | true | false | null | reference | ( expr )
    reference: ident ( '.' ident )*   where ident may contain inner hyphens

Error texts are part of the trace format and are reproduced verbatim. Places where the order of
evaluation decides which error is reported are marked ORDER below.
-/

namespace Exegra

inductive UnOp where
  | not | neg
  deriving BEq, Inhabited

inductive BinOp where
  | implies | or | and | eq | ne | lt | le | gt | ge | add | sub | mul | div | rem
  deriving BEq, Inhabited

def UnOp.name : UnOp → String
  | .not => "!"
  | .neg => "-"

def BinOp.name : BinOp → String
  | .implies => "=>" | .or => "||" | .and => "&&" | .eq => "==" | .ne => "!="
  | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .rem => "%"

def BinOp.ofName? : String → Option BinOp
  | "=>" => some .implies | "||" => some .or | "&&" => some .and
  | "==" => some .eq | "!=" => some .ne
  | "<" => some .lt | "<=" => some .le | ">" => some .gt | ">=" => some .ge
  | "+" => some .add | "-" => some .sub | "*" => some .mul | "/" => some .div | "%" => some .rem
  | _ => none

/-- A parsed expression. -/
inductive Ast where
  | lit (v : Value)
  | ref (path : List String)
  | un (op : UnOp) (a : Ast)
  | bin (op : BinOp) (a b : Ast)
  deriving Inhabited

/-! ## Tokenizer -/

inductive Tok where
  | num (x : Float)
  | str (s : String)
  | ident (s : String)
  | op (s : String)
  | eof
  deriving Inhabited

/-- The token as `${tk.v}` prints it in a message. -/
def Tok.text : Tok → String
  | .num x => Num.jsNumberToString x
  | .str s => s
  | .ident s => s
  | .op o => o
  | .eof => "null"

/-- Operators in the order the tokenizer tries them (two-character ones first). -/
def operators : List String :=
  ["=>", "||", "&&", "==", "!=", "<=", ">=", "<", ">", "+", "-", "*", "/", "%", "!", "(", ")", "."]

/-- ASCII letter or `_`. -/
def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'
/-- ASCII letter, digit or `_`. -/
def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- The rest of an identifier after its first character: identifier characters, then any number
of `-` followed by an identifier start and identifier characters. Returns the characters taken
and the remainder. -/
def identTail : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if isIdentChar c then
      let (t, r) := identTail cs
      (c :: t, r)
    else match c, cs with
      | '-', d :: ds =>
        if isIdentStart d then
          let (t, r) := identTail ds
          ('-' :: d :: t, r)
        else ([], c :: cs)
      | _, _ => ([], c :: cs)

/-- Split off the longest prefix of characters satisfying `p`. -/
def spanChars (p : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs => if p c then let (t, r) := spanChars p cs; (c :: t, r) else ([], c :: cs)

/-- Split at the first occurrence of `q`: the text before it and the text after it. -/
def untilQuote (q : Char) : List Char → Option (List Char × List Char)
  | [] => none
  | c :: cs => if c == q then some ([], cs) else (untilQuote q cs).map fun (t, r) => (c :: t, r)

/-- The first operator that prefixes the input, in `operators` order. -/
def matchOperator (cs : List Char) : Option String :=
  operators.find? fun o => o.toList.isPrefixOf cs

/-- Tokenize. Every iteration consumes at least one character, so `fuel` = length + 1 always
suffices. -/
def tokenizeAux : Nat → List Char → List Tok → Except String (List Tok)
  | 0, _, acc => .ok (acc.reverse ++ [.eof])
  | _ + 1, [], acc => .ok (acc.reverse ++ [.eof])
  | fuel + 1, c :: cs, acc =>
    if c == ' ' || c == '\t' || c == '\n' || c == '\r' then tokenizeAux fuel cs acc
    else if c == '"' || c == '\'' then
      match untilQuote c cs with
      | none => .error "Unterminated string literal"
      | some (body, rest) => tokenizeAux fuel rest (.str (String.ofList body) :: acc)
    else if c.isDigit then
      -- NUMBER = /\d+(?:\.\d+)?/
      let (intPart, rest) := spanChars Char.isDigit (c :: cs)
      let (frac, rest) := match rest with
        | '.' :: d :: ds => if d.isDigit then spanChars Char.isDigit (d :: ds) else ([], rest)
        | _ => ([], rest)
      let x := Num.ofDecimal false (Num.digitsToNat (intPart ++ frac)) (-(frac.length : Int))
      tokenizeAux fuel rest (.num x :: acc)
    else if isIdentStart c then
      let (t, rest) := identTail cs
      tokenizeAux fuel rest (.ident (String.ofList (c :: t)) :: acc)
    else match matchOperator (c :: cs) with
      | some o => tokenizeAux fuel ((c :: cs).drop o.length) (.op o :: acc)
      | none => .error s!"Unexpected character '{c}'"

def tokenize (src : String) : Except String (List Tok) :=
  let cs := src.toList
  tokenizeAux (cs.length + 1) cs []

/-! ## Parser

Recursive descent over the token list. Every call either consumes a token or moves one
precedence level up (at most eight in a row), so the nesting depth is below
`10 * (tokens + 2)`, which is the fuel given; running out of fuel cannot happen. -/

/-- Binary operators of a precedence level, lowest level first. -/
def levelOps : Nat → List String
  | 0 => ["=>"]
  | 1 => ["||"]
  | 2 => ["&&"]
  | 3 => ["==", "!="]
  | 4 => ["<", "<=", ">", ">="]
  | 5 => ["+", "-"]
  | 6 => ["*", "/", "%"]
  | _ => []

def headTok : List Tok → Tok
  | [] => .eof
  | t :: _ => t

def isOp (ts : List Tok) (o : String) : Bool :=
  match headTok ts with
  | .op p => p == o
  | _ => false

abbrev PR := Except String (Ast × List Tok)

/-- The rest of a reference after its first name: `( '.' ident )*`. -/
def refRest : List Tok → List String → Except String (List String × List Tok)
  | .op "." :: .ident n :: ts, acc => refRest ts (n :: acc)
  | .op "." :: _ :: _, _ => .error "Expected a name after \".\""
  | [.op "."], _ => .error "Expected a name after \".\""
  | ts, acc => .ok (acc.reverse, ts)

mutual
def binary : Nat → Nat → List Tok → PR
  | 0, _, _ => .error "Malformed expression"
  | fuel + 1, level, ts =>
    if level ≥ 7 then unary fuel ts
    else match binary fuel (level + 1) ts with
      | .error e => .error e
      | .ok (left, ts) => binLoop fuel level left ts

def binLoop : Nat → Nat → Ast → List Tok → PR
  | 0, _, _, _ => .error "Malformed expression"
  | fuel + 1, level, left, ts =>
    match headTok ts with
    | .op o =>
      if (levelOps level).contains o then
        match BinOp.ofName? o with
        | none => .error "Malformed expression"
        | some .implies =>
          -- `=>` is right associative: the right operand is parsed at the same level.
          match binary fuel level ts.tail with
          | .error e => .error e
          | .ok (right, ts) => .ok (.bin .implies left right, ts)
        | some bop =>
          match binary fuel (level + 1) ts.tail with
          | .error e => .error e
          | .ok (right, ts) => binLoop fuel level (.bin bop left right) ts
      else .ok (left, ts)
    | _ => .ok (left, ts)

def unary : Nat → List Tok → PR
  | 0, _ => .error "Malformed expression"
  | fuel + 1, ts =>
    if isOp ts "!" || isOp ts "-" then
      let op := if isOp ts "!" then UnOp.not else UnOp.neg
      match unary fuel ts.tail with
      | .error e => .error e
      | .ok (a, ts) => .ok (.un op a, ts)
    else primary fuel ts

def primary : Nat → List Tok → PR
  | 0, _ => .error "Malformed expression"
  | fuel + 1, ts =>
    match ts with
    | [] => .error "Unexpected end of expression"
    | .eof :: _ => .error "Unexpected end of expression"
    | .num x :: ts => .ok (.lit (.num x), ts)
    | .str s :: ts => .ok (.lit (.str s), ts)
    | .ident "true" :: ts => .ok (.lit (.bool true), ts)
    | .ident "false" :: ts => .ok (.lit (.bool false), ts)
    | .ident "null" :: ts => .ok (.lit .null, ts)
    | .ident n :: ts =>
      match refRest ts [n] with
      | .error e => .error e
      | .ok (path, ts) => .ok (.ref path, ts)
    | .op "(" :: ts =>
      match binary fuel 0 ts with
      | .error e => .error e
      | .ok (inner, ts) =>
        if isOp ts ")" then .ok (inner, ts.tail) else .error "Expected \")\""
    | t :: _ => .error s!"Unexpected \"{t.text}\""
end

/-- Parse an expression; the error is the parser's message. -/
def parseExpr (src : String) : Except String Ast := do
  let ts ← tokenize src
  let (ast, rest) ← binary (10 * (ts.length + 2)) 0 ts
  match headTok rest with
  | .eof => pure ast
  | t => throw s!"Unexpected \"{t.text}\""

/-! ## Evaluator -/

def requireType (v : Value) (ty op : String) : Except String Unit :=
  if v.typeName == ty then .ok () else .error s!"Operator \"{op}\" needs a {ty}, got {v.typeName}"

def isTrue : Value → Bool
  | .bool true => true
  | _ => false

def numOf : Value → Float
  | .num x => x
  | _ => Float.nan

def BinOp.isArith : BinOp → Bool
  | .add | .sub | .mul | .div | .rem => true
  | _ => false

/-- The declared type an arithmetic expression is computed in: that of its first typed operand
(a literal takes the type of the other operand). Only arithmetic and references have one. -/
def staticTy (tys : TyEnv) : Ast → STy
  | .ref p => tys p
  | .un .neg a => staticTy tys a
  | .bin op a b =>
    if op.isArith then
      match staticTy tys a with
      | .none => staticTy tys b
      | t => t
    else .none
  | _ => .none

/-- Is `x` a value of the integer type `k`: a whole number within its range? -/
def IntKind.holds (k : IntKind) (x : Float) : Bool :=
  x.floor == x && k.lo ≤ x && x ≤ k.hi

/-- The result of an arithmetic operator in type `ty` (WG-4902): untyped arithmetic is IEEE;
integer arithmetic checks that both operands and the exact result `r` are values of the type,
and otherwise ends the step with an error. On integers within `2^53` a double computes `+`, `-`
and `*` exactly whenever the exact result is within `2^53`, and rounds monotonically otherwise,
so a result outside the range is never mistaken for one inside it. -/
def intResult (ty : STy) (op : String) (x y r : Float) : Except String Value :=
  match ty with
  | .int k =>
    if !(k.holds x) then .error s!"Operator \"{op}\" on {k.name}: operand {Num.jsNumberToString x} is not a {k.name}"
    else if !(k.holds y) then .error s!"Operator \"{op}\" on {k.name}: operand {Num.jsNumberToString y} is not a {k.name}"
    else if !(k.holds r) then .error s!"Integer overflow: \"{op}\" on {k.name} gives {Num.jsNumberToString r}, outside {Num.jsNumberToString k.lo}..{Num.jsNumberToString k.hi}"
    -- `r + 0` is `r` except that `-0` becomes `0`: an integer has no negative zero.
    else .ok (.num (r + 0))
  | _ => .ok (.num r)

/-- Division in type `ty`: integer division truncates toward zero. `x - fmod x y` is a multiple
of `y` no larger than `x` in magnitude, so it and the quotient are exact. -/
def divIn (ty : STy) (x y : Float) : Float :=
  match ty with
  | .int _ => (x - Num.fmod x y) / y
  | _ => x / y

/-- Evaluate. `resolve` maps a reference path to its value, `undef` when it has none; `tys` gives
the declared types of references (`TyEnv.untyped` for none). An absent value of an option type reads as
`null`; any other absent value is an unknown reference. -/
def eval (resolve : List String → Value) (tys : TyEnv) : Ast → Except String Value
  | .lit v => .ok v
  | .ref path =>
    match resolve path with
    | .undef =>
      match tys path with
      | .option => .ok .null
      | _ => .error s!"Unknown reference \"{".".intercalate path}\""
    | v => .ok v
  | .un op a => do
    let av ← eval resolve tys a
    match op with
    | .not => requireType av "boolean" "!"; pure (.bool !(isTrue av))
    | .neg =>
      requireType av "number" "-"
      intResult (staticTy tys a) "-" (numOf av) 0 (-(numOf av))
  | .bin op a b =>
    if op == .and || op == .or || op == .implies then do
      -- ORDER: the left operand is evaluated and type-checked first; the right one is neither
      -- evaluated nor type-checked when the left one decides.
      let av ← eval resolve tys a
      requireType av "boolean" op.name
      let aTrue := isTrue av
      if op == .and && !aTrue then return .bool false
      if op == .or && aTrue then return .bool true
      if op == .implies && !aTrue then return .bool true
      let bv ← eval resolve tys b
      requireType bv "boolean" op.name
      pure bv
    else do
      -- ORDER: both operands are evaluated, left first, before any type check.
      let av ← eval resolve tys a
      let bv ← eval resolve tys b
      if op == .eq then return .bool (av.eqv bv)
      if op == .ne then return .bool !(av.eqv bv)
      if op == .add then
        match av, bv with
        | .str x, .str y => return .str (x ++ y)
        | _, _ => pure ()
      -- ORDER: the left operand's type is checked before the right one's.
      requireType av "number" op.name
      requireType bv "number" op.name
      let x := numOf av
      let y := numOf bv
      let ty := staticTy tys (.bin op a b)
      match op with
      | .lt => pure (.bool (decide (x < y)))
      | .le => pure (.bool (decide (x ≤ y)))
      | .gt => pure (.bool (decide (x > y)))
      | .ge => pure (.bool (decide (x ≥ y)))
      | .add => intResult ty "+" x y (x + y)
      | .sub => intResult ty "-" x y (x - y)
      | .mul => intResult ty "*" x y (x * y)
      -- ORDER: division by zero (also by -0) is reported after both type checks.
      | .div => if y == 0 then throw "Division by zero" else intResult ty "/" x y (divIn ty x y)
      | .rem => if y == 0 then throw "Division by zero" else intResult ty "%" x y (Num.fmod x y)
      | _ => throw "Malformed expression"

end Exegra
