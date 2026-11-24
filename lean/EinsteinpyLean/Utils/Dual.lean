/-!
# Model of `einsteinpy.utils.dual`

Mirrors `src/einsteinpy/utils/dual.py` at commit `63e1c54`. This file uses only core Lean.

There are two layers in this file.

* The generic layer (`Dual.add`, `Dual.mul`, ...) works over any type with `+ - * neg`. It has no
  errors, so `Spec.lean` can instantiate it with `ℝ` and prove the ring laws and the derivative rules.
* The Python layer (`Py.*`) works on `Float` and mirrors what Python does, including the
  exceptions (`ZeroDivisionError`, `OverflowError`, `TypeError`, `AttributeError`), the
  float-to-int conversion of Python ints, the complex results of a negative base to a
  fractional power, and the different rules of `numpy.float64`.

Python floats and Lean `Float` are both IEEE doubles, and `Float.pow`, `Float.sin` and so on
call the same C library, so the difftest compares bit patterns, not tolerances.
-/

namespace EinsteinpyLean.Utils

/-- The Python exception classes that the mirrored code can raise. `tag` is the class name. -/
inductive Exc where
  /-- `float` division or `0.0 ** negative`. -/
  | zeroDivision
  /-- `float ** float` out of range, or an int too large for a float. -/
  | overflow
  /-- `float(complex)`, `float(DualNumber)` and `x ** DualNumber`. -/
  | typeError
  /-- `other.val` on a plain number in `DualNumber.__eq__`. -/
  | attributeError
  /-- `_diff_g` argument checks. The message is the Python message. -/
  | valueError (msg : String)
  /-- numpy indexing out of range. -/
  | indexError
  deriving Repr, BEq, DecidableEq, Inhabited

def Exc.tag : Exc → String
  | .zeroDivision => "ZeroDivisionError"
  | .overflow => "OverflowError"
  | .typeError => "TypeError"
  | .attributeError => "AttributeError"
  | .valueError m => "ValueError:" ++ m
  | .indexError => "IndexError"

/-- `a + b ε` with `ε² = 0`. -/
structure Dual (α : Type) where
  val : α
  deriv : α
  deriving Repr, BEq, DecidableEq, Inhabited

/-! ## Generic layer, no errors -/

namespace Dual

variable {α : Type} [Add α] [Sub α] [Mul α] [Neg α]

/-- dual.py:48-51 `__add__` with a `DualNumber`. -/
def add (a b : Dual α) : Dual α := ⟨a.val + b.val, a.deriv + b.deriv⟩
/-- dual.py:53 `__add__` with a plain number (also `__radd__`). -/
def addS (a : Dual α) (c : α) : Dual α := ⟨a.val + c, a.deriv⟩
/-- dual.py:58-61 `__sub__` with a `DualNumber`. -/
def sub (a b : Dual α) : Dual α := ⟨a.val - b.val, a.deriv - b.deriv⟩
/-- dual.py:63 `__sub__` with a plain number. -/
def subS (a : Dual α) (c : α) : Dual α := ⟨a.val - c, a.deriv⟩
/-- dual.py:70-75 `__mul__` with a `DualNumber`. -/
def mul (a b : Dual α) : Dual α := ⟨a.val * b.val, a.deriv * b.val + a.val * b.deriv⟩
/-- dual.py:77 `__mul__` with a plain number (also `__rmul__`). -/
def mulS (a : Dual α) (c : α) : Dual α := ⟨a.val * c, a.deriv * c⟩
/-- dual.py:121 `__neg__`. -/
def neg (a : Dual α) : Dual α := ⟨-a.val, -a.deriv⟩
/-- dual.py:66 `__rsub__` with a plain number: `DualNumber(c, 0) - self`, where `0` is `zero`. -/
def rsubS (a : Dual α) (c zero : α) : Dual α := sub ⟨c, zero⟩ a

/-- The quotient of dual.py:87-90 without the zero cases: the quotient rule. -/
def divRule {α : Type} [Sub α] [Mul α] [Div α] (a b : Dual α) : Dual α :=
  ⟨a.val / b.val, (a.deriv * b.val - a.val * b.deriv) / (b.val * b.val)⟩

/-- dual.py:124 `sin`, with `sin` and `cos` of the number type supplied. -/
def sinWith (sin cos : α → α) (a : Dual α) : Dual α := ⟨sin a.val, a.deriv * cos a.val⟩
/-- dual.py:127 `cos`. -/
def cosWith (sin cos : α → α) (a : Dual α) : Dual α := ⟨cos a.val, -a.deriv * sin a.val⟩
/-- dual.py:133 `exp`. -/
def expWith (exp : α → α) (a : Dual α) : Dual α := ⟨exp a.val, a.deriv * exp a.val⟩
/-- dual.py:130 `log`. -/
def logWith [Div α] (log : α → α) (a : Dual α) : Dual α := ⟨log a.val, a.deriv / a.val⟩
/-- dual.py:118 `__pow__`, with the power function and the exponent `p`, `p - 1` supplied. -/
def powWith (pw : α → α → α) (p pm1 : α) (a : Dual α) : Dual α :=
  ⟨pw a.val p, a.deriv * p * pw a.val pm1⟩

end Dual

/-! ## Python layer -/

namespace Py

/-- The second operand of a scalar operation: a Python `float`, a Python `int`, or a
`numpy.float64`. Python floats raise on division by zero and numpy floats do not. -/
inductive Scalar where
  | py (x : Float)
  | int (n : Int)
  | np (x : Float)
  deriving Repr, BEq, Inhabited

/-- `float(n)` for a Python int: exact below `2^53`, and an `OverflowError` once the int
rounds to `2^1024` (the difftest never uses an int between those). -/
def intToFloat (n : Int) : Except Exc Float :=
  if n.natAbs ≥ 2 ^ 1024 - 2 ^ 970 then throw .overflow else pure (Float.ofInt n)

def Scalar.toFloat : Scalar → Except Exc Float
  | .py x => pure x
  | .int n => intToFloat n
  | .np x => pure x

/-- Python `x / y` on floats (`ZeroDivisionError` for a zero divisor). -/
def fdiv (x y : Float) : Except Exc Float :=
  if y == 0 then throw .zeroDivision else pure (x / y)

/-- Python `float % 2 == 1`, the `DOUBLE_IS_ODD_INTEGER` test of `float_pow`. -/
def isOddInteger (x : Float) : Bool :=
  let a := x.abs
  a - 2 * (a / 2).floor == 1

/-- Python `x ** y` for two floats (CPython `float_pow`). `none` stands for a complex result,
the value for a negative base and a fractional exponent. -/
def powF (x y : Float) : Except Exc (Option Float) :=
  if y == 0 then pure (some 1)
  else if x.isNaN then pure (some x)
  else if y.isNaN then pure (some (if x == 1 then 1 else y))
  else if y.isInf then
    let ax := x.abs
    pure (some (if ax == 1 then 1 else if decide (y > 0) == decide (ax > 1) then y.abs else 0))
  else if x.isInf then
    let odd := isOddInteger y
    if y > 0 then pure (some (if odd then x else x.abs))
    else pure (some (if odd then (if x > 0 then 0 else -0.0) else 0))
  else if x == 0 then
    if y < 0 then throw .zeroDivision
    else pure (some (if isOddInteger y then x else 0))
  else if x < 0 && y != y.floor then
    -- complex_pow: an overflowing modulus is an OverflowError, otherwise the value is complex
    if (Float.pow x.abs y).isInf then throw .overflow else pure none
  else
    let neg := x < 0 && isOddInteger y
    let ax := x.abs
    if ax == 1 then pure (some (if neg then -1 else 1))
    else
      let r := Float.pow ax y
      if r.isInf then throw .overflow else pure (some (if neg then -r else r))

/-- `x ** y` where a plain float result is needed (`other.val ** 2`). -/
def powReal (x y : Float) : Except Exc Float := do
  match ← powF x y with
  | some r => pure r
  | none => throw .typeError

/-- `DualNumber(a, b)`: `float(a)` and `float(b)`, the arguments being plain numbers. -/
def mk (a b : Scalar) : Except Exc (Dual Float) := do
  let a ← a.toFloat
  let b ← b.toFloat
  pure ⟨a, b⟩

/-- dual.py:47-53 `__add__` and `__radd__`. -/
def addD (a b : Dual Float) : Dual Float := Dual.add a b
def addS (a : Dual Float) (c : Scalar) : Except Exc (Dual Float) := do pure (Dual.addS a (← c.toFloat))
def subD (a b : Dual Float) : Dual Float := Dual.sub a b
def subS (a : Dual Float) (c : Scalar) : Except Exc (Dual Float) := do pure (Dual.subS a (← c.toFloat))
def mulD (a b : Dual Float) : Dual Float := Dual.mul a b
def mulS (a : Dual Float) (c : Scalar) : Except Exc (Dual Float) := do pure (Dual.mulS a (← c.toFloat))

/-- dual.py:66-68 `__rsub__` with a plain number: `DualNumber(other, 0) - self`. -/
def rsubS (a : Dual Float) (c : Scalar) : Except Exc (Dual Float) := do
  pure (Dual.sub ⟨← c.toFloat, 0⟩ a)

/-- dual.py:79-90 `__truediv__` with a `DualNumber`. -/
def divD (a b : Dual Float) : Except Exc (Dual Float) := do
  if a.val == 0 && b.val == 0 then
    pure ⟨← fdiv a.deriv b.deriv, 0⟩
  else
    let v ← fdiv a.val b.val
    let num := a.deriv * b.val - a.val * b.deriv
    let sq ← powReal b.val 2
    pure ⟨v, ← fdiv num sq⟩

/-- dual.py:92 `__truediv__` with a plain number: `self.val / other` for a Python number,
numpy division for a `numpy.float64`. -/
def divS (a : Dual Float) (c : Scalar) : Except Exc (Dual Float) :=
  match c with
  | .np x => pure ⟨a.val / x, a.deriv / x⟩
  | _ => do
    let x ← c.toFloat
    pure ⟨← fdiv a.val x, ← fdiv a.deriv x⟩

/-- dual.py:105-107 `__rtruediv__` with a plain number: `DualNumber(other, 0).__truediv__(self)`. -/
def rdivS (a : Dual Float) (c : Scalar) : Except Exc (Dual Float) := do
  divD ⟨← c.toFloat, 0⟩ a

/-- dual.py:97-103 `__rtruediv__` called directly with a `DualNumber`. -/
def rdivD (a other : Dual Float) : Except Exc (Dual Float) :=
  if a.val == 0 && other.val == 0 then do pure ⟨← fdiv other.deriv a.deriv, 0⟩
  else do
    let v ← fdiv other.val a.val
    let num := other.deriv * a.val - other.val * a.deriv
    let sq ← powReal a.val 2
    pure ⟨v, ← fdiv num sq⟩

/-- dual.py:109-110 `__rsub__` called directly with a `DualNumber`. -/
def rsubD (a other : Dual Float) : Dual Float := Dual.sub other a

/-- dual.py:112-113 `__eq__` with a `DualNumber`. -/
def eqD (a b : Dual Float) : Bool := a.val == b.val && a.deriv == b.deriv
/-- `__eq__` with a plain number reads `other.val`: `AttributeError`. -/
def eqS : Except Exc Bool := throw .attributeError

def negD (a : Dual Float) : Dual Float := Dual.neg a

/-- dual.py:123-124 `__pow__`: `DualNumber(val ** p, deriv * p * val ** (p - 1))`. -/
def powS (a : Dual Float) (p : Scalar) : Except Exc (Dual Float) := do
  let pf ← p.toFloat
  match p with
  | .np y =>
    pure ⟨Float.pow a.val y, a.deriv * y * Float.pow a.val (y - 1)⟩
  | _ =>
    let pm1 : Float ← match p with
      | .int n => intToFloat (n - 1)
      | _ => pure (pf - 1)
    let r1 ← powF a.val pf
    let r2 ← powF a.val pm1
    match r1, r2 with
    | some v, some w => pure ⟨v, a.deriv * pf * w⟩
    | _, _ => throw .typeError

/-- dual.py:126 `sin`. -/
def sinD (a : Dual Float) : Dual Float := Dual.sinWith Float.sin Float.cos a
def cosD (a : Dual Float) : Dual Float := Dual.cosWith Float.sin Float.cos a
def expD (a : Dual Float) : Dual Float := Dual.expWith Float.exp a
/-- dual.py:134 `log`: `np.log` then `self.deriv / self.val`, a Python float division. -/
def logD (a : Dual Float) : Except Exc (Dual Float) := do
  pure ⟨Float.log a.val, ← fdiv a.deriv a.val⟩
/-- dual.py:130 `tan`: `np.sin(self) / np.cos(self)`, which calls `self.sin()` and `self.cos()`. -/
def tanD (a : Dual Float) : Except Exc (Dual Float) := divD (sinD a) (cosD a)

end Py

/-! ## `_deriv` and a small expression language

The difftest builds random expressions out of `DualNumber` operations. The program is a list of
instructions on a stack that starts with the single dual `x`. -/

namespace Py

inductive Instr where
  | dup | add | sub | mul | div | neg
  | sin | cos | tan | log | exp
  | pow (c : Scalar)
  /-- `t + c`, `c + t`, `t - c`, `c - t`, `t * c`, `c * t`, `t / c`, `c / t`. -/
  | addc (c : Scalar) | raddc (c : Scalar) | subc (c : Scalar) | rsubc (c : Scalar)
  | mulc (c : Scalar) | rmulc (c : Scalar) | divc (c : Scalar) | rdivc (c : Scalar)
  /-- Return a plain number instead of a dual. -/
  | retc (c : Scalar)
  deriving Repr, Inhabited

/-- What a function can return: a dual or a plain number. -/
inductive Out where
  | dual (d : Dual Float)
  | num (x : Float)

def step (st : List (Dual Float)) : Instr → Except Exc (List (Dual Float))
  | .dup => match st with | a :: r => pure (a :: a :: r) | [] => pure []
  | .add => match st with | b :: a :: r => pure (addD a b :: r) | _ => pure st
  | .sub => match st with | b :: a :: r => pure (subD a b :: r) | _ => pure st
  | .mul => match st with | b :: a :: r => pure (mulD a b :: r) | _ => pure st
  | .div => match st with | b :: a :: r => do pure ((← divD a b) :: r) | _ => pure st
  | .neg => match st with | a :: r => pure (negD a :: r) | _ => pure st
  | .sin => match st with | a :: r => pure (sinD a :: r) | _ => pure st
  | .cos => match st with | a :: r => pure (cosD a :: r) | _ => pure st
  | .tan => match st with | a :: r => do pure ((← tanD a) :: r) | _ => pure st
  | .log => match st with | a :: r => do pure ((← logD a) :: r) | _ => pure st
  | .exp => match st with | a :: r => pure (expD a :: r) | _ => pure st
  | .pow c => match st with | a :: r => do pure ((← powS a c) :: r) | _ => pure st
  | .addc c => match st with | a :: r => do pure ((← addS a c) :: r) | _ => pure st
  | .raddc c => match st with | a :: r => do pure ((← addS a c) :: r) | _ => pure st
  | .subc c => match st with | a :: r => do pure ((← subS a c) :: r) | _ => pure st
  | .rsubc c => match st with | a :: r => do pure ((← rsubS a c) :: r) | _ => pure st
  | .mulc c => match st with | a :: r => do pure ((← mulS a c) :: r) | _ => pure st
  | .rmulc c => match st with | a :: r => do pure ((← mulS a c) :: r) | _ => pure st
  | .divc c => match st with | a :: r => do pure ((← divS a c) :: r) | _ => pure st
  | .rdivc c => match st with | a :: r => do pure ((← rdivS a c) :: r) | _ => pure st
  | .retc _ => pure st

/-- Run a program on `x`. A trailing `retc` returns a plain number. -/
def run (prog : List Instr) (x : Dual Float) : Except Exc Out := do
  let mut st := [x]
  let mut ret : Option Float := none
  for i in prog do
    st ← step st i
    match i with
    | .retc c => ret := some (← c.toFloat)
    | _ => pure ()
  match ret with
  | some r => pure (.num r)
  | none => match st with
    | a :: _ => pure (.dual a)
    | [] => pure (.num 0)

/-- dual.py:137-157 `_deriv(func, x)`: the derivative of a dual result, `0.0` for a plain number. -/
def derivOf (prog : List Instr) (x : Float) : Except Exc Float := do
  match ← run prog ⟨x, 1⟩ with
  | .dual d => pure d.deriv
  | .num _ => pure 0

end Py

/-! ## `_diff_g` and `_jacobian_g` -/

namespace Py

/-- An entry of the numpy object array that a metric function returns. -/
inductive Elem where
  | dual (d : Dual Float)
  | flt (x : Float)
  | int (n : Int)
  deriving Inhabited

/-- A metric function: it gets the four dual coordinates and its parameters. -/
abbrev Metric := Array (Dual Float) → List Float → Except Exc (Array (Array Elem))

/-- `indices` is a tuple (numpy element access) or a list (numpy fancy indexing of rows). -/
inductive Idx where
  | tuple (l : List Int)
  | list (l : List Int)

/-- `wrt` is an int, or an integral float, which passes the membership test and then fails as a
list index. -/
inductive Wrt where
  | int (n : Int)
  | flt (x : Float)

/-- Python's rendering of an integral float for the message of `wrt`. -/
def fmtIntegralFloat (x : Float) : String :=
  let n : Int := if x < 0 then -(Int.ofNat (x.abs.toUInt64.toNat)) else Int.ofNat x.toUInt64.toNat
  (if x == 0 && x.toBits != 0 then "-0" else toString n) ++ ".0"

def Wrt.render : Wrt → String
  | .int n => toString n
  | .flt x => fmtIntegralFloat x

def Wrt.inRange : Wrt → Bool
  | .int n => n == 0 || n == 1 || n == 2 || n == 3
  | .flt x => x == 0 || x == 1 || x == 2 || x == 3

/-- numpy index `k` on an axis of length 4. -/
def npIndex (k : Int) : Except Exc Nat :=
  if -4 ≤ k && k < 4 then pure (if k < 0 then (k + 4).toNat else k.toNat) else throw .indexError

/-- dual.py:160-211 `_diff_g`. -/
def diffG (g : Metric) (prm : List Float) (coords : List Float) (idx : Idx) (wrt : Wrt) :
    Except Exc Float := do
  if !wrt.inRange then
    throw (.valueError s!"wrt takes values from [0, 1, 2, 3]. Supplied value: {wrt.render}")
  let len := match idx with | .tuple l => l.length | .list l => l.length
  if len != 2 then
    throw (.valueError "indices must be a 2-tuple containing indices for the metric.")
  if coords.length < 4 then throw .indexError
  let w : Nat ← match wrt with
    | .int n => pure n.toNat
    | .flt _ => throw .typeError
  let dc : Array (Dual Float) := #[
    ⟨coords[0]!, 0⟩, ⟨coords[1]!, 0⟩, ⟨coords[2]!, 0⟩, ⟨coords[3]!, 0⟩]
  let dc := dc.set! w ⟨coords[w]!, 1⟩
  let m ← g dc prm
  match idx with
  | .tuple [i, j] =>
    let i ← npIndex i
    let j ← npIndex j
    match (m[i]!)[j]! with
    | .dual d => pure d.deriv
    | _ => pure 0
  | .list l =>
    let _ ← l.mapM npIndex
    pure 0
  | _ => pure 0

/-- dual.py:214-240 `_jacobian_g`: the upper triangle through `_diff_g`, then
`J + J.T - diag(diag(J))` in floating point. -/
def jacobianG (g : Metric) (prm : List Float) (coords : List Float) (wrt : Wrt) :
    Except Exc (Array Float) := do
  let mut j : Array Float := Array.replicate 16 0
  for a in List.range 4 do
    for b in List.range 4 do
      if a ≤ b then
        j := j.set! (4 * a + b) (← diffG g prm coords (.tuple [(a : Int), (b : Int)]) wrt)
  let mut out : Array Float := Array.replicate 16 0
  for a in List.range 4 do
    for b in List.range 4 do
      let d := if a == b then j[4 * a + b]! else 0
      out := out.set! (4 * a + b) ((j[4 * a + b]! + j[4 * b + a]!) - d)
  pure out

end Py

end EinsteinpyLean.Utils
