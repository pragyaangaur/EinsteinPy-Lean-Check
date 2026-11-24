/-!
# Model of `einsteinpy.utils.exceptions` and `einsteinpy.units.primitive`

Mirrors `src/einsteinpy/utils/exceptions.py` and `src/einsteinpy/units.py` at commit `63e1c54`.
Core Lean only. The arguments are Python values without floats, because Python's float
formatting is not part of this model.
-/

namespace EinsteinpyLean.Utils

/-- A Python value that `str` and `repr` can be applied to. -/
inductive PyVal where
  | str (s : String)
  | int (n : Int)
  | bool (b : Bool)
  | none
  | list (l : List PyVal)
  | tuple (l : List PyVal)

/-- Python `repr` of a `str`: single quotes unless the text has `'` and no `"`. -/
def reprStr (s : String) : String :=
  let q := if s.contains '\'' && !s.contains '"' then '"' else '\''
  let esc (c : Char) : String :=
    if c == '\\' then "\\\\"
    else if c == q then "\\" ++ String.singleton c
    else if c == '\n' then "\\n"
    else if c == '\t' then "\\t"
    else if c == '\r' then "\\r"
    else if c.toNat < 32 || c.toNat == 127 then
      let d := Nat.toDigits 16 c.toNat
      "\\x" ++ String.ofList (List.replicate (2 - d.length) '0' ++ d)
    else String.singleton c
  String.singleton q ++ String.join (s.toList.map esc) ++ String.singleton q

mutual
/-- Python `repr`. -/
partial def PyVal.repr : PyVal → String
  | .str s => reprStr s
  | .int n => toString n
  | .bool b => if b then "True" else "False"
  | .none => "None"
  | .list l => "[" ++ ", ".intercalate (l.map PyVal.repr) ++ "]"
  | .tuple [x] => "(" ++ x.repr ++ ",)"
  | .tuple l => "(" ++ ", ".intercalate (l.map PyVal.repr) ++ ")"
end

/-- Python `str`: a `str` is itself, everything else is its `repr`. -/
def PyVal.str' : PyVal → String
  | .str s => s
  | v => v.repr

/-- exceptions.py:23-24 `BaseError.__init__`: `message = " ".join(str(i) for i in args)`. -/
def message (args : List PyVal) : String := " ".intercalate (args.map PyVal.str')

/-- exceptions.py:26-30 `__repr__` and `__str__`: `ClassName : message`. The class name is
`BaseError` or `CoordinateError`, whose constructor only calls the parent. -/
def errorRepr (cls : String) (args : List PyVal) : String := s!"{cls} : {message args}"

/-- A value that `primitive` can get. -/
inductive PrimArg where
  | int (n : Int)
  | pyFloat (x : Float)
  | npFloat (x : Float)
  | none
  | str (s : String)
  /-- an `astropy` unit object, which is not a `Quantity` -/
  | unit (u : String)
  /-- a scalar `Quantity`, whose `.value` is a `numpy.float64` -/
  | quantity (x : Float) (u : String)

/-- units.py:20-26 `primitive`: a `Quantity` becomes its `.value` (a numpy float), anything else
is kept. -/
def primitive (args : List PrimArg) : List PrimArg :=
  args.map fun
    | .quantity x _ => .npFloat x
    | a => a

end EinsteinpyLean.Utils
