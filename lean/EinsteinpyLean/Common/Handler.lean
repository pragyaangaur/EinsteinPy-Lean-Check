import EinsteinpyLean.Common.Arr

/-!
# The `epdiff` line protocol

`epdiff` reads one case per line on stdin and prints one answer per line. A line is
`<op> <arg> <arg> ...` separated by single spaces. Shared argument encodings:

- array: `<shape>:<data>`, both comma separated, for example `2,2:1,0,0,-1`. A scalar
  has an empty shape, `:7`. Rationals are written `p/q`.
- config string: the string itself, or `-` for the empty string.
- optional integer: an integer, or `N` for Python `None`.
-/

namespace EinsteinpyLean

abbrev Handler := List String → String

def parseArr (s : String) : Option Arr := do
  let [sh, dt] := s.splitOn ":" | none
  let shape ← if sh.isEmpty then some [] else (sh.splitOn ",").mapM String.toNat?
  let data ← if dt.isEmpty then some [] else (dt.splitOn ",").mapM Arr.parseRat
  if data.length != Arr.size shape then none
  some ⟨shape, data.toArray⟩

def parseConfig (s : String) : String := if s == "-" then "" else s

def parseOptInt (s : String) : Option (Option Int) :=
  if s == "N" then some none else (s.toInt?).map some

def badInput : String := "BADINPUT"

end EinsteinpyLean
