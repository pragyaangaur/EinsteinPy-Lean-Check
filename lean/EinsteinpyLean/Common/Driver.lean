import EinsteinpyLean.Common.Handler

/-! The read-eval loop shared by `epdiff` and the per-area executables `epdiff_<area>`. -/

namespace EinsteinpyLean

partial def runHandlers (hs : List (String × Handler)) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let rec loop : IO Unit := do
    let line ← stdin.getLine
    if line.isEmpty then return
    let words := line.trimAsciiEnd.toString.splitOn " "
    let out := match words with
      | op :: args => match hs.lookup op with
        | some h => h args
        | none => s!"UNKNOWN {op}"
      | [] => badInput
    stdout.putStrLn out
    stdout.flush
    loop
  loop

end EinsteinpyLean
