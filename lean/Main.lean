import EinsteinpyLean.Tensor.Diff
import EinsteinpyLean.Helpers.Diff

/-! `epdiff`: one case per stdin line, one answer per stdout line. -/

open EinsteinpyLean

def allHandlers : List (String × Handler) :=
  Tensor.handlers ++ Helpers.handlers

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let line := line.trimAsciiEnd.toString
  let words := line.splitOn " "
  let out := match words with
    | op :: args => match allHandlers.lookup op with
      | some h => h args
      | none => s!"UNKNOWN {op}"
    | [] => badInput
  stdout.putStrLn out
  stdout.flush
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
