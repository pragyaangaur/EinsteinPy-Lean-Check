import EinsteinpyLean.Common.Driver
import EinsteinpyLean.Tensor.Diff
import EinsteinpyLean.Helpers.Diff
import EinsteinpyLean.Predefined.Diff
import EinsteinpyLean.Utils.Diff
import EinsteinpyLean.Coordinates.Diff
import EinsteinpyLean.Metric.Diff
import EinsteinpyLean.Geodesic.Diff

/-! `epdiff`: every wired-in area. One case per stdin line, one answer per stdout line. -/

open EinsteinpyLean

def allHandlers : List (String × Handler) :=
  Tensor.handlers ++ Helpers.handlers ++ Predefined.handlers ++ Utils.handlers ++
    Coordinates.handlers ++ Metric.handlers ++ Geodesic.handlers

def main : IO Unit := do
  -- Two areas must never claim the same operation name, because lookup takes the first.
  let names := allHandlers.map (·.1)
  if names.eraseDups.length != names.length then
    IO.eprintln "duplicate handler names"
    IO.Process.exit 2
  runHandlers allHandlers
