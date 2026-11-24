import EinsteinpyLean.Common.Driver
import EinsteinpyLean.Tensor.Diff
import EinsteinpyLean.Helpers.Diff

/-! `epdiff`: every wired-in area. One case per stdin line, one answer per stdout line. -/

open EinsteinpyLean

def main : IO Unit :=
  runHandlers (Tensor.handlers ++ Helpers.handlers)
