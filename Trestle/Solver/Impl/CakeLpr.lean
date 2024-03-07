/-
Copyright (c) 2024 The LeanSAT Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import LeanSAT.Solver.Basic
import LeanSAT.Solver.Dimacs
import LeanSAT.Solver.Verif

import LeanSAT.Util.MkFIFO

namespace LeanSAT.Solver.Impl

def runCakeLpr (cake_lpr : String := "cake_lpr") (fml : ICnf) (proof : System.FilePath)
    : IO Bool :=
  Util.withTempFIFO fun cnfPath => do
  let cnfHandle ← IO.FS.Handle.mk cnfPath .write
  let cakeProc ← IO.Process.spawn {
    cmd := cake_lpr
    args := #[cnfPath.toString, proof.toString]
    stdout := .piped
  }
  Dimacs.printFormula (cnfHandle.putStr) fml
  cnfHandle.flush
  let output ← IO.asTask cakeProc.stdout.readToEnd Task.Priority.dedicated
  let _ ← cakeProc.wait
  let outputStr ← IO.ofExcept output.get
  dbgTrace outputStr fun () =>
  return true
