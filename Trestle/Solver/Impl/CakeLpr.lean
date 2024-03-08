/-
Copyright (c) 2024 The LeanSAT Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import LeanSAT.Solver.Basic
import LeanSAT.Solver.Dimacs

import LeanSAT.Util.MkFIFO

namespace LeanSAT.Solver.Impl

namespace CakeLpr

def runCakeLpr (cake_lpr : String := "cake_lpr") (fml : ICnf) (proof : System.FilePath)
    : IO Bool :=
  Util.withTempFIFO fun cnfPath => do
  let cakeProc ← IO.Process.spawn {
    cmd := cake_lpr
    args := #[cnfPath.toString, proof.toString]
    stdout := .piped
  }
  -- Note: opening a FIFO file to write blocks until someone opens the FIFO file to read
  let cnfHandle ← IO.FS.Handle.mk cnfPath .write
  Dimacs.printFormula (cnfHandle.putStr) fml
  cnfHandle.flush
  let output ← IO.asTask cakeProc.stdout.readToEnd Task.Priority.dedicated
  let _ ← cakeProc.wait
  let outputStr ← IO.ofExcept output.get
  return outputStr.trim = "s VERIFIED UNSAT"

end CakeLpr

def CakeLpr (solverCmd : String) (solverFlags : Array String := #[]) (cakelprCmd : String := "cake_lpr") : Solver IO where
  solve := fun fml =>
    Util.withTempFIFO fun proofPath => do
    let solver ← IO.Process.spawn {
      cmd := solverCmd
      args := solverFlags ++ #["-", proofPath.toString]
      stdin := .piped
      stdout := .piped
    }
    let (stdin, solver) ← solver.takeStdin
    Dimacs.printFormula (stdin.putStr) fml
    stdin.flush
    let output ← IO.asTask solver.stdout.readToEnd Task.Priority.dedicated

    let succeeded ← CakeLpr.runCakeLpr cakelprCmd fml proofPath

    let _ ← solver.wait
    let outputStr ← IO.ofExcept output.get
    let res ← IO.ofExcept <| Dimacs.parseResult fml.maxVar outputStr
    if succeeded then
      return res
    else
      return .error
