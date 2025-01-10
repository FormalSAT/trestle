/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Trestle.Solver.Basic
import Trestle.Solver.Dimacs

namespace Trestle.Solver.Impl

/-- Command-line DIMACS interface solver.

This is the simplest solver to configure -- `cmd` is expected to
be a command on the environment path which accepts DIMACS input
and produces DIMACS output.

This solver lives in IO, since we need access to process invocation.
-/
def DimacsCommand
  (cmd : String) (flags : List String := []) : Solver IO :=
  ⟨fun fml => do
  let child ← IO.Process.spawn {
    cmd := cmd
    args := flags.toArray
    stdin := .piped
    stdout := .piped
  }
  let (stdin, child) ← child.takeStdin
  Dimacs.printFormula (stdin.putStr) fml
  stdin.flush
  let output ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let _ ← child.wait
  let outputStr ← IO.ofExcept output.get
  IO.ofExcept <| Dimacs.parseResult fml.maxVar outputStr
  ⟩
