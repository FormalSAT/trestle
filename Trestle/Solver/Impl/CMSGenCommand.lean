/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Trestle.Solver.Basic
import Trestle.Solver.Dimacs

namespace Trestle.Solver.Impl


/-- Command-line CMSGen solver

Lives in IO, since we need access to process invocation.
-/
def CMSGenCommand
  (cmd : String := "cmsgen") (flags : List String := []) : ModelSample IO :=
  ⟨fun fml sampleSet count => do
  if sampleSet.isSome then
    dbgTrace "CMSGenCommand: sample set not supported; sampling all variables" fun () => pure ()
  -- CC: TODO for JG, figure out how to temp file across a fork
  IO.FS.withTempFile (fun _handle temp => do
  let child ← IO.Process.spawn {
    cmd := cmd
    args := flags.toArray ++ #[
      "--samplefile", temp.toString,
      "--samples", toString count]
    stdin := .piped
    stdout := .piped
  }
  let (stdin, child) ← child.takeStdin
  Dimacs.printFormula (stdin.putStr) fml
  stdin.flush
  let _ ← child.wait
  let sampleOutput ← IO.FS.readFile temp
  IO.ofExcept <| Dimacs.parseAssnLines fml.maxVar sampleOutput
  )⟩
