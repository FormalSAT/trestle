/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Trestle.Solver.Basic
import Trestle.Solver.Dimacs

namespace Trestle.Solver.Impl

namespace CakeLpr

def runCakeLpr (cake_lpr : String := "cake_lpr") (fml : ICnf) (proof : System.FilePath)
    : IO (Except String Bool) :=
  IO.FS.withTempFile fun cnfHandle cnfPath => do
  let cakeProc ← IO.Process.spawn {
    cmd := cake_lpr
    args := #[cnfPath.toString, proof.toString]
    stdout := .piped
    stderr := .piped
  }
  Dimacs.printFormula (cnfHandle.putStr) fml
  cnfHandle.flush
  let output ← IO.asTask cakeProc.stdout.readToEnd Task.Priority.dedicated
  let error ← IO.asTask cakeProc.stderr.readToEnd Task.Priority.dedicated
  let retval ← cakeProc.wait
  let outputStr ← IO.ofExcept output.get
  let errorStr ← IO.ofExcept error.get
  if outputStr.trim = "s VERIFIED UNSAT" then
    return .ok true
  else
    return .error s!"unexpected output from cake_lpr: retval {retval}\nSTDOUT:{outputStr}\nSTDERR:{errorStr}"

end CakeLpr

def CakeLpr (solverCmd : String) (solverFlags : Array String := #[]) (cakelprCmd : String := "cake_lpr") : Solver IO where
  solve := fun fml =>
    IO.FS.withTempFile fun _proofHandle proofPath => do
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
    match succeeded with
    | .ok true => return res
    | .ok false =>
      return .error "cakeLPR disagreed"
    | .error x =>
      return .error x

namespace CakeLpr

/-- Check that a CNF is unsat, using the CakeLPR verified pipeline.
If the CNF is found to be unsat, inserts an axiom asserting this result.

**Form 1:** Run a SAT solver and pipe the proof to CakeLPR.
Note that this expects there to be a `Solver IO` instance in context.

Example:
`#cakelpr_check_unsat myCnf`
results in the axiom
`axiom myCnfIsUnsat : ∀ τ, τ ⊭ myCnf.toPropFun`

**Form 2:** Run CakeLPR with a proof from a file.

Example:
`#cakelpr_check_unsat myCnf withProofFile "path/to/proof.lrat"`

**Form 3:** Run CakeLPR with a compositional proof from a file and hash file.
This is for cube & conquer proofs,
where we have a "compositional file" (the top-level proof)
and a "hash file" (storing hashes that evidence each cube's unsatisfiability)

Example:
`#cakelpr_check_unsat myCnf withCompFile "path/to/comp.lrat" withHashFile "path/to/hashes"`
-/
syntax "#cakelpr_check_unsat " ident : command

@[inherit_doc Trestle.Solver.Impl.CakeLpr.«command#cakelpr_check_unsat_»]
syntax "#cakelpr_check_unsat " ident " withProofFile " term : command

@[inherit_doc Trestle.Solver.Impl.CakeLpr.«command#cakelpr_check_unsat_»]
syntax "#cakelpr_check_unsat " ident " withCompFile " term " withHashFile " term : command

macro_rules
| `(#cakelpr_check_unsat $x) => do `(sorry)
