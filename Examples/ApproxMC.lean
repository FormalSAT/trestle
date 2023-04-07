import LeanSAT

open LeanSAT Notation

namespace Examples.ApproxMC

instance : Solver IO := Solver.Impl.DimacsCommand "cadical"
instance : Solver.ModelCount IO := Solver.Impl.ApproxMCCommand

def main : IO Unit := do
  let formula : Formula :=
    (0 ∨ 1 ∨ 2) ∧ ¬0
  IO.println formula.vars
  let res ← Solver.solve formula
  IO.println res
  let res ← Solver.ModelCount.modelCount formula formula.vars
  IO.println res
