import LeanSAT

open LeanSAT

instance : Solver IO := Solver.Impl.DimacsCommand "cadical"
instance : Solver.ApproxModelCount IO := Solver.Impl.ApproxMCCommand

def main : IO Unit := do
  let formula : Formula :=
    (0 ∨ 1 ∨ 2) ∧ ¬0
  IO.println formula.vars
  let res ← Solver.solve formula
  IO.println res
  let res ← Solver.ApproxModelCount.approxModelCount formula formula.vars
  IO.println res

#eval main
