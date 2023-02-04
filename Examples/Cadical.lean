import LeanSAT

open LeanSAT

instance : Solver IO := Solver.Impl.DimacsCommand "cadical"

def main : IO Unit := do
  let formula : Formula :=
    (0 ∨ 1 ∨ 2) ∧ (¬0) ∧ (¬ 1)
  let res ← Solver.solve formula
  IO.println res

#eval main
