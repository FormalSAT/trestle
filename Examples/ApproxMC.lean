import LeanSAT

open LeanSAT

namespace Examples.ApproxMC

instance : Solver IO := Solver.Impl.DimacsCommand "cadical"
instance : Solver.ModelCount IO := Solver.Impl.ApproxMCCommand

def main : IO Unit := do
  let formula : Formula :=
    open Encode Tseitin.Notation in
    let ((), enc) := EncCNF.new! do
      let x ← EncCNF.mkVar "x"
      let y ← EncCNF.mkVar "y"
      let z ← EncCNF.mkVar "z"
      Tseitin.tseitin
        ((x ∧ y ∧ z) ∨ (¬ x ∧ ¬ y))
    enc.toFormula
  IO.println formula.vars
  let res ← Solver.solve formula
  IO.println res
  let res ← Solver.ModelCount.modelCount formula formula.vars
  IO.println res
