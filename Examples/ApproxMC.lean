import LeanSAT

open LeanSAT

namespace Examples.ApproxMC

instance : Solver IO := Solver.Impl.DimacsCommand "cadical"
instance : Solver.ModelCount IO := Solver.Impl.ApproxMCCommand

open Encode in
def main : IO Unit := do
  let ((x,y,z), enc) := EncCNF.new! do
    let x ← EncCNF.mkVar "x"
    let y ← EncCNF.mkVar "y"
    let z ← EncCNF.mkVar "z"
    Tseitin.tseitin
      (.disj (.conj x (.conj y z)) (.conj (-x : ILit) (-y : ILit)))
    return (x,y,z)
  let formula : ICnf := enc.toFormula

  let res ← Solver.solve formula
  IO.println res
  let res ← Solver.ModelCount.modelCount formula (some [x,y,z])
  IO.println res
