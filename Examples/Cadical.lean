import LeanSAT

open LeanSAT

namespace Examples.Cadical

instance : Solver IO := Solver.Impl.DimacsCommand "cadical"

def main : IO Unit := do
  let x : IVar := 1
  let y : IVar := 2
  let z : IVar := 3
  let formula : ICnf :=
    #[ #[x, y, z], #[ -x ], #[ -y ] ]
  let res ← Solver.solve formula
  IO.println res
