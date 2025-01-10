/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Trestle

open Trestle

namespace Examples.ApproxMC

instance : Solver IO := Solver.Impl.DimacsCommand "cadical"
instance : Solver.ModelCount IO := Solver.Impl.ApproxMCCommand

open Encode Model.PropForm.Notation in
def main : IO Unit := do
  let x : Fin 3 := 0
  let y : Fin 3 := 1
  let z : Fin 3 := 2

  let enc : EncCNF (Fin 3) Unit := do
    Subtype.val tseitin[ {x} ∧ {y} ∧ {z} ∨ ¬{x} ∧ ¬{y} ]

  let ((),state) := enc.run

  let res ← Solver.solve state.cnf
  IO.println res
  let res ← Solver.ModelCount.modelCount state.cnf (some <|
    [x,y,z].map state.vMap)
  IO.println res
