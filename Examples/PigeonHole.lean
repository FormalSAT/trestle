/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Trestle

open Trestle Encode VEncCNF

structure Var (n : Nat) where
  pigeon : Fin (n+1)
  hole : Fin n
deriving DecidableEq, IndexType


def pigeonsInHole (h : Fin n) : List (Literal <| Var n) :=
  List.finRange (n+1) |>.map (Literal.pos <| Var.mk · h)

def holesWithPigeon (p : Fin (n+1)) : List (Literal (Var n)) :=
  List.finRange n |>.map (Literal.pos <| Var.mk p ·)

def encoding (n) : VEncCNF (Var n) Unit (fun τ =>
    (∀ p, ∃ h, τ (Var.mk p h)) ∧
    (∀ h, Cardinality.atMost 1 (Multiset.ofList <| pigeonsInHole h) τ)
  ) :=
  seq[
    for_all (List.toArray <| List.finRange (n+1)) fun p =>
      addClause (List.toArray (holesWithPigeon p))
  , for_all (List.toArray (List.finRange n)) fun h =>
      Cardinality.amoSeqCounter (List.toArray (pigeonsInHole h))
  ]
  |>.mapProp (by
    ext τ
    simp [holesWithPigeon, Clause.satisfies_iff, LitVar.satisfies_iff]
  )

def main (args : List String) : IO Unit := do
  let n := args[0]!.toNat!
  let cnfFile   := args[1]!
  let cubesFile := args[2]!
  let compFile  := args[3]!
  let enc := encoding n
  let ((),{cnf, vMap ..}) := enc.val.run
  IO.FS.withFile cnfFile .write fun handle =>
    Solver.Dimacs.printFormula handle.putStr cnf
  IO.FS.withFile cubesFile .write fun handle => do
    for i in IndexType.univ (Fin n) do
      let var := vMap {pigeon := i.succ, hole := i}
      handle.putStrLn s!"a -{var} 0"
  IO.FS.withFile compFile .write fun handle => do
    for i in IndexType.univ (Fin n) do
      let var := vMap {pigeon := i.succ, hole := i}
      handle.putStrLn s!"{var} 0"
    handle.putStrLn "0"
