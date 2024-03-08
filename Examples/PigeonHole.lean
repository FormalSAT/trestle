/-
Copyright (c) 2024 The LeanSAT Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import LeanSAT

open LeanSAT Encode VEncCNF

structure Var (n : Nat) where
  pigeon : Fin (n+1)
  hole : Fin n
deriving DecidableEq

instance : FinEnum (Var n) := .ofEquiv {
  toFun := fun {pigeon,hole} => (pigeon,hole)
  invFun := fun (pigeon,hole) => {pigeon,hole}
  left_inv := by intro; simp
  right_inv := by intro; simp
}

def pigeonsInHole (h : Fin n) : List (Literal <| Var n) :=
  List.finRange (n+1) |>.map (Literal.pos <| Var.mk · h)

def holesWithPigeon (p : Fin (n+1)) : List (Literal (Var n)) :=
  List.finRange n |>.map (Literal.pos <| Var.mk p ·)

def encoding (n) : VEncCNF (Var n) Unit (fun τ =>
    (∀ p, ∃ h, τ (Var.mk p h)) ∧
    (∀ h, atMost 1 (Multiset.ofList <| pigeonsInHole h) τ)
  ) :=
  seq[
    for_all (List.toArray <| List.finRange (n+1)) fun p =>
      addClause (List.toArray (holesWithPigeon p))
  , for_all (List.toArray (List.finRange n)) fun h =>
      amoPairwise (List.toArray (pigeonsInHole h))
  ]
  |>.mapProp (by
    ext τ
    simp [holesWithPigeon, Clause.satisfies_iff, LitVar.satisfies_iff
        , LitVar.toVar, LitVar.polarity]
  )

def main (args : List String) : IO Unit := do
  let n := args[0]!.toNat!
  let enc := encoding n
  let cnf := enc.val.toICnf
  Solver.Dimacs.printFormula IO.print cnf
