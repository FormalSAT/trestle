/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: Cayden Codel, James Gallicchio
-/


import Trestle.Encode.VEncCNF

namespace Trestle.Encode.Cardinality

/-!

## Cardinality specification predicates

This file defines useful predicates for specifying
the behavior of cardinality encodings.

-/

open VEncCNF Model PropFun

def card (lits : Multiset (Literal ν)) (τ : PropAssignment ν) : Nat :=
  lits.countP (τ ⊨ LitVar.toPropFun ·)

def cardPred (lits : Multiset (Literal ν)) (P : Nat → Prop) [DecidablePred P] :=
  fun τ => P (card lits τ)

@[simp]
theorem satisfies_cardPred (lits : Multiset (Literal ν)) (P) [DecidablePred P] (τ)
    : cardPred lits P τ ↔ P (card lits τ) := by
  unfold cardPred; simp

abbrev atMost (k : Nat) (lits : Multiset (Literal ν)) := cardPred lits (· ≤ k)
abbrev atLeast (k : Nat) (lits : Multiset (Literal ν)) := cardPred lits (· ≥ k)

abbrev exactly (k : Nat) (lits : Multiset (Literal ν)) := cardPred lits (· = k)

abbrev lessThan (k : Nat) (lits : Multiset (Literal ν)) := cardPred lits (· < k)

theorem ofList_eq_map_get (L : List α)
  : Multiset.ofList L = (Finset.univ.val.map fun i => L.get i) := by
  conv => lhs; rw [← List.finRange_map_get (l := L)]
  simp only [List.finRange_map_get, List.get_eq_getElem,
    Fin.univ_val_map, List.ofFn_getElem]

@[simp]
theorem card_singleton' (l : Literal ν)
    : card [l] = (fun τ => if τ ⊨ LitVar.toPropFun l then 1 else 0) := by
  ext τ
  rw [card, Multiset.coe_countP]
  simp [List.countP, List.countP.go]

@[simp]
theorem card_singleton (l : Literal ν)
    : card {l} = (fun τ => if τ ⊨ LitVar.toPropFun l then 1 else 0) := by
  ext τ
  simp [← Multiset.coe_singleton]

@[simp]
theorem card_append (L₁ L₂ : List (Literal ν))
    : card (L₁ ++ L₂) = card L₁ + card (Multiset.ofList L₂) := by
  ext τ
  simp [card]

@[simp]
theorem card_cons (l : Literal ν) (L : List (Literal ν))
    : card (l :: L) = card [l] + card (Multiset.ofList L) := by
  have : l :: L = [l] ++ L := rfl
  rw [this]
  exact card_append _ _

@[simp]
theorem card_map
    (L : List (Literal ν)) (f : ν → ν') (τ : PropAssignment ν')
    : card ((L.map (LitVar.map f)) : List (Literal ν')) τ = card L (τ ∘ f) := by
  simp only [card, Multiset.coe_countP, List.countP_map]
  congr
  ext l
  simp only [Function.comp_apply, LitVar.toPropFun_map,
    satisfies_map, decide_eq_decide]

theorem card_eq_one (ls : Multiset (Literal ν)) (nodup : ls.Nodup)
  : card ls τ = 1 ↔ ∃! l ∈ ls, τ ⊨ LitVar.toPropFun l := by
  open Classical in
  simp [card]
  rw [Multiset.countP_eq_card_filter, Multiset.card_eq_one]
  constructor
  · rintro ⟨a,h⟩
    use a
    have := fun x => congrArg (x ∈ ·) h
    simp at this
    simp [this]
  · rintro ⟨a, ⟨mem, a_true⟩, unique⟩
    use a
    rw [Multiset.ext]; intro b
    specialize unique b
    rw [Multiset.count_filter]
    if h : a = b then
      subst b; simp [a_true]; exact Multiset.count_eq_one_of_mem nodup mem
    else
      simp [Multiset.count_singleton, Ne.symm h]
      intro b_true b_mem
      apply h; rw [eq_comm]; apply unique; simp [b_mem, b_true]

end Trestle.Encode.Cardinality
