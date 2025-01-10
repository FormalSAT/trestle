/-

Common definitions of cardinality constraints.

-/

import Trestle.Encode.VEncCNF

namespace Trestle.Encode.Cardinality

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

theorem ofList_eq_map_get (L : List α)
  : Multiset.ofList L = (Finset.univ.val.map fun i => L.get i) := by
  conv => lhs; rw [← List.finRange_map_get (l := L)]
  simp only [List.finRange_map_get, List.get_eq_getElem,
    Fin.univ_val_map, List.ofFn_getElem]

@[simp]
theorem card_singleton (l : Literal ν)
    : card {l} = (fun τ => if τ ⊨ LitVar.toPropFun l then 1 else 0) := by
  ext τ
  sorry

@[simp]
theorem card_singleton' (l : Literal ν)
    : card [l] = (fun τ => if τ ⊨ LitVar.toPropFun l then 1 else 0) := by
  ext τ
  rw [card, Multiset.coe_countP]
  simp [List.countP, List.countP.go]

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

end Trestle.Encode.Cardinality
