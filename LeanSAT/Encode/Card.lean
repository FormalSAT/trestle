/-
Copyright (c) 2024 The LeanSAT Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import LeanSAT.Encode.VEncCNF
import LeanSAT.Encode.Tseitin

namespace LeanSAT.Encode

open VEncCNF Model PropFun

variable [LitVar L ν] [LawfulLitVar L ν] [DecidableEq L] [DecidableEq ν]

def card (lits : Multiset L) (τ : PropAssignment ν) : Nat :=
  lits.countP (τ ⊨ LitVar.toPropFun ·)

noncomputable def cardPred (lits : Multiset L) (P : Nat → Prop) [DecidablePred P] :=
  fun τ => P (card lits τ)

@[simp] theorem satisfies_cardPred (lits : Multiset L) (P) [DecidablePred P] (τ)
  : cardPred lits P τ ↔ P (card lits τ) := by
  unfold cardPred; simp

noncomputable abbrev atMost (k : Nat) (lits : Multiset L) := cardPred lits (· ≤ k)
noncomputable abbrev atLeast (k : Nat) (lits : Multiset L) := cardPred lits (· ≥ k)

theorem ofList_eq_map_get (L : List α)
  : Multiset.ofList L = (Finset.univ.val.map fun i => L.get i) := by
  conv => lhs; rw [← List.finRange_map_get (l := L)]

@[inline]
def amoPairwise (lits : Array L) :
    VEncCNF L Unit (atMost 1 (Multiset.ofList lits.data)) :=
  -- for every pair x,y of literals in `lits`, they can't both be true
  (for_all (Array.ofFn id) fun (i : Fin lits.size) =>
    for_all (Array.ofFn (fun (j : Fin (lits.size - i.succ)) =>
        (Fin.addNat j i.succ).cast (by
          cases i; cases j; simp at *; apply Nat.sub_add_cancel; assumption)))
      fun (j : Fin lits.size) =>
        addClause #[-lits[i], -lits[j]]
  ).mapProp (by
    rcases lits with ⟨list⟩
    ext τ
    simp [Clause.toPropFun, any, Array.getElem_eq_data_get]
    simp [Array.mem_def, Array.size]
    simp_rw [← not_and_or, not_and]
    rw [ofList_eq_map_get, card, Multiset.countP_map]
    rw [← Finset.filter_val, ← Finset.card_def, Finset.card_le_one]
    simp
    constructor
    · rintro l ⟨i,hi⟩ hτi ⟨j,hj⟩ hτj
      simp; by_contra i_ne_j
      if i < j then
        apply l ⟨i,hi⟩ ⟨j-(i+1),_⟩ hτi
        · convert hτj
          simp
          omega
        · omega
      else
        have : j < i := by omega
        apply l ⟨j,hj⟩ ⟨i-(j+1),_⟩ hτj
        · convert hτi
          simp
          omega
        · omega
    · rintro r ⟨x,hx⟩ ⟨y,hy⟩ hτx hτy
      specialize r _ hτx _ hτy
      simp at r
      omega
  )
