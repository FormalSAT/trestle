/-
Copyright (c) 2026 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio, Cayden Codel
-/

import Trestle.Encode.Cardinality.Defs

namespace Trestle.Encode.Cardinality

open VEncCNF Model PropFun

abbrev atMostOne (lits : Multiset (Literal ν)) := atMost 1 lits

class AMOEncoding (ν : Type) where
  encoding : (lits : Array (Literal ν)) → VEncCNF ν Unit (atMostOne (Multiset.ofList lits.toList))

open _root_.List in
/-- At most one literal in `lits` is true if two true literals actually share the same index. -/
theorem amo_iff (lits : Array (Literal ν)) (τ) :
  (atMostOne (Multiset.ofList lits.toList)) τ ↔
    ∀ i (_: i < lits.size) j (_: j < lits.size),
      τ ⊨ ↑lits[i] → τ ⊨ ↑lits[j] → i = j := by
  rcases lits with ⟨lits⟩
  simp [card]
  constructor
  · intro h i i_range j j_range i_sat j_sat
    by_contra ne
    wlog lt : i < j generalizing i j
    · apply this j j_range i i_range j_sat i_sat (Ne.symm ne) (by omega)
    clear ne
    have : [Fin.mk i i_range,⟨j,j_range⟩].map (lits[·]) <+ lits := by
      apply List.map_getElem_sublist
      simp [lt]
    replace this := @List.Sublist.countP_le _ (τ ⊨ LitVar.toPropFun ·) _ _ this
    simp [*] at this
    omega
  · intro h
    rw [countP_eq_length_filter]
    generalize hL : filter _ lits = L
    have L_sublist : L <+ lits := hL ▸ filter_sublist ..
    have L_sat : ∀ x ∈ L, τ ⊨ LitVar.toPropFun x := by rw [← hL]; simp
    clear hL
    have ⟨is,h2,is_lt⟩ := List.sublist_eq_map_getElem L_sublist; clear L_sublist
    subst h2
    match is with
    | [] | [_] => simp_all
    | i::j::rest =>
      exfalso
      simp at L_sat
      specialize h i i.isLt j j.isLt L_sat.1 L_sat.2.1
      rw [Fin.val_eq_val] at h; subst j; simp at is_lt

open _root_.List in
/-- At most one literal in `lits` is true if the truth of any `l₁` under `τ` implies the falsity of `l₂`. -/
theorem amo_iff_Pairwise (lits : Array (Literal ν)) (τ) :
  (atMostOne (Multiset.ofList lits.toList)) τ ↔ lits.Pairwise (fun l₁ l₂ => (τ ⊨ ↑l₁) → (τ ⊭ ↑l₂)) := by
  rcases lits with ⟨lits⟩
  simp [card]
  show _ ↔ List.Pairwise _ lits
  induction lits with
  | nil => simp
  | cons a l ih =>
    rw [countP_cons, pairwise_cons, ← ih]
    by_cases ha : τ ⊨ LitVar.toPropFun a
    · simp [ha]
      intro h
      have : countP (fun b => decide (τ ⊨ LitVar.toPropFun b)) l = 0 :=
        countP_eq_zero.mpr (by simpa using h)
      omega
    · simp [ha]

end Trestle.Encode.Cardinality /- namespace -/
