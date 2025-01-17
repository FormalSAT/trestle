/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: Cayden Codel
-/

import Trestle.Encode.Cardinality.Defs

namespace Trestle.Encode.Cardinality

/-

# At-most one encodings

TODO: When we accumulate more encodings, split into separate files.

-/

open VEncCNF Model PropFun

/--
  The pairwise at-most-one encoding.

  An O(n²) encoding comprising binary clauses of every pair of literals.
  Formally,

    ∀ x,y ∈ lits, x ≠ y → (¬x ∨ ¬y)

  The only way to satisfy the encoding is to never have any pair of literals
  both set to false in the assignment. Thus, at most one literal is true.
-/
@[inline]
def amoPairwise (lits : Array (Literal ν)) :
    VEncCNF ν Unit (atMost 1 (Multiset.ofList lits.toList)) := (
  -- for every pair (i, j) of literals in `lits`, they can't both be true
  for_all (Array.ofFn id) fun (j : Fin lits.size) =>
    for_all (Array.ofFn (fun (i : Fin j.val) =>
      Fin.castLT i (by cases i; cases j; omega)))
    fun (i : Fin lits.size) => by with_reducible
      exact addClause #[-lits[i], -lits[j]]
  ).mapProp (by
    rcases lits with ⟨list⟩
    ext τ
    simp [Clause.toPropFun, any, Array.mem_def, ← not_and_or, not_and]
    rw [ofList_eq_map_get, card, Multiset.countP_map,
      ← Finset.filter_val, ← Finset.card_def, Finset.card_le_one]
    simp only [List.get_eq_getElem, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h ⟨i, hi⟩ hτi ⟨j, hj⟩ hτj
      rcases lt_trichotomy i j with (h_lt | rfl | h_gt)
      · have := h ⟨j, hj⟩ ⟨i, h_lt⟩ hτi hτj
        contradiction
      · rfl
      · have := h ⟨i, hi⟩ ⟨j, h_gt⟩ hτj hτi
        contradiction
    · rintro r ⟨j, hj⟩ ⟨i, hi⟩ hτi hτj
      specialize r _ hτj ⟨i, Nat.lt_trans hi hj⟩ hτi
      simp only [Fin.mk.injEq] at r
      subst r
      simp only [lt_self_iff_false] at hi
  )


/--
  The sequential counter at-most-one encoding.

  An O(n) encoding constructed by repeatedly taking the first `k` literals
  from the list `l` such that

    l = a ++ b,  |a| = k

  and replacing `a` with a temporary variable `t` that is true when any literal
  in `a` is true. This forces the remaining literals in `b` to be false,
  if the overall AMO constraint is to be satisfied.
-/
def amoSeqCounter (lits : Array (Literal ν)) (k : Nat := 3) (hk : k ≥ 2 := by decide)
    : VEncCNF ν Unit (atMost 1 (Multiset.ofList lits.toList)) :=
  (VEncCNF.ite (lits.size ≤ k)
    (fun _ => amoPairwise lits)
    (fun _ =>
      let first_k_lits := lits.take k |>.map <| LitVar.map Sum.inl
      let rest := lits.extract k lits.size |>.map <| LitVar.map Sum.inl
      let tmp := Sum.inr 0
      withTemps 1 (
        seq[
          amoPairwise <| first_k_lits.push <| LitVar.mkPos tmp
        , amoSeqCounter (k := k) (hk := hk) <| #[LitVar.mkNeg tmp] ++ rest
        ]
      )
    )
  ).mapProp (by
    have ⟨list⟩ := lits
    ext τ
    split
    · rfl
    · constructor
      · intro hτ
        simp at hτ
        rcases hτ with ⟨σ,rfl, hσ₁, hσ₂⟩
        by_cases h_tmp : σ (Sum.inr 0)
        all_goals (
          try simp only [Fin.isValue, Bool.not_eq_true] at h_tmp
          simp [h_tmp, ← List.map_take, ← List.map_drop] at hσ₁ hσ₂
          rw [List.take_of_length_le (by simp only [List.length_drop, le_refl])] at hσ₂
          have := List.take_append_drop k list
          simp [atMost]
          rw [← this, card_append]
          simp [hσ₁, hσ₂]
        )
      · intro h_amo
        have := List.take_append_drop k list
        simp [atMost] at h_amo
        rw [← this, card_append] at h_amo
        simp at h_amo
        simp [← List.map_take, ← List.map_drop]
        -- CC: TODO have a `set` or `pmap` on assignments for sums
        let τ' : PropAssignment (ν ⊕ Fin 1) := (fun
            | Sum.inl v => τ v
            | Sum.inr v => card ↑(List.take k (list)) τ = 0)
        have h_eq : τ' ∘ Sum.inl = τ := rfl
        use τ'
        simp [h_eq]
        conv => rhs; rw [List.take_of_length_le (by simp only [List.length_drop, le_refl])]
        constructor <;> (simp [τ']; split <;> omega)
  )
termination_by lits.size

-- CC: Run it if you want
--#eval (amoSeqCounter #[LitVar.mkPos 0, LitVar.mkPos 1, LitVar.mkPos 2, LitVar.mkPos 3])
--  |>.val.toICnf

end Trestle.Encode.Cardinality
