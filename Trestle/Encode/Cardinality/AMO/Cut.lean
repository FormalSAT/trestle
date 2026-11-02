/-
Copyright (c) 2026 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio, Cayden Codel
-/

import Trestle.Encode.Cardinality.AMO.Pairwise

namespace Trestle.Encode.Cardinality

open VEncCNF Model PropFun

/--
  The cut4 at-most-one encoding.

  An O(n) encoding constructed by repeatedly taking the first `k` literals
  from the list `l` such that

    `l = a ++ b,  |a| = k`

  and replacing `a` with a temporary variable `t` that is true when any literal
  in `a` is true. This forces the remaining literals in `b` to be false,
  if the overall AMO constraint is to be satisfied.
-/
def amoCut4 (lits : Array (Literal ν)) (k : Nat := 3) (hk : k ≥ 2 := by decide)
    : VEncCNF ν Unit (atMost 1 (Multiset.ofList lits.toList)) :=
  (ite (lits.size ≤ k)
    (fun _ => amoPairwise lits)
    (fun _ =>
      let first_k_lits := lits.take k |>.map <| LitVar.map Sum.inl
      let rest := lits.extract k lits.size |>.map <| LitVar.map Sum.inl
      withTemp (fun tmp =>
        seq[
          amoPairwise <| first_k_lits.push <| LitVar.mkPos tmp
        , amoCut4 (k := k) (hk := hk) <| #[LitVar.mkNeg tmp] ++ rest
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
        obtain ⟨σ, hσ₁, hσ₂⟩ := hτ
        by_cases h_tmp : σ ()
        all_goals (
          try simp only [Bool.not_eq_true] at h_tmp
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
        simp [-List.map_take, -List.map_drop]
        use (fun _ => card ↑(List.take k list) τ = 0)
        simp only [decide_eq_true_eq, decide_eq_false_iff_not, ite_not]
        grind
  )
termination_by lits.size

/--
  The `amoCut4` encoding, except where the temporary variable is placed
  at the end of the cut list, rather than at the start. This results in all of the
  temporary variables appearing at the end of the encoding, which can have
  different propagation/performance characteristics.
-/
def amoCut4Pooled (lits : Array (Literal ν)) (k : Nat := 3) (hk : k ≥ 2 := by decide)
    : VEncCNF ν Unit (atMost 1 (Multiset.ofList lits.toList)) :=
   (ite (lits.size ≤ k)
    (fun _ => amoPairwise lits)
    (fun _ =>
      let first_k_lits := lits.take k |>.map <| LitVar.map Sum.inl
      let rest := lits.extract k lits.size |>.map <| LitVar.map Sum.inl
      withTemp (fun tmp =>
        seq[
          amoPairwise <| first_k_lits.push <| LitVar.mkPos tmp
        , amoCut4Pooled (k := k) (hk := hk) <| rest.push <| LitVar.mkNeg tmp
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
        obtain ⟨σ, hσ₁, hσ₂⟩ := hτ
        by_cases h_tmp : σ ()
        all_goals (
          try simp only [Bool.not_eq_true] at h_tmp
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
        simp [-List.map_take, -List.map_drop]
        use (fun _ => card ↑(List.take k list) τ = 0)
        simp only [decide_eq_true_eq, decide_eq_false_iff_not, ite_not]
        grind
  )
termination_by lits.size

instance cut4AMOEncoding : AMOEncoding ν where
  encoding := amoCut4

instance cut4PooledAMOEncoding : AMOEncoding ν where
  encoding := amoCut4Pooled

end Trestle.Encode.Cardinality /- namespace -/
