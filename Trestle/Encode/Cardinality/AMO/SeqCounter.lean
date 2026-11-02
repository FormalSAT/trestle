/-
Copyright (c) 2026 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio, Cayden Codel
-/

import Trestle.Encode.Cardinality.AMO.Pairwise

namespace Trestle.Encode.Cardinality

open VEncCNF Model PropFun

/--
  The sequential counter encoding for the at-most-one constraint.

  This O(n) encoding introduces `n - 1` auxiliary "signal" variables `s_i`,
  where any true `x_i` implies `s_i`, and any true `s_i` implies the
  truth of `s_{i + 1}` and the falsity of `x_{i + 1}`.
-/
def amoSequentialCounter (lits : Array (Literal ν)) :
  VEncCNF ν Unit (atMostOne (Multiset.ofList lits.toList)) := (
    withTemps (Fin (lits.size - 1)) fun S =>
      for_univ fun (i : Fin (lits.size - 1)) =>
        seq[
          imply (LitVar.map Sum.inl lits[i]) (S i)
        , imply (S i) (-LitVar.map Sum.inl lits[i.val + 1])
        , guard (i.val + 1 < lits.size - 1) fun hi =>
            imply (S i) (S ⟨i + 1, hi⟩)
        ]
  ).mapProp (by
    ext τ
    rw [amo_iff]
    simp [Fin.forall_iff]
    constructor
    · rintro ⟨t, ht⟩ i hi j hj si sj
      by_contra ne
      wlog lt : i < j generalizing i j
      · exact this j hj i hi sj si (Ne.symm ne) (by omega)
      obtain ⟨j, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      -- The signal propagates from `s_i` to `s_k` for `k ≥ i`
      have key : ∀ k (hk : k < lits.size - 1), i ≤ k → t ⟨k, hk⟩ := by
        intro k hk hik
        induction k, hik using Nat.le_induction with
        | base => exact (ht i hk).1 si
        | succ k _ ih => exact (ht k (by omega)).2.2 hk (ih (by omega))
      exact (ht j (by omega)).2.1 (key j _ (by omega)) sj
    · intro h
      use (fun ⟨k, _⟩ => ∃ (i : Nat) (_ : i ≤ k), τ ⊨ LitVar.toPropFun (lits[i]'(by omega)))
      simp
      intro i hi
      apply And.intro (fun h => ⟨i, by omega, h⟩)
      constructor
      · intro j hij hj h_con
        simp [h j (by omega) (i + 1) (by omega) hj h_con] at hij
      · intro _ j _ hj
        exact ⟨j, by omega, hj⟩
  )

instance sequentialCounterAMOEncoding : AMOEncoding ν where
  encoding := amoSequentialCounter

end Trestle.Encode.Cardinality /- namespace -/
