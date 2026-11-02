/-
Copyright (c) 2026 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio, Cayden Codel
-/

import Trestle.Encode.Cardinality.AMO.Defs

namespace Trestle.Encode.Cardinality

open VEncCNF Model PropFun

-- To implement: we will need to implement a subst or replacement for VEncCNF to replace literals by other literals or clauses.
-- These transformations will have to be respected given the `vMap`.
-- The most challenging will be the replacement of `l_i` with two clauses.

/-- The order encoding, except we do not substitute the literals. -/
def amoOrderEncoding (lits : Array (Literal ν))
    : VEncCNF ν Unit (atMostOne (Multiset.ofList lits.toList)) :=
  (withTemps (Fin (lits.size - 1)) fun temps =>
    for_univ fun (i : Fin (lits.size - 1)) =>
      seq[
        imply (LitVar.map Sum.inl lits[i]) (temps i)
      , imply (temps i) (-LitVar.map Sum.inl lits[i.val + 1])
      , guard (i.val + 1 < lits.size - 1) fun hi =>
          imply (temps i) (temps ⟨i + 1, hi⟩)
      ]
  ).mapProp (by
    ext τ
    rw [amo_iff]
    simp [Fin.forall_iff]
    constructor
    · rintro ⟨σ,rfl,h⟩ i i_range j j_range i_sat j_sat
      by_contra ne
      wlog lt : i < j generalizing i j
      · apply this j j_range i i_range j_sat i_sat
          <;> omega
      clear ne; revert j_sat
      have temp_i_true : σ (Sum.inr ⟨i,by omega⟩) = true := by
        have := h i (by omega) |>.1; simpa [i_sat] using this
      clear i_sat
      have temp_jsub1_true : σ (Sum.inr ⟨j-1,by omega⟩) = true := by
        induction j, lt using Nat.le_induction
        case base => simpa
        case succ j le ih =>
          specialize ih (by omega) temp_i_true
          have := h (j-1) (by omega) |>.2.2 (by omega)
          simp [ih] at this
          convert this using 4; omega
      have := h (j-1) (by omega) |>.2.1
      simp [temp_jsub1_true] at this
      convert this; omega
    · rintro h
      use fun | .inl v => τ v | .inr t => decide (∃ i ≤ t, τ ⊨ LitVar.toPropFun lits[i])
      --use τ.extend (decide (∃ i ≤ t, τ ⊨ LitVar.toPropFun lits[i]))
      constructor
      · ext v; simp
      intro i i_range
      refine ⟨?_,?_,?_⟩
      · rw [or_iff_not_imp_left]
        intro i_sat
        replace i_sat : τ ⊨ LitVar.toPropFun lits[i] := by
          simpa [LitVar.satisfies_iff] using i_sat
        dsimp; rw [decide_eq_true_iff]
        use ⟨i,i_range⟩
      · rw [or_iff_not_imp_right]
        intro t_sat
        simp at t_sat
        rcases t_sat with ⟨⟨j,j_range⟩,j_le_i,j_sat⟩
        intro i_sat
        replace i_sat : τ ⊨ LitVar.toPropFun lits[i+1] := by
          simpa [LitVar.satisfies_iff] using i_sat
        specialize h j _ (i+1) _ j_sat i_sat
        subst j; simp at j_le_i
      · intro i_range_tighter
        rw [or_iff_not_imp_left]
        intro t_sat
        simp at t_sat
        rcases t_sat with ⟨⟨j,j_range⟩,j_le_i,j_sat⟩
        dsimp; rw [decide_eq_true_iff]
        use ⟨j,j_range⟩
        simp_all; omega
    )

end Trestle.Encode.Cardinality /- namespace -/
