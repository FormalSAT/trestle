/-

At-most one encodings.

TODO: When we accumulate more encodings, split into separate files.

-/

import Trestle.Encode.Cardinality.Defs

namespace Trestle.Encode.Cardinality

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

def amoSeqCounter (k : Nat := 3) (hk : k ≥ 2) (lits : Array (Literal ν))
    : VEncCNF ν Unit (atMost 1 (Multiset.ofList lits.toList)) :=

  (VEncCNF.ite (lits.size ≤ k)
    (fun _ => amoPairwise lits) --(lits.map (LitVar.map Sum.inl)))
    (fun _ =>
      let first_k_lits := lits.take k |>.map <| LitVar.map Sum.inl
      let rest := lits.extract k lits.size |>.map <| LitVar.map Sum.inl
      let tmp := Sum.inr 0
      withTemps 1 (
        seq[
          amoPairwise <| first_k_lits.push <| LitVar.mkPos tmp
        , amoSeqCounter k hk <| #[LitVar.mkNeg tmp] ++ rest
        ]
      )
    )
  ).mapProp (by
    have ⟨list⟩ := lits
    ext τ
    induction list using List.strong_induction_on
    rename_i l₁ ih
    split
    · rfl
    · simp
      constructor
      · rintro ⟨τ', rfl, h_take, h_drop⟩
        by_cases h_tmp : τ' <| Sum.inr 0
        · simp [h_tmp] at h_take h_drop
          -- splice these together
          sorry
          done
        · sorry
          done
        done
      · sorry
        done
      done
  )
termination_by lits.size

end Trestle.Encode.Cardinality
