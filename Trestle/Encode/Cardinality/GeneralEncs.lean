/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Trestle.Encode.Cardinality.Defs

namespace Trestle.Encode.Cardinality

-- TODO(JG): this entire folder needs some reorganizing...

open VEncCNF Model PropFun

/-- Naive less-than-k encoding, using `(n choose k)` clauses. -/
def naiveLtK (k : Nat) (lits : Array (Literal ν)) :
  VEncCNF ν Unit (lessThan k (Multiset.ofList lits.toList)) :=
  -- among all subsets `S ⊆ lits` with `|S| = k`, at least one of the literals is false
  (for_all (lits.toList.sublistsLen k).toArray fun sublist =>
    addClause <| (sublist.toArray.map (-·))
  ) |>.mapProp (by
    ext τ; rcases lits with ⟨lits⟩
    rw [← not_iff_not]
    conv => lhs; simp [Clause.satisfies_iff]
    conv => rhs; simp [card, List.countP_eq_length_filter]
    constructor
    · rintro ⟨S,S_sub,rfl,all_true⟩
      apply List.Sublist.length_le
      calc
        _ = _ := by rw [eq_comm, List.filter_eq_self]; simpa using all_true
        List.Sublist _ _ := S_sub.filter _
    · intro length_ge
      simp at length_ge
      use lits.filter (τ ⊨ LitVar.toPropFun ·) |>.take k
      refine ⟨?_,?_,?_⟩
      · apply List.Sublist.trans
        · apply List.take_sublist
        · apply List.filter_sublist
      · simpa using length_ge
      · intro a ha; replace ha := List.mem_of_mem_take ha
        simp_all
  )

/-- Naive at-least-k encoding -/
def naiveAtLeastK (k : Nat) (lits : Array (Literal ν)) :
  VEncCNF ν Unit (atLeast k (Multiset.ofList lits.toList)) :=
  naiveLtK (lits.size + 1 - k) (lits.map (LitVar.negate))
  |>.mapProp (by
    ext τ
    simp [atMost, atLeast, card]
    conv => enter [1,1,1]; (calc _ = (fun l => !(τ ⊨ LitVar.toPropFun l)) := by ext l; simp)
    have := Array.size_eq_countP_add_countP (τ ⊨ LitVar.toPropFun ·) lits
    simp at this
    generalize Array.countP _ _ = Ts at this ⊢
    generalize Array.countP _ _ = Fs at this ⊢
    omega
  )

/-- Trivial at least one encoding (just a single clause) -/
@[inline] def atLeastOne (lits : Array (Literal ν)) :
    VEncCNF ν Unit (atLeast 1 (Multiset.ofList lits.toList)) :=
  addClause lits
  |>.mapProp (by
    ext τ
    simp [Clause.satisfies_iff, card]
  )
