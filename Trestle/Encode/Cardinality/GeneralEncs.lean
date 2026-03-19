/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Trestle.Encode.Cardinality.Defs

namespace Trestle.Encode.Cardinality

-- TODO(JG): this entire folder needs some reorganizing...

open VEncCNF Model PropFun

/-- Conditional, naive less-than-k encoding, using `(n choose k)` clauses.
This is identical to `naiveLtK`, but accepts an array of literals to be prepended to every clause.
-/
def naiveLtK.cond (cond : Clause (Literal ν)) (k : Nat) (lits : Array (Literal ν)) :
  VEncCNF ν Unit (condᶜ ⇨ lessThan k (Multiset.ofList lits.toList)) :=
  -- among all subsets `S ⊆ lits` with `|S| = k`, at least one of the literals is false
  (for_all (lits.toList.sublistsLen k).toArray fun sublist =>
    addClause <| (cond ++ sublist.toArray.map (-·))
  ) |>.mapProp (by
    ext τ; rcases lits with ⟨lits⟩
    rw [← not_iff_not]
    conv => lhs; simp [Clause.satisfies_iff, LitVar.neg_eq_iff_eq_neg]
    conv => rhs; simp [Clause.satisfies_iff, card, List.countP_eq_length_filter]
    constructor
    · rintro ⟨S,S_sub,rfl,all_true⟩
      constructor
      · intro x x_mem
        apply all_true; left; exact x_mem
      · apply List.Sublist.length_le
        convert S_sub.filter _
        rw [eq_comm, List.filter_eq_self]
        intro x x_mem
        specialize all_true (-x) (by simp [x_mem])
        simpa using all_true
    · rintro ⟨cond_satisfied,length_ge⟩
      use lits.filter (τ ⊨ LitVar.toPropFun ·) |>.take k
      refine ⟨?_,?_,?_⟩
      · apply List.Sublist.trans
        · apply List.take_sublist
        · apply List.filter_sublist
      · simpa using length_ge
      · rintro a (a_mem|a_mem)
        · exact cond_satisfied _ a_mem
        · replace a_mem := List.mem_of_mem_take a_mem
          simp_all
  )

/-- Naive less-than-k encoding, using `(n choose k)` clauses. -/
def naiveLtK (k : Nat) (lits : Array (Literal ν)) :
  VEncCNF ν Unit (lessThan k (Multiset.ofList lits.toList)) :=
  naiveLtK.cond #[] k lits
  |>.mapProp (by ext τ; simp)

/-- Conditional, naive at-least-k encoding -/
def naiveAtLeastK.cond (cond : Clause (Literal ν)) (k : Nat) (lits : Array (Literal ν)) :
  VEncCNF ν Unit (condᶜ ⇨ atLeast k (Multiset.ofList lits.toList)) :=
  naiveLtK.cond cond (lits.size + 1 - k) (lits.map (LitVar.negate))
  |>.mapProp (by
    ext τ
    simp [atLeast, card]
    apply imp_congr_right; rintro -
    conv => enter [1,1,1]; (calc _ = (fun l => !(τ ⊨ LitVar.toPropFun l)) := by ext l; simp)
    have := @Array.size_eq_countP_add_countP _ (τ ⊨ LitVar.toPropFun ·) lits
    simp at this
    generalize Array.countP _ _ = Ts at this ⊢
    generalize Array.countP _ _ = Fs at this ⊢
    omega
  )

/-- Conditional, naive at-least-k encoding -/
def naiveAtLeastK (k : Nat) (lits : Array (Literal ν)) :
  VEncCNF ν Unit (atLeast k (Multiset.ofList lits.toList)) :=
  naiveAtLeastK.cond #[] k lits
  |>.mapProp (by ext τ; simp)

/-- Trivial at least one encoding (just a single clause) -/
@[inline] def atLeastOne (lits : Array (Literal ν)) :
    VEncCNF ν Unit (atLeast 1 (Multiset.ofList lits.toList)) :=
  addClause lits
  |>.mapProp (by
    ext τ
    simp [Clause.satisfies_iff, card]
  )
