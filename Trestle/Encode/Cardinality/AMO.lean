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

open List in
theorem amo_iff (lits : Array (Literal ν)) (τ) :
  (atMost 1 (Multiset.ofList lits.toList)) τ ↔
    ∀ i (_: i < lits.size) j (_: j < lits.size),
      τ ⊨ LitVar.toPropFun lits[i] → τ ⊨ LitVar.toPropFun lits[j] → i = j := by
  have := Classical.decEq ν
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
    replace this := List.Sublist.countP_le (τ ⊨ LitVar.toPropFun ·) this
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

/--
  The pairwise at-most-one encoding.

  An O(n²) encoding comprising binary clauses of every pair of literals.
  Formally,

    ∀ x,y ∈ lits, x ≠ y → (¬x ∨ ¬y)

  The only way to satisfy the encoding is to never have any pair of literals
  both set to false in the assignment. Thus, at most one literal is true.
-/
def amoPairwise (lits : Array (Literal ν)) :
    VEncCNF ν Unit (atMost 1 (Multiset.ofList lits.toList)) := (
  -- for every pair (i, j) of literals in `lits`, they can't both be true
  for_all (Array.ofFn id) fun (j : Fin lits.size) =>
    for_all (Array.ofFn (fun (i : Fin j.val) =>
      Fin.castLT i (by cases i; cases j; omega)))
    fun (i : Fin lits.size) => by with_reducible
      exact addClause #[-lits[i], -lits[j]]
  ).mapProp (by
    ext τ; rw [amo_iff]
    simp [Fin.forall_iff]
    constructor
    · intro h i i_range j j_range i_sat j_sat
      wlog le : i ≤ j generalizing i j
      · rw [eq_comm]; apply this j j_range i i_range j_sat i_sat (by omega)
      specialize h j j_range i i_range i
      simp [i_sat, j_sat] at h
      apply Nat.le_antisymm le h
    · rintro h j j_range _ i_range i i_lt_j rfl
      specialize h i i_range j j_range
      simpa [Nat.ne_of_lt i_lt_j, imp_iff_not_or] using h
  )


/--
  The cut4 at-most-one encoding.

  An O(n) encoding constructed by repeatedly taking the first `k` literals
  from the list `l` such that

    l = a ++ b,  |a| = k

  and replacing `a` with a temporary variable `t` that is true when any literal
  in `a` is true. This forces the remaining literals in `b` to be false,
  if the overall AMO constraint is to be satisfied.
-/
def amoCut4 (lits : Array (Literal ν)) (k : Nat := 3) (hk : k ≥ 2 := by decide)
    : VEncCNF ν Unit (atMost 1 (Multiset.ofList lits.toList)) :=
  (VEncCNF.ite (lits.size ≤ k)
    (fun _ => amoPairwise lits)
    (fun _ =>
      let first_k_lits := lits.take k |>.map <| LitVar.map Sum.inl
      let rest := lits.extract k lits.size |>.map <| LitVar.map Sum.inl
      let tmp := Sum.inr ()
      withTemps Unit (
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
        rcases hτ with ⟨σ,rfl, hσ₁, hσ₂⟩
        by_cases h_tmp : σ (Sum.inr ())
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
        let τ' : PropAssignment (ν ⊕ Unit) := (fun
            | Sum.inl v => τ v
            | Sum.inr v => card ↑(List.take k (list)) τ = 0)
        have h_eq : τ' ∘ Sum.inl = τ := rfl
        use τ'
        simp [h_eq]
        conv => rhs; rw [List.take_of_length_le (by simp only [List.length_drop, le_refl])]
        constructor <;> (simp [τ']; split <;> omega)
  )
termination_by lits.size

/-- The order encoding, except we do not substitute the literals. -/
def amoOrdEncoding (lits : Array (Literal ν))
    : VEncCNF ν Unit (atMost 1 (Multiset.ofList lits.toList)) :=
  (VEncCNF.withTemps (Fin (lits.size - 1)) <|
    VEncCNF.for_all (Array.finRange (lits.size-1)) fun i =>
      seq[
        VEncCNF.addClause #[-LitVar.map Sum.inl lits[i]      ,  Literal.pos (Sum.inr i)]
      , VEncCNF.addClause #[-LitVar.map Sum.inl lits[i.val+1], -Literal.pos (Sum.inr i)]
      , VEncCNF.guard (i.val + 1 < lits.size-1) fun hi =>
          VEncCNF.addClause #[Literal.neg (Sum.inr i), Literal.pos (Sum.inr ⟨i+1,hi⟩)]
      ]
  ).mapProp (by
    ext τ
    rw [amo_iff]
    simp [Array.mem_def, Fin.forall_iff]
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

end Trestle.Encode.Cardinality
