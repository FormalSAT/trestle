/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.Autos

/-! ## Increment Sorted

We say a list is "increment sorted" when every
element in the list is `≤ (max before the element)+1`.

For example, `[0,1,2,0]` is inc sorted, and `[0,1,3,0]` is not.

For any list `L`, we can construct a permutation `p`
such that `L.map p` is inc sorted.

This is a funky looking function with a big job.
Given a list `L : List (Fin s)` of values, it returns a permutation on `Fin s`
such that `L` mapped by the permutation is "incrementally increasing".
i.e. `L'[j] = x + 1` implies `∃ j' < j, L[j'] = x`.
-/

def incSorted (L : List (Fin s)) : Prop :=
  ∀ pre x, pre ≠ [] → (pre ++ [x]) <+: L → ∃ y ∈ pre, x.val ≤ y.val + 1

theorem incSorted.nil : incSorted (s := s) [] := by simp [incSorted]
theorem incSorted.singleton : incSorted (s := s) [x] := by
  simp [incSorted]
  rintro (_|⟨pre_hd,pre_tl⟩) y h1 h2 <;> simp_all

theorem incSorted.snoc (L : List (Fin s)) (x : Fin s) (exists_prev : ∃ y ∈ L, x.val ≤ y.val + 1) (h : incSorted L) :
      incSorted (L ++ [x]) := by
  intro pre y pre_ne_nil pre_prefix
  rw [List.prefix_concat_iff] at pre_prefix
  cases pre_prefix
  case inl pre_eq_L =>
    replace pre_eq_L := List.append_inj' pre_eq_L rfl
    simp at pre_eq_L; rcases pre_eq_L with ⟨rfl,rfl⟩
    exact exists_prev
  case inr pre_prefix =>
    exact h pre y pre_ne_nil pre_prefix

def renumberIncr (L : List (Fin s)) : Equiv.Perm (Fin s) :=
  let dedup := L.reverse.dedup.reverse
  let pairs := dedup.zip (List.finRange s)
  Equiv.Perm.setAll pairs

/-- info: [0, 1, 2, 1, 3, 4, 0] -/
#guard_msgs in
#eval let L : List (Fin 10) := [0,2,1,2,5,3,0]
      L.map (renumberIncr L)

lemma renumberIncr.dedup_length (L : List (Fin s)) : L.dedup.length ≤ s := by
  simpa only [Fintype.card_fin] using L.nodup_dedup.length_le_card

lemma renumberIncr.dedup_length_of_not_mem (L : List (Fin s)) {x : Fin s} (hx : x ∉ L) :
    L.dedup.length < s := by
  simpa only [Fintype.card_fin, hx, not_false_eq_true, List.dedup_cons_of_not_mem]
    using (x :: L).nodup_dedup.length_le_card

theorem renumberIncr.eq_of_mem' (L : List (Fin s)) (i : Nat) (hi : i < L.reverse.dedup.reverse.length) :
      renumberIncr L (L.reverse.dedup.reverse[i]'hi) = ⟨i, by
        have := dedup_length L.reverse
        simp at hi; omega⟩ := by
  apply Equiv.Perm.setAll_eq_of_mem
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj i_lt_j
    simp at hi hj ⊢
    rw [L.reverse.nodup_dedup.getElem_inj_iff]
    omega
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj i_lt_j
    simp at hi hj ⊢
    omega
  · apply List.mem_iff_getElem.mpr
    have := dedup_length L.reverse
    simp at hi; simp_all

theorem renumberIncr.eq_of_mem (L : List (Fin s)) {x y : Fin s}
      (hy : y.val < L.reverse.dedup.reverse.length) (h : x = L.reverse.dedup.reverse[y]) :
      renumberIncr L x = y := by
  apply Equiv.Perm.setAll_eq_of_mem
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj i_lt_j
    simp at hi hj ⊢
    rw [L.reverse.nodup_dedup.getElem_inj_iff]
    omega
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj i_lt_j
    simp at hi hj ⊢
    omega
  · apply List.mem_iff_getElem.mpr
    have := dedup_length L.reverse
    use y
    simp at hy
    simp_all

theorem renumberIncr.snoc_mem (L : List (Fin s)) {x : Fin s} (x_mem : x ∈ L) :
    renumberIncr (L ++ [x]) = renumberIncr L := by
  simp [renumberIncr, x_mem]

theorem renumberIncr.snoc_not_mem (L : List (Fin s)) {x : Fin s} (x_not_mem : x ∉ L) :
    (∀ y ∈ L, renumberIncr (L ++ [x]) y = renumberIncr L y) ∧
      renumberIncr (L ++ [x]) x = ⟨L.reverse.dedup.length, dedup_length_of_not_mem L.reverse (by simpa using x_not_mem)⟩ := by
  constructor
  · intro y y_mem
    have ⟨i,hi, (h : L.reverse.dedup.reverse[i]'hi = y)⟩ := List.getElem_of_mem (by simp [y_mem])
    subst y
    rw [List.length_reverse] at hi
    refine Eq.trans (b := ⟨i,?i_lt⟩) ?L (Eq.symm ?R)
    case i_lt =>
      have := dedup_length L.reverse; omega
    case L =>
      apply eq_of_mem
      · simp [x_not_mem, List.getElem_append, hi]
      · simp [x_not_mem]; omega
    case R =>
      apply eq_of_mem
      · simp [x_not_mem, List.getElem_append, hi]
      · simp [x_not_mem]; omega
  · apply eq_of_mem <;> simp [x_not_mem]

theorem renumberIncr.exists_max (L : List (Fin s)) (nonempty : L ≠ []) :
    ∃ y ∈ L, renumberIncr L y = ⟨L.reverse.dedup.reverse.length-1, by
      have := dedup_length L.reverse; have := y.isLt; simp; omega⟩ := by
  have dedup_nonempty : L.reverse.dedup.reverse.length ≠ 0 := by
    intro h; simp at h; contradiction
  let prev_max := L.reverse.dedup.reverse[L.reverse.dedup.reverse.length-1]
  have : prev_max ∈ L := by
    have : prev_max ∈ _ := List.getElem_mem ..
    simpa using this
  use prev_max, this
  apply eq_of_mem
  · simp [prev_max]
  · simp; rw [List.length_reverse] at dedup_nonempty; omega

theorem renumberIncr.incSorted_map (L : List (Fin s)) :
    incSorted (L.map <| renumberIncr L) := by
  rw [← List.reverse_reverse L]
  induction L.reverse with
  | nil => simp; exact incSorted.nil
  | cons hd tl ih =>
    by_cases tl.length = 0
    case pos len_zero =>
      match tl with | [] => apply incSorted.singleton
    case neg tl_len_pos =>
    rw [List.reverse_cons, List.map_append]
    by_cases hd ∈ tl
    case pos mem =>
      rw [snoc_mem _ (by simpa using mem)]
      apply incSorted.snoc
      · simp; use hd; simp [mem]
      · simpa using ih
    case neg mem =>
      have ⟨tl_same, hd_maps⟩ := snoc_not_mem tl.reverse (mem ∘ List.mem_reverse.mp)
      simp_rw [List.mem_reverse] at tl_same
      apply incSorted.snoc
      · simp
        have ⟨y, y_mem, hy⟩ := exists_max tl.reverse (by simpa using tl_len_pos)
        use y
        rw [List.mem_reverse] at y_mem
        specialize tl_same _ y_mem
        simp [tl_same, y_mem, hd_maps, hy]
        omega
      · convert ih using 1
        simp +contextual [tl_same]
