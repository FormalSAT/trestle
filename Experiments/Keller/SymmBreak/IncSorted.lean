/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.Autos

import Mathlib.Logic.Equiv.Basic

/-! ## Increment Sorted

We say a list is "increment sorted" when every
element in the list is `≤ (max before the element)+1`.

For example, `[0,1,2,0]` is inc sorted, and `[0,1,3,0]` is not.

For any list `L`, we can construct a permutation `p`
such that `L.map p` is inc sorted.
-/

def incSorted (L : List Nat) : Prop :=
  ∀ pre x, pre ≠ [] → (pre ++ [x]) <+: L → ∃ y ∈ pre, x ≤ y + 1

theorem incSorted.nil : incSorted [] := by simp [incSorted]
theorem incSorted.singleton : incSorted [x] := by
  simp [incSorted]
  rintro (_|⟨pre_hd,pre_tl⟩) y h1 h2 <;> simp_all

theorem incSorted.snoc (L : List Nat) (x : Nat) (exists_prev : ∃ y ∈ L, x ≤ y + 1) (h : incSorted L) :
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

/--
Given a list `L : List Nat` of values,
returns a permutation on `Fin s` such that
`L` mapped by the permutation is incrementally sorted.
-/
def renumberIncr (L : List Nat) : Equiv.Perm Nat :=
  let dedup := L.reverse.dedup.reverse
  let pairs := dedup.mapIdx (fun i a => (a,i))
  Equiv.Perm.setAll pairs

/-- info: [0, 1, 2, 1, 3, 4, 0] -/
#guard_msgs in
#eval let L : List (Fin 10) := [0,2,1,2,5,3,0]
      L.map (renumberIncr L)

theorem renumberIncr.eq_of_mem_dedup (L : List Nat) {x y : Nat}
      (hy : y < L.reverse.dedup.reverse.length) (h : x = L.reverse.dedup.reverse[y]) :
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
    use y
    simp at hy
    simp_all
    omega

theorem renumberIncr.snoc_mem (L : List Nat) {x : Nat} (x_mem : x ∈ L) :
    renumberIncr (L ++ [x]) = renumberIncr L := by
  simp [renumberIncr, x_mem]

theorem renumberIncr.snoc_not_mem (L : List Nat) {x : Nat} (x_not_mem : x ∉ L) :
    (∀ y ∈ L, renumberIncr (L ++ [x]) y = renumberIncr L y) ∧
      renumberIncr (L ++ [x]) x = L.reverse.dedup.length := by
  constructor
  · intro y y_mem
    replace y_mem := List.getElem_of_mem (l := L.reverse.dedup.reverse)
      (by simp; exact y_mem)
    rcases y_mem with ⟨i,hi,rfl⟩
    simp at hi
    refine Eq.trans (b := i) ?L (Eq.symm ?R)
    case L =>
      apply eq_of_mem_dedup
      · simp [x_not_mem, List.getElem_append, hi]
      · simp [x_not_mem]; omega
    case R =>
      apply eq_of_mem_dedup
      · simp [x_not_mem, List.getElem_append, hi]
      · simp [x_not_mem]; omega
  · apply eq_of_mem_dedup <;> simp [x_not_mem]

theorem renumberIncr.eq_of_mem.aux (L : List Nat) (Lpre : List Nat) (x : Nat)
    (h : Lpre ++ [x] <+: L) (h_not_mem : x ∉ Lpre) :
  renumberIncr L x = Lpre.reverse.dedup.reverse.length := by
  rcases h with ⟨Lsuf, rfl⟩
  apply eq_of_mem_dedup
  · simp [List.dedup_append, h_not_mem]
    have := List.suffix_union_right Lsuf.reverse (x::Lpre.reverse.dedup)
    have := List.IsSuffix.getElem this (i := 0) (by simp)
    simp at this
    convert this using 2
    omega
  · simp [List.dedup_append, h_not_mem]
    rw [Nat.lt_iff_add_one_le]
    trans (x :: Lpre.reverse.dedup).length
    · simp
    · apply List.IsSuffix.length_le
      apply List.suffix_union_right

@[simp] theorem List.length_dedup_reverse [DecidableEq α] (L : List α) :
      L.reverse.dedup.length = L.dedup.length := by
  apply List.Perm.length_eq
  apply List.Perm.dedup
  apply List.reverse_perm

theorem renumberIncr.eq_of_mem (L : List Nat) (Lpre : List Nat) (x : Nat)
    (h : Lpre ++ [x] <+: L) (h_not_mem : x ∉ Lpre) :
  renumberIncr L x = Lpre.dedup.length := by
  rw [eq_of_mem.aux L Lpre x h h_not_mem]
  simp

theorem renumberIncr.exists_max (L : List Nat) (nonempty : L ≠ []) :
    ∃ y ∈ L, renumberIncr L y = L.reverse.dedup.reverse.length-1 := by
  have : L.dedup.length ≠ 0 := by simpa using nonempty
  let prev_max := L.reverse.dedup.reverse[L.reverse.dedup.reverse.length-1]'(by simp; omega)
  have : prev_max ∈ L := by
    have : prev_max ∈ _ := List.getElem_mem ..
    simpa using this
  use prev_max, this
  apply eq_of_mem_dedup
  · simp [prev_max]
  · simp; omega

theorem renumberIncr.incSorted_map (L : List Nat) :
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

private theorem Nat.finset_card_le_max' (S : Finset Nat) (nonempty : S.Nonempty) :
    S.card ≤ S.max' nonempty + 1 := by
  induction S using Finset.induction_on_max
  case h0 =>
    simp at nonempty
  case step max S lt_max ih =>
    -- if S is empty then this is trivial
    if empty : S = ∅ then
      subst S; simp
    else
    have nonempty' : S.Nonempty := Finset.nonempty_of_ne_empty empty

    specialize ih nonempty'

    have max_not_mem : max ∉ S := by
      intro contra; specialize lt_max _ contra; simp at lt_max
    have max'_lt_max := lt_max (S.max' nonempty') (Finset.max'_mem ..)
    clear lt_max

    calc
      _ = S.card+1  := by rw [Finset.card_insert_of_notMem max_not_mem]
      _ ≤ max + 1   := by omega
      _ = _         := by simp [Finset.max'_insert, max_eq_right_of_lt, *]

theorem renumberIncr.eq_of_gt_all (L : List Nat) (x : Nat) (h : ∀ y ∈ L, x > y) :
  renumberIncr L x = x := by
  simp [renumberIncr]
  apply Equiv.Perm.setAll_eq_of_not_mem
  · simp
    rintro - idx idx_range idx_eq_x -
    have : x ∈ L := by
      rw [← idx_eq_x]
      apply (List.reverse_perm _).subset
      apply List.dedup_subset
      apply List.getElem_mem
    clear! idx
    specialize h x this
    simp at h
  · simp
    rintro - idx idx_range -
    suffices ∃ y ∈ L, y + 1 ≥ L.dedup.length by
      rcases this with ⟨y,y_mem,y_ge⟩; specialize h y y_mem; omega
    have : L ≠ [] := by rintro rfl; simp at idx_range
    clear! idx h

    have : L.dedup.length = L.toFinset.card := by
      rw [List.card_toFinset]
    rw [this]; clear this

    have := Nat.finset_card_le_max' L.toFinset (by simp [this])
    refine ⟨_,?_,this⟩
    rw [← List.mem_toFinset]
    apply Finset.max'_mem

theorem renumberIncr.lt_bound (L : List Nat) (bound : Nat) (h : ∀ x ∈ L, x < bound) :
  ∀ y < bound, renumberIncr L y < bound := by
  intro x
  suffices bound ≤ (renumberIncr L) x → (renumberIncr L) x = x by
    intro y_range
    by_contra ge_bound
    push_neg at ge_bound
    specialize this ge_bound
    omega

  intro ge_bound
  have : renumberIncr L ((renumberIncr L) x) = (renumberIncr L) x := by
    apply renumberIncr.eq_of_gt_all
    intro y y_mem; specialize h y y_mem; omega
  simpa using this

def renumberIncr' (L : List Nat) (s) (h : ∀ x ∈ L, x < s) : Equiv.Perm (Fin s) :=
  let aux := renumberIncr L
  let boop : Equiv.Perm { n // n < s } := aux.subtypeEquiv (by
    intro i; unfold aux
    constructor
    · intro lt
      refine renumberIncr.lt_bound _ _ ?_ _ lt
      intro x x_mem; specialize h x x_mem; omega
    · contrapose
      simp
      intro hle
      rw [renumberIncr.eq_of_gt_all _ _ ?h]
      case h =>
        intro x hx; specialize h x hx; omega
      exact hle
    )
  Fin.equivSubtype.trans boop |>.trans Fin.equivSubtype.symm
