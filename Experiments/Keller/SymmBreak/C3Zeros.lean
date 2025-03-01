/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.SymmBreak.TwoCubes

namespace Keller.SymmBreak

/-! ## Maximal Nonzeros in c3

With `c0` and `c1` fixed, the `j ≥ 2` columns are still mostly unconstrained.
It turns out we can force lots of structure on these columns and on `c3`.

From adjacency with `c0` and `c1`, `c3[0] = 0` and `c3[1] = 1` are fixed.
(We don't prove this in Lean; it is true by unit propagation in the CNF).

Then, WLOG we can sort the columns `j ≥ 2` to put `c3` zero elements later
(if there is a zero before a nonzero, swap those cols).

Next we relate `c3` to certain special vertices.
For n=7 these vertices are `c7`, `c11`, `c19`, `c35`, `c67`.
These are special because we can flip one bit to swap them with `c3`
(see the `flipAt` automorphism for more details).

We want to force more nonzero elements into `c3`,
because this permits further symmetry-breaking down the road.
So, we break the symmetry by asserting

    `c3[j] ≠ 0 ∧ c3[j+1] = 0 → ⋁ cX[2:j+1] = 0`

Intuitively, if `c3` is nonzero up until `j`, but `cX` is nonzero up until `j+1`,
we swap `cX` into `c3`'s place to get a longer prefix of nonzero elements.

N.B.  Both of these conditions break the symmetry
      that columns can be arbitrarily reordered.
      But if we prove (or assume) `c3[2:j] = 1` for a range `[2:j]`,
      we *get back* this symmetry on columns `[2:j]`!
-/

structure C3ZerosSorted (n s) extends TwoCubes n s where
  /-- `c3` should have all its zeros at the end. -/
  c3_zeros_sorted : ∀ (j₁ j₂ : Fin (n+2)), 2 ≤ j₁.val ∧ j₁ < j₂ →
      (kclique.get 3)[j₁] = 0 → (kclique.get 3)[j₂] = 0

namespace C3ZerosSorted

theorem ofTwoCubes (tc : TwoCubes n s) : Nonempty (C3ZerosSorted n s) := by
  -- we're going to build up a sorted region inductively
  suffices ∀ (upTo : Nat),
    ∃ (tc' : TwoCubes n s) (zeroStart : Nat), (2 ≤ zeroStart ∧ zeroStart ≤ (upTo+2)) ∧
      ∀ j : Fin (n+2), 2 ≤ j.val ∧ j.val < (upTo+2) →
        if j.val < zeroStart then (tc'.kclique.get 3)[j] ≠ 0 else (tc'.kclique.get 3)[j] = 0
  by
    have ⟨tc',zeroStart,⟨zS_ge,zS_le⟩,h⟩ := this n; clear this
    refine ⟨tc', ?_⟩
    rintro j₁ j₂ ⟨j1_ge_2,j1_lt_j2⟩
    have h_at_j1 := h j₁ (by omega)
    have h_at_j2 := h j₂ (by omega)
    clear h
    split at h_at_j2
    · have : j₁.val < zeroStart := by omega
      simp_all
    · simp_all
  -- now we induct!
  intro upTo
  induction upTo with
  | zero =>
    -- easy done
    use tc, 2; simp
  | succ upTo ih =>
    rcases ih with ⟨tc',zeroStart,⟨zS_ge,zS_le⟩,ih⟩
    -- if upTo is already at the end, it's equivalent to the upTo+1 case
    if upTo_lt : upTo ≥ n then
      use tc', zeroStart, by omega
      rintro j ⟨j_ge,-⟩
      apply ih
      omega
    else
    replace upTo_lt : upTo < n := by omega

    if h : (tc'.kclique.get 3)[upTo+2] = 0 then
      -- if c3[upTo+2] = 0, we don't need to do any swapping around
      use tc', zeroStart, by omega
      intro j j_in_range
      if j.val < upTo + 2 then
        apply ih
        omega
      else
        have j_eq : j.val = upTo+2 := by omega
        have j_lt : ¬ (j.val < zeroStart) := by omega
        simp_rw [j_lt, if_false, Fin.getElem_fin, j_eq]
        simpa using h
    else

    if zS_ne : zeroStart = upTo+2 then
      -- again, we don't need to do any swapping around
      use tc', zeroStart+1, by omega
      intro j j_in_range
      if j.val = upTo+2 then
        have : j.val < zeroStart + 1 := by omega
        simp_all
      else
        have : j.val < zeroStart := by omega
        specialize ih j (by omega)
        simp_all
    else
    -- we need to actually swap columns (upTo+2) <-> zeroStart
    refine ⟨tc'.reorder (Equiv.swap ⟨zeroStart,by omega⟩ ⟨upTo+2, by omega⟩) ?_0 ?_1, ?_⟩
    case _0 | _1 =>
      apply Equiv.swap_apply_of_ne_of_ne <;>
        simp [Fin.ext_iff]
      omega

    -- first a proof that index 3 doesn't change
    have bv3_same :
      (BitVec.ofFn fun j =>
          (3 : BitVec (n+2))[(Equiv.swap (α := Fin (n+2)) ⟨zeroStart, by omega⟩ ⟨upTo + 2, by omega⟩).symm j]
      ) = 3#(n+2) := by
      apply BitVec.eq_of_getElem_eq; intro j hj
      simp only [BitVec.getElem_ofFn, Equiv.symm_swap]
      by_cases j_lt : j < 2
      case pos =>
        have := swap_preserves_earlier
                (a := ⟨zeroStart,by omega⟩) (b := ⟨upTo+2,by omega⟩)
                (i := ⟨j,hj⟩)
                (by simpa using zS_le) (by simp [Fin.lt_def]; omega)
        conv => enter [1,2]; rw [this]
        simp
      case neg =>
        replace j_lt : j ≥ 2 := by omega
        have := swap_at_least_stays_at_least (k := ⟨2,by omega⟩)
                (a := ⟨zeroStart,by omega⟩) (b := ⟨upTo+2,by omega⟩)
                (i := ⟨j,hj⟩)
                (hab := by simpa using zS_le)
                (hk := by simpa [Fin.le_def])
                (by simpa [Fin.le_def])
        simp only [Fin.le_def] at this
        simp only [Fin.getElem_fin, BitVec.ofNat_eq_ofNat, BitVec.getElem_ofNat]
        generalize (Equiv.swap (α := Fin (n+2)) _ _ _).val = j' at this ⊢
        rcases j_lt with (_|_|_) <;> rcases this with (_|_|_) <;> simp [Nat.testBit_succ]

    simp_rw [TwoCubes.kclique_reorder, KClique.get_map_reorder, bv3_same]
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]

    use zeroStart+1, by omega
    intro j j_in_range
    by_cases is_one : j.val < zeroStart + 1 <;> simp only [is_one, if_true, if_false]
    case pos =>
      if j_lt : j.val < zeroStart then
        -- `j ↦ j`
        specialize ih j (by omega)
        simp [j_lt] at ih
        convert ih
        apply Equiv.swap_apply_of_ne_of_ne
          <;> simp [Fin.ext_iff] <;> omega
      else
        -- `j = zeroStart ↦ upTo + 2`
        have j_eq : j = ⟨zeroStart, by omega⟩ := by simp [Fin.ext_iff]; omega
        simp [j_eq]; exact h
    case neg =>
      if j_lt : j.val < upTo + 2 then
        -- `j ↦ j`
        specialize ih j (by omega)
        have : ¬(j.val < zeroStart) := by omega
        simp [this] at ih
        convert ih
        apply Equiv.swap_apply_of_ne_of_ne
          <;> simp [Fin.ext_iff] <;> omega
      else
        -- `j = upTo + 2 ↦ zeroStart`
        have j_eq : j = ⟨upTo+2, by omega⟩ := by simp [Fin.ext_iff]; omega
        specialize ih ⟨zeroStart, by omega⟩ (by simp; omega)
        simpa [j_eq] using ih

end C3ZerosSorted

structure C3Zeros (n s) extends C3ZerosSorted n s where
  /-- `c3` has a nonzero prefix at least as long as any of the other `cX`s -/
  c3_more_nonzero : ∀ (col : Fin (n+2)), col ≥ 2 →
    let X : BitVec (n+2) := 3#(n+2) + BitVec.oneAt col
    ∀ (j : Fin (n+2)), j ≥ 2 →
      (∀ _j, 2 ≤ _j → _j < j → (kclique.get 3)[_j] ≠ 0) ∧ (kclique.get 3)[j] = 0 →
      (∃ (_j : Fin (n+2)), 2 ≤ _j ∧ _j ≤ j ∧ (kclique.get X)[_j] = 0)


namespace C3Zeros

theorem ofC3ZerosSorted (tc : C3ZerosSorted n s) : Nonempty (C3Zeros n s) :=
  sorry
