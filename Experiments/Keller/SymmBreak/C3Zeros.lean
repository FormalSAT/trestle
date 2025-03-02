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

Furthermore, we relate `c3` to certain special vertices.
For n=7 these vertices are `c7`, `c11`, `c19`, `c35`, `c67`.
These are special because we can flip one bit to swap them with `c3`
(see the `flipAt` automorphism for more details).

We want to force more nonzero elements into `c3`,
because this permits further symmetry-breaking down the road.
So, we break the symmetry by asserting

    `c3[j] ≠ 0 ∧ c3[j+1] = 0 → ⋁ cX[2:j+1] = 0`

Intuitively, if `c3` is nonzero up until `j`, but `cX` is nonzero up until `j+1`,
we swap `cX` into `c3`'s place to get a longer prefix of nonzero elements.

We must prove we can break these symmetries simultaneously,
because they interfere with one another.
The proof proceeds by building this structure on columns `[2:j]`,
inducting on j until we reach `n`.

N.B.  These conditions interfere with
      the column reordering symmetry.
      But if we prove (or assume) `c3[2:j] = 1`,
      we can reorder columns `[2:j]`.
      Similarly, if we prove (or assume) `c3[j:n] = 0`,
      we can reorder columns `[j:n]`.
-/

structure C3ZerosSorted (n s) extends TwoCubes n s where
  /-- `c3` should have all its zeros at the end. -/
  c3_zeros_sorted : ∀ (j₁ j₂ : Fin (n+2)), 2 ≤ j₁.val ∧ j₁ < j₂ →
      (kclique.get 3)[j₁] = 0 → (kclique.get 3)[j₂] = 0

namespace C3ZerosSorted

theorem ofTwoCubes (tc : TwoCubes n s) : Nonempty (C3ZerosSorted n s) := by
  -- we're going to build up a sorted region inductively
  suffices ∀ (upTo : Nat) (upTo_le : upTo ≤ n),
    ∃ (tc' : TwoCubes n s) (zeroStart : Nat), (2 ≤ zeroStart ∧ zeroStart ≤ (upTo+2)) ∧
      ∀ (j) (j_in_range : 2 ≤ j ∧ j < upTo+2),
        if j < zeroStart then (tc'.kclique.get 3)[j] ≠ 0 else (tc'.kclique.get 3)[j] = 0
  by
    have ⟨tc',zeroStart,⟨zS_ge,zS_le⟩,h⟩ := this n (by simp); clear this
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
  intro upTo upTo_le
  induction upTo with
  | zero =>
    -- easy done
    use tc, 2; simp
  | succ upTo ih =>
    rcases ih (Nat.le_of_lt upTo_le) with ⟨tc',zeroStart,⟨zS_ge,zS_le⟩,ih⟩
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
      if j < upTo + 2 then
        apply ih
        omega
      else
        have j_eq : j = upTo+2 := by omega
        have j_lt : ¬ (j < zeroStart) := by omega
        simp_rw [j_lt, if_false, j_eq]
        simpa using h
    else

    if zS_ne : zeroStart = upTo+2 then
      -- again, we don't need to do any swapping around
      use tc', zeroStart+1, by omega
      intro j j_in_range
      if j = upTo+2 then
        have : j < zeroStart + 1 := by omega
        simp_all
      else
        have : j < upTo+2 := by omega
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
    by_cases is_one : j < zeroStart + 1 <;> simp only [is_one, if_true, if_false]
    case pos =>
      if j_lt : j < zeroStart then
        -- `j ↦ j`
        specialize ih j (by omega)
        simp [j_lt] at ih
        convert ih
        rw [Equiv.swap_apply_of_ne_of_ne]
          <;> simp [Fin.ext_iff] <;> omega
      else
        -- `j = zeroStart ↦ upTo + 2`
        have j_eq : j = zeroStart := by omega
        simp [j_eq]; exact h
    case neg =>
      if j_lt : j < upTo + 2 then
        -- `j ↦ j`
        specialize ih j (by omega)
        have : ¬(j < zeroStart) := by omega
        simp [this] at ih
        convert ih
        rw [Equiv.swap_apply_of_ne_of_ne]
          <;> simp [Fin.ext_iff] <;> omega
      else
        -- `j = upTo + 2 ↦ zeroStart`
        have j_eq : j = upTo+2 := by omega
        specialize ih zeroStart (by omega)
        simpa [j_eq] using ih

end C3ZerosSorted

structure C3Zeros (n s) extends TwoCubes n s where
  /-- `c3` should have all its zeros at the end. -/
  c3_zeros_sorted : ∀ (j₁ j₂ : Nat) (range : 2 ≤ j₁ ∧ j₁ < j₂ ∧ j₂ < n+2),
      (kclique.get 3)[j₁] = 0 → (kclique.get 3)[j₂] = 0
  /-- `c3` has a nonzero prefix at least as long as any of the other `cX`s -/
  c3_more_nonzero : ∀ (col : Fin (n+2)), col.val ≥ 2 →
    let X : BitVec (n+2) := 3#(n+2) + BitVec.oneAt col
    ∀ (j : Nat) (range : 2 ≤ j ∧ j < n+1),
      (kclique.get 3)[j] ≠ 0 ∧ (kclique.get 3)[j+1] = 0 →
      (∃ (_j : Nat) (range : 2 ≤ _j ∧ _j ≤ j), (kclique.get X)[_j] = 0)


namespace C3Zeros

/-- This is a version of `C3Zeros` where the conditions only hold up to `upTo + 2`. -/
private structure UpTo (n s) (upTo : Nat) (upTo_le : upTo ≤ n) extends TwoCubes n s where
  zeroStart : Nat
  zeroStart_ge : zeroStart ≥ 2
  zeroStart_le : zeroStart ≤ upTo+2
  c3_nonzeros : ∀ (j) (range : 2 ≤ j ∧ j < zeroStart), (kclique.get 3)[j] ≠ 0
  c3_zeros : ∀ (j) (range : zeroStart ≤ j ∧ j < upTo+2), (kclique.get 3)[j] = 0
  c3_more_nonzero : ∀ (col) (range : 2 ≤ col ∧ col < upTo+2),
    let X : BitVec (n+2) := 3#(n+2) + BitVec.oneAt ⟨col, by omega⟩
    (∃ (j : Nat) (range : 2 ≤ j ∧ j < zeroStart), (kclique.get X)[j] = 0)

def UpTo.zero (tc : TwoCubes n s) : UpTo n s 0 (by simp) where
  toTwoCubes := tc
  zeroStart := 2
  zeroStart_ge := by simp
  zeroStart_le := by simp
  c3_nonzeros := by simp
  c3_zeros := by simp
  c3_more_nonzero := by simp

theorem UpTo.step (u : UpTo n s upTo upTo_le) (upTo_lt : upTo < n) : Nonempty (UpTo n s (upTo+1) upTo_lt) := by
  sorry

def UpTo.at_n (u : UpTo n s n (Nat.le_refl _)) : C3Zeros n s where
  toTwoCubes := u.toTwoCubes
  c3_zeros_sorted := by
    intro j₁ j₂ range h
    if j₂ ≥ u.zeroStart then
      exact u.c3_zeros j₂ (by omega)
    else
      have := u.c3_nonzeros j₁ (by omega)
      contradiction
  c3_more_nonzero := by
    rintro ⟨col,col_lt⟩ col_ge; simp at col_ge
    intro X j range ⟨ne_zero,eq_zero⟩
    -- ne_zero and eq_zero fix zeroStart
    have : u.zeroStart > j := by
      have := u.c3_zeros j
      simp only [ne_zero, imp_false] at this
      omega
    have : u.zeroStart ≤ j+1 := by
      have := u.c3_nonzeros (j+1)
      simp only [eq_zero] at this
      omega
    have ⟨j,range,h⟩ := u.c3_more_nonzero col (by omega)
    use j, by omega

theorem ofTwoCubes (tc : TwoCubes n s) : Nonempty (C3Zeros n s) := by
  suffices ∀ upTo h, Nonempty (UpTo n s upTo h) by
    have ⟨u⟩ := this n (Nat.le_refl _)
    exact ⟨UpTo.at_n u⟩
  intro upTo upTo_le
  induction upTo with
  | zero =>
    exact ⟨UpTo.zero tc⟩
  | succ upTo ih =>
    have ⟨u⟩ := ih (Nat.le_of_lt upTo_le)
    exact UpTo.step u _
