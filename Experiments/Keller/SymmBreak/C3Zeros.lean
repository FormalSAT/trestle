/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.SymmBreak.TwoCubes

namespace Keller.SymmBreak

/-! ## Maximal Nonzeros in c3

With `c0` and `c1` fixed, the `j ≥ 2` columns are still mostly unconstrained

```
      0   1   2   3   4   5   6
 c0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
 c1 |-0-| 1 | 0 | 0 | 0 | 0 | 0 |
```

In particular we can still reorder these columns arbitrarily.
So, we pick an ordering of columns `j ≥ 2` such that
the nonzero elements of `c3` occur *before* the zero elements:

  (1)  `c3[j] = 0 → c3[j+1] = 0`

Furthermore, we relate `c3` to certain special vertices.
For n=7 these vertices are `c7`, `c11`, `c19`, `c35`, `c67`.
These are special because we can flip one bit in their index
to swap them with `c3` (see the `flipAt` automorphism for details).

It will help later on to have more nonzero elements in `c3`.
So, if `c3` is nonzero up to `j`, and zero starting at `j+1`,
and `cX` is nonzero up until `j`, then `cX` should also be zero starting at `j+1`.
Otherwise we swap `cX` into `c3`'s place to get a longer
prefix of nonzero elements:

```
      0   1   2   3   4   5   6
 c0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
 c1 | 0 | 1 | 0 | 0 | 0 | 0 | 0 |
 c3 | 0 | 1 | 1 | 1 | 1 | 0 | 0 |
c19 | 0 | 1 | 2 | 2 | 1 | 0 | 1 |
                              ^ nonzero!!!

(exchange c3 with c19)

      0   1   2   3   4   5   6
 c0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
 c1 |-0-| 1 | 0 | 0 | 0 | 0 | 0 |
 c3 |-0-|-1-| 2 | 2 | 1 | 0 | 1 |
c19 |-0-|-1-| 1 | 1 |-1-| 0 | 0 |

(swap columns 5<->6)

      0   1   2   3   4   5   6
 c0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
 c1 |-0-| 1 | 0 | 0 | 0 | 0 | 0 |
 c3 |-0-|-1-| 2 | 2 | 1 | 1 | 0 |
c19 |-0-|-1-| 1 | 1 |-1-| 0 | 0 |

```

In code, for each `X` we enforce that:

    `c3[j] ≠ 0 ∧ c3[j+1] = 0 ∧ (⋀ cX[2:j] ≠ 0) → (⋀ cX[j+1:n+2] = 0)`

In this file, we prove that any clique with `c0` and `c1` fixed
can be transformed into one where both of these conditions on `c3` hold.
We prove both conditions simultaneously.

N.B.  These conditions interfere with the column reordering symmetry.
      But if we prove (or assume) `c3[2:j] = 1`, we can reorder columns `[2:j]`.
      Similarly, if we prove (or assume) `c3[j:n] = 0`,
      we can reorder columns `[j:n]`.
-/

def C3Zeros.X (row : Nat) (range : 2 ≤ row ∧ row < n+2) : BitVec (n+2) :=
  3#(n+2) ^^^ BitVec.oneAt ⟨row,range.2⟩

structure C3Zeros (n s) extends TwoCubes n s where
  /-- `c3` should have all its zeros at the end. -/
  c3_zeros_sorted : ∀ (j : Nat) (range : 2 ≤ j ∧ j + 1 < n+2),
      (kclique.get 3)[j] = 0 → (kclique.get 3)[j+1] = 0
  /-- if `c3` is nonzero up to `j`, then for the `cX` up to `j`,
      either there is a nonzero element at or before `j`,
      or *all* the elements after `j` are zero. -/
  c3_more_nonzero :
    ∀ (j : Nat) (range : 2 ≤ j ∧ j + 1 < n + 2),
      (kclique.get 3)[j] ≠ 0 ∧ (kclique.get 3)[j+1] = 0 →
      ∀ (row : Nat) (cr : 2 ≤ row ∧ row ≤ j),
      (∀ (_j : Nat) (range : 2 ≤ _j ∧ _j ≤ j),
        (kclique.get (C3Zeros.X row (by omega)))[_j] ≠ 0)
      → (∀ (_j : Nat) (range : j < _j ∧ _j < n + 2),
        (kclique.get (C3Zeros.X row (by omega)))[_j] = 0)


namespace C3Zeros

def X_get_col_eq_3_get_col (tc : TwoCubes n s) (row) (h) :
  (tc.kclique.get (X row h))[row] = (tc.kclique.get 3)[row] := by
  have := tc.kclique.get_adj_of_eq_xor (i₁ := 3) (i₂ := X row h) ⟨row,by omega⟩
  specialize this (by simp [X])
  exact this.1.symm

/-! ### Sketch of proof

Call the number of nonzero elements in `c3` on columns `[2:j]` as `numNz`.
The proof proceeds by finding cliques with higher `numNz`,
until eventually we can prove both properties in `C3Zeros`.

There are basically 4 cases:

  (0) We hit `numNz = n`, which suffices to prove `C3Zeros`.

  (1) `c3` already has another nonzero element at col `j ≥ 2+numNz`.
      If we swap `j` with `2+numNz`, the new clique will have `numNz+1`.

  (2) There's a `cX` with `2 ≤ row < 2+numNz`,
          and `cX` is entirely nonzero before `2+numNz`,
          and `cX` has a nonzero element at col `j ≥ 2+numNz`.
      If we flip `cX` up to `c3`, then we can apply the same argument as (1)
      to get to `numNz+1`.

  (3) Neither (1) nor (2) apply, which suffices to prove `C3Zeros`

-/

/-- asserts that `c3[2:2+numNz] ≠ 0`. -/
def hasNumNz (tc : TwoCubes n s) (numNz : Nat) (h : numNz ≤ n) : Prop :=
  ∀ (j) (range : 2 ≤ j ∧ j < 2+numNz), (tc.kclique.get 3)[j] ≠ 0

/-- all cliques can have `numNz = 0`. -/
theorem hasNumNz_zero (tc : TwoCubes n s) : hasNumNz tc 0 (Nat.zero_le _) := by
  simp [hasNumNz]

/--
  (0) We hit `numNz = n`, which suffices to prove `C3Zeros`.
-/
theorem of_hasNumNz_n (tc : TwoCubes n s) (h : hasNumNz tc n (Nat.le_refl _)) :
              Nonempty (C3Zeros n s) := by
  refine ⟨{
    toTwoCubes := tc
    c3_zeros_sorted := by
      intro j range j_zero
      have := h j (by omega)
      contradiction
    c3_more_nonzero := by
      rintro j range ⟨-,c3_jsucc_z⟩
      exfalso
      have := h (j+1) (by omega)
      contradiction
  }⟩

/--
  (1) `c3` already has another nonzero element at col `j ≥ 2+numNz`.
      If we swap `j` with `2+numNz`, the new clique will have `numNz+1`.
-/
theorem hasNumNz_succ_of_c3_nonzero (tc : TwoCubes n s) (numNz_lt : numNz < n)
      (hasNum : hasNumNz tc numNz (Nat.le_of_lt numNz_lt))
      (exists_nonzero : ∃ (j : Nat) (range : 2 + numNz ≤ j ∧ j < n+2),
          (tc.kclique.get 3)[j] ≠ 0)
      : ∃ tc : TwoCubes n s, hasNumNz tc (numNz+1) numNz_lt := by
  rcases exists_nonzero with ⟨j, range, j_nonzero⟩

  use tc.reorder (Equiv.swap ⟨j,by omega⟩ ⟨2+numNz,by omega⟩) ?fix0 ?fix1
  case fix0 | fix1 =>
    apply Equiv.swap_apply_of_ne_of_ne <;> simp [Fin.ext_iff] <;> omega

  intro j' range'
  rw [TwoCubes.kclique_reorder, KClique.get_map_reorder, Vector.getElem_ofFn]

  -- rewrite the bitvec to be 3 again (it's just 3)
  suffices (tc.kclique.get 3)[(Equiv.swap (α := Fin (n+2)) ⟨j, _⟩ ⟨2 + numNz, by omega⟩) ⟨j', by omega⟩] ≠ 0 by
    convert this
    apply BitVec.eq_of_getElem_eq; intro i hi
    simp only [BitVec.getElem_ofFn, Equiv.symm_swap, Fin.getElem_fin]
    -- for i < 2 the swap doesn't touch j, and for i ≥ 2 it doesn't matter
    by_cases i < 2
    case pos i_lt =>
      congr 1; rw [Equiv.swap_apply_of_ne_of_ne] <;> simp <;> omega
    case neg i_ge =>
      replace i_ge : i ≥ 2 := by omega
      simp [BitVec.getElem_eq_testBit_toNat, hi]
      generalize hi' : (Equiv.swap (α := Fin (n+2)) _ _ _).val = i'
      replace hi' : i' ≥ 2 := by
        simp [Equiv.swap, Equiv.swapCore] at hi'
        split at hi'
        · simp at hi'; omega
        · split at hi' <;> simp at hi' <;> omega

      rcases i_ge with (_|_|_) <;> rcases hi' with (_|_|_) <;> simp [Nat.testBit_succ]

  if j' = 2+numNz then
    -- the nonzero element we just swapped in is here
    subst j'; simp only [Equiv.swap_apply_right, Fin.getElem_fin]
    exact j_nonzero
  else
    -- it's the same nonzero element it was before
    have : j' < 2+numNz := by omega
    rw [Equiv.swap_apply_of_ne_of_ne ?beep ?boop]
    case beep | boop => simp; omega
    simpa using hasNum j' (by omega)

/-
  (2) There's a `cX` with `2 ≤ row < 2+numNz`,
          and `cX` is entirely nonzero before `2+numNz`,
          and `cX` has a nonzero element at col `j ≥ 2+numNz`.
      If we flip `cX` up to `c3`, then we can apply the same argument as (1)
      to get to `numNz+1`.
-/
theorem hasNumNz_succ_of_cX_nonzero (tc : TwoCubes n s) (numNz_lt : numNz < n)
    (hasNum : hasNumNz tc numNz (Nat.le_of_lt numNz_lt))
    (exists_nonzero : ∃ (row : Nat) (crange : 2 ≤ row ∧ row < 2+numNz),
      (∀ (j) (range : 2 ≤ j ∧ j < 2+numNz), (tc.kclique.get (X row (by omega)))[j] ≠ 0) ∧
      ∃ (j : Nat) (range : 2 + numNz ≤ j ∧ j < n+2),
      (tc.kclique.get (X row (by omega)))[j] ≠ 0)
    : ∃ tc : TwoCubes n s, hasNumNz tc (numNz+1) numNz_lt := by

  rcases exists_nonzero with ⟨row,crange,cX_nz,j,range,j_nonzero⟩

  -- swap cX to c3
  let tc' := tc.flipAt ⟨row,by omega⟩ (tc.kclique.get (X row (by omega)))[row]
    (j_ge := by simp; omega)
    (k_ne_0 := by rw [X_get_col_eq_3_get_col]; apply hasNum; omega)

  -- now we can apply (1)
  apply hasNumNz_succ_of_c3_nonzero tc'
  -- .... but we need to prove our obligations

  case hasNum =>
    intro j' range'
    simp [tc', KClique.get_map_flipAt, X_get_col_eq_3_get_col]
    exact cX_nz j' range'

  case exists_nonzero =>
    use j, range
    simp [tc', KClique.get_map_flipAt, X_get_col_eq_3_get_col]
    exact j_nonzero


open Classical in
theorem of_hasNumNz (tc : TwoCubes n s) (hasNum : hasNumNz tc numNz numNz_le) :
    Nonempty (C3Zeros n s) :=

  -- case (0)
  if numNz_ne : numNz = n then by
    subst numNz; apply of_hasNumNz_n tc hasNum
  else
  have numNz_lt : numNz < n := by omega

  -- case (1)
  if h_c3 : _ then
    have ⟨tc',hasNum'⟩ :=
      hasNumNz_succ_of_c3_nonzero tc numNz_lt hasNum h_c3
    of_hasNumNz tc' hasNum'
  else

  -- case (2)
  if h_cX : _ then
    have ⟨tc',hasNum'⟩ :=
      hasNumNz_succ_of_cX_nonzero tc numNz_lt hasNum h_cX
    of_hasNumNz tc' hasNum'
  else

  -- case (3)
  by
  push_neg at h_c3 h_cX
  exact ⟨{
    toTwoCubes := tc
    c3_zeros_sorted := by
      intro j range h
      apply h_c3
      have := hasNum j; simp only [ne_eq,h] at this
      simp at this
      omega
    c3_more_nonzero := by
      rintro j range ⟨j_nz,j_succ_z⟩ col crange cX_nz j' range'
      have : j = numNz + 1 := by
        have upper := h_c3 j; simp only [ne_eq,j_nz] at upper
        have lower := hasNum (j+1); simp only [ne_eq,j_succ_z] at lower
        clear * - range upper lower
        simp at upper lower
        omega
      apply h_cX col (by omega)
      · intro j'' range''; apply cX_nz; omega
      · omega
  }⟩

termination_by n - numNz

theorem ofTwoCubes (tc : TwoCubes n s) : Nonempty (C3Zeros n s) :=
  of_hasNumNz tc (hasNumNz_zero _)
