/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.SymmBreak.TwoCubes

namespace Keller.SymmBreak

/-! ## Minimal Zeros in c3

With `c0` and `c1` fixed, the `j ≥ 2` columns are still mostly unconstrained
-/

namespace C3MinZero

def count (v : Vector (Fin (s+1)) (n+2)) : Nat :=
  Finset.univ (α := Fin (n+2)) |>.filter (fun j => 2 ≤ j.val ∧ v[j.val] = 0) |>.card

theorem count_le_of_nz_prefix (v : Vector (Fin (s+1)) (n+2)) (nzCt : Nat) (nzCt_le : nzCt ≤ n)
  : (∀ j (_: 2 ≤ j ∧ j < nzCt + 2), v[j] ≠ 0) →
    count v ≤ n - nzCt := by
  intro h
  unfold count
  have cards_eq := Finset.filter_card_add_filter_neg_card_eq_card
    (α := Fin (n+2)) (s := {j | j.val ≥ 2}) (p := (v[·] = 0))
  simp [Finset.filter_filter] at cards_eq

  have card_n : Finset.card {j : Fin (n+2) | 2 ≤ j.val} = n := by
    apply Finset.card_eq_of_bijective (f := fun i h => ⟨i+2,by omega⟩)
      <;> simp [Fin.forall_iff]
    intro i h1 h2; use i-2; omega

  have card_le : Finset.card {j : Fin (n+2) | 2 ≤ j.val ∧ ¬v[j.val] = 0} ≥
            Finset.card {j : Fin (n+2) | 2 ≤ j.val ∧ j.val < nzCt + 2 } := by
    apply Finset.card_le_card
    intro j hj
    specialize h j.val
    simp_all

  have card_nzCt : Finset.card {j : Fin (n+2) | 2 ≤ j.val ∧ j.val < nzCt + 2 } = nzCt := by
    apply Finset.card_eq_of_bijective (f := fun i h => ⟨i+2,by omega⟩)
      <;> simp [Fin.forall_iff]
    intro i h1 h2 h3; use i-2; omega

  omega

theorem count_ge_of_z_suffix (v : Vector (Fin (s+1)) (n+2)) (nzCt : Nat) (nzCt_le : nzCt ≤ n)
  : (∀ j (_: nzCt + 2 ≤ j ∧ j < n + 2), v[j] = 0) →
    count v ≥ n-nzCt := by
  intro h
  unfold count
  have cards_eq := Finset.filter_card_add_filter_neg_card_eq_card
    (α := Fin (n+2)) (s := {j | 2 ≤ j.val}) (p := (v[·] = 0))
  simp [Finset.filter_filter] at cards_eq

  have card_n : Finset.card {j : Fin (n+2) | 2 ≤ j.val} = n := by
    apply Finset.card_eq_of_bijective (f := fun i h => ⟨i+2,by omega⟩)
      <;> simp [Fin.forall_iff]
    intro i h1 h2; use i-2; omega

  have card_le : Finset.card {j : Fin (n+2) | 2 ≤ j.val ∧ v[j.val] = 0} ≥
            Finset.card {j : Fin (n+2) | nzCt + 2 ≤ j.val ∧ j.val < n + 2 } := by
    apply Finset.card_le_card
    intro j hj
    specialize h j.val
    simp_all; omega

  have card_nzCt : Finset.card {j : Fin (n+2) | nzCt + 2 ≤ j.val ∧ j.val < n + 2 } = n - nzCt := by
    apply Finset.card_eq_of_bijective (f := fun i h => ⟨i + nzCt + 2,by omega⟩)
      <;> simp [Fin.forall_iff]
    intro i h1 h2; use i-(nzCt+2); omega

  omega

end C3MinZero

open C3MinZero in
structure C3MinZero (n s) extends TwoCubes n s where
  /-- `c3` has fewer zero elements on columns `j ≥ 2` than
    any other index `i` for which `i[1] = true` and the colors at
    all true bits `j ≥ 2` are nonzero. -/
  c3_min_zero :
    ∀ (i : BitVec (n+2)),
      i[1] = true →
      (∀ j (h : 2 ≤ j ∧ j < n+2), i[j] = true → (kclique.get i)[j] ≠ 0) →
      count (kclique.get 3#_) ≤ count (kclique.get i)


namespace C3MinZero

/-! ### Sketch of proof

Assume the condition is broken at index `i`.
We know `i[1] = true` and `∀ j ≥ 2, c_i[j] ≠ 0` and
that the number of zeros in `c0` is > than the number of zeros in `c_i`.

First, if `i[0] = false` we need to flip it to be true.
Flip all index bits at `j=0` and renumber column `j=1` to swap 0 with 1.
Now we have a new `i` with the same properties as before AND `i[0] = true`.

Next, for each column `j ≥ 2` where `i[j] = true`,
we apply a conditional bit flip at color `c_i[j]`.
Since `c_i[j] ≠ 0`, these bit flips do not change `c0` or `c1`,
but once all are applied, we have moved `c_i` into `c_3`'s spot.

Each time we apply this argument, the number of zeros strictly increases.
But it is bounded above by `n`, the number of columns, so the argument must terminate.
-/

theorem setCol0 (tc : TwoCubes n s) (i : BitVec (n+2)) (i1_true : i[1] = true)
    : ∃ tc' : TwoCubes n s, ∃ i' : BitVec (n+2), i'[0] = true ∧ i'[1] = true ∧
          (∀ j (h : 2 ≤ j ∧ j < n+2),
            i'[j] = i[j] ∧ (tc'.kclique.get i')[j] = (tc.kclique.get i)[j]) := by
  if i0_true : i[0] = true then
    use tc, i
    simp [*]
  else
    use tc.flip0, i ^^^ 1#_
    simp [*]
    intro j hj
    constructor
    · omega
    · have : ¬j = 1 := by omega
      simp [TwoCubes.flip0, KClique.get_map_permColors, KClique.get_map_flip,
        BitVec.xor_assoc, this]

theorem flipAtHighBits (tc : TwoCubes n s) (j : Nat) (i : BitVec (n+2))
    (i_bits_high : i[0] = true ∧ i[1] = true) (i_bits_low : ∀ j' (h : j ≤ j' ∧ j' < n+2), i[j'] = false)
    (high_bits_nz : ∀ j (h : 2 ≤ j ∧ j < n+2), i[j] = true → (tc.kclique.get i)[j] ≠ 0)
  : ∃ tc' : TwoCubes n s, tc.kclique.get i = tc'.kclique.get 3 := by
  if j > n+2 then
    exact flipAtHighBits tc (n+2) i i_bits_high (by simp) high_bits_nz
  else if j ≤ 2 then
    use tc; congr; ext j' h
    match j' with
    | 0 | 1 =>
      simp [i_bits_high]; simp [bv_toNat] <;> decide
    | j+2 =>
      rw [i_bits_low _ (by omega)]
      simp [bv_toNat]; simp [Nat.testBit, Nat.shiftRight_succ_inside]
  else
    match j with
    | j+1 =>
    if i[j] = false then
      apply flipAtHighBits tc j i i_bits_high ?_ high_bits_nz
      intro j' j'_range
      if j = j' then
        subst j'; assumption
      else
        apply i_bits_low
        omega
    else
      let tc' := tc.flipAt ⟨j,by omega⟩ (tc.kclique.get i)[j]
            (by simp; omega)
            (high_bits_nz j (by omega) (by simp [*]))
      let i' := i ^^^ BitVec.oneAt ⟨j,by omega⟩
      have tc'_i'_eq : (tc.kclique.get i) = (tc'.kclique.get i') := by
        simp [tc', i', KClique.get_map_flipAt, BitVec.xor_assoc]
        rw [KClique.get_xor_oneAt (h := by simp)]
        simp
      rw [tc'_i'_eq]
      apply flipAtHighBits (j := j)
      case i_bits_high =>
        simp [i', *]; omega
      case i_bits_low =>
        intro j' h; if j = j' then subst j'; simp [i', *] else simp [i', *]; apply i_bits_low; omega
      case high_bits_nz =>
        intro j' j'_range i'_j'
        rw [← tc'_i'_eq]
        have j_ne_j' : j ≠ j' := by rintro rfl; simp [i', *] at i'_j'
        apply high_bits_nz j' j'_range
        simpa [i', j_ne_j'] using i'_j'

theorem swapToC3 (tc : TwoCubes n s) (i : BitVec (n+2)) (i1_true : i[1] = true)
          (high_bits_nz : ∀ j (h : 2 ≤ j ∧ j < n+2), i[j] = true → (tc.kclique.get i)[j] ≠ 0)
    : ∃ tc' : TwoCubes n s, ∀ j (h : 2 ≤ j ∧ j < n+2),
          (tc'.kclique.get 3)[j] = (tc.kclique.get i)[j] := by
  have := setCol0 tc i i1_true
  rcases this with ⟨tc',i',i'0_true,i'1_true,h⟩
  have := flipAtHighBits tc' (n+2) i' (i_bits_high := by simp [*])
    (i_bits_low := by intros; exfalso; omega)
    (high_bits_nz := by
      intro j j_range i'_true
      rw [(h j j_range).1] at i'_true
      rw [(h j j_range).2]
      apply high_bits_nz j j_range i'_true)
  rcases this with ⟨tc'',h'⟩
  use tc''
  intro j j_range
  rw [← h', (h j j_range).2]


open Classical in
theorem ofTwoCubes (tc : TwoCubes n s) : Nonempty (C3MinZero n s) :=
  if h : _ then
    ⟨tc,h⟩
  else by
  push_neg at h
  rcases h with ⟨i,i1_true,high_bits_nz,count_lt⟩
  have ⟨tc',h⟩ := swapToC3 tc i i1_true high_bits_nz
  clear high_bits_nz
  replace h : ∀ j : Fin _,
      2 ≤ j.val ∧ (tc'.kclique.get 3#_)[j.val] = 0 ↔
      2 ≤ j.val ∧ (tc.kclique.get i)[j] = 0   := by
    simp; intro j hj; specialize h j (by omega); simp at h
    simp [h]
  have : count (tc'.kclique.get 3#(n + 2)) < count (tc.kclique.get 3#(n + 2)) := by
    unfold count
    simp [h]
    simpa using count_lt
  exact ofTwoCubes tc'
termination_by count (tc.kclique.get 3)

end C3MinZero

structure C3MinZeroSorted (n s) extends C3MinZero n s where
  c3_sorted : ∀ j (h : 2 ≤ j ∧ j + 1 < n+2), (kclique.get 3)[j] = 0 → (kclique.get 3)[j+1] = 0

namespace C3MinZeroSorted

section
variable (j₁) (j₁_range : 2 ≤ j₁ ∧ j₁ < n+2) (j₂) (j₂_range : 2 ≤ j₂ ∧ j₂ < n+2)

def swap : Equiv.Perm (Fin (n+2)) :=
  Equiv.swap ⟨j₁,by omega⟩ ⟨j₂,by omega⟩

theorem swap_lt_2 (j) : (swap j₁ j₁_range j₂ j₂_range j).val < 2 ↔ j.val < 2 := by
  simp [swap, Equiv.swap_apply_def]
  split
  · subst j; simp; omega
  · split
    · subst j; simp; omega
    · rfl

theorem swap_ge_2 (j) : 2 ≤ (swap j₁ j₁_range j₂ j₂_range j).val ↔ 2 ≤ j.val := by
  rw [← not_iff_not]; simp; exact swap_lt_2 ..

def idxMap : BitVec (n+2) → BitVec (n+2) :=
  fun idx => BitVec.ofFn fun j => idx[(swap j₁ j₁_range j₂ j₂_range).symm j]

theorem idxMap_three : idxMap j₁ j₁_range j₂ j₂_range (3#(n+2)) = 3#(n+2) := by
  unfold idxMap swap
  ext j₂ range
  simp [bv_toNat, range]
  rw [Bool.eq_iff_iff, Nat.testBit_three]
  conv => rhs; rw [Nat.testBit_three j₂]
  apply swap_lt_2 <;> assumption

theorem idxMap_get_1 : (idxMap j₁ j₁_range j₂ j₂_range i)[1] = i[1] := by
  unfold idxMap swap
  simp; congr; rw [Equiv.swap_apply_of_ne_of_ne] <;> simp <;> omega

theorem kclique_map_get_eq_get_idxMap (kc : KClique _ s) {i} {j} (j_range)
  : (kc.map (KAuto.permColumns (swap j₁ j₁_range j₂ j₂_range)) |>.get i)[j]'j_range =
    (kc.get (idxMap j₁ j₁_range j₂ j₂_range i))[(swap j₁ j₁_range j₂ j₂_range) ⟨j,by omega⟩] := by
  rw [KClique.get_map_permColumns]
  unfold idxMap
  simp

theorem kclique_map_swap_get (kc : KClique _ s) {i}
  : (kc.map (KAuto.permColumns (swap j₁ j₁_range j₂ j₂_range))).get i =
    Vector.ofFn fun j => (kc.get (idxMap j₁ j₁_range j₂ j₂_range i))[(swap j₁ j₁_range j₂ j₂_range) j] := by
  ext j j_range
  simp [kclique_map_get_eq_get_idxMap]

end

theorem count_perm_eq (p : Equiv.Perm (Fin (n+2))) (h : ∀ j, (p.symm j).val < 2 ↔ j.val < 2)
    (v : Vector (Fin (s+1)) _)
  : C3MinZero.count (Vector.ofFn fun j => v[p j]) = C3MinZero.count v := by
  unfold C3MinZero.count
  simp
  rw [← Finset.card_map (f := p.toEmbedding), Finset.map_filter]
  simp
  congr; ext j; simp; rintro -
  rw [← not_iff_not]
  simpa using h j

-- start from c3[j'] = 0 for j' > j and reduce `j` inductively until c3 is sorted
theorem reorderZero (tc : C3MinZero n s) (j) (j_range : j < n+2)
    (h_zeros : ∀ j' (h : j < j' ∧ j' < n+2), (tc.kclique.get 3#_)[j'] = 0)
  : Nonempty (C3MinZeroSorted n s) := by
  induction j using Nat.strong_induction_on generalizing tc
  next j₁ ih =>
  if h_nonzeros : ∀ j' (h : 2 ≤ j' ∧ j' < j₁), (tc.kclique.get 3)[j'] ≠ 0 then
    refine ⟨{toC3MinZero := tc, c3_sorted := ?_}⟩
    rintro j' j'_range j'_is_zero
    have : j' ≥ j₁ := by by_contra; apply h_nonzeros _ _ j'_is_zero; omega
    apply h_zeros; omega
  else
    push_neg at h_nonzeros
    rcases h_nonzeros with ⟨j₂,hj₂,j₂_zero⟩
    let tc' := tc.permColumns (swap j₁ (by omega) j₂ (by omega)) ?fix0 ?fix1
    case fix0 | fix1 =>
      apply Equiv.swap_apply_of_ne_of_ne <;> (simp; omega)
    let min' : C3MinZero n s := { tc' with c3_min_zero := ?c3_min_zero }
    case c3_min_zero =>
      intro i i1_true high_bits_nz
      simp [tc']
      convert tc.c3_min_zero (idxMap j₁ (by omega) j₂ (by omega) i) ?_ ?_ using 1
      case convert_1 =>
        simp [idxMap_get_1, i1_true]
      case convert_2 =>
        intro j j_range ij_true
        simp [idxMap] at ij_true
        specialize high_bits_nz _ ?_ ij_true
        · simp; rw [← swap_ge_2, Equiv.apply_symm_apply]; simp; omega
        simpa [tc', kclique_map_get_eq_get_idxMap] using high_bits_nz
      · rw [kclique_map_swap_get, idxMap_three, count_perm_eq]
        · intro j; rw [← swap_lt_2, Equiv.apply_symm_apply]
      · rw [kclique_map_swap_get, count_perm_eq]
        · intro j; rw [← swap_lt_2, Equiv.apply_symm_apply]
    apply ih (j₁-1) (by omega) min' (by omega)
    intro j j_range
    simp [min', tc']
    rw [kclique_map_get_eq_get_idxMap, idxMap_three]
    if j = j₁ then
      subst j; simp [swap]; exact j₂_zero
    else
      have : j > j₁ := by omega
      have : j ≠ j₂ := by omega
      simp [swap, Equiv.swap_apply_of_ne_of_ne, *]

theorem ofC3MinZero (tc : C3MinZero n s) : Nonempty (C3MinZeroSorted n s) := by
  apply reorderZero tc (n+1) (by omega) (by omega)



theorem c3_zeroSuffix (tc : C3MinZeroSorted n s) (j) (hj : 2 ≤ j ∧ j < n+2) :
  (tc.kclique.get 3#_)[j] = 0 → ∀ j' (_: j ≤ j' ∧ j' < n+2), (tc.kclique.get 3#_)[j'] = 0 := by
  intro zeroAtJ j' j'_range
  induction j' using Nat.strongRecOn
  next j' ih =>
  if j = j' then
    subst j'; exact zeroAtJ
  else
    specialize ih (j'-1) (by omega) (by omega)
    have := tc.c3_sorted _ (by omega) ih
    convert this; omega

theorem c3_nzPrefix (tc : C3MinZeroSorted n s) (j) (hj : 2 ≤ j ∧ j < n+2) :
  (tc.kclique.get 3#_)[j] ≠ 0 → ∀ j' (_: 2 ≤ j' ∧ j' ≤ j), (tc.kclique.get 3#_)[j'] ≠ 0 := by
  intro nzAtJ j' j'_range
  intro contra
  have := c3_zeroSuffix _ _ (by omega) contra j (by omega)
  contradiction
