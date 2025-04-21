/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio, Cayden Codel
-/

import Experiments.SR.Upstream

/-

Arrays that implicitly partition a pool of data into contiguous ranges.
Handles deletions.

TODO: Garbage collection when enough deletions have occurred.
TODO: Make the indexes `UInt64` and use a negation flag, since arrays
      will never get "too large"

-/

namespace Trestle

namespace RangeArray

@[inline, always_inline]
def markIndexAsDeleted (i : Int) : Int :=
  if i ≥ 0 then -i - 1 else i

@[inline, always_inline]
def getIndexFromMarkedIndex (i : Int) : Nat :=
  if i ≥ 0 then i.natAbs else i.natAbs - 1

@[simp]
theorem getIndex_markIndex (i : Int) :
    getIndexFromMarkedIndex (markIndexAsDeleted i) = getIndexFromMarkedIndex i := by
  simp [markIndexAsDeleted, getIndexFromMarkedIndex]
  by_cases hi : 0 ≤ i
  <;> simp only [hi, ↓reduceIte]
  · rcases Int.exists_nat_of_ge_zero hi with ⟨n, rfl⟩
    split <;> omega

theorem markIndexAsDeleted_coe (n : Nat) : markIndexAsDeleted n = -n - 1 := by
  simp [markIndexAsDeleted]

@[simp]
theorem getIndexFromMarkedIndex_coe (n : Nat) : getIndexFromMarkedIndex n = n := by
  simp [getIndexFromMarkedIndex]

@[simp]
theorem markIndex_getIndex_coe (n : Nat) : getIndexFromMarkedIndex (markIndexAsDeleted n) = n := by
  simp [markIndexAsDeleted, getIndexFromMarkedIndex]
  by_cases hn : 0 ≤ (n : Int)
  · split <;> omega
  · omega

theorem markIndex_getIndex_of_ge_zero {i : Int} :
    0 ≤ i → getIndexFromMarkedIndex (markIndexAsDeleted i) = i := by
  intro hi
  rcases Int.exists_nat_of_ge_zero hi with ⟨n, rfl⟩
  rw [markIndex_getIndex_coe]

end RangeArray


/-
  A structure with a single pool of data in an array, and a system for marking
  contiguous regions of that pool into (adjacent, non-overlapping) pieces.
  Also handles deletions.

  To be implemented: garbage collection that compresses the data array once
  enough regions have been deleted.
-/
structure RangeArray (α : Type u) where
  /-- The pool of data. Data is added in groups, or sub-arrays, at a time.
      These sub-arrays, called "containers", are demarcated by `indexes`
      as 0-indexed Nat pointers into `data`. -/
  data : Array α

  /-- We take the convention that `indexes.size` is the number of "committed"
      elements in the data array. The sign of the Int indicates whether the
      container under that index in `data` has been deleted.

      The size of a container is the difference between the absolute values of
      the index and its next highest neighbor (or `dataSize` if at the end).
      Indexes are (not necessarily strictly) monotonically increasing.

      Deleting a container does not delete the underlying region in `data`.
      Instead, we leave that for garbage collection.

      Rather, a deleted region has its index mapped via v ↦ (-v - 1), so
      that the sizes of adjacent containers can still be computed.
      Of course, a simple negation and absolute value mapping is most desirable,
      but Lean sets -0 = 0, and so we cannot differentiate between a deleted
      0-sized starting container and a non-deleted one.  -/
  indexes : Array Int

  /-- The (logical) size of the `data` array. Uncommitted elements will increase
        `data.size`, but will leave `dataSize` unchanged. -/
  dataSize : Nat

  -- CC: An alternate formulation of `indexes`, using LeanColls
  -- size : Nat
  --indexes : ArrayN Int size     -- Using LeanColls `ArrayN`

  /-- Counts the total size of the containers that have been deleted. -/
  deletedSize : Nat

  /- Invariants -/

  h_size : dataSize ≤ data.size
  h_dataSize_empty : indexes.size = 0 → dataSize = 0

  -- No index exceeds `dataSize`
  h_indexes : ∀ {i : Nat} (hi : i < indexes.size),
    RangeArray.getIndexFromMarkedIndex (indexes[i]'hi) ≤ dataSize

  -- The indexes are monotonically increasing in (unmarked) value
  h_indexes_inc : ∀ {i j : Nat} (hij : i ≤ j) (hj : j < indexes.size),
    RangeArray.getIndexFromMarkedIndex (indexes[i]'(Nat.lt_of_le_of_lt hij hj)) ≤
    RangeArray.getIndexFromMarkedIndex (indexes[j]'hj)

namespace RangeArray

open Nat

variable {α : Type u} (A : RangeArray α) (v : α)

/-- The number of indexes, or containers, in the `data` array. -/
abbrev size : Nat := A.indexes.size

/-- The total size of the committed containers in the `data` array. -/
abbrev dsize : Nat := A.dataSize

/-- The number of elements added via `push` but not yet committed. -/
abbrev usize : Nat := A.data.size - A.dsize

-- Initialize a RangeArray with some data.
-- We don't use this operation for proof checking, so no theorems are proved about it.
/- def mkRangeArray (n : Nat) (v : α) : RangeArray α := {
  data := Array.mkArray n v
  indexes := Insert.empty
  dataSize := n
  deletedSize := 0
  h_size := by simp [Size.size]
  h_dataSize_empty := by simp [Size.size]
  h_indexes := by intro i hi; contradiction
  h_indexes_inc := by intro i j hi hj; contradiction
} -/

def empty (size : Nat := 100) : RangeArray α := {
  data := Array.mkEmpty size
  indexes := Array.mkEmpty size
  dataSize := 0
  deletedSize := 0
  h_size := by simp
  h_dataSize_empty := by simp
  h_indexes := by simp
  h_indexes_inc := by simp
}

instance instInhabited [Inhabited α] : Inhabited (RangeArray α) where
  default := empty

/-- Adds a single element to the underlying data array, without adding a new index. -/
@[specialize]
def push : RangeArray α := { A with
  data := A.data.push v
  h_size := by simp only [Array.size_push]; exact le_succ_of_le A.h_size
}

/- Clears the elements added via `push`, but maintains the rest of the containers.
    Should never actually be called, but is used for correctness. -/
/-@[inline, always_inline]
def clear : RangeArray α :=
  if A.usize = 0 then A
  else { A with
    data := { toList := A.data.data.take A.dsize }
    h_size := by simp only [dsize, Array.size_mk, List.length_take,
      Array.data_length, Nat.min_eq_left A.h_size, Nat.le_refl]
  }
-/

/-- Creates a new container that contains any elements added via `push`. -/
def commit : RangeArray α :=
  let dsize' := A.dsize
  let dataSize := A.data.size
  { A with
  indexes := A.indexes.push (dsize' : Int)
  dataSize := dataSize
  h_size := le.refl
  h_dataSize_empty := by simp only [Array.size_push, add_one_ne_zero, false_implies]
  h_indexes := by
    simp only [Array.size_push]
    intro i hi
    rcases Nat.eq_or_lt_of_le (le_of_lt_succ hi) with (rfl | hi)
    · simp only [Array.getElem_push_eq, getIndexFromMarkedIndex_coe]
      exact A.h_size
    · simp only [Array.getElem_push_lt _ _ _ hi]
      exact Nat.le_trans (A.h_indexes hi) A.h_size
  h_indexes_inc := by
    simp only [Array.size_push]
    intro i j hij hj
    rcases Nat.eq_or_lt_of_le (succ_le_of_lt hj) with (hj | hj)
    · simp only [succ_eq_add_one, Nat.add_right_cancel_iff] at hj
      subst hj
      simp only [Array.getElem_push_eq, getIndexFromMarkedIndex_coe]
      rcases Nat.eq_or_lt_of_le hij with (rfl | hi)
      · simp only [Array.getElem_push_eq, getIndexFromMarkedIndex_coe, Nat.le_refl]
      · simp only [Array.getElem_push_lt _ _ _ hi]
        exact A.h_indexes hi
    · replace hj := succ_lt_succ_iff.mp hj
      simp only [Array.getElem_push_lt _ _ _ (Nat.lt_of_le_of_lt hij hj),
        Array.getElem_push_lt _ _ _ hj,
        ge_iff_le]
      exact A.h_indexes_inc hij _
}

/-- Gets the index of the `i`th container. -/
--@[inline, always_inline]
def index (i : Nat) (hi : i < A.size) : Nat :=
  getIndexFromMarkedIndex (A.indexes[i]'hi)

/-- Indexes outside `A.size` are 0. -/
--@[inline, always_inline]
def index! (i : Nat) : Nat :=
  if hi : i < A.size then
    index A i hi
  else 0

/-- Checks whether the ith container is deleted. -/
--@[inline, always_inline]
def isDeleted (i : Nat) (hi : i < A.size) : Bool :=
  (A.indexes[i]'hi) < 0

/--
  Checks whether the ith container is deleted.
  Containers outside of `A.size` are considered deleted.
-/
--@[inline, always_inline]
def isDeleted! (i : Nat) : Bool :=
  if hi : i < A.size then isDeleted A i hi
  else true

/--
  Gets the size of the container under the provided index.
  The size of the most-recently-added container is the old `A.usize`.

  Note that the `rsize` of a deleted container can be computed, but is
  undefined, since garbage collection might discard deleted containers.

  CC: Should we say that `rsize` of a deleted container is 0?
-/
--@[inline, always_inline]
def rsize (i : Nat) (hi : i < A.size) : Nat :=
  if hi_succ : i + 1 < A.size then
    A.index (i + 1) hi_succ - A.index i hi
  else --if i + 1 = A.size then
    A.dsize - A.index i hi

/--
  Gets the size of the container under the provided index.
  Returns 0 if the index is out of bounds.
-/
--@[inline, always_inline]
def rsize! (i : Nat) : Nat :=
  if hi : i < A.size then A.rsize i hi
  else 0

--@[inline, always_inline]
def delete (i : Nat) (hi : i < A.size) : RangeArray α :=
  let dSize := A.deletedSize
  let rSize := A.rsize i hi
  let v := markIndexAsDeleted (A.indexes[i]'hi)
  { A with
  indexes := A.indexes.set i v
  deletedSize := dSize + rSize
  h_dataSize_empty := by
    simp only [Array.size_set, List.length_eq_zero_iff]
    have := A.h_dataSize_empty
    intro h
    simp only [List.length_eq_zero_iff, h, true_implies] at this
    exact this
  h_indexes := by
    simp only [Array.size_set, v]
    intro j hj
    by_cases hij : i = j
    <;> simp [hij, Array.getElem_set]
    <;> exact A.h_indexes hj
  h_indexes_inc := by
    simp only [Array.size_set]
    intro j k hjk hk
    by_cases hjk_eq : j = k
    · simp only [v, hjk_eq, Nat.le_refl]
    · by_cases hij : i = j
      · simp only [v, hij, Array.getElem_set_self,
          getIndex_markIndex, ne_eq, hjk_eq, not_false_eq_true, Array.getElem_set]
        exact A.h_indexes_inc hjk hk
      · rw [Array.getElem_set_ne A.indexes i hi _ _ hij]
        by_cases hik : i = k
        · simp only [hik, Array.getElem_set_self,
            getIndex_markIndex, v]
          exact A.h_indexes_inc hjk hk
        · rw [Array.getElem_set_ne A.indexes i hi _ _ hik]
          exact A.h_indexes_inc hjk hk
}

--@[inline, always_inline]
def delete! (i : Nat) : RangeArray α :=
  if hi : i < A.size then A.delete i hi else A

-- CC: Can be implemented as `commit`, then `delete`.
/-- Creates a new container that contains any elements added via `addElement`,
    but that container is marked as deleted. -/
def commitDeleted : RangeArray α :=
  let dataSize := A.data.size
  let dSize := A.dsize
  { A with
  indexes := A.indexes.push (markIndexAsDeleted dSize)
  dataSize := dataSize
  h_size := le.refl
  h_dataSize_empty := by simp
  h_indexes := by
    simp only [Array.size_push]
    intro i hi
    rcases Nat.eq_or_lt_of_le (le_of_lt_succ hi) with (rfl | hi)
    · simp only [Array.getElem_push_eq, getIndex_markIndex, getIndexFromMarkedIndex_coe]
      exact A.h_size
    · simp only [Array.getElem_push_lt _ _ _ hi]
      exact Nat.le_trans (A.h_indexes hi) A.h_size
  h_indexes_inc := by
    simp only [Array.size_push]
    intro i j hij hj
    rcases Nat.eq_or_lt_of_le (succ_le_of_lt hj) with (hj | hj)
    · simp only [succ_eq_add_one, Nat.add_right_cancel_iff] at hj
      subst hj
      rcases Nat.eq_or_lt_of_le hij with (rfl | hi)
      · simp only [Array.getElem_push_eq, getIndex_markIndex,
          getIndexFromMarkedIndex_coe, Nat.le_refl]
      · simp only [Array.getElem_push_lt _ _ _ hi, Array.getElem_push_eq,
          getIndex_markIndex, getIndexFromMarkedIndex_coe]
        exact A.h_indexes hi
    · replace hj := succ_lt_succ_iff.mp hj
      simp only [Array.getElem_push_lt _ _ _ (Nat.lt_of_le_of_lt hij hj),
        Array.getElem_push_lt _ _ _ hj,
        ge_iff_le]
      exact A.h_indexes_inc hij _
}

/-- Commits deleted containers until the desired size. -/
def commitUntil (desiredSize : Nat) : RangeArray α :=
  let rec loop (n : Nat) (A' : RangeArray α) : RangeArray α :=
    match n with
    | 0 => A'
    | n + 1 => loop n A'.commitDeleted
  loop (desiredSize - A.size) A


/-! # get -/

--@[inline, always_inline, specialize]
def get (i : Nat) (hi : i < A.data.size) : α :=
  A.data[i]'hi

--@[inline, always_inline, specialize]
def get! [Inhabited α] (i : Nat) : α :=
  if hi : i < A.data.size then
    A.get i hi
  else default

/-! # oget and uget -/

theorem index_add_rsize_le_size {A : RangeArray α} {i : Nat} (hi : i < A.size) :
    A.index i hi + A.rsize i hi ≤ A.data.size := by
  simp only [index, rsize]
  split <;> rename _ => hi'
  · rw [← Nat.add_sub_assoc, Nat.add_comm, Nat.add_sub_cancel]
    exact Nat.le_trans (A.h_indexes hi') A.h_size
    apply A.h_indexes_inc (by simp)
  · rw [← Nat.add_sub_assoc, Nat.add_comm, Nat.add_sub_cancel]
    exact A.h_size
    exact A.h_indexes hi

theorem index_add_offset_lt_size {A : RangeArray α}
  {i : Nat} (hi : i < A.size) {offset : Nat} (h_offset : offset < A.rsize i hi) :
    A.index i hi + offset < A.data.size := by
  have := index_add_rsize_le_size hi
  apply Nat.lt_of_lt_of_le (by omega) this

@[inline, specialize]
def oget (A : RangeArray α) (i : Nat) (hi : i < A.size) (offset : Nat) (h_offset : offset < A.rsize i hi) : α :=
  A.get (A.index i hi + offset) (index_add_offset_lt_size hi h_offset)

@[inline, specialize]
def oget! [Inhabited α] (i offset : Nat) : α :=
  if hi : i < A.size then
    if ho : offset < A.rsize i hi then
      A.oget i hi offset ho
    else default
  else default

@[inline, specialize]
def uget (A : RangeArray α) (i : Nat) (hi : i < A.usize) : α :=
  A.get (A.dsize + i) (Nat.add_lt_of_lt_sub' hi)

@[inline, specialize]
def uget! [Inhabited α] (i : Nat) : α :=
  if hi : i < A.usize then
    A.uget i hi
  else default

/-! # models -/

/--
  A `RangeArray` models a 2D array of data, and an uncommitted list of data,
  if it agrees with the data at all indexes, and if the two agree on
  deleted indexes.
-/
structure models (R : RangeArray α) (Ls : List (Option (List α))) (L : List α) : Prop where
  (h_size₁ : R.size = Ls.length)
  (h_size₂ : R.usize = L.length)
  (h_some : ∀ ⦃i : Nat⦄ (hi : i < Ls.length),
    (R.isDeleted! i = false) ↔ (∃ (C : List α), Ls.get ⟨i, hi⟩ = some C))
  (h_sizes : ∀ ⦃i : Nat⦄ (hi : i < Ls.length) {sL : List α},
    Ls.get ⟨i, hi⟩ = some sL → R.rsize i (h_size₁ ▸ hi) = sL.length)
  (h_agree : ∀ ⦃i : Nat⦄ (hi : i < Ls.length) {sL : List α} (hsL : Ls.get ⟨i, hi⟩ = some sL),
        (∀ ⦃j : Nat⦄ (hj : j < sL.length),
          R.oget i (h_size₁ ▸ hi) j ((h_sizes hi hsL) ▸ hj) = sL.get ⟨j, hj⟩))
  (h_uncommitted : ∀ ⦃i : Nat⦄ (hi : i < L.length),
      R.uget i (h_size₂ ▸ hi) = L.get ⟨i, hi⟩)

end RangeArray

end Trestle
