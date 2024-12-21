/-

Arrays that implicitly partition a pool of data into contiguous ranges.
Handles deletions.

Authors: Cayden Codel, James Gallicchio
Carnegie Mellon University

-/

import Experiments.ProofChecking.Array
import Experiments.ProofChecking.ToLeanColls

import Mathlib.Data.Array.Lemmas
import Mathlib.Data.List.Basic
import Mathlib.Tactic

import LeanSAT.Upstream.ToStd
import LeanSAT.Upstream.ToMathlib

import LeanSAT.Data.Cnf
import LeanSAT.Data.ICnf
import LeanSAT.Model.PropFun

import LeanColls
open LeanColls

open Array Nat Fin

theorem Int.neg_cast_le (n : Nat) : -(n : Int) ≤ 0 := by simp
theorem Int.exists_nat_of_ge_zero {i : Int} : 0 ≤ i → ∃ (n : Nat), (n : Int) = i := by
  intro h
  exact CanLift.prf i h

universe u v w

namespace RangeArray

-- CC: TODO better names
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
  · rcases Int.exists_nat_of_ge_zero hi with ⟨n, rfl⟩
    simp [hi]
    split
    · linarith
    · rw [← neg_add', Int.natAbs_neg, ← Nat.cast_one, ← Nat.cast_add,
        Int.natAbs_cast, Nat.add_sub_cancel]
  · simp [hi]

theorem markIndexAsDeleted_coe (n : Nat) : markIndexAsDeleted n = -n - 1 := by
  simp [markIndexAsDeleted]

@[simp]
theorem getIndexFromMarkedIndex_coe (n : Nat) : getIndexFromMarkedIndex n = n := by
  simp [getIndexFromMarkedIndex]

@[simp]
theorem markIndex_getIndex_coe (n : Nat) : getIndexFromMarkedIndex (markIndexAsDeleted n) = n := by
  simp [markIndexAsDeleted, getIndexFromMarkedIndex]
  split
  · rename _ => h
    -- CC: Potentially make this a lemma?
    exact absurd h (Int.not_lt.mpr (Int.neg_cast_le n))
  · rw [← neg_add', Int.natAbs_neg, ← Nat.cast_one, ← Nat.cast_add, Int.natAbs_cast]
    exact add_tsub_cancel_right _ _

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

  /-- Invariants -/

  h_size : dataSize ≤ Size.size data
  h_dataSize_empty : Size.size indexes = 0 → dataSize = 0

  -- No index exceeds `dataSize`
  h_indexes : ∀ {i : Nat} (hi : i < Size.size indexes),
    RangeArray.getIndexFromMarkedIndex (Seq.get indexes ⟨i, hi⟩) ≤ dataSize

  -- The indexes are monotonically increasing in (unmarked) value
  h_indexes_inc : ∀ {i j : Nat} (hij : i ≤ j) (hj : j < Size.size indexes),
    RangeArray.getIndexFromMarkedIndex (Seq.get indexes ⟨i, lt_of_le_of_lt hij hj⟩) ≤
    RangeArray.getIndexFromMarkedIndex (Seq.get indexes ⟨j, hj⟩)

namespace RangeArray

variable {α : Type u} (A : RangeArray α) (v : α)

/-- The number of indexes, or containers, in the `data` array. -/
abbrev size : Nat := Size.size A.indexes

/-- The total size of the committed containers in the `data` array. -/
abbrev dsize : Nat := A.dataSize

/-- The number of elements added via `push` but not yet committed. -/
abbrev usize : Nat := (Size.size A.data) - A.dsize

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
  h_indexes := by simp [LeanColls.size]
  h_indexes_inc := by simp [LeanColls.size]
}

instance instInhabited [Inhabited α] : Inhabited (RangeArray α) where
  default := empty

/-- Adds a single element to the underlying data array, without adding a new index. -/
--@[inline, always_inline, specialize]
def push : RangeArray α := { A with
  data := Seq.snoc A.data v
  h_size := by simp [Seq.size_snoc]; exact le_succ_of_le A.h_size
}

/-- Clears the elements added via `push`, but maintains the rest of the containers.
    Should never actually be called, but is used for correctness. -/
def clear : RangeArray α :=
  if A.usize = 0 then A
  else { A with
    data := { data := A.data.data.take A.dsize }
    h_size := by simp [LeanColls.size]; exact A.h_size
  }

/-- Creates a new container that contains any elements added via `push`. -/
def commit : RangeArray α := { A with
  indexes := Seq.snoc A.indexes (A.dsize : Int)
  dataSize := Size.size A.data
  h_size := le.refl
  h_dataSize_empty := by simp
  h_indexes := by
    simp
    intro i hi
    rcases eq_or_lt_of_le (le_of_lt_succ hi) with (rfl | hi)
    · simp [le_add_right A.h_size]
      exact A.h_size
    · simp [Seq.get_snoc, hi]
      exact le_trans (A.h_indexes hi) A.h_size
  h_indexes_inc := by
    simp [Seq.size_snoc, Seq.get_snoc]
    intro i j hij hj
    rcases eq_or_lt_of_le (succ_le_of_lt hj) with (hj | hj)
    · simp at hj
      simp [hj]
      split <;> simp [A.h_indexes]
    · replace hj := succ_lt_succ_iff.mp hj
      simp [hj, lt_of_le_of_lt hij hj]
      exact A.h_indexes_inc hij _
}

/-- Gets the index of the ith container. -/
@[inline, always_inline]
def indexFin (i : Fin A.size) : Nat :=
  getIndexFromMarkedIndex (Seq.get A.indexes i)

/- Indexes outside `A.size` are 0. -/
@[inline, always_inline]
def index (i : Nat) : Nat :=
  if hi : i < A.size then
    indexFin A ⟨i, hi⟩
  else 0

/-- Checks whether the ith container is deleted. -/
@[inline, always_inline]
def isDeletedFin (i : Fin A.size) : Bool :=
  (Seq.get A.indexes i) < 0

/- Checks whether the ith container is deleted.
    Containers outside of `A.size` are considered deleted. -/
def isDeleted (i : Nat) : Bool :=
  if hi : i < A.size then isDeletedFin A ⟨i, hi⟩
  else true

/-- Gets the size of the container under the provided index.
    The size of the most-recently-added container is the old `A.usize`.

    Note that the `rsize` of a deleted container can be computed, but is
    undefined, since garbage collection might discard deleted containers.

    CC: Should we say that `rsize` of a deleted container is 0? -/
@[inline, always_inline]
def rsizeFin (i : Fin A.size) : Nat :=
  if hi : i.val + 1 < A.size then
    A.indexFin ⟨i.val + 1, hi⟩ - A.indexFin i
  else --if i + 1 = A.size then
    A.dsize - A.indexFin i

def rsize (i : Nat) : Nat :=
  if hi : i < A.size then A.rsizeFin ⟨i, hi⟩
  else 0

def deleteFin (i : Fin A.size) : RangeArray α :=
  let dSize := A.deletedSize
  let rSize := A.rsize i
  let v := markIndexAsDeleted (Seq.get A.indexes i)
  { A with
  indexes := Seq.set A.indexes i v
  deletedSize := dSize + rSize
  h_dataSize_empty := by simp; exact A.h_dataSize_empty
  h_indexes := by
    simp [Seq.get_set, dSize, rSize, v]
    rcases i with ⟨i, hi⟩
    intro j hj
    by_cases hij : i = j
    <;> simp [hij, A.h_indexes]
  h_indexes_inc := by
    simp [Seq.get_set, dSize, rSize, v]
    rcases i with ⟨i, hi⟩
    intro j k hjk hk
    by_cases hjk_eq : j = k
    <;> simp [hjk_eq]
    by_cases hij : i = j
    · simp [hij, hjk_eq, A.h_indexes_inc hjk]
    · simp [hij]
      by_cases hik : i = k
      <;> simp [hik, A.h_indexes_inc hjk]
}

def delete (i : Nat) : RangeArray α :=
  if hi : i < A.size then A.deleteFin ⟨i, hi⟩ else A

-- CC: Can be implemented as `commit`, then `delete`.
/-- Creates a new container that contains any elements added via `addElement`,
    but that container is marked as deleted. -/
def commitDeleted : RangeArray α := { A with
  indexes := Seq.snoc A.indexes (markIndexAsDeleted A.dsize)
  dataSize := A.data.size
  h_size := le.refl
  h_dataSize_empty := by simp
  h_indexes := by
    simp
    intro i hi
    rcases eq_or_lt_of_le (le_of_lt_succ hi) with (rfl | hi)
    · simp; exact A.h_size
    · simp [Seq.get_snoc, hi]
      exact le_trans (A.h_indexes hi) A.h_size
  h_indexes_inc := by
    simp [Seq.size_snoc, Seq.get_snoc]
    intro i j hij hj
    rcases eq_or_lt_of_le (succ_le_of_lt hj) with (hj | hj)
    · simp at hj
      simp [hj]
      split <;> simp [A.h_indexes]
    · replace hj := succ_lt_succ_iff.mp hj
      simp [hj, lt_of_le_of_lt hij hj]
      exact A.h_indexes_inc hij _
}

/-- Commits deleted containers until the desired size. -/
def commitUntil (desiredSize : Nat) : RangeArray α :=
  let rec loop (n : Nat) (A' : RangeArray α) : RangeArray α :=
    match n with
    | 0 => A'
    | n + 1 => loop n A'.commitDeleted
  loop (desiredSize - A.size) A

/-- Adds a container. Any uncommitted elements are also part of the container. -/
@[inline, always_inline]
def append (arr : Array α) :=
  (arr.foldl (init := A.clear) (fun A' v => A'.push v)) |>.commit

-- An alternate version that directly implements it.
-- CC: Actually slightly different, since this will include any uncomitted elements, while the above does not.
def append' (arr : Array α) := { A with
  data := A.data ++ arr
  indexes := Seq.snoc A.indexes (A.dsize : Int)
  dataSize := (Size.size A.data) + (Size.size arr)
  h_size := by simp [size_append, A.h_size]
  h_dataSize_empty := by simp [size_append, A.h_dataSize_empty]
  h_indexes := by
    simp
    intro i hi
    rcases eq_or_lt_of_le (le_of_lt_succ hi) with (rfl | hi)
    · simp
      exact le_add_right A.h_size
    · simp [Seq.get_snoc, hi]
      exact le_trans (A.h_indexes hi) (le_add_right A.h_size)
  h_indexes_inc := by
    intro i j hij hj
    simp at hj
    simp [Seq.get_snoc, hj]
    rcases eq_or_lt_of_le (succ_le_of_lt hj) with (hj | hj)
    · simp at hj
      simp [hj]
      split <;> simp [A.h_indexes]
    · replace hj := succ_lt_succ_iff.mp hj
      simp [hj, lt_of_le_of_lt hij hj]
      exact A.h_indexes_inc hij _
}

/-! # get -/

@[inline, always_inline]
def getFin (i : Fin (Size.size A.data)) : α :=
  Seq.get A.data i

@[inline, always_inline]
def get [Inhabited α] (i : Nat) : α :=
  if hi : i < Size.size A.data then
    A.getFin ⟨i, hi⟩
  else default

/-! # oget and uget -/

theorem indexFin_add_rsizeFin_le_size {A : RangeArray α}
      (i : Fin A.size) :
    A.indexFin i + A.rsizeFin i ≤ Size.size A.data := by
  rcases i with ⟨i, hi⟩
  simp [indexFin, rsizeFin]
  split <;> rename _ => hi'
  · rw [← Nat.add_sub_assoc, Nat.add_comm, Nat.add_sub_cancel]
    exact le_trans (A.h_indexes hi') A.h_size
    apply A.h_indexes_inc (by simp)
  · rw [← Nat.add_sub_assoc, Nat.add_comm, Nat.add_sub_cancel]
    exact A.h_size
    exact A.h_indexes hi

theorem indexFin_add_offset_lt_size {A : RangeArray α}
      (i : Fin A.size) (offset : Fin (A.rsizeFin i)) :
    A.indexFin i + offset.val < Size.size A.data := by
  have := indexFin_add_rsizeFin_le_size i
  apply lt_of_lt_of_le (by omega) this

@[inline, always_inline]
def ogetFin {A : RangeArray α} (i : Fin A.size) (offset : Fin (A.rsizeFin i)) : α :=
  A.getFin ⟨A.indexFin i + offset.val, indexFin_add_offset_lt_size i offset⟩

@[inline, always_inline]
def oget [Inhabited α] (i offset : Nat) : α :=
  if hi : i < A.size then
    if ho : offset < A.rsizeFin ⟨i, hi⟩ then
      A.ogetFin ⟨i, hi⟩ ⟨offset, ho⟩
    else default
  else default

@[inline, always_inline]
def ugetFin {A : RangeArray α} (i : Fin A.usize) : α :=
  A.getFin ⟨A.dsize + i.val, Nat.add_lt_of_lt_sub' i.isLt⟩

@[inline, always_inline]
def uget [Inhabited α] (i : Nat) : α :=
  if hi : i < A.usize then
    A.ugetFin ⟨i, hi⟩
  else default

/-! # models -/

/--
  A `RangeArray` models a 2D array of data, and an uncommitted list of data,
  if it agrees with the data at all indexes, and if the two agree on
  deleted indexes.

  Note that for `h_agree` and `h_uncommitted`, we use `.oget` and `.uget`
  rather than `.ogetFin` and `.ugetFin` because Lean struggles to close
  proof goals with slightly "wrong" dependent inequality proofs.
-/
structure models (R : RangeArray α) (Ls : List (Option (List α))) (L : List α) : Prop where
  (h_size₁ : R.size = Size.size Ls)
  (h_size₂ : R.usize = Size.size L)
  (h_some : ∀ {i : Nat} (hi : i < Size.size Ls),
    (R.isDeleted i = false) ↔ (∃ (C : List α), Seq.get Ls ⟨i, hi⟩ = some C))
  (h_sizes : ∀ {i : Nat} (hi : i < Size.size Ls) {sL : List α},
    Seq.get Ls ⟨i, hi⟩ = some sL → R.rsizeFin ⟨i, h_size₁ ▸ hi⟩ = Size.size sL)
  (h_agree : ∀ {i : Nat} (hi : i < Size.size Ls) {sL : List α} (hsL : Seq.get Ls ⟨i, hi⟩ = some sL),
        (∀ {j : Nat} (hj : j < (Size.size sL)),
          R.ogetFin ⟨i, h_size₁ ▸ hi⟩ ⟨j, (h_sizes hi hsL) ▸ hj⟩ = Seq.get sL ⟨j, hj⟩))
  (h_uncommitted : ∀ {i : Nat} (hi : i < Size.size L),
      R.ugetFin ⟨i, h_size₂ ▸ hi⟩ = Seq.get L ⟨i, hi⟩)

end RangeArray
