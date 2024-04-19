/-

Arrays that implicitly partition a pool of data into contiguous ranges.
Handles deletions.

Authors: Cayden Codel, James Gallicchio
Carnegie Mellon University

-/

import Experiments.ProofChecking.Array

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Array.Basic
import Mathlib.Tactic

import LeanSAT.Upstream.ToStd
import LeanSAT.Upstream.ToMathlib

import LeanSAT.Data.Cnf
import LeanSAT.Data.ICnf
import LeanSAT.Model.PropFun

--import LeanColls
--open LeanColls

open Array Nat Fin

theorem Int.neg_cast_le (n : Nat) : -(n : Int) ≤ 0 := by simp

universe u v w

namespace RangeArray

-- CC: TODO better names
@[inline, always_inline]
private def markIndexAsDeleted (i : Int) : Int :=
  if i ≥ 0 then -i - 1 else i

@[inline, always_inline]
private def getIndexFromMarkedIndex (i : Int) : Nat :=
  if i ≥ 0 then i.natAbs else i.natAbs - 1

@[simp]
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

end RangeArray

/-
  A structure with a single pool of data in an array, and a system for marking
  contiguous regions of that pool into (adjacent, non-overlapping) pieces.
  Also handles deletions.
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
      the index and its next highest neighbor (or `data.size` if at the end).
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
        `data.size`, but will leave size unchanged. -/
  dataSize : Nat

  -- CC: An alternate formulation of `indexes`, using LeanColls
  -- size : Nat
  --indexes : ArrayN Int size     -- Using LeanColls `ArrayN`

  /-- Counts the total size of the data array that has been deleted. -/
  deletedSize : Nat

  /-- Invariants -/

  h_size : dataSize ≤ data.size

  -- No index exceeds data.size
  h_indexes : ∀ {i : Nat} (hi : i < indexes.size),
    RangeArray.getIndexFromMarkedIndex (indexes.get ⟨i, hi⟩) ≤ dataSize

  -- The indexes are monotonically increasing in (unmarked) value
  h_indexes_inc : ∀ {i : Nat} (hi : i + 1 < indexes.size),
    RangeArray.getIndexFromMarkedIndex (indexes.get ⟨i, lt_of_succ_lt hi⟩) ≤
    RangeArray.getIndexFromMarkedIndex (indexes.get ⟨i + 1, hi⟩)

/-
CNF: <20 clauses>
LRAT:

21 1 4 -2 0 ...
25 2 -10 0 ...

data = [1, 5, 6, -2 | ]
indexes = [0, -4, -4, -4, -4, ]
indexes = [0, ]

fold at an index (run a function across a single specified clause)
folding across all indexes (hack this with Fin.foldRange [above])
add a sub-array (adding a clause)
delete (has something been deleted?)
(Garbage collect)

spec fns:
- array α @ i (where i is not deleted)
- array (array α) [all deleted clauses filtered out]

proofs:
- fold(M) at index i = fold(M) over (array @ i) or whatever
- fold(M) = fold(M) over array
- toArrays (delete RA) = RA' ↔ ∃ L M R, RA.toArrays = L ++ [M] ++ R ∧ RA'.toArrays = L ++ R
- garbageCollect RA = RA' → RA.toArrays = RA'.toArrays

-/

namespace RangeArray

variable {α : Type u} (A : RangeArray α) (v : α)

-- Initialize a RangeArray with some data.
-- We don't use this operation for proof checking, so no theorems are proved about it.
def mkRangeArray (n : Nat) (v : α) : RangeArray α := {
  data := Array.mkArray n v
  indexes := Array.empty
  dataSize := n
  deletedSize := 0
  h_size := by simp
  h_indexes := by simp; intro i hi; contradiction
  h_indexes_inc := by simp; intro i hi; contradiction
}

def empty (size : Nat := 100) : RangeArray α := {
  data := Array.mkEmpty size
  indexes := Array.mkEmpty size
  dataSize := 0
  deletedSize := 0
  h_size := by simp
  h_indexes := by simp
  h_indexes_inc := by simp
}

/-- The number of indexes, or containers in the `data` array. -/
abbrev size : Nat := A.indexes.size

/-- The size of the underlying data array. -/
abbrev dsize : Nat := A.dataSize

/-- Adds a container. Any uncommitted elements are also part of the container. -/
def add (arr : Array α) := { A with
  data := A.data ++ arr
  indexes := A.indexes.push A.dsize
  dataSize := A.data.size + arr.size
  h_size := by simp [size_append, A.h_size]
  h_indexes := by
    simp
    intro i hi
    rcases eq_or_lt_of_le (le_of_lt_succ hi) with (rfl | hi)
    · simp [le_add_right A.h_size]
    · simp [get_push, hi]
      exact le_trans (A.h_indexes hi) (le_add_right A.h_size)
  h_indexes_inc := by
    intro i hi
    simp at hi
    simp [get_push, hi]
    rcases eq_or_lt_of_le (succ_le_of_lt hi) with (hi' | hi')
    · rw [succ_eq_add_one] at hi'
      simp [hi']
      exact A.h_indexes _
    · simp [hi']
      exact A.h_indexes_inc hi'
}

/-- Adds a single element to the underlying data array, without adding a new index. -/
def addElement : RangeArray α := { A with
  data := A.data.push v
  h_size := by simp [size_push]; exact le_succ_of_le A.h_size
}

/-- Creates a new container that contains any elements added via `addElement`. -/
def commit : RangeArray α := { A with
  indexes := A.indexes.push A.dsize
  dataSize := A.data.size
  h_size := le.refl
  h_indexes := by
    simp
    intro i hi
    rcases eq_or_lt_of_le (le_of_lt_succ hi) with (rfl | hi)
    · simp [le_add_right A.h_size]
      exact A.h_size
    · simp [get_push, hi]
      exact le_trans (A.h_indexes hi) A.h_size
  h_indexes_inc := by
    intro i hi
    simp at hi
    simp [get_push, hi]
    rcases eq_or_lt_of_le (succ_le_of_lt hi) with (hi' | hi')
    · rw [succ_eq_add_one] at hi'
      simp [hi']
      exact A.h_indexes _
    · simp [hi']
      exact A.h_indexes_inc hi'
}

/-- Creates a new container that contains any elements added via `addElement`,
    but that container is marked as deleted. -/
def commitDeleted : RangeArray α := { A with
  indexes := A.indexes.push (markIndexAsDeleted A.dsize)
  dataSize := A.data.size
  h_size := le.refl
  h_indexes := by
    intro i hi
    simp at hi
    rcases eq_or_lt_of_le (le_of_lt_succ hi) with (rfl | hi)
    · simp [get_push, -markIndexAsDeleted_coe]
      exact A.h_size
    · simp [get_push, hi]
      exact le_trans (A.h_indexes hi) A.h_size
  h_indexes_inc := by
    intro i hi
    simp at hi
    simp [get_push, hi, -markIndexAsDeleted_coe]
    rcases eq_or_lt_of_le (succ_le_of_lt hi) with (hi' | hi')
    · rw [succ_eq_add_one] at hi'
      simp [hi', -markIndexAsDeleted_coe]
      exact A.h_indexes _
    · simp [hi']
      exact A.h_indexes_inc hi'
}

def commitEmptyUntil (desiredSize : Nat) : RangeArray α :=
  let rec loop (n : Nat) (A' : RangeArray α) : RangeArray α :=
    match n with
    | 0 => A'
    | n + 1 => loop n A'.commitDeleted
  loop (desiredSize - A.size) A

/-- Gets the index of the ith container. -/
def index (i : Nat) : Nat :=
  if hi : i < A.size then getIndexFromMarkedIndex (A.indexes.get ⟨i, hi⟩)
  else 0

def isDeleted (i : Nat) : Bool :=
  if hi : i < A.size then (A.indexes.get ⟨i, hi⟩) < 0
  else true

/-- Gets the size of the range under the provided index. -/
def rsize (i : Nat) : Nat :=
  if i + 1 < A.size then A.index (i + 1) - A.index i
  else if i + 1 = A.size then A.dsize - A.index i
  else 0

def uncommittedSize : Nat := A.dsize - A.dataSize

@[inline, always_inline]
def get (i : Fin A.data.size) : α :=
  A.data.get i

@[inline, always_inline]
def get? (i : Nat) : Option α :=
  A.data.get? i

@[inline, always_inline]
def getO (i : Fin A.size) (offset : Fin (A.rsize i)) : α :=
  A.data.get ⟨A.index i + offset.val, by sorry⟩

@[inline, always_inline]
def getO? (i offset : Nat) : Option α :=
  A.data.get? (A.index i + offset)

def delete (i : Nat) : RangeArray α :=
  if hi : i < A.size then { A with
    indexes := A.indexes.set ⟨i, hi⟩ (markIndexAsDeleted (A.indexes.get ⟨i, hi⟩))
    deletedSize := A.deletedSize + A.rsize i
    h_indexes := by
      simp
      intro j hj
      stop
      by_cases hij : i = j
      · subst hij
        rw [Array.get_set]
        simp [getIndexFromMarkedIndex, markIndexAsDeleted]
        split
        · rename _ => h
          simp
          have : -(A.indexes[i]) ≤ 0 := Int.neg_nonpos_of_nonneg h
          have : ¬(1 ≤ -A.indexes[i]) := Int.not_lt.mpr this
          simp [this]
          rw [← neg_add', Int.natAbs_neg]
          have : 0 ≤ A.indexes[i] + 1 := by sorry
          sorry
          done
      done
    h_indexes_inc := by
      intro j hj
      stop
      done
  }
  else A

@[simp] theorem size_empty : (empty : RangeArray α).size = 0 := rfl
@[simp] theorem dsize_empty : (empty : RangeArray α).dsize = 0 := by simp [empty, dsize]
@[simp] theorem rsize_empty : (empty : RangeArray α).rsize 0 = 0 := by simp [empty]; rfl
@[simp] theorem size_add (arr : Array α) : (A.add arr).size = A.size + 1 := by simp [add, size]


structure models (R : RangeArray α) (as : Array (Array α)) (c : Array α) : Prop where
  (h_size₁ : R.size = as.size)
  (h_size₂ : R.data.size - R.dsize = c.size)
  (h_sizes : ∀ {i : Nat} (hi : i < as.size), R.rsize i = (as.get ⟨i, hi⟩).size)
  (h_agree : ∀ {i : Nat} (hi : i < as.size), !R.isDeleted i →
      (∀ {j : Nat} (hj : j < (as.get ⟨i, hi⟩).size),
        R.getO ⟨i, h_size₁ ▸ hi⟩ ⟨j, h_sizes hi ▸ hj⟩ = (as.get ⟨i, hi⟩).get ⟨j, hj⟩))
  (h_uncommitted : ∀ {i : Nat} (hi : i < c.size),
      R.get ⟨R.dsize + i, by rw [← h_size₂] at hi; exact add_lt_of_lt_sub' hi⟩ = c.get ⟨i, hi⟩)

theorem models_empty (size : Nat) : models (empty size) (#[] : Array (Array α)) #[] := by
  constructor <;> simp [empty]

variable {R : RangeArray α} {as : Array (Array α)} {c : Array α}

theorem models_add : models R as c → ∀ (arr : Array α), models (R.add arr) (as.push (c ++ arr)) #[] := by
  rintro h_models ⟨arr⟩
  induction' arr with x xs ih generalizing c
  · stop
    constructor <;> simp [add, getOffset]
    · intro i hi h_del j hj
      stop
      done
    done
  · stop
  done

theorem models_add_of_empty : models R as #[] → ∀ (arr : Array α), models (R.add arr) (as.push arr) #[] := by
  intro h_models arr
  convert models_add h_models arr
  exact (nil_append arr).symm

theorem models_addElement : models R as c → ∀ (a : α), models (R.addElement a) as (c.push a) := by
  stop
  done

theorem models_commit : models R as c → models (R.commit) (as.push c) #[] := by
  stop
  done

theorem models_delete {i : Nat} : models R as c → models (R.delete i) as c := by
  stop
  done

--theorem fn_eq_of_models : models R as c → ∀ (f : Nat → α)

#exit

theorem index_OoB {A : RangeArray α} {i : Nat} : i ≥ A.size → A.index i = 0 := by
  simp [index]
  intro h hcon
  exact absurd hcon (not_lt_of_ge h)

theorem rsize_OoB {A : RangeArray α} {i : Nat} : i ≥ A.size → A.rsize i = 0 := by
  simp [rsize]
  intro h
  have := le_trans h (le_succ _)
  simp [index_OoB h, index_OoB this]
  rintro _ heq
  simp [← heq] at h

theorem index_add_rsize_of_lt {A : RangeArray α} {i : Nat} :
    i + 1 < A.size → A.index i + A.rsize i = A.index (i + 1) := by
  intro hi
  simp [index, rsize, hi, lt_of_succ_lt hi, -get_eq_getElem]
  rw [← Nat.add_sub_assoc, Nat.add_comm, Nat.add_sub_cancel]
  exact A.h_indexes_inc i hi

theorem index_add_rsize_of_eq {A : RangeArray α} {i : Nat} :
    i + 1 = A.size → A.index i + A.rsize i = A.dsize := by
  intro hi
  have hi' := lt_of_succ_le (le_of_eq hi)
  simp [index, rsize, hi, hi', -get_eq_getElem]
  rw [← Nat.add_sub_assoc, Nat.add_comm, Nat.add_sub_cancel]
  exact A.h_indexes ⟨i, hi'⟩

/-! # fold -/

@[inline, specialize]
def foldlM_index {β : Type v} {m : Type v → Type w} [Monad m] (f : β → α → m β)
    (init : β) (A : RangeArray α) (i : Nat) : m β :=
  A.data.foldlM f init (A.index i) (A.index i + A.rsize i)

@[inline]
def foldl_index {β : Type v} (f : β → α → β)
    (init : β) (A : RangeArray α) (i : Nat) : β :=
  A.data.foldl f init (A.index i) (A.index i + A.rsize i)

@[simp]
theorem foldlM_index_empty {β : Type v} {m : Type v → Type w} [Monad m]
    (f : β → α → m β) (init : β) (i : Nat) :
      (empty : RangeArray α).foldlM_index f init i = return init := by
  simp [foldlM_index, empty]

@[simp]
theorem foldl_index_empty {β : Type v} (f : β → α → β) (init : β) (i : Nat) :
      (empty : RangeArray α).foldl_index f init i = init := by
  simp [foldl_index, empty]

@[simp]
theorem foldlM_index_add {β : Type v} {m : Type v → Type w} [Monad m]
    (f : β → α → m β) (init : β) (arr : Array α) (i : Nat) :
      (A.add arr).foldlM_index f init i =
        if i = A.size then arr.foldlM f init
        else A.foldlM_index f init i := by
  simp [foldlM_index, add, foldlM]
  sorry

@[simp]
theorem foldl_index_add {β : Type v} (f : β → α → β) (init : β) (arr : Array α) (i : Nat) :
      (A.add arr).foldl_index f init i =
        if i = A.size then arr.foldl f init
        else A.foldl_index f init i := by
  simp [foldl_index, empty, foldlM_index_empty]
  sorry

theorem foldlM_index_trivial {β : Type v} {m : Type v → Type w} [Monad m]
    {A : RangeArray α} {i : Nat} : (A.rsize i) = 0 →
      ∀ (f : β → α → m β) init, A.foldlM_index f init i = return init := by
  sorry

theorem foldl_index_trivial {β : Type v} {A : RangeArray α} {i : Nat} :
    (A.rsize i) = 0 → ∀ (f : β → α → β) init, A.foldl_index f init i = init := by
  intro hr
  simp [foldl_index, Array.foldl]
  sorry

@[inline]
def foldlM {β : Type v} {m : Type v → Type w} [Monad m]
    (g : β → α → m β) (f : β → β → m β)
    (initg initf : β) (A : RangeArray α)
    (start : Nat := 0) (stop : Nat := A.size) : m β :=
  let minStop := min stop A.size
  let rec loop (i : Nat) (b : β) : m β := do
    if h : i < minStop then
      loop (i + 1) (
        if !A.isDeleted i then
          ← f b (← A.foldlM_index g initg i)
        else b)
    else return b
  termination_by minStop - i
  loop start initf

@[inline]
def foldlM_over_indexes {β : Type v} {m : Type v → Type w} [Monad m]
    (f : β → Nat → m β) (init : β) (A : RangeArray α)
    (start : Nat := 0) (stop : Nat := A.size) : m β :=
  let minStop := min stop A.size
  let rec loop (i : Nat) (b : β) : m β := do
    if h : i < minStop then
      loop (i + 1) (
        if !A.isDeleted i then
          ← f b i
        else b)
    else return b
  termination_by minStop - i
  loop start init

@[inline]
def foldl_over_indexes {β : Type v}
    (f : β → Nat → β) (init : β) (A : RangeArray α)
    (start : Nat := 0) (stop : Nat := A.size) : β :=
  Id.run <| A.foldlM_over_indexes f init start stop

@[inline]
def foldl {β : Type v} (g : β → α → β) (f : β → β → β)
    (initg initf : β) (A : RangeArray α) (start : Nat := 0) (stop : Nat := A.size) :=
  Id.run <| A.foldlM g f initg initf start stop
--Fin.foldRange (fun i b => f_outer b (A.foldl_index f_inner init_inner i)) init_outer start stop

@[simp]
theorem foldlM_empty {β : Type v} {m : Type v → Type w} [Monad m]
    (g : β → α → m β) (f : β → β → m β) (initg initf : β) (start stop : Nat) :
      (empty : RangeArray α).foldlM g f initg initf start stop = return initf := by
  stop
  simp [RangeArray.foldlM]
  simp [foldlM, empty]
  rintro rfl
  exact Array.foldlM_empty _ _ _ _

@[simp]
theorem foldl_empty {β : Type v} (g : β → α → β) (f : β → β → β)
    (initg initf : β) (start stop : Nat) :
      (empty : RangeArray α).foldl g f initg initf start stop = initf := by
  simp [foldl, Id.run]

theorem foldlM_add {β : Type v} {m : Type v → Type w} [Monad m]
    (g : β → α → m β) (f : β → β → m β) (initg initf : β)
    (A : RangeArray α) (arr : Array α) :
      (A.add arr).foldlM g f initg initf = do
        { f (← A.foldlM g f initg initf) (← arr.foldlM g initg) } := by
  stop
  done

theorem foldl_add {β : Type v} (g : β → α → β) (f : β → β → β)
    (initg initf : β) (A : RangeArray α) (arr : Array α) :
      (A.add arr).foldl g f initg initf = f (A.foldl g f initg initf) (arr.foldl g initg) := by
  --simp [foldl, foldlM_add]
  --intro hi f init
  simp [Array.foldl, Id.run]
  --exact foldlM_add (m := Id) g f initg initf _ _
  sorry
  done

/-! # model -/

def subArray (i : Nat) : Array α :=
  A.foldl_index Array.push #[] i

#check foldlM.loop
#check Nat.lt_trichotomy

theorem foldlM_eq_subArray_foldlM {β : Type v} {m : Type v → Type w} [Monad m]
    (f : β → α → m β) (init : β) (i : Nat) :
      A.foldlM_index f init i = (A.subArray i).foldlM f init := by
  simp [subArray, foldlM_index]
  generalize h_range : A.rsize i = range
  induction range using Nat.recAux generalizing i with
  | zero => simp [foldl_index_trivial h_range]
  | succ range ih =>
    sorry
    done

end RangeArray

----------------------------------

namespace LeanSAT

open LeanSAT LeanSAT.Model PropFun

open RangeArray

instance : ToString (RangeArray ILit) where
  toString F := F.foldl (· ++ s!" {·}") (· ++ "\n" ++ ·) "" ""

def toPropFun (F : RangeArray ILit) : PropFun IVar :=
    F.foldl (· ⊔ ·.toPropFun) (· ⊓ ·) ⊥ ⊤

@[simp]
theorem toPropFun_empty : toPropFun (RangeArray.empty : RangeArray ILit) = ⊤ := by
  simp [toPropFun]

theorem toPropFun_add (RA : RangeArray ILit) (C : IClause) :
    toPropFun (RA.add C) = (toPropFun RA) ⊓ C.toPropFun := by
  simp_rw [toPropFun]
  rw [foldl_add, Clause.foldl_bot_toPropFun_eq]

end LeanSAT

#exit

/-
/-! ### extract -/

theorem extract_loop_zero (as bs : Array α) (start : Nat) : extract.loop as 0 start bs = bs := by
  rw [extract.loop]; split <;> rfl

theorem extract_loop_succ (as bs : Array α) (size start : Nat) (h : start < as.size) :
    extract.loop as (size+1) start bs = extract.loop as size (start+1) (bs.push as[start]) := by
  rw [extract.loop, dif_pos h]; rfl

theorem extract_loop_of_ge (as bs : Array α) (size start : Nat) (h : start ≥ as.size) :
    extract.loop as size start bs = bs := by
  rw [extract.loop, dif_neg (Nat.not_lt_of_ge h)]

theorem extract_loop_eq_aux (as bs : Array α) (size start : Nat) :
    extract.loop as size start bs = bs ++ extract.loop as size start #[] := by
  induction size using Nat.recAux generalizing start bs with
  | zero => rw [extract_loop_zero, extract_loop_zero, append_nil]
  | succ size ih =>
    if h : start < as.size then
      rw [extract_loop_succ (h:=h), ih (bs.push _), push_eq_append_singleton]
      rw [extract_loop_succ (h:=h), ih (#[].push _), push_eq_append_singleton, nil_append]
      rw [append_assoc]
    else
      rw [extract_loop_of_ge (h:=Nat.le_of_not_lt h)]
      rw [extract_loop_of_ge (h:=Nat.le_of_not_lt h)]
      rw [append_nil]

theorem extract_loop_eq (as bs : Array α) (size start : Nat) (h : start + size ≤ as.size) :
  extract.loop as size start bs = bs ++ as.extract start (start + size) := by
  simp [extract]; rw [extract_loop_eq_aux, Nat.min_eq_left h, Nat.add_sub_cancel_left]
-/

theorem rsize_lt_size (i : Fin A.size) : A.rsize i ≤ A.dsize - A.index i := by
  simp [index, rsize]
  by_cases h_index : i.val + 1 < A.size <;> simp [h_index]
  rw [Nat.sub_add_cancel]
  exact A.h_indexes ⟨i.val + 1, h_index⟩
  exact A.h_indexes i

def get (i : Fin A.size) (j : Fin (A.rsize i)) : α :=
  A.data.get ⟨A.index i, by
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩
    have := A.h_indexes ⟨i, hi⟩
    rcases eq_or_lt_of_le this with (hi_eq | hi_lt)
    · have h : A.dsize - A.index ⟨i, hi⟩ = 0 := by
        exact (Nat.sub_eq_iff_eq_add' this).mpr (id hi_eq.symm)
      have := rsize_lt_size _ ⟨i, hi⟩
      rw [h, le_zero] at this
      rw [this] at hj
      contradiction
    · exact hi_lt⟩

def delete (i : Fin A.size) : RangeArray α := { A with
  deleted := A.deleted.set ⟨i, by rw [← A.h_sizes_eq]; exact i.isLt⟩ true
  deletedSize := A.deletedSize + A.rsize i
  h_sizes_eq := by simp [A.h_sizes_eq]
}

def isDeleted (i : Fin A.size) : Bool := A.deleted.get ⟨i, by rw [← A.h_sizes_eq]; exact i.isLt⟩

@[simp] theorem size_empty : (empty : RangeArray α).size = 1 := by simp [empty, size]
@[simp] theorem dsize_empty : (empty : RangeArray α).dsize = 0 := by simp [empty, dsize]; rfl
@[simp] theorem rsize_empty : (empty : RangeArray α).rsize ⟨0, by simp⟩ = 0 := by simp [empty]; rfl
@[simp] theorem size_push : (A.push v).size = A.size := by simp [push, size]
@[simp] theorem dsize_push : (A.push v).dsize = A.dsize + 1 := by simp [push, dsize]

@[simp]
theorem rsize_push (i : Fin A.size) : (A.push v).rsize i =
    if i.val + 1 = A.size then A.rsize i + 1 else A.rsize i := by
  simp [push, rsize]
  rcases i with ⟨i, hi⟩
  by_cases h_index : i + 1 < A.size
  · simp [h_index, Nat.ne_of_lt h_index]; rfl
  · simp [h_index]
    simp at h_index
    simp [le_antisymm h_index (succ_le_of_lt hi), index]
    rw [Nat.sub_add_comm]
    exact A.h_indexes _

@[simp] theorem size_cap : (A.cap).size = A.size + 1 := by simp [cap, size]
@[simp] theorem dsize_cap : (A.cap).dsize = A.dsize := by simp [cap, dsize]

@[simp]
theorem rsize_cap (i : Fin A.size) : (A.cap).rsize ⟨i.val, by rw [size_cap]; exact lt_succ_of_lt i.isLt⟩ = A.rsize i := by
  simp [cap, rsize, index]; sorry

@[simp] theorem size_delete (i : Fin A.size) : (A.delete i).size = A.size := by simp [delete, size]
@[simp] theorem dsize_delete (i : Fin A.size) : (A.delete i).dsize = A.dsize := by simp [delete, dsize]

@[simp]
theorem rsize_delete (i j : Fin A.size) : (A.delete i).rsize j =
    if i.val = j.val then 0 else A.rsize j := by
  simp [delete, rsize]; sorry

def zeroFin : Fin A.size := ⟨0, A.h_indexes_size_pos⟩
def predFin : Fin A.size := ⟨A.size - 1, by
    match hA' : A.size with
    | 0 => have hA := A.h_indexes_size_pos; simp [hA'] at hA; | n + 1 => simp⟩

@[inline, specialize]
def foldlM_index {β : Type v} {m : Type v → Type w} [Monad m] (f : β → α → m β)
    (init : β) (A : RangeArray α) (i : Fin A.size) : m β :=
  A.data.foldlM f init (A.index i) (A.index i + A.rsize i)

@[inline]
def foldl_index {β : Type v} (f : β → α → β)
    (init : β) (A : RangeArray α) (i : Fin A.size) : β :=
  Id.run <| A.foldlM_index f init i

@[simp]
theorem foldlM_index_empty {β : Type v} {m : Type v → Type w} [Monad m]
    (f : β → α → m β) (init : β) (i : Fin empty.size) :
      (empty : RangeArray α).foldlM_index f init i = return init := by
  simp [foldlM_index, empty, foldlM]
  rcases i with ⟨i, hi⟩
  simp at hi
  subst hi
  simp
  sorry

@[simp]
theorem foldl_index_empty {β : Type v} (f : β → α → β) (init : β) (i : Fin empty.size) :
      (empty : RangeArray α).foldl_index f init i = init := by
  simp [foldl_index, empty, foldlM_index_empty]
  sorry

theorem foldl_index_push_lt {β : Type v} (f : β → α → β) (init : β) (i : Fin A.size) (h : i.val + 1 < A.size) :
    (A.push v).foldl_index f init i = A.foldl_index f init i := by
  simp [foldl_index, push, foldlM_index]
  sorry

theorem foldl_index_push_eq {β : Type v} (f : β → α → β) (init : β) (i : Fin A.size) (h : i.val + 1 = A.size) :
    (A.push v).foldl_index f init i = f init v := by
  simp [foldl_index, push, foldlM_index]
  sorry

/-
@[inline, specialize]
def foldlM {α : Type u} {β : Type v} {γ : Type w} {m₁ : Type v → Type w} {m₂ : Type w → Type x}
    [Monad m₁] [Monad m₂] (f_inner : β → α → m₁ β) (f_outer : γ → β → m₂ γ)
    (init_inner : β) (init_outer : γ) (A : RangeArray α) (start stop : Fin A.size) : m₂ γ := -/

@[inline, specialize]
def foldlM {α : Type u} {β : Type v} {m : Type v → Type w}
    [Monad m] (f_inner : β → α → m β) (f_outer : β → β → m β)
    (init_inner init_outer : β) (A : RangeArray α)
    (start : Fin A.size := A.zeroFin)
    (stop : Fin A.size := A.predFin) : m β :=
  Fin.foldRangeM (fun i b => do
    if !A.isDeleted i then
      f_outer b (← A.foldlM_index f_inner init_inner i)
    else
      return b) init_outer start stop

@[inline]
def foldl {α : Type u} {β : Type v} (f_inner : β → α → β) (f_outer : β → β → β)
    (init_inner init_outer : β) (A : RangeArray α)
      (start : Fin A.size := A.zeroFin)
      (stop : Fin A.size := A.predFin) : β :=
  Fin.foldRange (fun i b => f_outer b (A.foldl_index f_inner init_inner i)) init_outer start stop

@[simp]
theorem foldl_empty {α : Type u} {β : Type v} (f_inner : β → α → β) (f_outer : β → β → β)
    (init_inner init_outer : β) (start stop : Fin empty.size) :
      (empty : RangeArray α).foldl f_inner f_outer init_inner init_outer start stop = init_outer := by
  rcases start with ⟨start, hstart⟩
  rcases stop with ⟨stop, hstop⟩
  simp at hstart hstop
  simp [foldl, hstart, hstop]

structure models (RA : RangeArray α) (A : Array (Array α)) : Prop :=
  (h_outer_size : RA.size = A.size)
  (h_inner_size : ∀ (i : Fin RA.size), RA.rsize i = Array.size (A.get ⟨i.val, by
      have := i.isLt; simp [h_outer_size] at this; exact this⟩))
  (h_data : ∀ (i : Fin RA.size) (j : Fin (RA.rsize i)), RA.get i j = (A.get ⟨i.val, by
      have := i.isLt; simp [h_outer_size] at this; exact this⟩).get ⟨j.val, by
        have := j.isLt; simp [h_inner_size] at this; exact this⟩)

instance [ToString α] : ToString (RangeArray α) where
  toString A := A.foldl (· ++ s!" {·}") (· ++ "\n" ++ ·) "" ""

end RangeArray

open LeanSAT LeanSAT.Model PropFun

abbrev FlatCnf := RangeArray ILit

namespace FlatCnf

open RangeArray

instance : ToString FlatCnf where
  toString F := F.foldl (· ++ s!" {·}") (· ++ "\n" ++ ·) "" ""

def toPropFun (F : FlatCnf) : PropFun IVar :=
    F.foldl (· ⊔ ·.toPropFun) (· ⊓ ·) ⊥ ⊤
      ⟨0, F.h_indexes_size_pos⟩ ⟨F.size - 1, by
        match hF' : F.size with
        | 0 =>
          have hF := F.h_indexes_size_pos
          simp [hF'] at hF
        | n + 1 => simp⟩

def backToPropFun (F : FlatCnf) : PropFun IVar :=
  F.foldl_index (· ⊔ ·.toPropFun) ⊥ ⟨F.size - 1, by
    match hF' : F.size with
    | 0 =>
      have hF := F.h_indexes_size_pos
      simp [hF'] at hF
    | n + 1 => simp⟩

@[simp]
theorem toPropFun_empty : toPropFun (RangeArray.empty : FlatCnf) = ⊤ := by
  simp [toPropFun]

@[simp]
theorem backToPropFun_empty : backToPropFun (RangeArray.empty : FlatCnf) = ⊥ := by
  simp [backToPropFun]

variable (F : FlatCnf) (l : ILit)

@[simp]
theorem backToPropFun_push : backToPropFun (push F l) = F.backToPropFun ⊔ l.toPropFun := by
  simp [backToPropFun, push, Id.run]
  sorry
  done

end FlatCnf


#exit
def get  (i : Fin A.data.size) : α := A.data.get i
def get? (i : Nat) : Option α := A.data.get? i
def get! [Inhabited α] (A : RangeArray α) (i : Nat) : α := A.data.get! i

def set (i : Fin A.data.size) (v : α) : RangeArray α := { A with
  data := A.data.set i v
  h_indexes := by rw [size_set]; exact A.h_indexes
}

def set! (i : Nat) (v : α) : RangeArray α := { A with
  data := A.data.set! i v
  h_indexes := by rw [size_set!]; exact A.h_indexes
}

def range (index : Fin A.indexes.size) : Nat × Nat :=
  if hi : index.val + 1 = A.indexes.size then
    ⟨A.indexes.get index, A.data.size⟩
  else
    ⟨A.indexes.get index, A.indexes.get ⟨index.val + 1, Fin.succFin_of_ne hi⟩⟩

def range! (index : Nat) : Nat × Nat :=
  if hi : index < A.indexes.size then
    A.range ⟨index, hi⟩
  else
    ⟨0, 0⟩

def backRange : Nat × Nat :=
  if A.indexes.back = A.data.size then
    if A.indexes.size < 2 then
      ⟨0, 0⟩
    else
      ⟨A.indexes.get! (A.indexes.size - 2), A.indexes.get! (A.indexes.size - 1)⟩
  else
    ⟨A.indexes.back, A.data.size⟩

def sizeAt (index : Fin A.indexes.size) : Nat :=
  let ⟨s, e⟩ := A.range index
  e - s

def sizeAt! (index : Nat) : Nat :=
  let ⟨s, e⟩ := A.range! index
  e - s

def getAt (index : Fin A.indexes.size) (i : Fin (A.sizeAt index)) : α :=
  A.get ⟨(A.indexes.get index) + i.val, by
    have ⟨i, hi⟩ := i
    simp [sizeAt, range] at hi
    by_cases h_index : index.val + 1 = A.indexes.size
    · simp [h_index] at hi
      have := Nat.add_lt_add_right hi (CArray.get A.indexes index)
      rw [Nat.sub_add_cancel (le_of_lt_succ (A.h_indexes index))] at this
      rw [add_comm]
      exact this
    · simp [h_index] at hi
      simp only [gt_iff_lt]
      have := Nat.add_lt_add_right hi (CArray.get A.indexes index)
      rw [Nat.sub_add_cancel] at this
      rw [add_comm]
      exact lt_of_lt_of_le this (le_of_lt_succ (A.h_indexes ⟨index.val + 1, _⟩))
      · apply Nat.not_lt.mp
        intro h_contra
        rw [Nat.sub_eq_zero_of_le (le_of_lt h_contra)] at hi
        contradiction⟩

def getAt! [Inhabited α] (index i : Nat) : α :=
  A.get! ((A.indexes.get! index) + i)

/-! # fold -/

@[inline]
def foldlMAtIndex {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : β → α → m β) (init : β) (A : RangeArray α) (index : Nat) : m β :=
  let ⟨s, e⟩ := A.range! index
  A.data.foldlM f init s e

@[inline]
def foldrMAtIndex {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : α → β → m β) (init : β) (A : RangeArray α) (index : Nat) : m β :=
  let ⟨s, e⟩ := A.range! index
  A.data.foldrM f init s e

@[inline]
def foldlAtIndex {α : Type u} {β : Type v} (f : β → α → β) (init : β) (A : RangeArray α) (index : Nat) : β :=
  Id.run <| A.foldlMAtIndex f init index

@[inline]
def foldrAtIndex {α : Type u} {β : Type v} (f : α → β → β) (init : β) (A : RangeArray α) (index : Nat) : β :=
  Id.run <| A.foldrMAtIndex f init index

@[inline]
def foldlMOverIndices {β : Type v} {m : Type v → Type w} [Monad m] (f : β → Nat → m β) (init : β) (A : RangeArray α) (start := 0) (stop := A.indexes.size) :=
  A.indexes.foldlM f init start stop

@[inline]
def foldrMOverIndices {β : Type v} {m : Type v → Type w} [Monad m] (f : Nat → β → m β) (init : β) (A : RangeArray α) (start := 0) (stop := A.indexes.size) :=
  A.indexes.foldrM f init start stop

@[inline]
def foldlOverIndices {β : Type v} (f : β → Nat → β) (init : β) (A : RangeArray α) (start := 0) (stop := A.indexes.size) :=
  Id.run <| A.foldlMOverIndices f init start stop

@[inline]
def foldrOverIndices {β : Type v} (f : Nat → β → β) (init : β) (A : RangeArray α) (start := 0) (stop := A.indexes.size) :=
  Id.run <| A.foldrMOverIndices f init start stop

/-! # fold behavior -/

/- The goal is to prove that the RangeArray acts like an array of arrays. -/

/-
section fromArrays

variable (as : Array (Array α)) (RA : RangeArray α)

def fromArrays : RangeArray α :=
  as.foldl (fun RA a => (a.foldl (fun RA x => RA.push x) RA).cap) (RangeArray.empty)

@[simp]
theorem fromArrays_empty : (fromArrays (#[] : Array (Array α))) = RangeArray.empty := by
  simp [fromArrays, empty, foldl]

@[simp]
theorem fromArrays_nil : (fromArrays ({ data := [] } : Array (Array α))) = RangeArray.empty := by
  simp [fromArrays, empty, foldl]

@[simp]
theorem foldlM_eq {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
    (f : β → α → m β) (init : β) (as : Array (Array α))
      (index : Nat) (h_index : index < as.size) :
    (fromArrays as).foldlMAtIndex f init index = (as.get ⟨index, h_index⟩).foldlM f init := by
  have ⟨as⟩ := as
  rw [foldlMAtIndex]
  induction' as with A AS ih generalizing index
  · simp at h_index
  · match index with
    | 0 =>
      simp [fromArrays, Array.foldl_eq_foldl_data]
      done
    done
  done
  -/



def toPropFun (A : RangeArray ILit) : PropFun IVar :=
  Fin.foldl A.numPartitions (fun F index =>
    A.foldlAtIndex)
  --sorry

#exit

@[simp] theorem size_fromArrays : (fromArrays as).size = as.size := by sorry
  /-rcases as with ⟨as⟩
  induction' as with B BS ih
  · simp [fromArrays]; rfl
  ·
    done
  simp [fromArrays]
  done -/

-- def getAt (index : Fin A.indexes.size) (i : Fin (A.sizeAt index))
theorem fromArrays_foldl {β : Type v} (as : Array (Array α)) (index : Fin as.size)
    (f : β → α → β) (init : β) :
    (as.get index).foldl f init = (fromArrays as).foldlAtIndex f init index.val := by
  sorry
  done


end fromArrays

instance [ToString α] : ToString (RangeArray α) where
  toString a := s!"({a.data}, {a.indexes})"

end RangeArray
