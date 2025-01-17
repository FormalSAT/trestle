/-

Arrays that implicitly partition a pool of data into contiguous ranges.
Handles deletions.

Author: Cayden Codel
Carnegie Mellon University

-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Array.Basic
import Mathlib.Tactic
import Trestle.Data.CArray
import Trestle.Upstream.ToStd
import Trestle.Upstream.ToMathlib

/-
  A structure with a single pool of data in an array, and a system for marking
  contiguous regions of that pool into pieces. Also handles deletions.
-/
structure RangeArray (α : Type _) where
  data : CArray α
  indexes : CArray Nat
  /- We want every index in the RangeArray to point "into" data in bounds. However,
     the clearing property makes it so that the data beyond the lsize limit in
     indexes might be larger than data's logical size (lsize). So we separate out
     the hypothesis that everything in the logical data of indexes is in bounds. -/
  h_indexes : ∀ (i : Fin indexes.size), (indexes.get i) < data.size + 1

namespace RangeArray

open Nat CArray

variable {α : Type u} (A : RangeArray α) (v : α)

def mkRangeArray (n : Nat) (v : α) : RangeArray α := {
  data := CArray.mkCArray n v
  indexes := CArray.singleton 0
  h_indexes := by
    intro i
    simp [size_mkCArray, CArray.singleton, CArray.get]
    exact succ_pos _
}

def empty : RangeArray α := {
  data := CArray.empty
  indexes := CArray.singleton 0
  h_indexes := by
    intro i
    simp [size_mkCArray, CArray.singleton, CArray.get]
    exact succ_pos _
}

def size : Nat := A.data.size
def numPartitions : Nat := A.indexes.size - 1

-- Pushes an element of data onto the back
def push : RangeArray α := { A with
  data := A.data.push v
  h_indexes := by
    intro i
    rw [size_push]
    exact lt_succ_of_lt (A.h_indexes i)
}

-- Caps off the current section (by adding the start of the next section)
-- Sets the next section as deleted until an element is added via push
def cap : RangeArray α := { A with
  indexes := A.indexes.push A.data.size
  h_indexes := by
    intro i
    rcases i with ⟨i, hi⟩
    rw [size_push] at hi
    rcases Order.lt_succ_iff_eq_or_lt.mp hi with (rfl | hi)
    · simp
    · rw [get_push_lt A.indexes (A.data.size) ⟨i, hi⟩]
      exact A.h_indexes _
}

-- Calls cap until the desired number of caps is reached
-- More efficient as a fold, or an append?
-- def forIn {β : Type u} {m : Type u → Type v} [Monad m] (range : Range) (init : β) (f : Nat → β → m (ForInStep β)) : m β
def capUntil (desiredNumCaps : Nat) : RangeArray α :=
  let rec loop (j : Nat) (A' : RangeArray α) : RangeArray α :=
    match j with
    | 0     => A'
    | j + 1 => loop j (A'.cap)
  loop (desiredNumCaps - A.numPartitions) A

def clear : RangeArray α := { A with
  data := A.data.clear
  indexes := (A.indexes.clear).push 0
  h_indexes := by
    intro i
    rcases i with ⟨i, hi⟩
    simp at hi
    have := get_push_eq (A.indexes.clear) 0
    rw [size_clear] at this
    aesop
}

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

section fromArrays

variable (as : Array (Array α))

def fromArrays : RangeArray α :=
  as.foldl (fun A a => (a.foldl (fun A x => A.push x) A).cap) (RangeArray.empty)

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
