/-

Arrays that implicitly partition a pool of data into contiguous ranges.
Handles deletions.

Author: Cayden Codel
Carnegie Mellon University

-/

-- It appears that we don't need to use these
--import Experiments.ProofChecking.CArray
import Experiments.ProofChecking.Array

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Array.Basic
import Mathlib.Tactic

import LeanSAT.Upstream.ToStd
import LeanSAT.Upstream.ToMathlib

import LeanSAT.Data.Cnf
import LeanSAT.Data.ICnf
import LeanSAT.Model.PropFun

import LeanColls

open LeanColls

namespace Fin

def foldRangeM {β : Type v} {m : Type v → Type w} [Monad m]
    {n : Nat} (f : Fin n → β → m β) (init : β) (s e : Fin n) : m β :=
  let rec loop (i : Fin n) (b : β) : m β := do
    if h : i < e then
      loop ⟨i.val + 1, lt_of_le_of_lt (Nat.succ_le_of_lt h) e.isLt⟩ (← f ⟨i, by exact lt_trans h e.isLt⟩ b)
    else
      pure b
  termination_by e.val - i.val
  loop s init

def foldRange {β : Type v} (f : Fin n → β → β) (init : β) (s e : Fin n) : β :=
  Id.run <| foldRangeM f init s e

@[simp]
theorem foldRangeM_eq {β : Type v} {m : Type v → Type w} [Monad m]
    (f : Fin n → β → m β) (init : β) (s : Fin n) :
    foldRangeM f init s s = return init := by
  simp [foldRange, foldRangeM, foldRangeM.loop]

theorem foldRangeM_lt {β : Type v} {m : Type v → Type w} [Monad m]
    (f : Fin n → β → m β) (init : β) (s e : Fin n) (h : s < e) :
    foldRangeM f init s e = do
      { foldRangeM f (← f s init) ⟨s.val + 1, lt_of_le_of_lt (Nat.succ_le_of_lt h) e.isLt⟩ e } := by
  simp [foldRange, foldRangeM]
  rw [foldRangeM.loop]
  simp [h]

theorem foldRangeM_gt {β : Type v} {m : Type v → Type w} [Monad m]
    (f : Fin n → β → m β) (init : β) (s e : Fin n) (h : e < s) :
    foldRangeM f init s e = return init := by
  simp [foldRange, foldRangeM]
  rw [foldRangeM.loop]
  simp [h]
  exact fun hcon => absurd (le_of_lt hcon) (not_le_of_gt h)

@[simp]
theorem foldRange_eq {β : Type v} (f : Fin n → β → β) (init : β) (s : Fin n) :
    foldRange f init s s = init := by
  simp [foldRange, foldRangeM, Id.run, foldRangeM.loop]

theorem foldRange_lt {β : Type v} (f : Fin n → β → β) (init : β) (s e : Fin n) (h : s < e) :
    foldRange f init s e = foldRange f (f s init) ⟨s.val + 1, lt_of_le_of_lt (Nat.succ_le_of_lt h) e.isLt⟩ e := by
  simp [foldRange, foldRangeM]
  rw [foldRangeM.loop]
  simp [h]

theorem foldRange_gt {β : Type v} (f : Fin n → β → β) (init : β) (s e : Fin n) (h : e < s) :
    foldRange f init s e = init := by
  simp [foldRange, foldRangeM, Id.run]
  rw [foldRangeM.loop]
  simp [h]
  exact fun hcon => absurd (le_of_lt hcon) (not_le_of_gt h)

end Fin

/-
  A structure with a single pool of data in an array, and a system for marking
  contiguous regions of that pool into pieces. Also handles deletions.
-/
structure RangeArray (α : Type _) where
  data : Array α
  indexes : Array Nat
  deleted : Array Bool
  deletedSize : Nat /-- Counts the total size of the data array that has been deleted. -/

  /- We want every index in the RangeArray to point "into" data in bounds. However,
     the clearing property makes it so that the data beyond the lsize limit in
     indexes might be larger than data's logical size (lsize). So we separate out
     the hypothesis that everything in the logical data of indexes is in bounds. -/
  h_indexes_size_pos : indexes.size > 0
  h_indexes : ∀ (i : Fin indexes.size), (indexes.get i) ≤ data.size
  h_sizes_eq : indexes.size = deleted.size

namespace RangeArray

open Nat Array

variable {α : Type u} (A : RangeArray α) (v : α)

def mkRangeArray (n : Nat) (v : α) : RangeArray α := {
  data := Array.mkArray n v
  indexes := Array.singleton 0
  deleted := Array.singleton true
  deletedSize := 0
  h_indexes := by simp; intro; exact Nat.zero_le _
  h_indexes_size_pos := by simp
  h_sizes_eq := by simp
}

def empty : RangeArray α := {
  data := Array.empty
  indexes := Array.singleton 0
  deleted := Array.singleton true
  deletedSize := 0
  h_indexes := by simp; intro; exact Nat.zero_le _
  h_indexes_size_pos := by simp
  h_sizes_eq := by simp
}

/-- The (logical) size of the number of indexes (including unfinished backs). -/
abbrev size : Nat := A.indexes.size

/-- The (logical) size of the underlying data array. -/
abbrev dsize : Nat := A.data.size

/-- The (logical) number of times `cap` has been called. -/
abbrev caps : Nat := A.indexes.size - 1

/-- Pushes an element of data onto the back of the data array.
    By default, new "partitions" are considered deleted until `push` is called. -/
def push : RangeArray α := { A with
  data := A.data.push v
  deleted := A.deleted.setBack false
  h_indexes := by
    simp
    intro i
    exact le_trans (A.h_indexes i) (Nat.le_succ _)
  h_sizes_eq := by simp [A.h_sizes_eq]
}

-- Caps off the current section (by adding the start of the next section)
-- Sets the next section as deleted until an element is added via push
def cap : RangeArray α := { A with
  indexes := A.indexes.push A.data.size
  deleted := A.deleted.push true
  h_indexes := by
    rintro ⟨i, hi⟩
    simp at hi ⊢
    rcases eq_or_lt_of_le (le_of_lt_succ hi) with (rfl | hi)
    · simp
    · simp [get_push, hi]
      exact A.h_indexes ⟨i, hi⟩
  h_indexes_size_pos := by simp
  h_sizes_eq := by simp [A.h_sizes_eq]
}

-- Calls cap until the desired number of caps is reached
def capUntil (desiredCaps : Nat) : RangeArray α :=
  let rec loop (j : Nat) (A' : RangeArray α) : RangeArray α :=
    match j with
    | 0     => A'
    | j + 1 => loop j (A'.cap)
  loop (desiredCaps - A.caps) A

def index (i : Fin A.size) : Nat := A.indexes.get i

/-- Gets the size of the range under the provided index. -/
def rsize (i : Fin A.size) : Nat :=
  if hi : i.val + 1 < A.size then
    A.index ⟨i.val + 1, hi⟩ - A.index i
  else
    A.dsize - A.index i

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
