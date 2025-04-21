/-

Theorems about the `RangeArray` operations.
The separation of definitions and theorems allows Lean to compile
executables, even if there are broken proofs.

Author: Cayden Codel
Carnegie Mellon University

-/

import Experiments.SR.Data.RangeArray.Defs

namespace Trestle

namespace RangeArray

open Nat

variable {α : Type u} (A : RangeArray α) (v : α) (i : Nat)

/-! # Fin versions equal their un-Fin versions -/

theorem index_eq_index! {A : RangeArray α} {i : Nat} (hi : i < A.size)
    : A.index i hi = A.index! i := by
  simp only [index!, hi, reduceDIte]

@[simp]
theorem index!_le_dataSize (i : Nat) : A.index! i ≤ A.dsize := by
  by_cases hi : i < A.size
  <;> simp only [index!, hi, reduceDIte, zero_le]
  exact A.h_indexes hi

theorem index_le_index_of_le {A : RangeArray α} {i j : Nat} (hij : i ≤ j) (hj : j < A.size)
    : A.index! i ≤ A.index! j := by
  simp only [index!, Nat.lt_of_le_of_lt hij hj, reduceDIte, hj]
  exact A.h_indexes_inc hij hj

theorem isDeleted_eq_isDeleted! {A : RangeArray α} {i : Nat} (hi : i < A.size)
    : A.isDeleted i hi = A.isDeleted! i := by
  simp only [isDeleted!, Array.length_toList, hi, ↓reduceDIte]

theorem rsize_eq_rsize! {A : RangeArray α} {i : Nat} (hi : i < A.size)
    : A.rsize i hi = A.rsize! i := by
  simp only [rsize!, hi, reduceDIte]

theorem delete_eq_delete! {i : Nat} (hi : i < A.size)
    : A.delete i hi = A.delete! i := by
  simp only [delete!, hi, reduceDIte]

/-! # empty -/

@[simp]
theorem size_empty (n : Nat) : (empty n : RangeArray α).size = 0 := by
  simp only [size, empty, Array.mkEmpty_eq, List.size_toArray, List.length_nil]

@[simp]
theorem dsize_empty (n : Nat) : (empty n : RangeArray α).dsize = 0 := by
  simp only [dsize, empty, Array.mkEmpty_eq]

@[simp]
theorem usize_empty (n : Nat) : (empty n : RangeArray α).usize = 0 := by
  simp only [usize, empty, Array.mkEmpty_eq, List.size_toArray,
    List.length_nil, Nat.sub_self]

/-! # push -/

@[simp] theorem size_push : (A.push v).size = A.size := by simp only [size, push]
@[simp] theorem dsize_push : (A.push v).dsize = A.dsize := by simp only [push, dsize]

@[simp]
theorem data_size_push : (A.push v).data.size = A.data.size + 1 := by
  simp only [push, Array.size_push]

@[simp]
theorem usize_push : (A.push v).usize = A.usize + 1 := by
  simp only [usize, push, Array.size_push, dsize, Nat.sub_add_comm A.h_size]

@[simp]
theorem index!_push : (A.push v).index! i = A.index! i := by
  simp only [index!, push, Array.length_toList, index]

@[simp]
theorem rsize_push {A : RangeArray α} {i : Nat} (hi : i < A.size) (v : α) :
    (A.push v).rsize i hi = A.rsize i hi := by
  simp only [rsize, Array.length_toList, size_push, dsize_push]; rfl

@[simp]
theorem rsize!_push : (A.push v).rsize! i = A.rsize! i := by
  simp only [rsize!, Array.length_toList, size_push, rsize_push]

@[simp]
theorem isDeleted!_push : (A.push v).isDeleted! i = A.isDeleted! i := by
  simp only [isDeleted!, size, push, isDeleted]

@[simp]
theorem delete!_push_comm : (A.push v).delete! i = (A.delete! i).push v := by
  simp only [delete!, size_push, delete, dsize_push, rsize_push]
  split
  · congr 1
  · rfl

/-! # delete! -/

@[simp]
theorem size_delete! : (A.delete! i).size = A.size := by
  simp only [size, delete!, delete]
  split <;> rename _ => hi
  · simp only [Array.size_set]
  · rfl

@[simp]
theorem size_delete {A : RangeArray α} {i : Nat} (hi : i < A.size)
    : (A.delete i hi).size = A.size :=
  delete_eq_delete! .. ▸ size_delete! ..

@[simp]
theorem dsize_delete! : (A.delete! i).dsize = A.dsize := by
  rw [delete!]; split <;> rfl

@[simp]
theorem dsize_delete {A : RangeArray α} {i : Nat} (hi : i < A.size)
    : (A.delete i hi).dsize = A.dsize :=
  delete_eq_delete! .. ▸ dsize_delete! ..

@[simp]
theorem usize_delete! : (A.delete! i).usize = A.usize := by
  rw [delete!]; split <;> rfl

@[simp]
theorem usize_delete {A : RangeArray α} {i : Nat} (hi : i < A.size)
    : (A.delete i hi).usize = A.usize :=
  delete_eq_delete! .. ▸ usize_delete! ..

-- This theorem won't be true when we implement garbage collection
-- theorem index_delete_ne {i j : Nat} (hij : i ≠ j) :
--    (A.delete! i).index! j = A.index! j := by

-- This theorem will hold, regardless of garbage collection
theorem rsize!_delete!_ne {i j : Nat} (hij : i ≠ j) (A : RangeArray α)
    : (A.delete! i).rsize! j = A.rsize! j := by
  simp only [delete!, Array.length_toList]
  split <;> rename _ => hi <;> try rfl
  simp only [rsize!, rsize, size, delete, Array.size_set]
  split <;> rename _ => hj <;> try rfl
  simp only [index, Array.getElem_set, hij, ↓reduceIte]
  split <;> rename _ => hj' <;> try rfl
  split <;> rename _ => hij' <;> simp [hij']

@[simp]
theorem isDeleted!_delete!_eq : (A.delete! i).isDeleted! i = true := by
  simp only [isDeleted!, Array.length_toList, size_delete!, dite_eq_right_iff]
  by_cases hi : i < A.indexes.size
  · simp only [hi, isDeleted, delete!, Array.length_toList, ↓reduceDIte,
      delete, markIndexAsDeleted, ge_iff_le, Array.getElem_set_self,
      decide_eq_true_eq, forall_const]
    split <;> omega
  · simp only [hi, forall_false]

theorem isDeleted!_delete!_ne {i j : Nat} (hij : i ≠ j)
    : (A.delete! i).isDeleted! j = A.isDeleted! j := by
  simp only [delete!, Array.length_toList]
  split <;> rename _ => hi <;> try rfl
  simp only [isDeleted!, delete, Array.length_toList, Array.size_set]
  split <;> try rfl
  simp only [isDeleted, Array.getElem_set, hij, ↓reduceIte]

-- Not marked `@[simp]` due to similar reasons as `Array.getElem_set`
theorem isDeleted!_delete! (i j : Nat)
    : (A.delete! i).isDeleted! j
        = if i = j then true else A.isDeleted! j := by
  split <;> rename _ => hij
  · subst hij; exact isDeleted!_delete!_eq A i
  · exact isDeleted!_delete!_ne A hij

theorem isDeleted!_true_of_ge {A : RangeArray α} {i : Nat} (hi : i ≥ A.size)
    : A.isDeleted! i = true := by
  simp only [isDeleted!, Array.length_toList, Nat.not_lt_of_ge hi, ↓reduceDIte]

theorem lt_of_isDeleted!_false {A : RangeArray α} {i : Nat}
    : A.isDeleted! i = false → i < A.size := by
  intro hi
  rw [isDeleted!] at hi
  split at hi
  · assumption
  · contradiction

/-! # commit -/

@[simp]
theorem size_commit : A.commit.size = A.size + 1 := by
  simp only [size, commit, Array.size_push]

@[simp]
theorem dsize_commit : A.commit.dsize = A.data.size :=
  rfl

@[simp]
theorem usize_commit : A.commit.usize = 0 := by
  simp only [usize, commit, dsize, Nat.sub_self]

theorem index!_commit_lt {A : RangeArray α} {i : Nat} (hi : i < A.size)
    : (A.commit).index! i = A.index! i := by
  rw [size] at hi
  simp only [index!, size, commit, Array.size_push, lt_succ_of_lt hi,
    ↓reduceDIte, index, Array.getElem_push, hi]

@[simp]
theorem index_commit_lt {A : RangeArray α} {i : Nat} (hi : i < A.size)
    : (A.commit).index i (by simp [Nat.lt_succ_of_lt hi]) = A.index i hi := by
  simp only [index_eq_index!]
  exact index!_commit_lt hi

@[simp]
theorem index!_commit_eq : (A.commit).index! A.size = A.dsize := by
  simp only [index!, size, commit, Array.size_push, Nat.lt_add_one,
    ↓reduceDIte, index, Array.getElem_push_eq, getIndexFromMarkedIndex_coe]

@[simp]
theorem index_commit_eq : (A.commit).index A.size (by simp) = A.dsize :=
  index_eq_index! .. ▸ index!_commit_eq ..

theorem index!_commit_gt {A : RangeArray α} {i : Nat} (hi : i > A.size)
    : (A.commit).index! i = 0 := by
  rw [size] at hi
  simp only [index!, size, commit, Array.size_push, dite_eq_right_iff]
  intro
  omega

theorem rsize!_commit_lt {A : RangeArray α} {i : Nat} (hi : i < A.size)
    : (A.commit).rsize! i = A.rsize! i := by
  rw [size] at hi
  simp only [rsize!, size, commit, Array.size_push, hi, Nat.lt_succ_of_lt hi,
    ↓reduceDIte, rsize, Nat.add_lt_add_iff_right, index, Array.getElem_push]
  split <;> rfl

@[simp]
theorem rsize_commit_lt {A : RangeArray α} {i : Nat} (hi : i < A.size)
    : (A.commit).rsize i (by simp [Nat.lt_succ_of_lt hi]) = A.rsize i hi := by
  simp only [rsize_eq_rsize!]
  exact rsize!_commit_lt hi

@[simp]
theorem rsize!_commit_eq : (A.commit).rsize! A.size = A.usize := by
  simp only [rsize!, size, commit, dsize, Array.size_push, Nat.lt_add_one,
    ↓reduceDIte, rsize, Nat.lt_irrefl, index, Array.getElem_push_eq,
    getIndexFromMarkedIndex_coe, usize]

@[simp]
theorem rsize_commit_eq : (A.commit).rsize A.size (by simp) = A.usize :=
  rsize_eq_rsize! .. ▸ rsize!_commit_eq ..

@[simp]
theorem rsize!_commit_gt {A : RangeArray α} {i : Nat} (hi : i > A.size)
    : (A.commit).rsize! i = 0 := by
  rw [size] at hi
  simp only [rsize!, size, commit, Array.size_push, dite_eq_right_iff]
  intro
  omega

theorem isDeleted!_commit_lt {A : RangeArray α} {i : Nat} (hi : i < A.size)
    : (A.commit).isDeleted! i = A.isDeleted! i := by
  rw [size] at hi
  simp only [isDeleted!, size, commit, Array.size_push, Nat.lt_succ_of_lt hi,
    ↓reduceDIte, isDeleted, Array.getElem_push, hi]

theorem isDeleted_commit_lt {A : RangeArray α} {i : Nat} (hi : i < A.size)
    : (A.commit).isDeleted i (by simp [Nat.lt_succ_of_lt hi]) = A.isDeleted i hi := by
  simp only [isDeleted_eq_isDeleted!]
  exact isDeleted!_commit_lt hi

@[simp]
theorem isDeleted!_commit_eq : (A.commit).isDeleted! A.size = false := by
  simp only [isDeleted!, size, commit, Array.size_push, Nat.lt_add_one,
    ↓reduceDIte, isDeleted, Array.getElem_push_eq, decide_eq_false_iff_not,
    Int.not_lt, Int.ofNat_zero_le]

@[simp]
theorem isDeleted_commit_eq : (A.commit).isDeleted A.size (by simp) = false :=
  isDeleted_eq_isDeleted! .. ▸ isDeleted!_commit_eq ..

theorem isDeleted!_commit_gt {A : RangeArray α} {i : Nat} (hi : i > A.size) :
    (A.commit).isDeleted! i = true := by
  rw [size] at hi
  simp only [isDeleted!, size, commit, Array.size_push, dite_eq_right_iff]
  intro
  omega

section get

variable [Inhabited α]

theorem get_eq_get! {A : RangeArray α} {i : Nat} (hi : i < A.data.size)
    : A.get i hi = A.get! i := by
  simp only [get!, hi, ↓reduceDIte]

theorem get!_push_lt {A : RangeArray α} {i : Nat} (hi : i < A.data.size) (v : α)
    : (A.push v).get! i = A.get! i := by
  simp only [get!, get, push, Array.size_push, hi, lt_succ_of_lt hi,
    ↓reduceDIte, Array.getElem_push]

theorem get_push_lt {A : RangeArray α} {i : Nat} (hi : i < A.data.size) (v : α)
    : (A.push v).get i (by simp [Nat.lt_succ_of_lt hi]) = A.get i hi := by
  simp only [get_eq_get!]
  exact get!_push_lt hi v

@[simp]
theorem get!_push_eq : (A.push v).get! A.data.size = v := by
  simp only [get!, get, push, Array.size_push, Nat.lt_add_one,
    ↓reduceDIte, Array.getElem_push_eq]

@[simp]
theorem get_push_eq : (A.push v).get A.data.size (by simp) = v := by
  simp only [get_eq_get!]
  exact get!_push_eq ..

theorem get!_push_gt {A : RangeArray α} {i : Nat} (hi : i > A.data.size) (v : α)
    : (A.push v).get! i = default := by
  simp only [get!, push, Array.size_push, dite_eq_right_iff]
  intro
  omega

@[simp]
theorem get!_commit : (A.commit).get! i = A.get! i := by
  simp only [get!, commit, get]

@[simp]
theorem get_commit {A : RangeArray α} {i} (hi : i < A.data.size)
    : (A.commit).get i hi = A.get i (by simp [hi]) := by
  simp only [get_eq_get!]
  exact get!_commit ..

theorem oget_eq_oget! {A : RangeArray α} {i offset : Nat} {hi : i < A.size} (ho : offset < A.rsize i hi)
    : A.oget i hi offset ho = A.oget! i offset := by
  simp only [oget!, Array.length_toList, hi, ↓reduceDIte, ho]

omit [Inhabited α] in
theorem oget_eq_get {A : RangeArray α} {i offset : Nat} {hi : i < A.size} (ho : offset < A.rsize i hi)
    : A.oget i hi offset ho
        = A.get (A.index i hi + offset) (index_add_offset_lt_size hi ho) := by
  rfl

theorem uget_eq_uget! {A : RangeArray α} {i} (hi : i < A.usize)
    : A.uget i hi = A.uget! i := by
  simp only [uget!, hi, ↓reduceDIte]

@[simp]
theorem oget!_push (A : RangeArray α) (i offset : Nat) (v : α)
    : (A.push v).oget! i offset = A.oget! i offset := by
  simp only [oget!, oget, Array.length_toList, size_push, rsize_push]
  split <;> try rfl
  split <;> try rfl
  exact get_push_lt ..

@[simp]
theorem oget_push {A : RangeArray α} {i offset : Nat} (hi : i < A.size) (ho : offset < A.rsize i hi) (v : α)
    : (A.push v).oget i hi offset ho = A.oget i hi offset ho := by
  simp only [oget_eq_oget!, oget!_push]

theorem oget!_commit_lt {A : RangeArray α} {i offset : Nat} (hi : i < A.size) (ho : offset < A.rsize! i)
    : (A.commit).oget! i offset = A.oget! i offset := by
  simp only [oget!, Array.length_toList, size_commit, Nat.lt_succ_of_lt hi,
    ↓reduceDIte, rsize_eq_rsize!, hi, rsize!_commit_lt, ho, oget,
    index_eq_index!, index!_commit_lt hi, get_eq_get!, get!_commit]

@[simp]
theorem oget_commit_lt {A : RangeArray α} {i offset : Nat}
        (hi : i < A.size) (ho : offset < A.rsize i hi)
    : (A.commit).oget i (by simp [Nat.lt_succ_of_lt hi]) offset (by simp [rsize_commit_lt hi, ho])
        = A.oget i hi offset ho := by
  rw [rsize_eq_rsize!] at ho
  simp only [oget_eq_oget!, oget!_commit_lt hi ho]

-- Can't mark this `@[simp]` because it has an assumption
theorem oget!_commit_eq {A : RangeArray α} {offset : Nat} (ho : offset < A.usize)
    : (A.commit).oget! A.size offset = A.uget! offset := by
  simp only [oget!, Array.length_toList, size_commit, Nat.lt_add_one,
    ↓reduceDIte, rsize_commit_eq, ho, oget, index_commit_eq, get_eq_get!,
    get!_commit, uget!, uget]

theorem oget!_delete!_ne {i j : Nat} (hij : i ≠ j) (A : RangeArray α) (offset : Nat)
    : (A.delete! i).oget! j offset = A.oget! j offset := by
  simp only [oget!, Array.length_toList, size_delete!]
  simp only [delete!, Array.length_toList, id_eq]
  split <;> rename_i hj <;> try rfl
  split <;> rename_i hi <;> try rfl
  simp only [delete_eq_delete!, rsize_eq_rsize!, rsize!_delete!_ne hij]
  split <;> try rfl
  simp only [oget, get, delete!, Array.length_toList, hi, ↓reduceDIte,
    delete, index, Array.getElem_set, hij, ↓reduceIte]

theorem uget!_push_lt {A : RangeArray α} {i} (hi : i < A.usize) (v : α)
    : (A.push v).uget! i = A.uget! i := by
  simp only [uget!, uget, usize_push, hi, lt_succ_of_lt hi,
    ↓reduceDIte, dsize_push, get_eq_get!]
  simp only [usize] at hi
  exact get!_push_lt (by omega) _

@[simp]
theorem uget_push_lt {A : RangeArray α} {i} (hi : i < A.usize) (v : α)
    : (A.push v).uget i (by simp [Nat.lt_succ_of_lt hi]) = A.uget i hi := by
  simp only [uget_eq_uget!]
  exact uget!_push_lt hi v

@[simp]
theorem uget!_push_eq : (A.push v).uget! A.usize = v := by
  have : A.dsize + A.usize = A.data.size := by
    have := A.h_size
    simp only [dsize, usize]
    omega
  simp [uget!, uget, this, get_push_eq]

@[simp]
theorem uget_push_eq : (A.push v).uget A.usize (by simp) = v := by
  simp only [uget_eq_uget!]
  exact uget!_push_eq ..

theorem uget!_push_gt {A : RangeArray α} {i} (hi : i > A.usize) (v : α)
    : (A.push v).uget! i = default := by
  simp only [uget!, uget, usize_push, hi, dite_eq_right_iff]
  intro
  omega

@[simp]
theorem uget!_delete! (A : RangeArray α) (i j : Nat) :
    (A.delete! j).uget! i = A.uget! i := by
  simp [delete!]
  split <;> rfl

end get /- section -/

#exit

section models

variable [Inhabited α] {R : RangeArray α} {Ls : List (Option (List α))} {L : List α} (h_models : models R Ls L)

theorem get_eq_some_of_models_of_not_deleted {i : Nat} :
    R.isDeleted! i = false → ∃ (hi : i < Size.size Ls) (sL : _), Seq.get! Ls ⟨i, hi⟩ = some sL := by
  intro h_del
  by_cases hi : i < Size.size Ls
  · have := h_models.h_some hi
    simp [h_del] at this
    use hi
  · rw [← h_models.h_size₁] at hi
    rw [isDeleted_true_of_ge (not_lt.mp hi)] at h_del
    contradiction

@[simp]
theorem models_empty (size : Nat) : models (empty size) ([] : List (Option (List α))) [] := by
  constructor <;> simp

theorem models_push : ∀ (v : α), models (R.push v) Ls (Seq.snoc L v) := by
  intro v
  constructor
  case h_size₁ => simp only [size_push, h_models.h_size₁]
  case h_size₂ => simp only [usize_push, h_models.h_size₂, Seq.size_snoc]
  case h_some => refine h_models.h_some
  case h_sizes => refine h_models.h_sizes
  case h_agree =>
    intro i hi sL hsL j hj
    have := h_models.h_agree hi hsL hj
    -- CC: `R.push` lurks in the dependent types. We unfold to access it explicitly
    simp only [oget_eq_oget, oget_push] at this ⊢
    exact this
  case h_uncommitted =>
    intro i hi
    have hi₁ := hi
    rw [Seq.size_snoc, ← h_models.h_size₂] at hi₁
    rcases eq_or_lt_of_le (le_of_lt_succ hi₁) with (hi' | hi')
    · conv => lhs; simp [hi']
      rw [h_models.h_size₂] at hi'
      simp only [uget_eq_uget, uget_push_eq, hi',  lt_self_iff_false, reduceDIte]
    · conv => lhs; simp [uget_push_lt hi']
      rw [Seq.get_snoc]
      rw [h_models.h_size₂] at hi'
      split <;> rename _ => hi₂
      · -- CC: `R.push` lurks in the dependent types. We unfold to access it explicitly
        have := h_models.h_uncommitted hi'
        simp [uget_eq_uget] at this ⊢
        rw [uget_push_lt (h_models.h_size₂ ▸ hi')]
        exact this
      · simp at hi₂ hi
        have := le_antisymm hi₂ (le_of_lt_succ hi)
        rw [this] at hi'
        exact absurd hi' (not_lt.mpr (le_refl _))

theorem models_commit : models (R.commit) (Seq.snoc Ls (some L)) [] := by
  constructor
  case h_size₁ => simp only [size_commit, h_models.h_size₁, Seq.size_snoc]
  case h_size₂ => simp only [usize_commit, List.size_nil]
  case h_some =>
    intro i hi
    simp only [Seq.size_snoc] at hi
    simp only [Seq.get_snoc]
    split <;> rename _ => hi₂
    · rw [← h_models.h_size₁] at hi₂
      conv => lhs; simp [isDeleted_commit_lt hi₂]
      rw [h_models.h_size₁] at hi₂
      exact h_models.h_some hi₂
    · simp only [not_lt] at hi₂
      have := le_antisymm (le_of_lt_succ hi) hi₂
      rw [← h_models.h_size₁] at this
      simp only [this, isDeleted_commit_eq, Option.some.injEq, exists_eq']
  case h_sizes =>
    intro i hi sL hsL
    simp only [Seq.size_snoc] at hi
    simp only [rsize_eq_rsize]
    rcases eq_or_lt_of_le (le_of_lt_succ hi) with (rfl | hi₂)
    · conv => lhs; rw [← h_models.h_size₁]
      simp [h_models.h_size₂]
      simp [Seq.get_snoc] at hsL
      subst hsL
      rfl
    · rw [← h_models.h_size₁] at hi₂
      rw [rsize_commit_lt hi₂]
      rw [h_models.h_size₁] at hi₂
      simp [ hi₂] at hsL
      have := h_models.h_sizes hi₂ hsL
      simp only [rsize_eq_rsize] at this
      exact this
  · intro i hi sL hsL j hj
    simp only [Seq.size_snoc] at hi
    simp only [oget_eq_oget]
    rcases eq_or_lt_of_le (le_of_lt_succ hi) with (hi₂ | hi₂)
    · simp [hi₂] at hsL
      subst hsL
      rw [← h_models.h_size₁] at hi₂
      rw [hi₂, oget_commit_eq ((h_models.h_size₂).symm ▸ hj)]
      have := h_models.h_uncommitted hj
      simp only [uget_eq_uget] at this
      exact this
    · simp [ hi₂] at hsL
      rw [← h_models.h_sizes hi₂ hsL] at hj
      rw [← h_models.h_size₁] at hi₂
      rw [rsize_eq_rsize] at hj
      rw [oget_commit_lt hi₂ hj]
      rw [h_models.h_size₁] at hi₂
      clear hj
      have := h_models.h_agree hi₂ hsL hj
      rw [oget_eq_oget] at this
      exact this
  case h_uncommitted => simp only [List.size_nil, not_lt_zero', IsEmpty.forall_iff, implies_true]

theorem models_delete! : ∀ {i : Nat} (hi : i < Size.size Ls),
    models (R.delete! i) (Seq.set Ls ⟨i, hi⟩ none) L := by
  intro i hi
  constructor
  case h_size₁ => simp only [size_delete, h_models.h_size₁, Seq.size_set]
  case h_size₂ => simp only [usize_delete, h_models.h_size₂]
  case h_some =>
    intro j hj
    by_cases hij : i = j
    · simp [hij]
    · rw [isDeleted_delete_ne R hij]
      simp [Seq.get_set, hij, -eq_iff_iff]
      simp at hj
      exact h_models.h_some hj
  case h_sizes =>
    intro j hj sL hsL
    by_cases hij : i = j
    · simp [Seq.get_set, hij] at hsL
    · simp [Seq.get_set, hij] at hsL
      simp at hj
      rw [rsize_eq_rsize, rsize_delete_ne hij]
      have := h_models.h_sizes hj hsL
      rw [rsize_eq_rsize] at this
      exact this
  case h_agree =>
    intro j hj sL hsL k hk
    by_cases hij : i = j
    <;> simp [Seq.get_set, hij] at hsL
    simp at hj
    have := h_models.h_some hj
    simp [hsL] at this
    rw [oget_eq_oget, oget_delete_ne R hij]
    have := h_models.h_agree hj hsL hk
    rw [oget_eq_oget] at this
    exact this
  case h_uncommitted =>
    intro j hj
    have := h_models.h_uncommitted hj
    simp [uget_eq_uget, uget_delete] at this ⊢
    exact this

theorem eq_nil_of_models_of_usize_zero : R.usize = 0 → L = [] := by
  intro h_usize
  simp only [h_models.h_size₂, LeanColls.size, List.length_eq_zero] at h_usize
  cases L <;> first | rfl | simp at h_usize

end models /- section -/


end RangeArray

end Trestle
