/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Mathlib.Data.Finset.Basic

import ProofChecker.Data.HashMap.Lemmas

def HashSet (α : Type) [BEq α] [Hashable α] := HashMap α Unit

namespace HashSet

variable {α : Type} [BEq α] [Hashable α]

def empty (α : Type) [BEq α] [Hashable α] : HashSet α :=
  HashMap.empty

def isEmpty (s : HashSet α) : Bool :=
  HashMap.isEmpty s

def insert (s : HashSet α) (a : α) : HashSet α :=
  HashMap.insert s a ()

def singleton (a : α) : HashSet α :=
  empty α |>.insert a

def contains (s : HashSet α) (a : α) : Bool :=
  HashMap.contains s a

def union (s t : HashSet α) : HashSet α :=
  HashMap.fold (init := s) (fun acc a _ => acc.insert a) t

def inter (s t : HashSet α) : HashSet α :=
  HashMap.fold (init := empty α) (fun acc a _ =>
    if s.contains a then acc.insert a else acc) t

variable [DecidableEq α]

def toFinset (s : HashSet α) : Finset α :=
  HashMap.fold (init := ∅) (fun X a _ => Insert.insert a X) s

variable [LawfulBEq α] [HashMap.LawfulHashable α]

theorem toFinset_sub (s : HashSet α) (a : α) : a ∈ s.toFinset → s.contains a := by
  dsimp [toFinset]
  apply HashMap.foldRecOn
    (C := fun acc => a ∈ acc → s.contains a)
    (hInit := by simp)
  simp only [Finset.mem_insert]
  intro _ a _ ih hFind hMem
  cases hMem with
  | inl h =>
    apply HashMap.contains_iff _ _ |>.mpr 
    exact h ▸ ⟨_, hFind⟩
  | inr h => exact ih h

theorem sub_toFinset (s : HashSet α) (a : α) : s.contains a → a ∈ s.toFinset := by
  dsimp [toFinset, contains]
  intro hContains
  have ⟨_, hFind⟩ := HashMap.contains_iff _ _ |>.mp hContains
  have ⟨_, hEq⟩ := HashMap.fold_of_mapsTo_of_comm s (fun (X : Finset α) a _ => Insert.insert a X) ∅
    hFind ?comm
  case comm =>
    intros
    ext
    aesop
  simp [hEq]

theorem mem_toFinset (s : HashSet α) (a : α) : a ∈ s.toFinset ↔ s.contains a :=
  ⟨toFinset_sub s a, sub_toFinset s a⟩

theorem not_mem_toFinset (s : HashSet α) (a : α) : a ∉ s.toFinset ↔ ¬s.contains a := by
  simp [mem_toFinset]

@[simp]
theorem toFinset_empty : toFinset (empty α) = ∅ := by
  ext
  simp [mem_toFinset, empty, contains, HashMap.not_contains_empty]

theorem toFinset_of_isEmpty (s : HashSet α) : s.isEmpty → s.toFinset = ∅ := by
  intro h
  ext
  simp [mem_toFinset, contains, HashMap.not_contains_of_isEmpty _ _ h]

@[simp]
theorem toFinset_insert (s : HashSet α) (a : α) :
    toFinset (s.insert a) = Insert.insert a s.toFinset := by
  ext
  simp [mem_toFinset, insert, contains, HashMap.contains_insert]
  tauto

@[simp]
theorem toFinset_singleton (a : α) : toFinset (singleton a) = {a} := by
  simp [singleton, toFinset_insert]

theorem toFinset_union_sub (s t : HashSet α) : (s.union t).toFinset ⊆ s.toFinset ∪ t.toFinset := by
  dsimp [union]
  intro x
  apply HashMap.foldRecOn
    (C := fun (acc : HashSet α) => x ∈ acc.toFinset → x ∈ s.toFinset ∪ t.toFinset)
    (hInit := by simp; tauto)
  intro _ a _ _ hFind
  have : a ∈ t.toFinset := by
    have := HashMap.contains_iff _ _|>.mpr ⟨_, hFind⟩
    simp [mem_toFinset, contains, this]
  aesop

theorem sub_toFinset_union_left (s t : HashSet α) : s.toFinset ⊆ (s.union t).toFinset := by
  dsimp [union]
  intro x
  apply HashMap.foldRecOn
    (C := fun (acc : HashSet α) => x ∈ s.toFinset → x ∈ acc.toFinset)
    (hInit := id)
  aesop

theorem sub_toFinset_union (s t : HashSet α) : s.toFinset ∪ t.toFinset ⊆ (s.union t).toFinset := by
  apply Finset.union_subset (sub_toFinset_union_left s t)
  dsimp [union]
  intro _ h
  have ⟨_, hFind⟩ := HashMap.contains_iff _ _|>.mp (mem_toFinset _ _ |>.mp h)
  have ⟨_, h⟩ := HashMap.fold_of_mapsTo_of_comm t (init := s) (fun acc a _ => acc.insert a)
    hFind (by intros; apply HashMap.insert_comm)
  simp [h]

@[simp]
theorem toFinset_union (s t : HashSet α) : (s.union t).toFinset = s.toFinset ∪ t.toFinset :=
  subset_antisymm (toFinset_union_sub s t) (sub_toFinset_union s t)

theorem toFinset_inter_sub (s t : HashSet α) : (s.inter t).toFinset ⊆ s.toFinset ∩ t.toFinset := by
  dsimp [inter]
  intro x
  apply HashMap.foldRecOn
    (C := fun (acc : HashSet α) => x ∈ acc.toFinset → x ∈ s.toFinset ∩ t.toFinset)
    (hInit := by simp)
  intro _ a _ _ hFind
  have : a ∈ t.toFinset := by
    have := HashMap.contains_iff _ _|>.mpr ⟨_, hFind⟩
    simp [mem_toFinset, contains, this]
  split <;>
    aesop (add norm mem_toFinset)

theorem sub_toFinset_inter (s t : HashSet α) : s.toFinset ∩ t.toFinset ⊆ (s.inter t).toFinset := by
  intro x
  simp only [inter, Finset.mem_inter]
  intro ⟨hS, hT⟩
  have ⟨_, hFind⟩ := HashMap.contains_iff _ _|>.mp (mem_toFinset _ _ |>.mp hT)
  have ⟨_, h⟩ := HashMap.fold_of_mapsTo_of_comm t (init := empty α)
    (fun acc a _ => if s.contains a then acc.insert a else acc)
    hFind ?comm
  case comm =>
    intros
    dsimp [insert]
    split_ifs <;>
      aesop (add norm HashMap.insert_comm)
  rw [h]
  split
  . simp
  . have : x ∉ s.toFinset :=
      not_mem_toFinset _ _ |>.mpr (by assumption)
    contradiction

@[simp]
theorem toFinset_inter (s t : HashSet α) : (s.inter t).toFinset = s.toFinset ∩ t.toFinset :=
  subset_antisymm (toFinset_inter_sub s t) (sub_toFinset_inter s t)

def Union (l : Array (HashSet α)) : HashSet α :=
  l.foldl (init := empty α) union

theorem toFinset_Union (l : Array (HashSet α)) :
    toFinset (Union l) = l.foldl (init := ∅) fun acc s => acc ∪ s.toFinset := by
  have : ∀ t, toFinset (l.foldl (init := t) union) =
      l.foldl (init := t.toFinset) fun acc s => acc ∪ s.toFinset := by
    simp only [Array.foldl_eq_foldl_data]
    induction l.data <;> simp_all
  simp [Union, this]

/-- Calculate the union of an array of `HashSet`s, and check if the array elements are all pairwise
disjoint. Return `(⋃ ss, true)` if array elements are pairwise disjoint, otherwise `(⋃ ss, false)`.
-/
def disjointUnion (ss : Array (HashSet α)) : HashSet α × Bool :=
  ss.foldl (init := (.empty α, true)) fun (U, b) t =>
    (U.union t, b && (U.inter t).isEmpty)

theorem disjointUnion_characterization (ss : Array (HashSet α)) :
    (∀ a, a ∈ (disjointUnion ss).fst.toFinset ↔ ∃ s ∈ ss.data, a ∈ s.toFinset)
    ∧ ((disjointUnion ss).snd →
      ∀ (i j : Fin ss.size), i ≠ j → ss[i].toFinset ∩ ss[j].toFinset = ∅) :=
  have ⟨h₁, h₂, h₃⟩ := ss.foldl_induction
    (motive := fun i (acc : HashSet α × Bool) =>
      (∀ a ∈ acc.1.toFinset, ∃ s ∈ ss.data, a ∈ s.toFinset) ∧
      (∀ (j : Fin ss.size), j < i → ss[j].toFinset ⊆ acc.1.toFinset) ∧
      (acc.2 → ∀ (j k : Fin ss.size), j < i → k < i → j ≠ k → ss[j].toFinset ∩ ss[k].toFinset = ∅))
    (init := (empty α, true)) (h0 := by simp)
    (f := fun acc t =>
      (acc.1.union t, acc.2 && (acc.1.inter t).isEmpty))
    (hf := by
      intro i (U, b) ⟨ih₁, ih₂, ih₃⟩
      simp only [toFinset_union, Finset.mem_union]
      refine ⟨?step₁, ?step₂, ?step₃⟩
      case step₁ =>
        intro a hMem
        cases hMem with
        | inl h =>
          exact ih₁ a h
        | inr h =>
          exact ⟨ss[i], Array.get_mem_data ss i, h⟩
      case step₂ =>
        intro j hJ
        cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hJ) with
        | inl h =>
          have := ih₂ j h
          exact subset_trans this (Finset.subset_union_left _ _)
        | inr h =>
          simp [h, Finset.subset_union_right]
      case step₃ =>
        intro hB j k hJ hK hNe
        simp only [Bool.and_eq_true] at hB
        cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hJ) <;>
          cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hK)
        case inl.inl hJ hK =>
          exact ih₃ hB.left j k hJ hK hNe
        case inr.inr hJ hK =>
          have := hJ.trans hK.symm
          exact absurd (Fin.eq_of_val_eq this) hNe
        case inl.inr hJ hK =>
          have hB := toFinset_of_isEmpty _ hB.right
          simp only [toFinset_inter] at hB
          apply Finset.subset_empty.mp
          have := ih₂ j hJ
          have := Finset.inter_subset_inter_right this (u := ss[k].toFinset)
          simp_all
        case inr.inl hJ hK =>
          have hB := toFinset_of_isEmpty _ hB.right
          rw [toFinset_inter, Finset.inter_comm] at hB
          apply Finset.subset_empty.mp
          have := ih₂ k hK
          have := Finset.inter_subset_inter_left this (s := ss[j].toFinset)
          simp_all)
  by
    dsimp [disjointUnion]
    refine ⟨fun a => ⟨fun hMem => h₁ a hMem, ?_⟩,
      fun h i j hNe => h₃ h i j i.isLt j.isLt hNe⟩
    intro ⟨s, hS, hA⟩
    have ⟨i, hI⟩ := Array.get_of_mem_data hS
    exact h₂ i i.isLt (hI ▸ hA)

theorem mem_disjointUnion (ss : Array (HashSet α)) (a : α) :
    a ∈ (disjointUnion ss).fst.toFinset ↔ ∃ s ∈ ss.data, a ∈ s.toFinset :=
  disjointUnion_characterization ss |>.left a

theorem disjoint_disjointUnion (ss : Array (HashSet α)) : (disjointUnion ss).snd →
    ∀ (i j : Nat) (hI : i < ss.size) (hJ : j < ss.size), i ≠ j →
      ss[i].toFinset ∩ ss[j].toFinset = ∅ :=
  fun h i j hI hJ hNe =>
    disjointUnion_characterization ss |>.right h ⟨i, hI⟩ ⟨j, hJ⟩ (by simp [hNe])

end HashSet
