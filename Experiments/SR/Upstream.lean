/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio, Cayden Codel
-/

import Trestle.Upstream.ToStd

theorem Int.neg_cast_le (n : Nat) : -(n : Int) ≤ 0 :=
  Int.neg_nonpos_of_nonneg (ofNat_zero_le n)

theorem Int.exists_nat_of_ge_zero {i : Int} : 0 ≤ i → ∃ (n : Nat), (n : Int) = i := by
  intro h
  cases i
  · rename Nat => n
    exact ⟨n, rfl⟩
  · contradiction

@[simp]
theorem Array.foldlM_nil {m : Type v → Type w} [Monad m] (f : β → α → m β)
    (init : β) (start stop : Nat) :
    Array.foldlM f init { toList := [] } start stop = pure init :=
  Array.foldlM_empty

@[simp]
theorem Array.foldlM_trivial {m : Type v → Type w} [Monad m] (f : β → α → m β)
    (init : β) (as : Array α) (i : Nat) :
    as.foldlM f init i i = pure init := by
  simp [foldlM, Id.run]
  split <;> rename _ => hi
  · simp [foldlM.loop]
  · rw [foldlM.loop]
    simp at hi
    simp [Nat.not_lt_of_le (Nat.le_of_lt hi)]

@[simp]
theorem Array.foldl_trivial (f : β → α → β)
    (init : β) (as : Array α) (i : Nat) :
    as.foldl f init i i = init := by
  simp [foldl, Id.run, pure]
