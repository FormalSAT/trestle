/-
Copyright (c) the LeanSAT contributors.

Authors: Wojciech Nawrocki
-/

import Mathlib.Data.Set.Basic

namespace LeanSAT.Model

/-! ### Propositional assignments -/

/-- A (total) assignment of truth values to propositional variables. -/
def PropAssignment (ν : Type u) := ν → Bool

namespace PropAssignment

@[ext] theorem ext (v1 v2 : PropAssignment ν) (h : ∀ x, v1 x = v2 x) : v1 = v2 := funext h

def set [DecidableEq ν] (τ : PropAssignment ν) (x : ν) (v : Bool) :
    PropAssignment ν :=
  fun y => if y = x then v else τ y

@[simp]
theorem set_get [DecidableEq ν] (τ : PropAssignment ν) (x : ν) (v : Bool) :
    τ.set x v x = v := by
  simp [set]

theorem set_get_of_ne [DecidableEq ν] {x y : ν} (τ : PropAssignment ν) (v : Bool) :
    x ≠ y → τ.set x v y = τ y := by
  intro h
  simp [set, h.symm]

@[simp]
theorem set_set [DecidableEq ν] (τ : PropAssignment ν) (x : ν) (v v' : Bool) :
    (τ.set x v).set x v' = τ.set x v' := by
  ext x'
  dsimp [set]; split <;> simp_all

@[simp]
theorem set_same [DecidableEq ν] (τ : PropAssignment ν) (x : ν) :
    τ.set x (τ x) = τ := by
  ext x'
  dsimp [set]; split <;> simp_all

-- TODO: is this defined in mathlib for functions in general?
def agreeOn (X : Set ν) (σ₁ σ₂ : PropAssignment ν) : Prop :=
  ∀ x ∈ X, σ₁ x = σ₂ x

theorem agreeOn_refl (X : Set ν) (σ : PropAssignment ν) : agreeOn X σ σ :=
  fun _ _ => rfl
theorem agreeOn.symm : agreeOn X σ₁ σ₂ → agreeOn X σ₂ σ₁ :=
  fun h x hX => Eq.symm (h x hX)
theorem agreeOn.trans : agreeOn X σ₁ σ₂ → agreeOn X σ₂ σ₃ → agreeOn X σ₁ σ₃ :=
  fun h₁ h₂ x hX => Eq.trans (h₁ x hX) (h₂ x hX)

theorem agreeOn.subset : X ⊆ Y → agreeOn Y σ₁ σ₂ → agreeOn X σ₁ σ₂ :=
  fun hSub h x hX => h x (hSub hX)

theorem agreeOn_empty (σ₁ σ₂ : PropAssignment ν) : agreeOn ∅ σ₁ σ₂ :=
  fun _ h => False.elim (Set.not_mem_empty _ h)

variable [DecidableEq ν]

theorem agreeOn_set_of_not_mem {x : ν} {X : Set ν} (σ : PropAssignment ν) (v : Bool) : x ∉ X →
    agreeOn X (σ.set x v) σ := by
  -- I ❤ A️esop
  aesop (add norm unfold agreeOn, norm unfold set)
