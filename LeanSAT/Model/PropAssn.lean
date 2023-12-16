/-
Copyright (c) the LeanSAT contributors.

Authors: Wojciech Nawrocki, James Gallicchio
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import LeanSAT.Upstream.ToMathlib

namespace LeanSAT.Model

/-! ### Propositional assignments -/

/-- A (total) assignment of truth values to propositional variables. -/
def PropAssignment (ν : Type u) := ν → Bool

namespace PropAssignment

instance : Inhabited (PropAssignment ν) :=
  inferInstanceAs (Inhabited (_ → _))

@[ext] theorem ext (v1 v2 : PropAssignment ν) (h : ∀ x, v1 x = v2 x) : v1 = v2 := funext h

def set [DecidableEq ν] (τ : PropAssignment ν) (x : ν) (v : Bool) :
    PropAssignment ν :=
  fun y => if y = x then v else τ y

@[simp]
theorem set_get [DecidableEq ν] (τ : PropAssignment ν) (x : ν) (v : Bool) :
    τ.set x v x = v := by
  simp [set]

@[simp]
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

theorem set_comm [DecidableEq ν] (τ : PropAssignment ν) (x₁ b₁ x₂ b₂) (h : x₁ ≠ x₂)
  : (τ.set x₂ b₂).set x₁ b₁ = (τ.set x₁ b₁).set x₂ b₂ := by
  ext v
  simp [set]; split <;> split <;> (subst_vars; simp at *)

/-- Assignment which agrees with `τ'` on `xs` but `τ` everywhere else. -/
def setMany [DecidableEq ν] (τ : PropAssignment ν) (xs : Finset ν) (τ' : PropAssignment ν)
  : PropAssignment ν :=
  fun v => if v ∈ xs then τ' v else τ v

@[simp] theorem setMany_mem [DecidableEq ν] (τ : PropAssignment ν) (xs) (τ') (h : v ∈ xs)
  : (setMany τ xs τ') v = τ' v := by
  simp [setMany, h]

@[simp] theorem setMany_not_mem [DecidableEq ν] (τ : PropAssignment ν) (xs) (τ') (h : ¬ v ∈ xs)
  : (setMany τ xs τ') v = τ v := by
  simp [setMany, h]

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

theorem agreeOn_setMany [DecidableEq ν] (τ : PropAssignment ν) (xs : Finset ν) (τ')
  : agreeOn xs (τ.setMany xs τ') τ' := by
  intro v hv
  simp at hv
  simp [setMany, hv]

theorem agreeOn_setMany_compl [DecidableEq ν] (τ : PropAssignment ν) (xs : Finset ν) (τ')
  : agreeOn xsᶜ (τ.setMany xs τ') τ := by
  intro v hv
  simp at hv
  simp [setMany, hv]

def map (f : ν₂ → ν₁) (τ : PropAssignment ν₁) : PropAssignment ν₂ :=
  τ ∘ f

@[simp] theorem app_map : map f τ v = τ (f v) := rfl

def setManyMap (τ : PropAssignment ν) (τ' : PropAssignment ν') (f : ν → Option ν')
  : PropAssignment ν :=
  fun v =>
    match f v with
    | none => τ v
    | some v' => τ' v'

theorem setManyMap_setManyMap
      (τ1 : PropAssignment ν1) (τ2 : PropAssignment ν2) (τ3 : PropAssignment ν3)
      (f1 : ν1 → Option ν2) (f2 : ν2 → Option ν3)
  : setManyMap τ1 (setManyMap τ2 τ3 f2) f1 = setManyMap (setManyMap τ1 τ2 f1) τ3 (fun x => (f1 x).bind f2)
  := by
  ext v
  simp [setManyMap]
  split <;> simp [*]
