/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Mathlib.Data.Set.Basic
import Mathlib.Order.BooleanAlgebra

import ProofChecker.Model.ToMathlib

/-! Formulas of propositional logic. -/

/-- A propositional formula over variables of type `ν`. -/
inductive PropForm (ν : Type u)
  | var (x : ν)
  | tr
  | fls
  | neg (φ : PropForm ν)
  | conj (φ₁ φ₂ : PropForm ν)
  | disj (φ₁ φ₂ : PropForm ν)
  | impl (φ₁ φ₂ : PropForm ν)
  | biImpl (φ₁ φ₂ : PropForm ν)
  deriving Repr, DecidableEq, Inhabited

namespace PropForm

-- HACK: a `let` doesn't work with structural recursion
local macro "go " n:ident : term =>
  `(let s := $(Lean.mkIdent `PropForm.toString) $n
    if s.contains ' ' then s!"({s})" else s)
protected def toString [ToString ν] : PropForm ν → String
  | var x        => toString x
  | tr           => "⊤"
  | fls          => "⊥"
  | neg φ        => s!"¬{go φ}"
  | conj φ₁ φ₂   => s!"{go φ₁} ∧ {go φ₂}"
  | disj φ₁ φ₂   => s!"{go φ₁} ∨ {go φ₂}"
  | impl φ₁ φ₂   => s!"{go φ₁} → {go φ₂}"
  | biImpl φ₁ φ₂ => s!"{go φ₁} ↔ {go φ₂}"

instance [ToString ν] : ToString (PropForm ν) :=
  ⟨PropForm.toString⟩

end PropForm

/-- An assignment of truth values to propositional variables. -/
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

end PropAssignment

namespace PropForm

/-- The unique evaluation function on formulas which extends `τ`. -/
@[simp]
def eval (τ : PropAssignment ν) : PropForm ν → Bool
  | var x => τ x
  | tr => true
  | fls => false
  | neg φ => !(eval τ φ)
  | conj φ₁ φ₂ => (eval τ φ₁) && (eval τ φ₂)
  | disj φ₁ φ₂ => (eval τ φ₁) || (eval τ φ₂)
  | impl φ₁ φ₂ => (eval τ φ₁) ⇨ (eval τ φ₂)
  | biImpl φ₁ φ₂ => eval τ φ₁ = eval τ φ₂

/-! Satisfying assignments -/

/-- An assignment satisfies a formula `φ` when `φ` evaluates to `⊤` at that assignment. -/
def satisfies (τ : PropAssignment ν) (φ : PropForm ν) : Prop :=
  φ.eval τ = true

/-- This instance is scoped so that `τ ⊨ φ : Prop` implies `φ : PropForm _` via the `outParam` only
when `PropForm` is open. -/
scoped instance : SemanticEntails (PropAssignment ν) (PropForm ν) where
  entails := PropForm.satisfies

open SemanticEntails renaming entails → sEntails

variable {τ : PropAssignment ν} {x : ν} {φ φ₁ φ₂ φ₃ : PropForm ν}

@[simp]
theorem satisfies_var : τ ⊨ var x ↔ τ x := by
  simp [sEntails, satisfies]

@[simp]
theorem satisfies_tr : τ ⊨ tr := by
  simp [sEntails, satisfies]

@[simp]
theorem not_satisfies_fls : τ ⊭ fls :=
  fun h => nomatch h

@[simp]
theorem satisfies_neg : τ ⊨ neg φ ↔ τ ⊭ φ := by
  simp [sEntails, satisfies]

@[simp]
theorem satisfies_conj : τ ⊨ conj φ₁ φ₂ ↔ τ ⊨ φ₁ ∧ τ ⊨ φ₂ := by
  simp [sEntails, satisfies]

@[simp]
theorem satisfies_disj : τ ⊨ disj φ₁ φ₂ ↔ τ ⊨ φ₁ ∨ τ ⊨ φ₂ := by
  simp [sEntails, satisfies]

@[simp]
theorem satisfies_impl : τ ⊨ impl φ₁ φ₂ ↔ (τ ⊨ φ₁ → τ ⊨ φ₂) := by
  simp only [sEntails, satisfies, eval]
  cases (eval τ φ₁) <;> simp [himp_eq]

theorem satisfies_impl' : τ ⊨ impl φ₁ φ₂ ↔ τ ⊭ φ₁ ∨ τ ⊨ φ₂ := by
  simp only [sEntails, satisfies, eval]
  cases (eval τ φ₁) <;> simp [himp_eq]

@[simp]
theorem satisfies_biImpl : τ ⊨ biImpl φ₁ φ₂ ↔ (τ ⊨ φ₁ ↔ τ ⊨ φ₂) := by
  simp [sEntails, satisfies]

theorem satisfies_biImpl' : τ ⊨ biImpl φ₁ φ₂ ↔ ((τ ⊨ φ₁ ∧ τ ⊨ φ₂) ∨ (τ ⊭ φ₁ ∧ τ ⊭ φ₂)) := by
  simp only [sEntails, satisfies, eval]
  cases (eval τ φ₁) <;> aesop

/-! Semantic entailment and equivalence. -/

/-- A formula `φ₁` semantically entails `φ₂` when `τ ⊨ φ₁` implies `τ ⊨ φ₂`.

This is actually defined in terms of the Boolean lattice and the above statement is a theorem.
Note that the two-valued Boolean model is universal, so this formulation of semantic entailment
is equivalent to entailment in every Boolean algebra, and also (by completeness) to provability. -/
def entails (φ₁ φ₂ : PropForm ν) : Prop :=
  ∀ (τ : PropAssignment ν), φ₁.eval τ ≤ φ₂.eval τ

/-- An equivalent formulation of semantic entailment in terms of satisfying assignments. -/
theorem entails_ext : entails φ₁ φ₂ ↔ (∀ (τ : PropAssignment ν), τ ⊨ φ₁ → τ ⊨ φ₂) := by
  have : ∀ τ, (φ₁.eval τ → φ₂.eval τ) ↔ φ₁.eval τ ≤ φ₂.eval τ := by
    intro τ
    cases (eval τ φ₁)
    . simp
    . simp only [true_implies]
      exact ⟨fun h => h ▸ le_rfl, top_unique⟩
  simp [sEntails, entails, satisfies, this]

theorem entails_refl (φ : PropForm ν) : entails φ φ :=
  fun _ => le_rfl
theorem entails.trans : entails φ₁ φ₂ → entails φ₂ φ₃ → entails φ₁ φ₃ :=
  fun h₁ h₂ τ => le_trans (h₁ τ) (h₂ τ)

theorem entails_tr (φ : PropForm ν) : entails φ tr :=
  fun _ => le_top
theorem fls_entails (φ : PropForm ν) : entails fls φ :=
  fun _ => bot_le

theorem entails_disj_left (φ₁ φ₂ : PropForm ν) : entails φ₁ (disj φ₁ φ₂) :=
  fun _ => le_sup_left
theorem entails_disj_right (φ₁ φ₂ : PropForm ν) : entails φ₂ (disj φ₁ φ₂) :=
  fun _ => le_sup_right
theorem disj_entails : entails φ₁ φ₃ → entails φ₂ φ₃ → entails (disj φ₁ φ₂) φ₃ :=
  fun h₁ h₂ τ => sup_le (h₁ τ) (h₂ τ)

theorem conj_entails_left (φ₁ φ₂ : PropForm ν) : entails (conj φ₁ φ₂) φ₁ :=
  fun _ => inf_le_left
theorem conj_entails_right (φ₁ φ₂ : PropForm ν) : entails (conj φ₁ φ₂) φ₂ :=
  fun _ => inf_le_right
theorem entails_conj : entails φ₁ φ₂ → entails φ₁ φ₃ → entails φ₁ (conj φ₂ φ₃) :=
  fun h₁ h₂ τ => le_inf (h₁ τ) (h₂ τ)

theorem entails_disj_conj (φ₁ φ₂ φ₃ : PropForm ν) :
    entails (conj (disj φ₁ φ₂) (disj φ₁ φ₃)) (disj φ₁ (conj φ₂ φ₃)) :=
  fun _ => le_sup_inf

theorem conj_neg_entails_fls (φ : PropForm ν) : entails (conj φ (neg φ)) fls :=
  fun τ => BooleanAlgebra.inf_compl_le_bot (eval τ φ)

theorem tr_entails_disj_neg (φ : PropForm ν) : entails tr (disj φ (neg φ)) :=
  fun τ => BooleanAlgebra.top_le_sup_compl (eval τ φ)

/-- Two formulas are semantically equivalent when they always evaluate to the same thing. -/
def equivalent (φ₁ φ₂ : PropForm ν) : Prop :=
  ∀ (τ : PropAssignment ν), φ₁.eval τ = φ₂.eval τ

theorem equivalent_iff_entails :
    equivalent φ₁ φ₂ ↔ (entails φ₁ φ₂ ∧ entails φ₂ φ₁) := by
  simp only [equivalent, entails]
  aesop (add safe le_antisymm)

theorem equivalent_ext :
    equivalent φ₁ φ₂ ↔ (∀ (τ : PropAssignment ν), τ ⊨ φ₁ ↔ τ ⊨ φ₂) := by
  simp only [equivalent_iff_entails, entails_ext]
  aesop

theorem equivalent_refl (φ : PropForm ν) : equivalent φ φ :=
  fun _ => rfl
theorem equivalent.symm : equivalent φ₁ φ₂ → equivalent φ₂ φ₁ :=
  fun h τ => (h τ).symm
theorem equivalent.trans : equivalent φ₁ φ₂ → equivalent φ₂ φ₃ → equivalent φ₁ φ₃ :=
  fun h₁ h₂ τ => (h₁ τ).trans (h₂ τ)
theorem entails.antisymm : entails φ₁ φ₂ → entails φ₂ φ₁ → equivalent φ₁ φ₂ :=
  fun h₁ h₂ => equivalent_iff_entails.mpr ⟨h₁, h₂⟩

-- Equivalently, when `impl φ₁ φ₂` always evaluates to `⊤`.

end PropForm