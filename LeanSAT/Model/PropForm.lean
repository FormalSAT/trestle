/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Mathlib.Data.Set.Basic

import LeanSAT.Upstream.ToMathlib
import LeanSAT.Model.PropAssn

namespace LeanSAT.Model

/-! ### Propositional formulas -/

/-- A propositional formula over variables of type `ν`.

This is the inductively defined syntax of formulas.
Later on we can take a quotient to identify `x ∨ ¬x` with `⊤`, for example. -/
inductive PropForm (ν : Type u)
  | var (x : ν)
  | tr
  | fls
  | neg    (φ : PropForm ν)
  | conj   (φ₁ φ₂ : PropForm ν)
  | disj   (φ₁ φ₂ : PropForm ν)
  | impl   (φ₁ φ₂ : PropForm ν)
  | biImpl (φ₁ φ₂ : PropForm ν)
  deriving Repr, DecidableEq, Inhabited

namespace PropForm

protected def toString [ToString ν] : PropForm ν → String
  | var x        => toString x
  | tr           => "⊤"
  | fls          => "⊥"
  | neg φ        => s!"¬{go φ}"
  | conj φ₁ φ₂   => s!"{go φ₁} ∧ {go φ₂}"
  | disj φ₁ φ₂   => s!"{go φ₁} ∨ {go φ₂}"
  | impl φ₁ φ₂   => s!"{go φ₁} → {go φ₂}"
  | biImpl φ₁ φ₂ => s!"{go φ₁} ↔ {go φ₂}"
where go n :=
  let s := PropForm.toString n
  if s.contains ' ' then s!"({s})" else s
termination_by
  toString f => 2 * sizeOf f
  go f => 1 + 2 * sizeOf f

instance [ToString ν] : ToString (PropForm ν) :=
  ⟨PropForm.toString⟩

instance : Coe L (PropForm L) := ⟨.var⟩

def conj' (fs : List (PropForm L)) : PropForm L :=
  match fs.foldr (init := none) (fun f =>
    fun
    | none => some f
    | some f' => some <| .conj f f'
  ) with
  | none => .tr
  | some f => f

def disj' (fs : List (PropForm L)) : PropForm L :=
  match fs.foldr (init := none) (fun f =>
    fun
    | none => some f
    | some f' => some <| .disj f f'
  ) with
  | none => .fls
  | some f => f

/-- The unique extension of `τ` from variables to formulas. -/
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

/-! ### Satisfying assignments -/

/-- An assignment satisfies a formula `φ` when `φ` evaluates to `⊤` at that assignment. -/
def satisfies (τ : PropAssignment ν) (φ : PropForm ν) : Prop :=
  φ.eval τ = true

/-- This instance is scoped so that `τ ⊨ φ : Prop` implies `φ : PropForm _` via the `outParam`
only when `PropForm` is open. -/
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

/-! ### Semantic entailment and equivalence -/

/-- A formula `φ₁` semantically entails `φ₂` when `τ ⊨ φ₁` implies `τ ⊨ φ₂`.

This is actually defined in terms of the Boolean lattice
to reuse various `le_blah` theorems,
and the above statement is a theorem (`entails_ext`). -/
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

/-- Two formulas are semantically equivalent when they always evaluate to the same thing.

This is a strong notion of equivalence.
See `equivalentOver` for a weaker one. -/
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

/-! ## Define notation for `PropForm`s -/

namespace Notation

-- The notation for `Prop` has default priority (1000).
-- When open, we want to always supercede `Prop` notation.
scoped notation:max (priority := 1100) " ¬ " b:40 => neg b
scoped infixr:35    (priority := 1100) " ∧ "      => conj
scoped infixr:30    (priority := 1100) " ∨ "      => disj
scoped infixr:25    (priority := 1100) " → "      => impl
scoped infix:20     (priority := 1100) " ↔ "      => biImpl

example (a b c d : ν) : PropForm ν :=
  a ∧ b ∨ c → d  ↔  (¬a ∨ ¬b) ∧ ¬c ∨ d

end Notation
