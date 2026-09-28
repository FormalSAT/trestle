/-
Copyright (c) 2026 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: Wojciech Nawrocki
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic

import Trestle.Upstream.ToMathlib
import Trestle.Model.PropAssn

namespace Trestle.Model

/-! ## Propositional formulas -/

/--
  A propositional formula over variables of type `ν`.

  This is the inductively defined syntax of formulas.
  However, in Trestle we mostly work with `PropFun`s, which are formed
  by taking a quotient over `PropForm`
  Later on we can take a quotient to identify `x ∨ ¬x` with `⊤`, for example.
-/
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

variable {ν : Type u} {L : Type v}

protected def toString [ToString ν] : PropForm ν → String
  | var x        => toString x
  | tr           => "⊤"
  | fls          => "⊥"
  | neg φ        => s!"¬{go φ}"
  | conj φ₁ φ₂   => s!"{go φ₁} ∧ {go φ₂}"
  | disj φ₁ φ₂   => s!"{go φ₁} ∨ {go φ₂}"
  | impl φ₁ φ₂   => s!"{go φ₁} → {go φ₂}"
  | biImpl φ₁ φ₂ => s!"{go φ₁} ↔ {go φ₂}"
termination_by f => 2 * sizeOf f
where go n :=
  let s := PropForm.toString n
  if s.contains ' ' then s!"({s})" else s
termination_by 1 + 2 * sizeOf n

instance instToString [ToString ν] : ToString (PropForm ν) :=
  ⟨PropForm.toString⟩

instance instCoeLiteral : Coe L (PropForm L) := ⟨.var⟩

instance instTop : Top (PropForm ν) := ⟨.tr⟩
instance instBot : Bot (PropForm ν) := ⟨.fls⟩
instance instCompl : Compl (PropForm ν) := ⟨.neg⟩
@[simp] theorem top_def : .tr = (⊤ : PropForm ν) := rfl
@[simp] theorem bot_def : .fls = (⊥ : PropForm ν) := rfl
@[simp] theorem compl_def (φ) : .neg φ = (φᶜ : PropForm ν) := rfl

def all (fs : List (PropForm L)) : PropForm L :=
  match fs.foldr (init := none) (fun f =>
    fun
    | none => some f
    | some f' => some <| .conj f f'
  ) with
  | none => ⊤
  | some f => f

def any (fs : List (PropForm L)) : PropForm L :=
  match fs.foldr (init := none) (fun f =>
    fun
    | none => some f
    | some f' => some <| .disj f f'
  ) with
  | none => ⊥
  | some f => f

/-- Maps a function `f` variable-wise on the formula. Useful for pointwise substitutions. -/
@[simp]
def vmap (f : ν₁ → ν₂) : PropForm ν₁ → PropForm ν₂
  | .var l => .var (f l)
  | .tr => ⊤
  | .fls => ⊥
  | .neg φ => (vmap f φ)ᶜ
  | .conj φ₁ φ₂ => .conj (vmap f φ₁) (vmap f φ₂)
  | .disj φ₁ φ₂ => .disj (vmap f φ₁) (vmap f φ₂)
  | .impl φ₁ φ₂ => .impl (vmap f φ₁) (vmap f φ₂)
  | .biImpl φ₁ φ₂ => .biImpl (vmap f φ₁) (vmap f φ₂)

/-- Variables appearing in the formula. Sometimes called its "support set". -/
@[reducible, simp]
def vars [DecidableEq ν] : PropForm ν → Finset ν
  | var y => {y}
  | tr | fls => ∅
  | neg φ => vars φ
  | conj φ₁ φ₂ | disj φ₁ φ₂ | impl φ₁ φ₂ | biImpl φ₁ φ₂ => vars φ₁ ∪ vars φ₂

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

@[simp] theorem eval_var (τ : PropAssignment ν) (x : ν) : eval τ (var x) = τ x := rfl
@[simp] theorem eval_tr (τ : PropAssignment ν) : eval τ ⊤ = true := rfl
@[simp] theorem eval_fls (τ : PropAssignment ν) : eval τ ⊥ = false := rfl
@[simp] theorem eval_compl (τ : PropAssignment ν) (φ : PropForm ν) : eval τ (φᶜ) = !(eval τ φ) := rfl

/-! ### Satisfying assignments -/

/-- An assignment satisfies a formula `φ` when `φ` evaluates to `⊤` at that assignment. -/
def satisfies (τ : PropAssignment ν) (φ : PropForm ν) : Prop :=
  φ.eval τ = true

/-- This instance is scoped so that `τ ⊨ φ : Prop` implies `φ : PropForm _` via the `outParam`
only when `PropForm` is open. -/
scoped instance : SemanticEntails (PropAssignment ν) (PropForm ν) where
  entails := PropForm.satisfies

open SemanticEntails renaming entails → sEntails

instance (τ : PropAssignment ν) (φ : PropForm ν) : Decidable (τ ⊨ φ) :=
  match h : φ.eval τ with
    | true => isTrue h
    | false => isFalse fun h' => nomatch h.symm.trans h'

variable {τ : PropAssignment ν} {x : ν} {φ φ₁ φ₂ φ₃ : PropForm ν}

instance : Decidable (τ ⊨ φ) := inferInstanceAs (Decidable (φ.eval τ))

@[simp]
theorem satisfies_var : τ ⊨ var x ↔ τ x := by
  simp [sEntails, satisfies]

@[simp]
theorem satisfies_tr (τ : PropAssignment ν) : τ ⊨ ⊤ := by
  simp [sEntails, satisfies]

@[simp]
theorem not_satisfies_fls (τ : PropAssignment ν) : τ ⊭ ⊥ :=
  fun h => nomatch h

@[simp]
theorem satisfies_compl : τ ⊨ φᶜ ↔ τ ⊭ φ := by
  simp [sEntails, satisfies, ← compl_def]

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
  cases (eval τ φ₁) <;> simp

/-! ### Semantic entailment and equivalence -/

/-- A formula `φ₁` semantically entails `φ₂` when `τ ⊨ φ₁` implies `τ ⊨ φ₂`.

This is actually defined in terms of the Boolean lattice
to reuse various `le_blah` theorems,
and the above statement is a theorem (`entails_ext`). -/
def entails (φ₁ φ₂ : PropForm ν) : Prop :=
  ∀ (τ : PropAssignment ν), φ₁.eval τ ≤ φ₂.eval τ

instance instLE : LE (PropForm ν) where
  le := entails

section entails

variable (φ φ₁ φ₂ φ₃ : PropForm ν)

theorem le_def : (φ₁ ≤ φ₂) = entails φ₁ φ₂ := rfl

/-- An equivalent formulation of semantic entailment in terms of satisfying assignments. -/
theorem entails_ext {φ₁ φ₂} : φ₁ ≤ φ₂ ↔ (∀ (τ : PropAssignment ν), τ ⊨ φ₁ → τ ⊨ φ₂) := by
  have : ∀ τ, (φ₁.eval τ → φ₂.eval τ) ↔ φ₁.eval τ ≤ φ₂.eval τ := by
    intro τ
    cases (eval τ φ₁)
    . simp
    . simp only [true_implies]
      exact ⟨fun h => h ▸ le_rfl, top_unique⟩
  simp [le_def, sEntails, entails, satisfies, this]

@[refl] theorem entails_refl : φ ≤ φ :=
  fun _ => le_rfl
@[trans] theorem entails.trans : φ₁ ≤ φ₂ → φ₂ ≤ φ₃ → φ₁ ≤ φ₃ :=
  fun h₁ h₂ τ => le_trans (h₁ τ) (h₂ τ)

@[simp] theorem entails_tr : φ ≤ ⊤ :=
  fun _ => le_top
@[simp] theorem fls_entails : ⊥ ≤ φ :=
  fun _ => bot_le

theorem entails_disj_left : φ₁ ≤ (disj φ₁ φ₂) :=
  fun _ => le_sup_left
theorem entails_disj_right : φ₂ ≤ (disj φ₁ φ₂) :=
  fun _ => le_sup_right
theorem disj_entails {φ₁ φ₂ φ₃ : PropForm ν} : φ₁ ≤ φ₃ → φ₂ ≤ φ₃ → (disj φ₁ φ₂) ≤ φ₃ :=
  fun h₁ h₂ τ => sup_le (h₁ τ) (h₂ τ)

theorem conj_entails_left : (conj φ₁ φ₂) ≤ φ₁ :=
  fun _ => inf_le_left
theorem conj_entails_right : (conj φ₁ φ₂) ≤ φ₂ :=
  fun _ => inf_le_right
theorem entails_conj {φ₁ φ₂ φ₃ : PropForm ν} : φ₁ ≤ φ₂ → φ₁ ≤ φ₃ → φ₁ ≤ (conj φ₂ φ₃) :=
  fun h₁ h₂ τ => le_inf (h₁ τ) (h₂ τ)

theorem entails_disj_conj : (conj (disj φ₁ φ₂) (disj φ₁ φ₃)) ≤ (disj φ₁ (conj φ₂ φ₃)) :=
  fun _ => le_sup_inf

theorem conj_neg_entails_fls : (conj φ (neg φ)) ≤ ⊥ :=
  fun τ => BooleanAlgebra.inf_compl_le_bot (eval τ φ)

theorem tr_entails_disj_neg : ⊤ ≤ (disj φ (neg φ)) :=
  fun τ => BooleanAlgebra.top_le_sup_compl (eval τ φ)

end entails /- section -/

/-- Two formulas are semantically equivalent when they always evaluate to the same thing.

This is a strong notion of equivalence.
See `equivalentOver` for a weaker one. -/
def equivalent (φ₁ φ₂ : PropForm ν) : Prop :=
  ∀ (τ : PropAssignment ν), φ₁.eval τ = φ₂.eval τ

-- `equivalent` can be written as `≃`.
instance instEquiv : HasEquiv (PropForm ν) where
  Equiv := equivalent

theorem equivalent_iff_entails : φ₁ ≈ φ₂ ↔ (φ₁ ≤ φ₂ ∧ φ₂ ≤ φ₁) := by
  simp only [equivalent]
  constructor
  · intro h
    constructor
    <;> (intro τ; rw [h τ])
  · rintro ⟨h₁, h₂⟩ τ
    exact le_antisymm (h₁ τ) (h₂ τ)

theorem equivalent_ext : φ₁ ≈ φ₂ ↔ (∀ (τ : PropAssignment ν), τ ⊨ φ₁ ↔ τ ⊨ φ₂) := by
  simp only [equivalent_iff_entails]
  constructor
  · rintro ⟨h₁, h₂⟩ τ
    exact ⟨h₁ τ, h₂ τ⟩
  · exact fun h => ⟨fun τ => (h τ).mp, fun τ => (h τ).mpr⟩

@[refl] theorem equivalent_refl (φ : PropForm ν) : φ ≈ φ :=
  fun _ => rfl
@[symm] theorem equivalent.symm : φ₁ ≈ φ₂ → φ₂ ≈ φ₁ :=
  fun h τ => (h τ).symm
@[trans] theorem equivalent.trans : φ₁ ≈ φ₂ → φ₂ ≈ φ₃ → φ₁ ≈ φ₃ :=
  fun h₁ h₂ τ => (h₁ τ).trans (h₂ τ)
theorem equivalent.antisymm : φ₁ ≤ φ₂ → φ₂ ≤ φ₁ → φ₁ ≈ φ₂ :=
  fun h₁ h₂ => equivalent_iff_entails.mpr ⟨h₁, h₂⟩

section vmapAndVars

variable {ν₁ : Type u} {ν₂ : Type v} (f : ν₁ → ν₂) (φ φ₁ φ₂ : PropForm ν₁)

@[simp] theorem vmap_tr : (⊤ : PropForm ν₁).vmap f = ⊤ := by simp
@[simp] theorem vmap_fls : (⊥ : PropForm ν₁).vmap f = ⊥ := rfl
@[simp] theorem vmap_var (x : ν₁) : (var x).vmap f = var (f x) := rfl
@[simp] theorem vmap_compl : (φᶜ).vmap f = (φ.vmap f)ᶜ := rfl

theorem satisfies_vmap {φ : PropForm ν₁} {f} {τ : PropAssignment ν₂}
    : τ ⊨ φ.vmap f ↔ (τ.map f) ⊨ φ := by
  induction φ <;> simp [vmap, *]

variable [DecidableEq ν] [DecidableEq ν₁] [DecidableEq ν₂]

@[simp] theorem vars_tr : (⊤ : PropForm ν).vars = ∅ := rfl
@[simp] theorem vars_fls : (⊥ : PropForm ν).vars = ∅ := rfl
@[simp] theorem vars_var (x : ν) : (var x).vars = {x} := rfl
@[simp] theorem vars_compl : (φᶜ).vars = φ.vars := rfl

@[simp]
theorem vars_map : vars (φ.vmap f) = φ.vars.image f := by
  induction φ <;> simp [Finset.image_union, *]

end vmapAndVars /- section -/

/-! ### Define notation for `PropForm`s -/

namespace Notation

declare_syntax_cat propform

syntax "[propform| " propform " ]" : term

syntax:max "{ " term:min " }" : propform
syntax:max "(" propform:min ")" : propform

syntax:40 " ¬" propform:41 : propform
syntax:35 propform:36 " ∧ " propform:35 : propform
syntax:30 propform:31 " ∨ " propform:30 : propform
syntax:25 propform:26 " → " propform:25 : propform
syntax:20 propform:21 " ↔ " propform:20 : propform

macro_rules
| `([propform| {$t:term} ]) => `(($t : PropForm _))
| `([propform| ($f:propform) ]) => `([propform| $f ])
| `([propform| ¬ $f:propform ]) => `(PropForm.neg [propform| $f ])
| `([propform| $f1 ∧ $f2 ]) => `(PropForm.conj [propform| $f1 ] [propform| $f2 ])
| `([propform| $f1 ∨ $f2 ]) => `(PropForm.disj [propform| $f1 ] [propform| $f2 ])
| `([propform| $f1 → $f2 ]) => `(PropForm.impl [propform| $f1 ] [propform| $f2 ])
| `([propform| $f1 ↔ $f2 ]) => `(PropForm.biImpl [propform| $f1 ] [propform| $f2 ])

example (a b c d : ν) : PropForm ν :=
  [propform| {a} ∧ {b} ∨ {c} → {d}  ↔  (¬{a} ∨ ¬{b}) ∧ ¬{c} ∨ {d} ]

end Notation
