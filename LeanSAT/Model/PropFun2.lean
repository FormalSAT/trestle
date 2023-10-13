import Mathlib.Data.Set.Finite
import Mathlib.Order.BooleanAlgebra

import LeanSAT.Model.PropForm

variable [DecidableEq ν]

def semVars' (φ : PropAssignment ν → Bool) : Set ν :=
  { x | ∃ (τ : PropAssignment ν), φ τ = true ∧ φ (τ.set x (!τ x)) = false }

def PropFun (ν : Type u) [DecidableEq ν] :=
  { φ : PropAssignment ν → Bool // Set.Finite (semVars' φ) }

namespace PropFun

/-! ### Basic definitions and Boolean algebra construction -/

@[simp]
theorem semVars'_top : semVars' (⊤ : PropAssignment ν → Bool) = ∅ := by
  simp [semVars']

@[simp]
theorem semVars'_bot : semVars' (⊥ : PropAssignment ν → Bool) = ∅ := by
  simp [semVars']

@[simp]
theorem semVars'_neg (φ : PropAssignment ν → Bool) : semVars' (φᶜ) = semVars' φ := by
  ext
  aesop (add norm unfold semVars')

theorem semVars'_inf (φ₁ φ₂ : PropAssignment ν → Bool) : semVars' (φ₁ ⊓ φ₂) ⊆ semVars' φ₁ ∪ semVars' φ₂ := by
  intro
  aesop (add norm unfold semVars')

theorem semVars'_sup (φ₁ φ₂ : PropAssignment ν → Bool) : semVars' (φ₁ ⊔ φ₂) ⊆ semVars' φ₁ ∪ semVars' φ₂ := by
  intro
  aesop (add norm unfold semVars')

instance : Top (PropFun ν) where
  top := ⟨⊤, by simp⟩

instance : Bot (PropFun ν) where
  bot := ⟨⊥, by simp⟩

instance : HasCompl (PropFun ν) where
  compl φ := ⟨φ.1ᶜ, by simp [φ.2]⟩

instance : Inf (PropFun ν) where
  inf φ₁ φ₂ := ⟨φ₁.1 ⊓ φ₂.1, .subset (.union φ₁.2 φ₂.2) (semVars'_inf _ _)⟩

instance : Sup (PropFun ν) where
  sup φ₁ φ₂ := ⟨φ₁.1 ⊔ φ₂.1, .subset (.union φ₁.2 φ₂.2) (semVars'_sup _ _)⟩

instance : SDiff (PropFun ν) where
  sdiff φ₁ φ₂ := ⟨φ₁.1 ⊓ φ₂.1ᶜ, .subset (.union φ₁.2 (by simp [φ₂.2])) (semVars'_inf _ _)⟩

instance : BooleanAlgebra (PropFun ν) :=
  Function.Injective.booleanAlgebra _ Subtype.coe_injective
    (by intros; rfl) (by intros; rfl) rfl rfl (by intros; rfl) (by intros; rfl)

/-! ### Variable constructor -/

@[simp]
theorem semVars'_var (x : ν) : semVars' (ν := ν) (· x) = {x} := by
  ext y
  simp only [semVars', ne_eq, Set.mem_setOf_eq, Set.mem_singleton_iff]
  refine ⟨?mp, ?mpr⟩
  case mp =>
    intro ⟨τ, hτ⟩
    by_contra h
    have := τ.set_get_of_ne (!τ y) h
    rw [this] at hτ
    cases hτ.1.symm.trans hτ.2
  case mpr =>
    intro h; cases h
    use (fun _ => true)
    simp

def var (x : ν) : PropFun ν :=
  ⟨(· x), by simp⟩

/-! ### Satisfying assignments -/

def satisfies (τ : PropAssignment ν) (φ : PropFun ν) : Prop :=
  φ.1 τ = true

/-- This instance is scoped so that when `PropFun` is open,
`τ ⊨ φ` implies `φ : PropFun _` via the `outParam`. -/
scoped instance : SemanticEntails (PropAssignment ν) (PropFun ν) where
  entails := PropFun.satisfies

open SemanticEntails renaming entails → sEntails

@[ext]
theorem ext : (∀ (τ : PropAssignment ν), τ ⊨ φ₁ ↔ τ ⊨ φ₂) → φ₁ = φ₂ := by
  intro h
  apply Subtype.ext
  ext
  apply Bool.eq_iff_eq_true_iff.mpr (h _)

/-! ### Semantic variables -/

/-- The *semantic variables* of `φ` are those it is sensitive to as a Boolean function.
Unlike `PropForm.vars`, this set is stable under equivalence of formulas. -/
noncomputable def semVars (φ : PropFun ν) : Finset ν :=
  Set.Finite.toFinset φ.2

theorem mem_semVars (x : ν) (φ : PropFun ν) :
    x ∈ φ.semVars ↔ ∃ (τ : PropAssignment ν), τ ⊨ φ ∧ τ.set x (!τ x) ⊭ φ := by
  simp [semVars, semVars', sEntails, satisfies]

/-- Any two assignments with opposing evaluations on `φ`
disagree on a semantic variable of `φ`. -/
theorem exists_semVar {φ : PropFun ν} {σ₁ σ₂ : PropAssignment ν} : σ₁ ⊨ φ → σ₂ ⊭ φ →
    ∃ x ∈ φ.semVars, σ₁ x ≠ σ₂ x := by
  sorry -- How to prove this?

end PropFun

-- TODO: put this in a separate module connecting to PropForm
namespace PropFun

def PropFun.ofForm (φ : PropForm ν) : PropFun ν :=
  ⟨φ.eval, sorry⟩

local notation "⟦" t "⟧" => PropFun.ofForm t

theorem exact {φ₁ φ₂ : PropForm ν} : @Eq (PropFun ν) ⟦φ₁⟧ ⟦φ₂⟧ → PropForm.equivalent φ₁ φ₂ :=
  sorry

theorem sound {φ₁ φ₂ : PropForm ν} : PropForm.equivalent φ₁ φ₂ → @Eq (PropFun ν) ⟦φ₁⟧ ⟦φ₂⟧ :=
  sorry

end PropFun