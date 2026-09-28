/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Trestle.Model.PropVars
import Trestle.Model.OfFun
import Mathlib.Data.Finset.Preimage

namespace Trestle.Model


/-! ## Substitution

This file defines operations on [PropForm] and [PropFun] for
substituting the variables in a formula with other variables,
or in general with other formulas.

The main definitions are:
- [PropForm.subst], [PropFun.subst]
- [PropForm.substOne], [PropFun.substOne]
- [PropForm.map], [PropFun.map]
- [PropForm.pmap], [PropFun.pmap]
-/

/-! ### `subst` -/

open PropFun in
def PropAssignment.subst (f : ν → PropFun ν') (τ : PropAssignment ν') : PropAssignment ν :=
  fun v => τ ⊨ f v

/-! # PropForm -/

namespace PropForm

open PropFun

@[reducible]
def subst (p : PropForm ν₁) (f : ν₁ → PropForm ν₂) : PropForm ν₂ :=
  match p with
  | .var l => f l
  | .tr => .tr
  | .fls => .fls
  | .neg φ => .neg (φ.subst f)
  | .conj φ₁ φ₂ => .conj (φ₁.subst f) (φ₂.subst f)
  | .disj φ₁ φ₂ => .disj (φ₁.subst f) (φ₂.subst f)
  | .impl φ₁ φ₂ => .impl (φ₁.subst f) (φ₂.subst f)
  | .biImpl φ₁ φ₂ => .biImpl (φ₁.subst f) (φ₂.subst f)

section subst

variable (f f₁ : ν₁ → PropForm ν₂) (f₂ : ν₂ → PropForm ν₃) (φ φ₁ φ₂ : PropForm ν₁)

theorem subst_assoc : (subst (subst φ f₁) f₂) = subst φ (fun v => subst (f₁ v) f₂) := by
  induction φ <;> simp [subst, *]

@[simp]
theorem vars_subst [DecidableEq ν₁] [DecidableEq ν₂]
    : vars (φ.subst f) = (vars φ).biUnion (fun v1 => vars (f v1)) := by
  induction φ <;> grind

@[simp]
theorem satisfies_subst {φ : PropForm ν₁} {f} {τ : PropAssignment ν₂}
    : τ ⊨ φ.subst f ↔ τ.subst (⟦f ·⟧) ⊨ φ := by
  induction φ <;> simp [subst, PropAssignment.subst, *]

theorem subst_congr {φ₁ φ₂ : PropForm ν₁} (hφ : ⟦φ₁⟧ = ⟦φ₂⟧)
    : ∀ (σ : ν₁ → PropForm ν₂), (⟦φ₁.subst σ⟧ : PropFun _) = ⟦φ₂.subst σ⟧ := by
  intro σ
  apply PropFun.ext
  intro τ
  have := PropFun.exact hφ
  simp_rw [PropFun.satisfies_mk, satisfies_subst, ← PropFun.satisfies_mk, satisfies_mk]
  exact rel_congr (this (PropAssignment.subst (fun x => ⟦σ x⟧) τ)) rfl

end subst /- section -/

/-! ### `substOne` -/

/-- Substitutes a `PropForm` ψ for a single variable in another `PropForm` φ. -/
def substOne [DecidableEq ν] (φ : PropForm ν) (v : ν) (ψ : PropForm ν) : PropForm ν :=
  φ.subst (fun v' => if v' = v then ψ else .var v')

section substOne

variable {ν : Type u} [DecidableEq ν] (φ φ₁ φ₂ : PropForm ν) (v : ν) (ψ ψ₁ ψ₂ : PropForm ν)

theorem satisfies_substOne {φ : PropForm ν} {v} {τ : PropAssignment ν} {ψ : PropForm ν}
    : τ ⊨ φ.substOne v ψ ↔ τ.set v (τ ⊨ ψ) ⊨ φ := by
  simp [substOne]
  apply iff_of_eq; congr
  ext v
  simp [PropAssignment.subst, PropAssignment.set]
  split <;> simp

theorem substOne_congr {φ₁ φ₂ ψ₁ ψ₂} (v : ν) (hφ : ⟦φ₁⟧ = ⟦φ₂⟧) (hψ : ⟦ψ₁⟧ = ⟦ψ₂⟧)
    : ⟦φ₁.substOne v ψ₁⟧ = ⟦φ₂.substOne v ψ₂⟧ := by
  apply PropFun.ext
  intro τ
  simp [substOne]
  rw [← PropFun.satisfies_mk, ← PropFun.satisfies_mk, hφ]
  apply iff_of_eq; congr; ext v
  grind

theorem vars_substOne : (PropForm.substOne φ v ψ).vars ⊆ (φ.vars \ {v}) ∪ ψ.vars := by
  induction φ with
  | var =>
      intro v hv; simp [subst, substOne] at hv ⊢
      split at hv
      · simp [hv]
      · simp at hv; subst_vars; simp [*]
  | tr  => simp [substOne]
  | fls => simp [substOne]
  | neg φ₁ ih =>
    simp [substOne]
    intro x hx
    split
    · exact Finset.subset_union_right
    · rename_i hv
      simp [hx, hv]
  | disj φ₁ φ₂ ih₁ ih₂
  | conj φ₁ φ₂ ih₁ ih₂
  | impl φ₁ φ₂ ih₁ ih₂
  | biImpl φ₁ φ₂ ih₁ ih₂ =>
    intro v hv; simp [substOne] at *
    rcases hv with (⟨w, hφ, hw⟩ | ⟨w, hφ, hw⟩)
    all_goals (
      split at hw
      <;> rename_i h
      · subst h
        simp only [hw, or_true]
      · simp only [vars, Finset.mem_singleton] at hw; subst hw
        simp only [hφ, or_true, true_or, h, not_false_eq_true, and_self]
    )

end substOne /- section -/

end PropForm

/-! # PropFun -/

namespace PropFun

/--
  Maps a function `f : ν₁ → PropForm ν₂` across the variables/literals of `φ`,
  replacing the variables with the output of `f`.

  Named `substL` because it "lifts" the range from `PropForm` to `PropFun`.
-/
def substL (φ : PropFun ν₁) (f : ν₁ → PropForm ν₂) : PropFun ν₂ :=
  φ |> PropFun.lift (⟦PropForm.subst · f⟧)
    (fun _ _ h => PropForm.subst_congr (PropFun.eq.mpr h) f)

section substL

variable {ν₁ : Type u} {ν₂ : Type v} (f : ν₁ → PropForm ν₂) (φ φ₁ φ₂ : PropFun ν₁) (v : ν₁)

@[simp] theorem substL_var : substL (.var v) f = ⟦f v⟧ := rfl
@[simp] theorem substL_bot : substL ⊥ f = ⊥ := rfl
@[simp] theorem substL_top : substL ⊤ f = ⊤ := rfl

@[simp]
theorem substL_disj : substL (φ₁ ⊔ φ₂) f = substL φ₁ f ⊔ substL φ₂ f := by
  obtain ⟨φ₁, rfl⟩ := φ₁.exists_rep
  obtain ⟨φ₂, rfl⟩ := φ₂.exists_rep
  rfl

@[simp]
theorem substL_conj : substL (φ₁ ⊓ φ₂) f = substL φ₁ f ⊓ substL φ₂ f := by
  obtain ⟨φ₁, rfl⟩ := φ₁.exists_rep
  obtain ⟨φ₂, rfl⟩ := φ₂.exists_rep
  rfl

@[simp]
theorem substL_compl : substL φᶜ f = (substL φ f)ᶜ := by
  obtain ⟨φ, rfl⟩ := φ.exists_rep
  rfl

/-- Substitution commutes with satisfaction/entailment. -/
@[simp]
theorem satisfies_substL {φ : PropFun ν₁} {f} {τ : PropAssignment ν₂} :
    τ ⊨ φ.substL f ↔ τ.subst (⟦f ·⟧) ⊨ φ := by
  obtain ⟨φ, rfl⟩ := φ.exists_rep
  simp [substL]

theorem substL_le_of_le {φ₁ φ₂ : PropFun ν₁}
    : φ₁ ≤ φ₂ → ∀ (f : ν₁ → PropForm ν₂), substL φ₁ f ≤ substL φ₂ f := by
  intro h f
  refine entails_ext.mpr fun τ' hτ' => ?_
  simp at hτ' ⊢
  exact entails_ext.mp h _ hτ'

theorem substL_congr {φ : PropFun ν₁} {f g : ν₁ → PropForm ν₂} (h : ∀ v, ⟦f v⟧ = ⟦g v⟧)
    : φ.substL f = φ.substL g := by
  ext τ; simp [h]

end substL /- section -/

/-- Substitution by `PropFun`s, rather than by `PropForm`s. See `PropFun.substL`. -/
noncomputable def subst (φ : PropFun ν₁) (f : ν₁ → PropFun ν₂) : PropFun ν₂ :=
  φ.substL (fun v => (f v).out)

section subst

variable {ν₁ : Type u} {ν₂ : Type v} (φ φ₁ φ₂ : PropFun ν₁) (f f₁ : ν₁ → PropFun ν₂)
  (τ : PropAssignment ν₂) (v : ν₁)

theorem substL_eq_subst {f : ν₁ → PropForm ν₂} : φ.substL f = φ.subst (⟦f ·⟧) := by
  ext τ; simp [subst]

/-- Substitution commutes with satisfaction/entailment. -/
@[simp]
theorem satisfies_subst {φ : PropFun ν₁} {f} {τ : PropAssignment ν₂}
    : τ ⊨ φ.subst f ↔ τ.subst f ⊨ φ := by
  simp [subst]

theorem subst_le_of_le {φ₁ φ₂ : PropFun ν₁}
    : φ₁ ≤ φ₂ → ∀ (f : ν₁ → PropFun ν₂), subst φ₁ f ≤ subst φ₂ f := by
  intro h f
  refine entails_ext.mpr fun τ' hτ' => ?_
  simp at hτ' ⊢
  exact entails_ext.mp h _ hτ'

@[simp] theorem subst_var : subst (.var v) f = f v := by simp [subst]
@[simp] theorem subst_bot : subst ⊥ f = ⊥ := rfl
@[simp] theorem subst_top : subst ⊤ f = ⊤ := rfl

@[simp] theorem subst_disj : subst (φ₁ ⊔ φ₂) f = subst φ₁ f ⊔ subst φ₂ f := by simp [subst]
@[simp] theorem subst_conj : subst (φ₁ ⊓ φ₂) f = subst φ₁ f ⊓ subst φ₂ f := by simp [subst]
@[simp] theorem subst_compl : subst φᶜ f = (subst φ f)ᶜ := by simp [subst]

theorem semVars_substL [DecidableEq ν₁] [DecidableEq ν₂]
    {φ : PropFun ν₁} {f : ν₁ → PropForm ν₂}
  : semVars (φ.substL f) ⊆ (semVars φ).biUnion (fun v => semVars ⟦f v⟧) := by
  intro v2 hv2
  rw [Finset.mem_biUnion]
  -- an assignment for which `v2` is meaningful
  rw [mem_semVars] at hv2; obtain ⟨τ, hsat, hunsat⟩ := hv2
  simp only [satisfies_substL] at hsat hunsat
  -- the two assignments disagree on some variable, which is then a semantic variable
  obtain ⟨x, h1, h2⟩ := exists_semVar hsat hunsat
  refine ⟨x, h2, ?_⟩
  rw [mem_semVars]
  simp [PropAssignment.subst] at h1
  -- `τ` and `τ.set v2 !τ v2` disagree on `f x`, so `v2` is a semantic variable of it
  by_cases h : τ ⊨ (⟦f x⟧ : PropFun ν₂)
  · exact ⟨τ, h, fun hc => h1 ⟨fun _ => hc, fun _ => h⟩⟩
  · refine ⟨τ.set v2 !τ v2, ?_, ?_⟩
    · by_contra hc
      exact h1 ⟨fun hh => absurd hh h, fun hh => absurd hh hc⟩
    · simp only [PropAssignment.get_set_self, Bool.not_not, PropAssignment.set_set,
        PropAssignment.set_get]
      exact h

theorem semVars_subst [DecidableEq ν₁] [DecidableEq ν₂] {φ} {f : ν₁ → PropFun ν₂}
    : semVars (φ.subst f) ⊆ (semVars φ).biUnion (fun v1 => semVars (f v1)) := by
  simpa [subst] using semVars_substL (φ := φ) (f := fun v => (f v).out)

end subst /- section -/

/--
  Substitutes the `PropFun` `φ` for the variable `v` in `ψ`.

  Only `φ` needs to be lifted: once it is a `PropForm`, the substitution
  itself is just `substL`.
-/
def substOne [DecidableEq ν] (φ : PropFun ν) (v : ν) (ψ : PropFun ν) : PropFun ν :=
  ψ.lift (fun ψ => φ.substL (fun v' => if v' = v then ψ else .var v'))
    (fun _ _ h => substL_congr fun v' => by by_cases hv : v' = v <;> simp [hv, sound h])

section substOne

@[simp]
theorem satisfies_substOne [DecidableEq ν] {φ ψ : PropFun ν} {v : ν} {τ : PropAssignment ν}
    : τ ⊨ φ.substOne v ψ ↔ τ.set v (τ ⊨ ψ) ⊨ φ := by
  obtain ⟨ψ, rfl⟩ := ψ.exists_rep
  simp only [substOne, lift_mk, satisfies_substL]
  apply iff_of_eq; congr; funext v'
  by_cases hv : v' = v
  <;> simp [hv, PropAssignment.subst, PropAssignment.get_set]

end substOne /- section -/

end PropFun
