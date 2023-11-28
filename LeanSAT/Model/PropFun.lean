/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import LeanSAT.Model.PropForm

namespace LeanSAT.Model

/-! # Propositional Formulas mod Equivalence

This file defines the type of propositional formulas over
a set `ν` of variables, quotiented by strong equivalence.

We show that they form a Boolean algebra
with ordering given by semantic entailment.
This allows us to use Mathlib's lattice notation & lemmas.

-/

open PropForm in
instance PropFun.setoid (ν : Type u) : Setoid (PropForm ν) where
  r := equivalent
  iseqv := {
    refl  := equivalent_refl
    symm  := equivalent.symm
    trans := equivalent.trans
  }

/-- A propositional function is a propositional formula up to semantic equivalence. -/
def PropFun ν := Quotient (PropFun.setoid ν)

namespace PropFun

/-- Applied backwards,
this reduces an equivalence between two syntactic formulas
to an equality between the functions they denote. -/
theorem exact {φ₁ φ₂ : PropForm ν} : @Eq (PropFun ν) ⟦φ₁⟧ ⟦φ₂⟧ → PropForm.equivalent φ₁ φ₂ :=
  Quotient.exact

theorem sound {φ₁ φ₂ : PropForm ν} : PropForm.equivalent φ₁ φ₂ → @Eq (PropFun ν) ⟦φ₁⟧ ⟦φ₂⟧ :=
  @Quotient.sound _ (PropFun.setoid ν) _ _

def var (x : ν) : PropFun ν := ⟦.var x⟧

def tr : PropFun ν := ⟦.tr⟧

def fls : PropFun ν := ⟦.fls⟧

def neg : PropFun ν → PropFun ν :=
  Quotient.map (.neg ·) (by
    intro _ _ h τ
    simp [h τ])

def conj : PropFun ν → PropFun ν → PropFun ν :=
  Quotient.map₂ (.conj · ·) (by
    intro _ _ h₁ _ _ h₂ τ
    simp [h₁ τ, h₂ τ])

def disj : PropFun ν → PropFun ν → PropFun ν :=
  Quotient.map₂ (.disj · ·) (by
    intro _ _ h₁ _ _ h₂ τ
    simp [h₁ τ, h₂ τ])

def impl : PropFun ν → PropFun ν → PropFun ν :=
  Quotient.map₂ (.impl · ·) (by
    intro _ _ h₁ _ _ h₂ τ
    simp [h₁ τ, h₂ τ])

def biImpl : PropFun ν → PropFun ν → PropFun ν :=
  Quotient.map₂ (.biImpl · ·) (by
    intro _ _ h₁ _ _ h₂ τ
    simp [h₁ τ, h₂ τ])

/-! Evaluation -/

/-- The unique extension of `τ` from variables to propositional functions. -/
def eval (τ : PropAssignment ν) : PropFun ν → Bool :=
  Quotient.lift (PropForm.eval τ) (fun _ _ h => h τ)

@[simp]
theorem eval_mk (τ : PropAssignment ν) (φ : PropForm ν) :
    eval τ ⟦φ⟧ = φ.eval τ :=
  rfl

@[simp]
theorem eval_var (τ : PropAssignment ν) (x : ν) : eval τ (var x) = τ x := by
  simp [eval, var]

@[simp]
theorem eval_tr (τ : PropAssignment ν) : eval τ tr = true := by
  simp [eval, tr]

@[simp]
theorem eval_fls (τ : PropAssignment ν) : eval τ fls = false := by
  simp [eval, fls]

@[simp]
theorem eval_neg (τ : PropAssignment ν) (φ : PropFun ν) : eval τ (neg φ) = !(eval τ φ) := by
  have ⟨φ, h⟩ := Quotient.exists_rep φ
  simp [← h, eval, neg]

@[simp]
theorem eval_conj (τ : PropAssignment ν) (φ₁ φ₂ : PropFun ν) :
    eval τ (conj φ₁ φ₂) = (eval τ φ₁ && eval τ φ₂) := by
  have ⟨φ₁, h₁⟩ := Quotient.exists_rep φ₁
  have ⟨φ₂, h₂⟩ := Quotient.exists_rep φ₂
  simp [← h₁, ← h₂, conj, eval]

@[simp]
theorem eval_disj (τ : PropAssignment ν) (φ₁ φ₂ : PropFun ν) :
    eval τ (disj φ₁ φ₂) = (eval τ φ₁ || eval τ φ₂) := by
  have ⟨φ₁, h₁⟩ := Quotient.exists_rep φ₁
  have ⟨φ₂, h₂⟩ := Quotient.exists_rep φ₂
  simp [← h₁, ← h₂, eval, disj]

@[simp]
theorem eval_impl (τ : PropAssignment ν) (φ₁ φ₂ : PropFun ν) :
    eval τ (impl φ₁ φ₂) = (eval τ φ₁) ⇨ (eval τ φ₂) := by
  have ⟨φ₁, h₁⟩ := Quotient.exists_rep φ₁
  have ⟨φ₂, h₂⟩ := Quotient.exists_rep φ₂
  simp [← h₁, ← h₂, eval, impl]

@[simp]
theorem eval_biImpl (τ : PropAssignment ν) (φ₁ φ₂ : PropFun ν) :
    eval τ (biImpl φ₁ φ₂) = (eval τ φ₁ = eval τ φ₂) := by
  have ⟨φ₁, h₁⟩ := Quotient.exists_rep φ₁
  have ⟨φ₂, h₂⟩ := Quotient.exists_rep φ₂
  simp [← h₁, ← h₂, eval, biImpl]

/-! Satisfying assignments -/

def satisfies (τ : PropAssignment ν) (φ : PropFun ν) : Prop :=
  φ.eval τ = true

/-- This instance is scoped so that when `PropFun` is open,
`τ ⊨ φ` implies `φ : PropFun _` via the `outParam`. -/
scoped instance : SemanticEntails (PropAssignment ν) (PropFun ν) where
  entails := PropFun.satisfies

open SemanticEntails renaming entails → sEntails

@[ext]
theorem ext : (∀ (τ : PropAssignment ν), τ ⊨ φ₁ ↔ τ ⊨ φ₂) → φ₁ = φ₂ := by
  have ⟨φ₁, h₁⟩ := Quotient.exists_rep φ₁
  have ⟨φ₂, h₂⟩ := Quotient.exists_rep φ₂
  simp only [← h₁, ← h₂]
  intro h
  apply Quotient.sound ∘ PropForm.equivalent_ext.mpr
  apply h

/-! Semantic entailment -/

def entails (φ₁ φ₂ : PropFun ν) : Prop :=
  ∀ (τ : PropAssignment ν), φ₁.eval τ ≤ φ₂.eval τ

@[simp]
theorem entails_mk {φ₁ φ₂ : PropForm ν} : entails ⟦φ₁⟧ ⟦φ₂⟧ ↔ PropForm.entails φ₁ φ₂ :=
  ⟨id, id⟩

theorem entails_ext {φ₁ φ₂ : PropFun ν} :
    entails φ₁ φ₂ ↔ (∀ (τ : PropAssignment ν), τ ⊨ φ₁ → τ ⊨ φ₂) := by
  have ⟨φ₁, h₁⟩ := Quotient.exists_rep φ₁
  have ⟨φ₂, h₂⟩ := Quotient.exists_rep φ₂
  simp only [← h₁, ← h₂, entails_mk]
  exact PropForm.entails_ext

theorem entails_refl (φ : PropFun ν) : entails φ φ :=
  fun _ => le_rfl
theorem entails.trans : entails φ₁ φ₂ → entails φ₂ φ₃ → entails φ₁ φ₃ :=
  fun h₁ h₂ τ => le_trans (h₁ τ) (h₂ τ)
theorem entails.antisymm : entails φ ψ → entails ψ φ → φ = ψ := by
  intro h₁ h₂
  ext τ
  exact ⟨entails_ext.mp h₁ τ, entails_ext.mp h₂ τ⟩

theorem entails_tr (φ : PropFun ν) : entails φ tr :=
  fun _ => le_top
theorem fls_entails (φ : PropFun ν) : entails fls φ :=
  fun _ => bot_le

theorem entails_disj_left (φ₁ φ₂ : PropFun ν) : entails φ₁ (disj φ₁ φ₂) :=
  fun _ => by simp only [eval_disj]; exact le_sup_left
theorem entails_disj_right (φ₁ φ₂ : PropFun ν) : entails φ₂ (disj φ₁ φ₂) :=
  fun _ => by simp only [eval_disj]; exact le_sup_right
theorem disj_entails : entails φ₁ φ₃ → entails φ₂ φ₃ → entails (disj φ₁ φ₂) φ₃ :=
  fun h₁ h₂ τ => by simp only [eval_disj]; exact sup_le (h₁ τ) (h₂ τ)

theorem conj_entails_left (φ₁ φ₂ : PropFun ν) : entails (conj φ₁ φ₂) φ₁ :=
  fun _ => by simp only [eval_conj]; exact inf_le_left
theorem conj_entails_right (φ₁ φ₂ : PropFun ν) : entails (conj φ₁ φ₂) φ₂ :=
  fun _ => by simp only [eval_conj]; exact inf_le_right
theorem entails_conj : entails φ₁ φ₂ → entails φ₁ φ₃ → entails φ₁ (conj φ₂ φ₃) :=
  fun h₁ h₂ τ => by simp only [eval_conj]; exact le_inf (h₁ τ) (h₂ τ)

theorem entails_disj_conj (φ₁ φ₂ φ₃ : PropFun ν) :
    entails (conj (disj φ₁ φ₂) (disj φ₁ φ₃)) (disj φ₁ (conj φ₂ φ₃)) :=
  fun _ => by simp only [eval_conj, eval_disj]; exact le_sup_inf

theorem conj_neg_entails_fls (φ : PropFun ν) : entails (conj φ (neg φ)) fls :=
  fun τ => by simp only [eval_conj, eval_neg]; exact BooleanAlgebra.inf_compl_le_bot (eval τ φ)

theorem tr_entails_disj_neg (φ : PropFun ν) : entails tr (disj φ (neg φ)) :=
  fun τ => by simp only [eval_disj, eval_neg]; exact BooleanAlgebra.top_le_sup_compl (eval τ φ)

theorem impl_eq (φ ψ : PropFun ν) : impl φ ψ = disj ψ (neg φ) := by
  ext τ
  simp only [sEntails, satisfies, eval_impl, eval_disj, eval_neg]
  rfl

/-! From this point onwards we use lattice notation for `PropFun`s
in order to get the mathlib laws for free. -/

instance : BooleanAlgebra (PropFun ν) where
  le := entails
  top := tr
  bot := fls
  compl := neg
  sup := disj
  inf := conj
  himp := impl
  le_refl := entails_refl
  le_trans := @entails.trans _
  le_antisymm := @entails.antisymm _
  le_top := entails_tr
  bot_le := fls_entails
  le_sup_left := entails_disj_left
  le_sup_right := entails_disj_right
  sup_le _ _ _ := disj_entails
  inf_le_left := conj_entails_left
  inf_le_right := conj_entails_right
  le_inf _ _ _ := entails_conj
  le_sup_inf := entails_disj_conj
  inf_compl_le_bot := conj_neg_entails_fls
  top_le_sup_compl := tr_entails_disj_neg
  himp_eq := impl_eq

@[simp]
theorem satisfies_mk {τ : PropAssignment ν} {φ : PropForm ν} : τ ⊨ ⟦φ⟧ ↔ PropForm.satisfies τ φ :=
  ⟨id, id⟩

@[simp]
theorem satisfies_var {τ : PropAssignment ν} {x : ν} : τ ⊨ var x ↔ τ x := by
  simp [sEntails, satisfies]

@[simp]
theorem satisfies_set {τ : PropAssignment ν} [DecidableEq ν] : τ.set x ⊤ ⊨ var x := by
  simp

@[simp]
theorem satisfies_tr {τ : PropAssignment ν} : τ ⊨ ⊤ :=
  by simp [sEntails, satisfies, Top.top]

@[simp]
theorem not_satisfies_fls {τ : PropAssignment ν} : τ ⊭ ⊥ :=
  fun h => nomatch h

@[simp]
theorem satisfies_neg {τ : PropAssignment ν} : τ ⊨ (φᶜ) ↔ τ ⊭ φ := by
  simp [sEntails, satisfies, HasCompl.compl]

@[simp]
theorem satisfies_conj {τ : PropAssignment ν} : τ ⊨ φ₁ ⊓ φ₂ ↔ τ ⊨ φ₁ ∧ τ ⊨ φ₂ := by
  simp [sEntails, satisfies, Inf.inf]

@[simp]
theorem satisfies_disj {τ : PropAssignment ν} : τ ⊨ φ₁ ⊔ φ₂ ↔ τ ⊨ φ₁ ∨ τ ⊨ φ₂ := by
  simp [sEntails, satisfies, Sup.sup]

@[simp]
theorem satisfies_impl {τ : PropAssignment ν} : τ ⊨ φ₁ ⇨ φ₂ ↔ (τ ⊨ φ₁ → τ ⊨ φ₂) := by
  simp only [sEntails, satisfies, eval_impl, HImp.himp]
  cases (eval τ φ₁) <;> simp [himp_eq]

theorem satisfies_impl' {τ : PropAssignment ν} : τ ⊨ φ₁ ⇨ φ₂ ↔ τ ⊭ φ₁ ∨ τ ⊨ φ₂ := by
  simp only [sEntails, satisfies, eval_impl, HImp.himp]
  cases (eval τ φ₁) <;> simp [himp_eq]

@[simp]
theorem satisfies_biImpl {τ : PropAssignment ν} : τ ⊨ biImpl φ₁ φ₂ ↔ (τ ⊨ φ₁ ↔ τ ⊨ φ₂) := by
  simp [sEntails, satisfies]

instance : Nontrivial (PropFun ν) where
  exists_pair_ne := by
    use ⊤, ⊥
    intro h
    have : ∀ (τ : PropAssignment ν), τ ⊨ ⊥ ↔ τ ⊨ ⊤ := fun _ => h ▸ Iff.rfl
    simp only [not_satisfies_fls, satisfies_tr, iff_true] at this 
    apply this (fun _ => true)

theorem eq_top_iff {φ : PropFun ν} : φ = ⊤ ↔ ∀ (τ : PropAssignment ν), τ ⊨ φ :=
  ⟨fun h => by simp [h], fun h => by ext; simp [h]⟩

theorem eq_bot_iff {φ : PropFun ν} : φ = ⊥ ↔ ∀ (τ : PropAssignment ν), τ ⊭ φ :=
  ⟨fun h => by simp [h], fun h => by ext; simp [h]⟩

theorem biImpl_eq_impls (φ ψ : PropFun ν) : biImpl φ ψ = (φ ⇨ ψ) ⊓ (ψ ⇨ φ) := by
  ext τ
  aesop

/-! Lemmas to push `Quotient.mk` inwards. -/

-- TODO: custom simp set?

@[simp]
theorem mk_var (x : ν) : ⟦.var x⟧ = var x := rfl

@[simp]
theorem mk_tr : @Eq (PropFun ν) ⟦.tr⟧ ⊤ := rfl

@[simp]
theorem mk_fls : @Eq (PropFun ν) ⟦.fls⟧ ⊥ := rfl

@[simp]
theorem mk_neg (φ : PropForm ν) : @Eq (PropFun ν) ⟦.neg φ⟧ (⟦φ⟧)ᶜ := rfl

@[simp]
theorem mk_conj (φ₁ φ₂ : PropForm ν) : @Eq (PropFun ν) ⟦.conj φ₁ φ₂⟧ (⟦φ₁⟧ ⊓ ⟦φ₂⟧) := rfl

@[simp]
theorem mk_disj (φ₁ φ₂ : PropForm ν) : @Eq (PropFun ν) ⟦.disj φ₁ φ₂⟧ (⟦φ₁⟧ ⊔ ⟦φ₂⟧) := rfl

@[simp]
theorem mk_impl (φ₁ φ₂ : PropForm ν) : @Eq (PropFun ν) ⟦.impl φ₁ φ₂⟧ (⟦φ₁⟧ ⇨ ⟦φ₂⟧) := rfl
