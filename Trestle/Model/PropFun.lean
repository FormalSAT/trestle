/-
Copyright (c) 2026 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: Wojciech Nawrocki
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Multiset.Lattice

import Trestle.Model.PropForm

namespace Trestle.Model

/-! # Propositional Formulas mod Equivalence

This file defines the type of propositional formulas over a variable type `ν`,
quotiented by strong equivalence.

We show that they form a `BooleanAlgebra` with ordering `≤` given by
semantic entailment. This allows us to use Mathlib's lattice notation & lemmas.

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

variable {ν : Type u} {β : Type v}

-- We re-define many `Quotient` definitions to provide an API for `PropFun`.

/--
  Injects a `PropForm` into a `PropFun`.

  If you `open PropFun`, you can use the `⟦·⟧` notation.
-/
def mk (φ : PropForm ν) : PropFun ν :=
  Quotient.mk _ φ

/-- Overloaded quotient bracket notation `⟦·⟧` for `PropFun`. -/
scoped notation:arg (priority := high) "⟦" φ "⟧" => PropFun.mk φ

instance instCoePropForm : Coe (PropForm ν) (PropFun ν) where
  coe := (⟦·⟧)

@[inherit_doc Quotient.lift]
protected def lift (f : PropForm ν → β) (h : ∀ (φ₁ φ₂ : PropForm ν), φ₁ ≈ φ₂ → f φ₁ = f φ₂) : PropFun ν → β :=
  Quotient.lift f h

@[simp] theorem lift_mk (f : PropForm ν → β) (h) (φ : PropForm ν) : PropFun.lift f h ⟦φ⟧ = f φ := rfl

@[inherit_doc Quotient.out]
noncomputable def out (φ : PropFun ν) : PropForm ν :=
  Quotient.out φ

@[simp] theorem out_eq (φ : PropFun ν) : ⟦φ.out⟧ = φ := Quotient.out_eq φ
@[simp] theorem mk_out (φ : PropForm ν) : (⟦φ⟧ : PropFun ν).out ≈ φ := Quotient.mk_out φ
@[simp] theorem out_equiv_out {φ₁ φ₂ : PropFun ν} : φ₁.out ≈ φ₂.out ↔ φ₁ = φ₂ := Quotient.out_equiv_out

/-- For each `PropFun` `φ`, there exists a `PropForm` `φ'` that represents it. -/
theorem exists_rep (φ : PropFun ν) : ∃ (φ' : PropForm ν), ⟦φ'⟧ = φ :=
  ⟨φ.out, out_eq φ⟩

@[inherit_doc Quotient.exact]
theorem exact {φ₁ φ₂ : PropForm ν} : ⟦φ₁⟧ = ⟦φ₂⟧ → φ₁ ≈ φ₂ :=
  Quotient.exact

@[inherit_doc Quotient.sound]
theorem sound {φ₁ φ₂ : PropForm ν} : φ₁ ≈ φ₂ → ⟦φ₁⟧ = ⟦φ₂⟧ :=
  @Quotient.sound _ (PropFun.setoid ν) _ _

/-- Two `PropForm`s equal under the quotient are also equivalent. -/
theorem eq {x y : PropForm ν} : ⟦x⟧ = ⟦y⟧ ↔ x ≈ y :=
  Quotient.eq

/--
  Given an indexed family of `PropFun`s `f : ι → PropFun ν`, returns a
  quotiented function that sends each `i : ι` to a representative `PropForm`.
-/
noncomputable def choice {ι : Type w} (f : ι → PropFun ν) :
    @Quotient (ι → PropForm ν) inferInstance :=
  Quotient.choice f

@[simp]
theorem choice_eq {ι : Type w} (f : ι → PropForm ν) :
    (PropFun.choice (⟦f ·⟧)) = Quotient.mk _ f :=
  Quotient.choice_eq f

/-- The family chosen by `PropFun.choice f` represents `f` pointwise. -/
@[simp]
theorem choice_out {ι : Type w} (f : ι → PropFun ν) (i : ι) :
    ⟦(choice f).out i⟧ = f i :=
  (sound (Quotient.exact (Quotient.out_eq (choice f)) i)).trans (out_eq (f i))

@[inherit_doc Quotient.map]
protected def map (f : PropForm ν → PropForm ν') (hf : ∀ ⦃a b⦄, a ≈ b → f a ≈ f b) : PropFun ν → PropFun ν' :=
  Quotient.map f hf

@[inherit_doc Quotient.map₂]
protected def map₂ (f : PropForm ν → PropForm ν → PropForm ν') (hf : ∀ ⦃a₁ a₂⦄, a₁ ≈ a₂ → ∀ ⦃b₁ b₂⦄,  b₁ ≈ b₂ → f a₁ b₁ ≈ f a₂ b₂) :
    PropFun ν → PropFun ν → PropFun ν' :=
  Quotient.map₂ f hf

/-! logical operations on `PropFun` -/

def var (x : ν) : PropFun ν := ⟦.var x⟧

instance instCoeVar : Coe ν (PropFun ν) := ⟨.var⟩

def tr : PropFun ν := ⟦.tr⟧

def fls : PropFun ν := ⟦.fls⟧

def neg : PropFun ν → PropFun ν :=
  PropFun.map (.neg ·) (by
    intro _ _ h τ
    simp [h τ])

def conj : PropFun ν → PropFun ν → PropFun ν :=
  PropFun.map₂ (.conj · ·) (by
    intro _ _ h₁ _ _ h₂ τ
    simp [h₁ τ, h₂ τ])

def disj : PropFun ν → PropFun ν → PropFun ν :=
  PropFun.map₂ (.disj · ·) (by
    intro _ _ h₁ _ _ h₂ τ
    simp [h₁ τ, h₂ τ])

def impl : PropFun ν → PropFun ν → PropFun ν :=
  PropFun.map₂ (.impl · ·) (by
    intro _ _ h₁ _ _ h₂ τ
    simp [h₁ τ, h₂ τ])

def biImpl : PropFun ν → PropFun ν → PropFun ν :=
  PropFun.map₂ (.biImpl · ·) (by
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
  simp [var, eval_mk, PropForm.eval]

@[simp]
theorem eval_tr (τ : PropAssignment ν) : eval τ tr = true := by
  simp [tr, eval_mk, PropForm.eval]

@[simp]
theorem eval_fls (τ : PropAssignment ν) : eval τ fls = false := by
  simp [fls, eval_mk, PropForm.eval]

theorem eval_neg (τ : PropAssignment ν) (φ : PropFun ν) : eval τ (neg φ) = !(eval τ φ) := by
  obtain ⟨φ, rfl⟩ := exists_rep φ
  simp only [eval, neg]
  rfl

theorem eval_conj (τ : PropAssignment ν) (φ₁ φ₂ : PropFun ν) :
    eval τ (conj φ₁ φ₂) = (eval τ φ₁ && eval τ φ₂) := by
  obtain ⟨φ₁, rfl⟩ := exists_rep φ₁
  obtain ⟨φ₂, rfl⟩ := exists_rep φ₂
  simp only [conj, eval]
  rfl

theorem eval_disj (τ : PropAssignment ν) (φ₁ φ₂ : PropFun ν) :
    eval τ (disj φ₁ φ₂) = (eval τ φ₁ || eval τ φ₂) := by
  obtain ⟨φ₁, rfl⟩ := exists_rep φ₁
  obtain ⟨φ₂, rfl⟩ := exists_rep φ₂
  simp only [eval]
  rfl

theorem eval_impl (τ : PropAssignment ν) (φ₁ φ₂ : PropFun ν) :
    eval τ (impl φ₁ φ₂) = (eval τ φ₁) ⇨ (eval τ φ₂) := by
  obtain ⟨φ₁, rfl⟩ := exists_rep φ₁
  obtain ⟨φ₂, rfl⟩ := exists_rep φ₂
  simp only [eval, impl]
  rfl

theorem eval_biImpl (τ : PropAssignment ν) (φ₁ φ₂ : PropFun ν) :
    eval τ (biImpl φ₁ φ₂) = (eval τ φ₁ = eval τ φ₂) := by
  obtain ⟨φ₁, rfl⟩ := exists_rep φ₁
  obtain ⟨φ₂, rfl⟩ := exists_rep φ₂
  simp [eval, biImpl]
  exact decide_eq_true_iff

/-! Satisfying assignments -/

def satisfies (τ : PropAssignment ν) (φ : PropFun ν) : Prop :=
  φ.eval τ = true

/-- This instance is scoped so that when `PropFun` is open,
`τ ⊨ φ` implies `φ : PropFun _` via the `outParam`. -/
scoped instance : SemanticEntails (PropAssignment ν) (PropFun ν) where
  entails := PropFun.satisfies

open SemanticEntails renaming entails → sEntails

instance (τ : PropAssignment ν) (φ : PropFun ν) : Decidable (τ ⊨ φ) :=
  match h : φ.eval τ with
    | true => isTrue h
    | false => isFalse fun h' => nomatch h.symm.trans h'

@[ext]
theorem ext : (∀ (τ : PropAssignment ν), τ ⊨ φ₁ ↔ τ ⊨ φ₂) → φ₁ = φ₂ := by
  obtain ⟨φ₁, rfl⟩ := exists_rep φ₁
  obtain ⟨φ₂, rfl⟩ := exists_rep φ₂
  intro h
  apply sound ∘ PropForm.equivalent_ext.mpr
  apply h

/-! Semantic entailment -/

instance {τ : PropAssignment ν} : Decidable (τ ⊨ φ) :=
  inferInstanceAs (Decidable (φ.eval τ = true))

def entails (φ₁ φ₂ : PropFun ν) : Prop :=
  ∀ (τ : PropAssignment ν), φ₁.eval τ ≤ φ₂.eval τ

@[simp]
theorem entails_mk {φ₁ φ₂ : PropForm ν} : entails ⟦φ₁⟧ ⟦φ₂⟧ ↔ PropForm.entails φ₁ φ₂ :=
  ⟨id, id⟩

theorem entails_ext {φ₁ φ₂ : PropFun ν} :
    entails φ₁ φ₂ ↔ (∀ (τ : PropAssignment ν), τ ⊨ φ₁ → τ ⊨ φ₂) := by
  obtain ⟨φ₁, rfl⟩ := exists_rep φ₁
  obtain ⟨φ₂, rfl⟩ := exists_rep φ₂
  simp only [entails_mk]
  exact PropForm.entails_ext

@[refl]
theorem entails_refl (φ : PropFun ν) : entails φ φ :=
  fun _ => le_rfl
@[trans]
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

theorem biImpl_eq (φ ψ : PropFun ν) : biImpl φ ψ = conj (impl φ ψ) (impl ψ φ) := by
  ext τ
  simp only [SemanticEntails.entails, satisfies, eval_biImpl,
    eval_conj, eval_impl, Bool.and_eq_true]
  by_cases hφ : eval τ φ
  <;> by_cases hψ : eval τ ψ
  <;> simp [hφ, hψ]

/-! From this point onwards we use lattice notation for `PropFun`s
in order to get the mathlib laws for free. -/

instance instBooleanAlgebra : BooleanAlgebra (PropFun ν) where
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

/-

Now that we have shown that `PropFun`s are instances of `BooleanAlgebra`,
we should use lattice operations/syntax. These `@[simp]` lemmas ensure
that manual operations get converted into lattice syntax.

We "re-prove" the following theorems because they apply to new syntax,
since apparently Lean's simplifier matches on the head symbol, and e.g.
`Compl.compl` is a different head symbol than `PropFun.neg`.

-/

section mk_quotient

variable (φ φ₁ φ₂ : PropForm ν)

@[simp] theorem mk_var (x : ν) : ⟦.var x⟧ = var x := rfl
@[simp] theorem mk_tr : ⟦.tr⟧ = (⊤ : PropFun ν) := rfl
@[simp] theorem mk_fls : ⟦.fls⟧ = (⊥ : PropFun ν) := rfl
@[simp] theorem mk_compl (φ : PropForm ν) : ⟦φᶜ⟧ = (⟦φ⟧)ᶜ := rfl

@[simp] theorem mk_conj : ⟦.conj φ₁ φ₂⟧ = (⟦φ₁⟧ ⊓ ⟦φ₂⟧) := rfl
@[simp] theorem mk_disj : ⟦.disj φ₁ φ₂⟧ = (⟦φ₁⟧ ⊔ ⟦φ₂⟧) := rfl
@[simp] theorem mk_impl : ⟦.impl φ₁ φ₂⟧ = (⟦φ₁⟧ ⇨ ⟦φ₂⟧) := rfl
@[simp] theorem mk_biImpl : ⟦.biImpl φ₁ φ₂⟧ = (⟦φ₁⟧ ⇔ ⟦φ₂⟧) := biImpl_eq ⟦φ₁⟧ ⟦φ₂⟧

end mk_quotient /- section -/

section eval

variable (τ : PropAssignment ν) (φ φ₁ φ₂ : PropFun ν)

@[simp] theorem neg_eq_compl : neg φ = φᶜ := rfl
@[simp] theorem conj_eq_inf : conj φ₁ φ₂ = φ₁ ⊓ φ₂ := rfl
@[simp] theorem disj_eq_sup : disj φ₁ φ₂ = φ₁ ⊔ φ₂ := rfl
@[simp] theorem impl_eq_himp : impl φ₁ φ₂ = φ₁ ⇨ φ₂ := rfl

@[simp] theorem eval_neg' : eval τ (φᶜ) = !(eval τ φ) := eval_neg τ φ
@[simp] theorem eval_conj' : eval τ (φ₁ ⊓ φ₂) = (eval τ φ₁ && eval τ φ₂) := eval_conj τ φ₁ φ₂
@[simp] theorem eval_disj' : eval τ (φ₁ ⊔ φ₂) = (eval τ φ₁ || eval τ φ₂) := eval_disj τ φ₁ φ₂
@[simp] theorem eval_impl' : eval τ (φ₁ ⇨ φ₂) = (eval τ φ₁) ⇨ (eval τ φ₂) := eval_impl τ φ₁ φ₂

-- We use the new notation for bi-implication `⇔` here. See `ToMathlib.lean`.
@[simp]
theorem eval_biImpl' : eval τ (φ₁ ⇔ φ₂) = (eval τ φ₁ = eval τ φ₂) := by
  by_cases hφ₁ : eval τ φ₁
  <;> by_cases hφ₂ : eval τ φ₂
  <;> simp [hφ₁, hφ₂]

end eval /- section -/

/- Now write some lemmas for semantic entailment. -/

section satisfies

variable {τ : PropAssignment ν} {φ φ₁ φ₂ : PropFun ν}

/-- Semantic entailment commutes with quotienting from `PropForm`.  -/
@[simp]
theorem satisfies_mk {τ : PropAssignment ν} {φ : PropForm ν} :
    τ ⊨ ⟦φ⟧ ↔ (open PropForm in τ ⊨ φ) :=
  ⟨id, id⟩

@[simp]
theorem satisfies_var {τ : PropAssignment ν} {x : ν} : τ ⊨ var x ↔ τ x := by
  simp only [SemanticEntails.entails, satisfies, eval_var]

@[simp]
theorem satisfies_set [DecidableEq ν] (τ : PropAssignment ν) (x : ν) : τ.set x ⊤ ⊨ var x := by
  simp only [top_eq_true, satisfies_var, PropAssignment.get_set_self]

@[simp]
theorem satisfies_tr (τ : PropAssignment ν) : τ ⊨ ⊤ := by
  simp only [SemanticEntails.entails, satisfies, Top.top, eval_tr]

@[simp]
theorem not_satisfies_fls (τ : PropAssignment ν) : τ ⊭ ⊥ :=
  fun h => nomatch h

@[simp]
theorem satisfies_neg : τ ⊨ (φᶜ) ↔ τ ⊭ φ := by
  simp only [SemanticEntails.entails, satisfies, compl, eval_neg,
    Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_true]

@[simp]
theorem satisfies_conj : τ ⊨ φ₁ ⊓ φ₂ ↔ τ ⊨ φ₁ ∧ τ ⊨ φ₂ := by
  simp only [SemanticEntails.entails, satisfies, eval_conj', Bool.and_eq_true]

@[simp]
theorem satisfies_disj : τ ⊨ φ₁ ⊔ φ₂ ↔ τ ⊨ φ₁ ∨ τ ⊨ φ₂ := by
  simp only [SemanticEntails.entails, satisfies, eval_disj', Bool.or_eq_true]

@[simp]
theorem satisfies_impl : τ ⊨ φ₁ ⇨ φ₂ ↔ (τ ⊨ φ₁ → τ ⊨ φ₂) := by
  simp only [sEntails, satisfies, eval_impl, HImp.himp]
  cases (eval τ φ₁) <;> simp

theorem satisfies_impl' : τ ⊨ φ₁ ⇨ φ₂ ↔ τ ⊭ φ₁ ∨ τ ⊨ φ₂ := by
  simp only [sEntails, satisfies, eval_impl, HImp.himp]
  cases (eval τ φ₁) <;> simp

@[simp]
theorem satisfies_biImpl : τ ⊨ (φ₁ ⇔ φ₂) ↔ (τ ⊨ φ₁ ↔ τ ⊨ φ₂) := by
  simp only [satisfies_conj, satisfies_impl]
  exact Iff.symm iff_iff_implies_and_implies

end satisfies /- section -/

instance instNontrivial : Nontrivial (PropFun ν) where
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

-- CC: I feel like there's a simpler proof here
@[simp]
theorem var_ne_bot (v : ν) : var v ≠ ⊥ := by
  intro h_con
  simp only [eq_bot_iff, satisfies_var, Bool.not_eq_true] at h_con
  have := h_con (fun _ => true)
  contradiction

@[simp]
theorem var_ne_top (v : ν) : var v ≠ ⊤ := by
  intro h_con
  simp only [eq_top_iff, satisfies_var] at h_con
  have := h_con (fun _ => false)
  contradiction

@[simp]
theorem bot_ne_var (v : ν) : ⊥ ≠ var v :=
  Ne.symm (var_ne_bot v)

@[simp]
theorem top_ne_var (v : ν) : ⊤ ≠ var v :=
  Ne.symm (var_ne_top v)

@[simp]
theorem biImpl_top_left (φ : PropFun ν) : ⊤ ⇔ φ = φ := by
  simp only [top_himp, himp_top, le_top, inf_of_le_left]

@[simp]
theorem biImpl_top_right (φ : PropFun ν) : φ ⇔ ⊤ = φ := by
  simp only [himp_top, top_himp, le_top, inf_of_le_right]

@[simp]
theorem biImpl_bot_left (φ : PropFun ν) : (⊥ ⇔ φ) = φᶜ := by
  simp only [bot_himp, himp_bot, le_top, inf_of_le_right]

@[simp]
theorem biImpl_bot_right (φ : PropFun ν) : (φ ⇔ ⊥) = φᶜ := by
  simp only [himp_bot, bot_himp, le_top, inf_of_le_left]

-- CC: Some additional simplifications, for reasoning about ≤
theorem inf_le_iff_compl_sup {φ₁ φ₂ φ₃ : PropFun ν} : φ₁ ⊓ φ₂ ≤ φ₃ ↔ φ₁ ≤ φ₂ᶜ ⊔ φ₃ :=
  BooleanAlgebra.inf_le_iff_le_compl_sup

theorem inf_compl_le_iff_le_sup {φ₁ φ₂ φ₃ : PropFun ν} : φ₁ ⊓ φ₂ᶜ ≤ φ₃ ↔ φ₁ ≤ φ₂ ⊔ φ₃ :=
  BooleanAlgebra.inf_compl_le_iff_le_sup

theorem le_iff_inf_compl_le_bot {φ₁ φ₂ : PropFun ν} : φ₁ ≤ φ₂ ↔ φ₁ ⊓ φ₂ᶜ ≤ ⊥ :=
  BooleanAlgebra.le_iff_inf_compl_le_bot

theorem le_iff_inf_compl_eq_bot {φ₁ φ₂ : PropFun ν} : φ₁ ≤ φ₂ ↔ φ₁ ⊓ φ₂ᶜ = ⊥ :=
  BooleanAlgebra.le_iff_inf_compl_eq_bot

theorem ne_top_left_of_disj_ne_top {φ₁ φ₂ : PropFun ν} : φ₁ ⊔ φ₂ ≠ ⊤ → φ₁ ≠ ⊤ := by
  rintro h rfl
  simp only [le_top, sup_of_le_left, ne_eq, not_true_eq_false] at h

theorem ne_top_right_of_disj_ne_top {φ₁ φ₂ : PropFun ν} : φ₁ ⊔ φ₂ ≠ ⊤ → φ₂ ≠ ⊤ := by
  rintro h rfl
  simp only [le_top, sup_of_le_right, ne_eq, not_true_eq_false] at h

theorem ne_top_of_disj_ne_top {φ₁ φ₂ : PropFun ν} : φ₁ ⊔ φ₂ ≠ ⊤ → φ₁ ≠ ⊤ ∧ φ₂ ≠ ⊤ :=
  fun h => ⟨ne_top_left_of_disj_ne_top h, ne_top_right_of_disj_ne_top h⟩

theorem var.inj [DecidableEq ν] : (var (ν := ν)).Injective := by
  intro v₁ v₂ h
  rw [PropFun.ext_iff] at h
  have h₁ := (h (fun v => v = v₂)).mpr (satisfies_var.mpr (by simp))
  simpa using satisfies_var.mp h₁

@[simp]
theorem var_eq_var_iff [DecidableEq ν] (v v' : ν) : var v = var v' ↔ v = v' := by
  constructor
  · intro; apply var.inj; assumption
  · rintro rfl; rfl

theorem eq_compl_iff_ne {φ₁ φ₂ : PropFun ν} : φ₁ = (φ₂)ᶜ → φ₁ ≠ φ₂ := by
  rintro rfl h; rw [PropFun.ext_iff] at h; simp at h

theorem compl_eq_iff_ne {φ₁ φ₂ : PropFun ν} : (φ₁)ᶜ = φ₂ → φ₁ ≠ φ₂ := by
  rintro rfl h; rw [PropFun.ext_iff] at h; simp at h

@[simp]
theorem var_ne_var_compl [DecidableEq ν] (v₁ v₂ : ν) : var v₁ ≠ (var v₂)ᶜ := by
  intro h
  rw [PropFun.ext_iff] at h
  set τ : PropAssignment ν := (fun v => v = v₁ || v = v₂) with hτ
  have this := h τ
  simp only [satisfies_var, satisfies_neg] at this
  simp [hτ] at this

@[simp]
theorem var_compl_ne_var [DecidableEq ν] (v₁ v₂ : ν) : (var v₁)ᶜ ≠ (var v₂) := by
  intro h
  rw [PropFun.ext_iff] at h
  set τ : PropAssignment ν := (fun v => v = v₁ || v = v₂) with hτ
  have this := h τ
  simp only [satisfies_var, satisfies_neg] at this
  simp [hτ] at this

theorem compl_eq_iff_eq_compl {φ₁ φ₂ : PropFun ν} : φ₁ᶜ = φ₂ ↔ φ₁ = φ₂ᶜ := by
  constructor
  <;> rintro rfl
  <;> simp only [compl_compl]

theorem eq_compl_iff_compl_eq {φ₁ φ₂ : PropFun ν} : φ₁ = φ₂ᶜ ↔ φ₁ᶜ = φ₂ :=
  Iff.symm (@compl_eq_iff_eq_compl _ φ₁ φ₂)

/-! ### All/any -/

def all (a : Multiset (PropFun ν)) : PropFun ν :=
  Multiset.inf a

def any (a : Multiset (PropFun ν)) : PropFun ν :=
  Multiset.sup a

@[simp]
theorem satisfies_all {a : Multiset (PropFun ν)} {τ : PropAssignment ν}
    : τ ⊨ all a ↔ ∀ i ∈ a, τ ⊨ i := by
  induction a using Multiset.induction with
  | empty => simp [all]
  | cons => simp_all [all]

@[simp]
theorem satisfies_any {a : Multiset (PropFun ν)} {τ : PropAssignment ν}
    : τ ⊨ any a ↔ ∃ i ∈ a, τ ⊨ i := by
  induction a using Multiset.induction with
  | empty => simp [any]
  | cons => simp_all [any]

@[simp]
theorem any_zero : any (0 : Multiset (PropFun ν)) = ⊥ := by
  simp only [any, Multiset.sup_zero]

@[simp]
theorem any_empty : any (∅ : Multiset (PropFun ν)) = ⊥ := by
  simp only [Multiset.empty_eq_zero, any_zero]

@[simp]
theorem all_zero : all (0 : Multiset (PropFun ν)) = ⊤ := by
  simp only [all, Multiset.inf_zero]

@[simp]
theorem all_empty : all (∅ : Multiset (PropFun ν)) = ⊤ := by
  simp only [Multiset.empty_eq_zero, all_zero]

@[simp]
theorem all_ofList_nil : all (Multiset.ofList ([] : List (PropFun ν))) = ⊤ := by
  simp only [all, Multiset.inf_coe, List.foldr_nil]

@[simp]
theorem all_ofList_cons (l : PropFun ν) (ls : List (PropFun ν))
    : all (l :: ls) = l ⊓ all ls := by
  simp only [all, Multiset.inf_coe, List.foldr_cons]

/-! # Variables -/

def vmap (f : ν₁ → ν₂) (φ : PropFun ν₁) : PropFun ν₂ :=
  φ.lift (⟦PropForm.vmap f ·⟧) (fun _ _ h => by
    ext τ
    simp only [satisfies_mk, PropForm.satisfies_vmap]
    exact PropForm.equivalent_ext.mp h _)

section vmap

/-- A variable-wise function `f` commutes across satisfaction/entailment via `vmap`. -/
@[simp]
theorem satisfies_vmap {φ : PropFun ν₁} {f} {τ : PropAssignment ν₂}
    : τ ⊨ φ.vmap f ↔ (τ.map f) ⊨ φ := by
  obtain ⟨φ, rfl⟩ := φ.exists_rep
  simp only [vmap, lift_mk, satisfies_mk, PropForm.satisfies_vmap]

variable (f : ν₁ → ν₂) (φ φ₁ φ₂ : PropFun ν₁)

@[simp] theorem vmap_top (f : ν₁ → ν₂) : vmap f (⊤ : PropFun ν₁) = (⊤ : PropFun ν₂) := rfl
@[simp] theorem vmap_bot (f : ν₁ → ν₂) : vmap f (⊥ : PropFun ν₁) = (⊥ : PropFun ν₂) := rfl
@[simp] theorem vmap_var (f : ν₁ → ν₂) (x : ν₁) : vmap f (var x) = var (f x) := rfl
@[simp] theorem vmap_compl (f : ν₁ → ν₂) (φ : PropFun ν₁) : vmap f (φᶜ) = (vmap f φ)ᶜ := by
  induction φ using Quotient.ind
  rfl
@[simp] theorem vmap_conj : vmap f (φ₁ ⊓ φ₂) = (vmap f φ₁ ⊓ vmap f φ₂) := by ext; simp
@[simp] theorem vmap_disj : vmap f (φ₁ ⊔ φ₂) = (vmap f φ₁ ⊔ vmap f φ₂) := by ext; simp
@[simp] theorem vmap_impl : vmap f (φ₁ ⇨ φ₂) = (vmap f φ₁ ⇨ vmap f φ₂) := by ext; simp
@[simp] theorem vmap_biImpl : vmap f (φ₁ ⇔ φ₂) = (vmap f φ₁ ⇔ vmap f φ₂) := by ext; simp

end vmap /- section -/

/-! # Satisfiable and Equisatisfiable -/

def Sat (φ : PropFun ν) : Prop :=
  ∃ (τ : PropAssignment ν), τ ⊨ φ

def EquiSat (φ₁ φ₂ : PropFun ν) : Prop :=
  Sat φ₁ ↔ Sat φ₂

@[symm]
theorem EquiSat.symm {φ₁ φ₂ : PropFun ν} : EquiSat φ₁ φ₂ ↔ EquiSat φ₂ φ₁ :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

@[trans]
theorem EquiSat.trans {φ₁ φ₂ φ₃ : PropFun ν} : EquiSat φ₁ φ₂ → EquiSat φ₂ φ₃ → EquiSat φ₁ φ₃ :=
  fun h₁ h₂ => ⟨fun h => h₂.1 (h₁.1 h), fun h => h₁.2 (h₂.2 h)⟩

@[simp]
theorem top_sat : Sat (⊤ : PropFun ν) := by
  use (fun _ => ⊤)
  apply satisfies_tr

@[simp]
theorem bot_not_sat : ¬Sat (⊥ : PropFun ν) := by
  intro h
  rcases h with ⟨τ, h⟩
  exact nomatch h

@[simp]
theorem not_sat_iff_eq_bot {F : PropFun ν} : ¬Sat F ↔ F = ⊥ := by
  simp [Sat]
  constructor
  · intro hF
    ext τ
    constructor
    · intro h
      have := hF _ h
      contradiction
    · intro h_con
      contradiction
  · rintro rfl
    simp only [not_satisfies_fls, not_false_eq_true, implies_true]

theorem eq_bot_of_equisat {F C : PropFun ν} : EquiSat F (F ⊓ C) → (F ⊓ C) = ⊥ → F = ⊥ := by
  rintro ⟨h₁, _⟩ hFC
  rw [hFC] at h₁
  have := mt h₁ bot_not_sat
  exact not_sat_iff_eq_bot.mp (mt h₁ bot_not_sat)

theorem equisat_of_entails {F C : PropFun ν} : F ≤ C → EquiSat F (F ⊓ C) := by
  intro h_entails
  simp only [EquiSat, Sat, satisfies_conj]
  exact ⟨fun ⟨τ, hτ⟩ => ⟨τ, hτ, h_entails τ hτ⟩, fun ⟨τ, hτ, _⟩ => ⟨τ, hτ⟩⟩

namespace Notation
open PropForm.Notation

declare_syntax_cat propfun

syntax "[propfun| " propfun " ]" : term

syntax:max "{ " term:45 " }" : propfun
syntax:max "(" propfun ")" : propfun

syntax:40 " ¬" propfun:41 : propfun
syntax:35 propfun:36 " ∧ " propfun:35 : propfun
syntax:30 propfun:31 " ∨ " propfun:30 : propfun
syntax:25 propfun:26 " → " propfun:25 : propfun
syntax:20 propfun:21 " ↔ " propfun:20 : propfun

macro_rules
| `([propfun| {$t:term} ]) => `(show PropFun _ from $t)
| `([propfun| ($f:propfun) ]) => `([propfun| $f ])
| `([propfun| ¬ $f:propfun ]) => `(([propfun| $f ])ᶜ)
| `([propfun| $f1 ∧ $f2 ]) => `([propfun| $f1 ] ⊓ [propfun| $f2 ])
| `([propfun| $f1 ∨ $f2 ]) => `([propfun| $f1 ] ⊔ [propfun| $f2 ])
| `([propfun| $f1 → $f2 ]) => `([propfun| $f1 ] ⇨ [propfun| $f2 ])
| `([propfun| $f1 ↔ $f2 ]) => `(PropFun.biImpl [propfun| $f1 ] [propfun| $f2 ])

example (a b c : ν) : PropFun ν :=
  [propfun| {a} ∧ ¬{b} ∧ {c} ]

end Notation
