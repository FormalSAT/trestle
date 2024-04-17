/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Tactic.ByContra

import ProofChecker.Model.PropTerm

/-! Definitions and theorems relating propositional formulas and functions to variables

## Main definitions

`PropForm.vars` - the set of syntactic variables of a formula
`PropTerm.semVars` - the set of semantic variables of a function
`PropTerm.equivalentOver X` - two functions are equivalent over a set `X` of variables
`PropTerm.hasUniqueExtension X Y` - the assignments to a function extend uniquely from a set `X` to
a set `Y` of variables

NOTE: Semantic notions are not generally defined on `PropForm`s. They are expected to be used on
`PropForm`s by composing with `⟦-⟧`.

NOTE: We try to delay talking about dependently-typed functions `{x // x ∈ X} → Bool` for as long as
possible by developing the theory in terms of total assignments `ν → Bool`. Assignments with finite
domain are eventually considered in `ModelCount.lean`. -/

namespace PropAssignment

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

end PropAssignment

namespace PropForm

variable [DecidableEq ν]

/-- Variables appearing in the formula. Sometimes called its "support set". -/
def vars : PropForm ν → Finset ν
  | var y => {y}
  | tr | fls => ∅
  | neg φ => vars φ
  | conj φ₁ φ₂ | disj φ₁ φ₂ | impl φ₁ φ₂ | biImpl φ₁ φ₂ => vars φ₁ ∪ vars φ₂

theorem eval_of_agreeOn_vars {φ : PropForm ν} {σ₁ σ₂ : PropAssignment ν} : σ₁.agreeOn φ.vars σ₂ →
    φ.eval σ₁ = φ.eval σ₂ := by
  intro h
  induction φ <;> simp_all [PropAssignment.agreeOn, eval, vars]

theorem eval_ext {φ : PropForm ν} {σ₁ σ₂ : PropAssignment ν} : (∀ x ∈ φ.vars, σ₁ x = σ₂ x) →
    φ.eval σ₁ = φ.eval σ₂ :=
  eval_of_agreeOn_vars

theorem eval_set_of_not_mem_vars {x : ν} {φ : PropForm ν} {τ : PropAssignment ν} :
    x ∉ φ.vars → φ.eval (τ.set x b) = φ.eval τ := by
  intro hNMem
  apply eval_of_agreeOn_vars
  intro y hY
  have : y ≠ x := fun h => hNMem (h ▸ hY)
  simp [PropAssignment.set, this]

theorem agreeOn_vars {φ : PropForm ν} {σ₁ σ₂ : PropAssignment ν} :
    σ₁.agreeOn φ.vars σ₂ → (σ₁ ⊨ φ ↔ σ₂ ⊨ φ) := by
  intro h
  simp [SemanticEntails.entails, satisfies, eval_of_agreeOn_vars h]

set_option push_neg.use_distrib true in
lemma mem_vars_of_flip {φ : PropForm ν} {τ : PropAssignment ν} (x : ν) : τ ⊨ φ →
    τ.set x (!τ x) ⊭ φ → x ∈ φ.vars := by
  intro hτ hτ'
  induction φ generalizing τ with
  | tr => exfalso; exact hτ' satisfies_tr
  | fls => exfalso; exact not_satisfies_fls hτ
  | var y =>
    simp_all only [vars, satisfies_var, Finset.mem_singleton]
    by_contra h
    exact hτ' (hτ ▸ τ.set_get_of_ne (!τ x) h)
  | _ =>
    simp_all only
      [satisfies_conj, satisfies_disj, satisfies_impl', satisfies_biImpl', vars, Finset.mem_union]
    push_neg at hτ'
    aesop

theorem exists_flip {φ : PropForm ν} {σ₁ σ₂ : PropAssignment ν} : σ₁ ⊨ φ → σ₂ ⊭ φ →
    ∃ (x : ν) (τ : PropAssignment ν), σ₁ x ≠ σ₂ x ∧ τ ⊨ φ ∧ τ.set x (!τ x) ⊭ φ :=
  fun h₁ h₂ =>
    let s := φ.vars.filter fun x => σ₁ x ≠ σ₂ x
    have hS : ∀ x ∈ s, σ₁ x ≠ σ₂ x := fun _ h => Finset.mem_filter.mp h |>.right
    have hSC : ∀ x ∈ φ.vars \ s, σ₁ x = σ₂ x := fun _ h => by simp_all
    have ⟨x, τ, hMem, hτ, hτ'⟩ := go h₁ h₂ s hS hSC rfl
    ⟨x, τ, hS _ hMem, hτ, hτ'⟩
-- NOTE(Jeremy): a proof using `Finset.induction` would likely be shorter
where go {σ₁ σ₂ : PropAssignment ν} (h₁ : σ₁ ⊨ φ) (h₂ : σ₂ ⊭ φ)
    (s : Finset ν) (hS : ∀ x ∈ s, σ₁ x ≠ σ₂ x) (hSC : ∀ x ∈ φ.vars \ s, σ₁ x = σ₂ x) :
    {n : Nat} → s.card = n →
    ∃ (x : ν) (τ : PropAssignment ν), x ∈ s ∧ τ ⊨ φ ∧ τ.set x (!τ x) ⊭ φ
  | 0,   hCard =>
    -- In the base case, σ₁ and σ₂ agree on all φ.vars, contradiction.
    have : s = ∅ := Finset.card_eq_zero.mp hCard
    have : σ₁.agreeOn φ.vars σ₂ := fun _ h => by simp_all
    have : σ₂ ⊨ φ := (agreeOn_vars this).mp h₁
    False.elim (h₂ this)
  | _+1, hCard => by
    -- In the inductive case, let σ₁' := σ₁[x₀ ↦ !(σ₁ x₀)] and see if σ₁' satisfies φ or not.
    have ⟨x₀, s', h₀, h', hCard'⟩ := Finset.card_eq_succ.mp hCard
    have h₀S : x₀ ∈ s := h' ▸ Finset.mem_insert_self x₀ s'
    let σ₁' := σ₁.set x₀ (!σ₁ x₀)
    by_cases h₁' : σ₁' ⊨ φ
    case neg =>
      -- If σ₁' no longer satisfies φ, we're done.
      use x₀, σ₁
      refine ⟨h' ▸ Finset.mem_insert_self x₀ s', h₁, h₁'⟩
    case pos =>
      -- If σ₁' still satisfies φ, proceed by induction.
      have hS' : ∀ x ∈ s', σ₁' x ≠ σ₂ x := fun x hMem => by
        have hX : x₀ ≠ x := fun h => h₀ (h ▸ hMem)
        simp only [σ₁.set_get_of_ne (!σ₁ x₀) hX]
        exact hS _ (h' ▸ Finset.mem_insert_of_mem hMem)
      have hSC' : ∀ x ∈ φ.vars \ s', σ₁' x = σ₂ x := fun x hMem => by
        by_cases hX : x₀ = x
        case pos =>
          simp only [← hX, σ₁.set_get, Bool.bnot_eq_to_not_eq]
          apply hS _ h₀S
        case neg =>
          simp only [σ₁.set_get_of_ne _ hX]
          apply hSC
          aesop
      have ⟨x, τ, hMem, H⟩ := go h₁' h₂ s' hS' hSC' hCard'
      refine ⟨x, τ, h' ▸ Finset.mem_insert_of_mem hMem, H⟩

end PropForm

namespace PropTerm

variable [DecidableEq ν]

/-- See `semVars`. -/
private def semVars' (φ : PropTerm ν) : Set ν :=
  { x | ∃ (τ : PropAssignment ν), τ ⊨ φ ∧ τ.set x (!τ x) ⊭ φ }

private theorem semVars'_subset_vars (φ : PropForm ν) : semVars' ⟦φ⟧ ⊆ φ.vars :=
  fun x ⟨_, hτ, hτ'⟩ => PropForm.mem_vars_of_flip x hτ hτ'

private instance semVars'_finite (φ : PropTerm ν) : Set.Finite φ.semVars' :=
  have ⟨φ', h⟩ := Quotient.exists_rep φ
  Set.Finite.subset (Finset.finite_toSet _) (h ▸ semVars'_subset_vars φ')

/-- The *semantic variables* of `φ` are those it is sensitive to as a Boolean function.
Unlike `vars`, this set is stable under equivalence of formulas. -/
noncomputable def semVars (φ : PropTerm ν) : Finset ν :=
  Set.Finite.toFinset φ.semVars'_finite

theorem mem_semVars (φ : PropTerm ν) (x : ν) :
    x ∈ φ.semVars ↔ ∃ (τ : PropAssignment ν), τ ⊨ φ ∧ τ.set x (!τ x) ⊭ φ := by
  simp [Set.Finite.mem_toFinset, semVars, semVars']

/-- Any two assignments with opposing evaluations on `φ` disagree on a semantic variable of `φ`. -/
theorem exists_semVar {φ : PropTerm ν} {σ₁ σ₂ : PropAssignment ν} : σ₁ ⊨ φ → σ₂ ⊭ φ →
    ∃ (x : ν), σ₁ x ≠ σ₂ x ∧ x ∈ φ.semVars := by
  have ⟨φ', hMk⟩ := Quotient.exists_rep φ
  dsimp
  rw [← hMk, satisfies_mk, satisfies_mk]
  intro h₁ h₂
  have ⟨x, τ, hNe, hτ, hτ'⟩ := PropForm.exists_flip h₁ h₂
  use x, hNe
  simp only [mem_semVars]
  use τ
  rw [satisfies_mk, satisfies_mk]
  exact ⟨hτ, hτ'⟩

theorem agreeOn_semVars {φ : PropTerm ν} {σ₁ σ₂ : PropAssignment ν} :
    σ₁.agreeOn φ.semVars σ₂ → (σ₁ ⊨ φ ↔ σ₂ ⊨ φ) := by
  suffices ∀ {σ₁ σ₂}, σ₁.agreeOn φ.semVars σ₂ → σ₁ ⊨ φ → σ₂ ⊨ φ from
    fun h => ⟨this h, this h.symm⟩
  intro σ₁ σ₂ h h₁
  by_contra h₂
  have ⟨x, hNe, hMem⟩ := exists_semVar h₁ h₂
  exact hNe (h x hMem)

theorem eval_of_agreeOn_semVars {φ : PropTerm ν} {σ₁ σ₂ : PropAssignment ν} :
    σ₁.agreeOn φ.semVars σ₂ → φ.eval σ₁ = φ.eval σ₂ := by
  intro h
  have := agreeOn_semVars h
  dsimp only [SemanticEntails.entails, satisfies] at this
  aesop

@[simp]
theorem semVars_var (x : ν) : (var x).semVars = {x} := by
  ext y
  simp only [Finset.mem_singleton, mem_semVars, satisfies_var]
  refine ⟨?mp, ?mpr⟩
  case mp =>
    intro ⟨τ, hτ, hτ'⟩
    by_contra h
    have := τ.set_get_of_ne (!τ y) h
    exact hτ' (hτ ▸ this)
  case mpr =>
    intro h; cases h
    use (fun _ => true)
    simp

@[simp]
theorem semVars_tr (ν) [DecidableEq ν] : (⊤ : PropTerm ν).semVars = ∅ := by
  ext
  simp [mem_semVars]

@[simp]
theorem semVars_fls (ν) [DecidableEq ν] : (⊥ : PropTerm ν).semVars = ∅ := by
  ext
  simp [mem_semVars]

@[simp]
theorem semVars_neg (φ : PropTerm ν) : φᶜ.semVars = φ.semVars := by
  ext x
  simp only [mem_semVars]
  constructor <;> {
    intro ⟨τ, hτ, hτ'⟩
    simp only [satisfies_neg, not_not] at hτ hτ' ⊢
    let τ' := τ.set x (!τ x)
    have : (!τ' x) = τ x := by
      simp only [τ.set_get x, Bool.not_not]
    refine ⟨τ', hτ', ?_⟩
    rw [τ.set_set, this, τ.set_same]
    exact hτ
  }

theorem semVars_conj (φ₁ φ₂ : PropTerm ν) : (φ₁ ⊓ φ₂).semVars ⊆ φ₁.semVars ∪ φ₂.semVars := by
  intro x
  simp only [Finset.mem_union, mem_semVars, satisfies_conj, not_and_or]
  aesop

theorem semVars_disj (φ₁ φ₂ : PropTerm ν) : (φ₁ ⊔ φ₂).semVars ⊆ φ₁.semVars ∪ φ₂.semVars := by
  intro x
  simp only [Finset.mem_union, mem_semVars]
  aesop

theorem semVars_impl (φ₁ φ₂ : PropTerm ν) : (φ₁ ⇨ φ₂).semVars ⊆ φ₁.semVars ∪ φ₂.semVars := by
  rw [himp_eq]
  have := semVars_disj (φ₁ᶜ) φ₂
  rw [sup_comm, semVars_neg] at this
  exact this

theorem semVars_biImpl (φ₁ φ₂ : PropTerm ν) :
    (PropTerm.biImpl φ₁ φ₂).semVars ⊆ φ₁.semVars ∪ φ₂.semVars := by
  rw [biImpl_eq_impls]
  apply subset_trans (semVars_conj _ _)
  apply Finset.union_subset
  . apply semVars_impl
  . rw [Finset.union_comm]
    apply semVars_impl

/-- Two functions φ₁ and φ₂ are equivalent over X when for every assignment τ, models of φ₁
extending τ over X are in bijection with models of φ₂ extending τ over X. -/
-- This is `sequiv` here: https://github.com/ccodel/verified-encodings/blob/master/src/cnf/encoding.lean
def equivalentOver (X : Set ν) (φ₁ φ₂ : PropTerm ν) :=
  ∀ τ, (∃ (σ₁ : PropAssignment ν), σ₁.agreeOn X τ ∧ σ₁ ⊨ φ₁) ↔
       (∃ (σ₂ : PropAssignment ν), σ₂.agreeOn X τ ∧ σ₂ ⊨ φ₂)

-- NOTE: This is a better definition than `equivalentOver`. It would be nice to clean the proofs up
-- to use it, but it's not essential.
def extendsOver (X : Set ν) (φ₁ φ₂ : PropTerm ν) :=
  ∀ (σ₁ : PropAssignment ν), σ₁ ⊨ φ₁ → ∃ (σ₂ : PropAssignment ν), σ₂.agreeOn X σ₁ ∧ σ₂ ⊨ φ₂

theorem equivalentOver_iff_extendsOver (X : Set ν) (φ₁ φ₂ : PropTerm ν) :
    equivalentOver X φ₁ φ₂ ↔ (extendsOver X φ₁ φ₂ ∧ extendsOver X φ₂ φ₁) := by
  constructor
  case mp =>
    intro h
    exact ⟨fun σ₁ h₁ => h σ₁ |>.mp ⟨σ₁, σ₁.agreeOn_refl X, h₁⟩,
      fun σ₂ h₂ => h σ₂ |>.mpr ⟨σ₂, σ₂.agreeOn_refl X, h₂⟩⟩
  case mpr =>
    intro ⟨h₁, h₂⟩
    intro τ
    constructor
    case mp =>
      intro ⟨σ₁, hAgree₁, hσ₁⟩
      have ⟨σ₂, hAgree₂, hσ₂⟩ := h₁ σ₁ hσ₁
      exact ⟨σ₂, hAgree₂.trans hAgree₁, hσ₂⟩
    case mpr =>
      intro ⟨σ₂, hAgree₂, hσ₂⟩
      have ⟨σ₁, hAgree₁, hσ₁⟩ := h₂ σ₂ hσ₂
      exact ⟨σ₁, hAgree₁.trans hAgree₂, hσ₁⟩

theorem equivalentOver_refl (φ : PropTerm ν) : equivalentOver X φ φ :=
  fun _ => ⟨id, id⟩
theorem equivalentOver.symm : equivalentOver X φ₁ φ₂ → equivalentOver X φ₂ φ₁ :=
  fun e τ => (e τ).symm
theorem equivalentOver.trans : equivalentOver X φ₁ φ₂ → equivalentOver X φ₂ φ₃ →
    equivalentOver X φ₁ φ₃ :=
  fun e₁ e₂ τ => (e₁ τ).trans (e₂ τ)

theorem equivalentOver.subset {X Y : Set ν} : X ⊆ Y → equivalentOver Y φ₁ φ₂ →
    equivalentOver X φ₁ φ₂ := by
  intro hSub
  suffices ∀ φ₁ φ₂ τ, equivalentOver Y φ₁ φ₂ →
      (∃ (σ₁ : PropAssignment ν), σ₁.agreeOn X τ ∧ σ₁ ⊨ φ₁) →
      ∃ (σ₂ : PropAssignment ν), σ₂.agreeOn X τ ∧ σ₂ ⊨ φ₂ from
    fun e τ => ⟨this φ₁ φ₂ τ e, this φ₂ φ₁ τ e.symm⟩
  intro φ₁ φ₂ τ e ⟨σ₁, hA, hS⟩
  have ⟨σ₃, hA', hS'⟩ := (e σ₁).mp ⟨σ₁, σ₁.agreeOn_refl _, hS⟩
  exact ⟨σ₃, hA'.subset hSub |>.trans hA, hS'⟩

theorem equivalentOver_semVars {X : Set ν} : φ₁.semVars ⊆ X → φ₂.semVars ⊆ X →
    equivalentOver X φ₁ φ₂ → φ₁ = φ₂ := by
  suffices ∀ {φ₁ φ₂} {τ : PropAssignment ν}, φ₂.semVars ⊆ X →
      equivalentOver X φ₁ φ₂ → τ ⊨ φ₁ → τ ⊨ φ₂ by
    intro h₁ h₂ e
    ext τ
    exact ⟨this h₂ e, this h₁ e.symm⟩
  intro φ₁ φ₂ τ h₂ e h
  have ⟨σ₁, hA, hS⟩ := (e τ).mp ⟨τ, τ.agreeOn_refl _, h⟩
  have : σ₁ ⊨ φ₂ ↔ τ ⊨ φ₂ := agreeOn_semVars (hA.subset h₂)
  exact this.mp hS

/-- A function has the unique extension property from `X` to `Y` (both sets of variables) when any
satisfying assignment, if it exists, is uniquely determined on `Y` by its values on `X`. Formally,
any two satisfying assignments which agree on `X` must also agree on `Y`. -/
/- TODO: Model equivalence is expected to follow from this. For example:
equivalentOver φ₁.vars ⟦φ₁⟧ ⟦φ₂⟧ ∧ hasUniqueExtension ⟦φ₂⟧ φ₁.vars φ₂.vars →
{ σ : { x // x ∈ φ₁.vars} → Bool | σ ⊨ φ₁ } ≃ { σ : { x // x ∈ φ₂.vars } → Bool | σ ⊨ φ₂ } -/
def hasUniqueExtension (X Y : Set ν) (φ : PropTerm ν) :=
  ∀ ⦃σ₁ σ₂ : PropAssignment ν⦄, σ₁ ⊨ φ → σ₂ ⊨ φ → σ₁.agreeOn X σ₂ → σ₁.agreeOn Y σ₂

theorem hasUniqueExtension_refl (X : Set ν) (φ : PropTerm ν) : hasUniqueExtension X X φ :=
  by simp [hasUniqueExtension]
  
theorem hasUniqueExtension.subset_left : X ⊆ X' → hasUniqueExtension X Y φ →
    hasUniqueExtension X' Y φ :=
  fun hSub h _ _ h₁ h₂ hAgree => h h₁ h₂ (hAgree.subset hSub)

theorem hasUniqueExtension.subset_right : Y' ⊆ Y → hasUniqueExtension X Y φ →
    hasUniqueExtension X Y' φ :=
  fun hSub h _ _ h₁ h₂ hAgree => (h h₁ h₂ hAgree).subset hSub

theorem hasUniqueExtension.trans : hasUniqueExtension X Y φ → hasUniqueExtension Y Z φ →
    hasUniqueExtension X Z φ :=
  fun hXY hYZ _ _ h₁ h₂ hAgree => hAgree |> hXY h₁ h₂ |> hYZ h₁ h₂
  
theorem hasUniqueExtension.conj_right (ψ : PropTerm ν) :
    hasUniqueExtension X Y φ → hasUniqueExtension X Y (φ ⊓ ψ) :=
  fun hXY _ _ h₁ h₂ hAgree => hXY (satisfies_conj.mp h₁).left (satisfies_conj.mp h₂).left hAgree

theorem hasUniqueExtension.conj_left (ψ : PropTerm ν) :
    hasUniqueExtension X Y φ → hasUniqueExtension X Y (ψ ⊓ φ) :=
  fun hXY _ _ h₁ h₂ hAgree => hXY (satisfies_conj.mp h₁).right (satisfies_conj.mp h₂).right hAgree
  
theorem hasUniqueExtension_to_empty (X : Set ν) (φ : PropTerm ν) : hasUniqueExtension X ∅ φ :=
  hasUniqueExtension_refl X φ |>.subset_right (Set.empty_subset X)

end PropTerm

namespace PropForm

variable [DecidableEq ν]

theorem equivalentOver_of_equivalent : equivalent φ₁ φ₂ → PropTerm.equivalentOver X ⟦φ₁⟧ ⟦φ₂⟧ :=
  fun h => Quotient.sound h ▸ PropTerm.equivalentOver_refl ⟦φ₁⟧

theorem semVars_eq_of_equivalent (φ₁ φ₂ : PropForm ν) : equivalent φ₁ φ₂ →
    PropTerm.semVars ⟦φ₁⟧ = PropTerm.semVars ⟦φ₂⟧ :=
  fun h => Quotient.sound h ▸ rfl

theorem semVars_subset_vars (φ : PropForm ν) : PropTerm.semVars ⟦φ⟧ ⊆ φ.vars := by
  simp only [PropTerm.semVars, Set.Finite.toFinset_subset]
  exact PropTerm.semVars'_subset_vars φ

theorem equivalentOver_vars {X : Set ν} : φ₁.vars ⊆ X → φ₂.vars ⊆ X →
    PropTerm.equivalentOver X ⟦φ₁⟧ ⟦φ₂⟧ → equivalent φ₁ φ₂ :=
  fun h₁ h₂ h => Quotient.exact
    (PropTerm.equivalentOver_semVars
      (subset_trans (semVars_subset_vars φ₁) h₁)
      (subset_trans (semVars_subset_vars φ₂) h₂)
      h)

end PropForm