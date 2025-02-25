/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: Wojciech Nawrocki
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.ByContra

import Trestle.Upstream.ToStd
import Trestle.Model.PropFun

namespace Trestle.Model

/-! Definitions and theorems relating propositional formulas and functions to variables

## Main definitions

`PropForm.vars` - the set of syntactic variables of a formula
`PropFun.semVars` - the set of semantic variables of a function
`PropFun.equivalentOver X` - two functions are equivalent over a set `X` of variables
`PropFun.hasUniqueExtension X Y` - the assignments to a function extend uniquely from a set `X` to
a set `Y` of variables

NOTE: Semantic notions are not generally defined on `PropForm`s.
They are expected to be used on `PropForm`s by composing with `⟦-⟧`.

NOTE: We try to delay talking about dependently-typed functions `{x // x ∈ X} → Bool`
for as long as possible by developing the theory in terms of total assignments `ν → Bool`. -/

namespace PropForm

open PropAssignment

variable [DecidableEq ν]

/-! ### Syntactic Variables -/

/-- Variables appearing in the formula. Sometimes called its "support set". -/
@[reducible, simp]
def vars : PropForm ν → Finset ν
  | var y => {y}
  | tr | fls => ∅
  | neg φ => vars φ
  | conj φ₁ φ₂ | disj φ₁ φ₂ | impl φ₁ φ₂ | biImpl φ₁ φ₂ => vars φ₁ ∪ vars φ₂

theorem eval_of_agreeOn_vars {φ : PropForm ν} {σ₁ σ₂ : PropAssignment ν}
    : σ₁.agreeOn φ.vars σ₂ → φ.eval σ₁ = φ.eval σ₂ := by
  intro h
  induction φ <;> simp_all [agreeOn, eval, vars]

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
  simp only [SemanticEntails.entails, satisfies, eval_of_agreeOn_vars h]

set_option push_neg.use_distrib true in
lemma mem_vars_of_flip {φ : PropForm ν} {τ : PropAssignment ν} (x : ν)
    : τ ⊨ φ → τ.set x (!τ x) ⊭ φ → x ∈ φ.vars := by
  intro hτ hτ'
  induction φ generalizing τ with
  | tr => exfalso; exact hτ' satisfies_tr
  | fls => exfalso; exact not_satisfies_fls hτ
  | var y =>
    simp_all only [vars, satisfies_var, Finset.mem_singleton]
    by_contra h
    exact hτ' (hτ ▸ τ.set_get_of_ne (!τ x) h)
  | neg φ ih =>
    simp only [satisfies_neg, Decidable.not_not] at hτ hτ'
    refine ih hτ' ?_
    simp [hτ]
  | conj φ₁ φ₂ ih₁ ih₂ =>
    simp only [satisfies_conj, not_and] at hτ hτ'
    rw [Finset.mem_union]
    rcases hτ with ⟨hτ₁, hτ₂⟩
    by_cases h : (τ.set x !τ x) ⊨ φ₁
    · exact Or.inr <| ih₂ hτ₂ (hτ' h)
    · exact Or.inl <| ih₁ hτ₁ h
  | disj φ₁ φ₂ ih₁ ih₂ =>
    simp only [satisfies_disj, not_or] at hτ hτ'
    rw [Finset.mem_union]
    rcases hτ' with ⟨hτ₁, hτ₂⟩
    rcases hτ with (h | h)
    · exact Or.inl <| ih₁ h hτ₁
    · exact Or.inr <| ih₂ h hτ₂
  | impl φ₁ φ₂ ih₁ ih₂ =>
    simp only [satisfies_impl, Classical.not_imp] at hτ hτ'
    rw [Finset.mem_union]
    rcases hτ' with ⟨hτ₁, hτ₂⟩
    by_cases h : τ ⊨ φ₁
    · exact Or.inr <| ih₂ (hτ h) hτ₂
    · refine Or.inl <| ih₁ hτ₁ ?_
      simp [h]
  | biImpl φ₁ φ₂ ih₁ ih₂ =>
    simp only [satisfies_biImpl] at hτ hτ'
    rw [Finset.mem_union]
    push_neg at hτ'
    rcases hτ' with (⟨hτ₁, hτ₂⟩ | ⟨hτ₁, hτ₂⟩)
    · by_cases h : τ ⊨ φ₂
      · exact Or.inr <| ih₂ h hτ₂
      · refine Or.inl <| ih₁ hτ₁ ?_
        simp
        intro h_con
        exact absurd (hτ.mp h_con) h
    · by_cases h : τ ⊨ φ₁
      · exact Or.inl <| ih₁ h hτ₁
      · refine Or.inr <| ih₂ hτ₂ ?_
        simp
        intro h_con
        exact absurd (hτ.mpr h_con) h

theorem exists_flip {φ : PropForm ν} {σ₁ σ₂ : PropAssignment ν} (h₁ : σ₁ ⊨ φ) (h₂ : σ₂ ⊭ φ) :
    ∃ (x : ν) (τ : PropAssignment ν), σ₁ x ≠ σ₂ x ∧ τ ⊨ φ ∧ τ.set x (!τ x) ⊭ φ :=
  let s := φ.vars.filter fun x => σ₁ x ≠ σ₂ x
  have hS : ∀ x ∈ s, σ₁ x ≠ σ₂ x := fun _ h => Finset.mem_filter.mp h |>.right
  have hSC : ∀ x ∈ φ.vars \ s, σ₁ x = σ₂ x := by simp_all [s]
  have ⟨x, τ, hx, hτ, hτ'⟩ := go h₁ h₂ s hS hSC
  ⟨x, τ, hS _ hx, hτ, hτ'⟩
where
  go {σ₁ σ₂ : PropAssignment ν} (h₁ : σ₁ ⊨ φ) (h₂ : σ₂ ⊭ φ)
      (s : Finset ν) (hS : ∀ x ∈ s, σ₁ x ≠ σ₂ x) (hSC : ∀ x ∈ φ.vars \ s, σ₁ x = σ₂ x) :
      ∃ (x : ν) (τ : PropAssignment ν), x ∈ s ∧ τ ⊨ φ ∧ τ.set x (!τ x) ⊭ φ := by
    induction s using Finset.induction generalizing σ₁
    . -- In the base case, σ₁ and σ₂ agree on all φ.vars, contradiction.
      have : σ₁.agreeOn φ.vars σ₂ := by rw [Finset.sdiff_empty] at hSC; exact hSC
      have : σ₂ ⊨ φ := (agreeOn_vars this).mp h₁
      exact False.elim (h₂ this)
    next x₀ s' hx₀ ih =>
      -- In the inductive case, let σ₁' := σ₁[x₀ ↦ !(σ₁ x₀)] and see if σ₁' satisfies φ or not.
      let σ₁' := σ₁.set x₀ (!σ₁ x₀)
      by_cases h₁' : σ₁' ⊨ φ
      case neg =>
        -- If σ₁' no longer satisfies φ, we're done.
        use x₀, σ₁
        simp +zetaDelta [h₁, h₁']
      case pos =>
        -- If σ₁' still satisfies φ, proceed by induction.
        have hS' : ∀ x ∈ s', σ₁' x ≠ σ₂ x := fun x hMem => by
          have hX : x₀ ≠ x := fun h => hx₀ (h ▸ hMem)
          simp only [σ₁', σ₁.set_get_of_ne (!σ₁ x₀) hX]
          exact hS _ (Finset.mem_insert_of_mem hMem)
        have hSC' : ∀ x ∈ φ.vars \ s', σ₁' x = σ₂ x := fun x hMem => by
          by_cases hX : x₀ = x
          case pos =>
            have := hS _ (Finset.mem_insert_self _ _)
            simp only [σ₁', ← hX, set_get, Bool.bnot_eq,
                        this, not_false_eq_true]
          case neg =>
            simp only [σ₁', σ₁.set_get_of_ne _ hX]
            refine hSC ?_ ?_
            simp only [Finset.mem_sdiff, Finset.mem_insert, not_or] at hMem ⊢
            rcases hMem with ⟨h_vars, h_nmem⟩
            exact ⟨h_vars, Ne.symm hX, h_nmem⟩
        have ⟨x, τ, hx, H⟩ := ih h₁' hS' hSC'
        exact ⟨x, τ, Finset.mem_insert_of_mem hx, H⟩

end PropForm

namespace PropFun

open PropAssignment

section semVars

variable [DecidableEq ν]

/-! ### Semantic Variables -/

/-- See `semVars`. -/
private def semVars' (φ : PropFun ν) : Set ν :=
  { x | ∃ (τ : PropAssignment ν), τ ⊨ φ ∧ τ.set x (!τ x) ⊭ φ }

private theorem semVars'_subset_vars (φ : PropForm ν) : semVars' ⟦φ⟧ ⊆ φ.vars :=
  fun x ⟨_, hτ, hτ'⟩ => PropForm.mem_vars_of_flip x hτ hτ'

private instance semVars'_finite (φ : PropFun ν) : Set.Finite φ.semVars' :=
  have ⟨φ', h⟩ := Quotient.exists_rep φ
  Set.Finite.subset (Finset.finite_toSet _) (h ▸ semVars'_subset_vars φ')

/-- The *semantic variables* of `φ` are those it is sensitive to as a Boolean function.
Unlike `vars`, this set is stable under equivalence of formulas. -/
noncomputable def semVars (φ : PropFun ν) : Finset ν :=
  Set.Finite.toFinset φ.semVars'_finite

theorem semVars_mk (φ : PropForm ν) : semVars ⟦φ⟧ ⊆ φ.vars := by
  have := semVars'_subset_vars φ
  unfold semVars
  simp [this]

theorem mem_semVars (φ : PropFun ν) (x : ν) :
    x ∈ φ.semVars ↔ ∃ (τ : PropAssignment ν), τ ⊨ φ ∧ τ.set x (!τ x) ⊭ φ := by
  simp [Set.Finite.mem_toFinset, semVars, semVars']

theorem not_mem_semVars (φ : PropFun ν) (x : ν) :
    x ∉ φ.semVars ↔ ∀ (τ : PropAssignment ν) (b), τ.set x b ⊨ φ ↔ τ ⊨ φ := by
  simp [mem_semVars, -Bool.forall_bool]
  constructor
  · intro h τ b
    if b = τ x then
      simp_all
    else
      have : b = !τ x := by apply Bool.eq_not_iff.mpr; assumption
      constructor <;> convert h _ ; simp [*]
  · intro h τ hτφ
    have := h τ (!τ x)
    simp [*]

/-- Any two assignments with opposing evaluations on `φ` disagree on a semantic variable of `φ`. -/
theorem exists_semVar {φ : PropFun ν} {σ₁ σ₂ : PropAssignment ν} : σ₁ ⊨ φ → σ₂ ⊭ φ →
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

theorem agreeOn_semVars {φ : PropFun ν} {σ₁ σ₂ : PropAssignment ν} :
    σ₁.agreeOn φ.semVars σ₂ → (σ₁ ⊨ φ ↔ σ₂ ⊨ φ) := by
  suffices ∀ {σ₁ σ₂}, agreeOn φ.semVars σ₁ σ₂ → σ₁ ⊨ φ → σ₂ ⊨ φ from
    fun h => ⟨this h, this h.symm⟩
  intro σ₁ σ₂ h h₁
  by_contra h₂
  have ⟨x, hNe, hMem⟩ := exists_semVar h₁ h₂
  exact hNe (h x hMem)

theorem eval_of_agreeOn_semVars {φ : PropFun ν} {σ₁ σ₂ : PropAssignment ν} :
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
theorem semVars_tr (ν) [DecidableEq ν] : (⊤ : PropFun ν).semVars = ∅ := by
  ext
  simp [mem_semVars]

@[simp]
theorem semVars_fls (ν) [DecidableEq ν] : (⊥ : PropFun ν).semVars = ∅ := by
  ext
  simp [mem_semVars]

@[simp]
theorem semVars_neg (φ : PropFun ν) : φᶜ.semVars = φ.semVars := by
  ext x
  simp only [mem_semVars]
  constructor <;> {
    intro ⟨τ, hτ, hτ'⟩
    simp only [satisfies_neg, not_not] at hτ hτ' ⊢
    let τ' := τ.set x (!τ x)
    have : (!τ' x) = τ x := by
      simp only [τ', τ.set_get x, Bool.not_not]
    refine ⟨τ', hτ', ?_⟩
    rw [τ.set_set, this, τ.set_same]
    exact hτ
  }

/-- Semantic variable set of a conjunction is contained in
the union of each sub-prop's semantic variables.

Note that there aren't any obvious lower bounds on this set.
Variables which are semantic in both sub-props may not be semantic:
 - `φ₁ = a ∨ b` (`b` is semantic)
 - `φ₂ = a ∨ ¬b` (`b` is semantic)
 - `φ₁ ⊓ φ₂ = a` (`b` is NOT semantic)
And variables in just one sub-prop may not be semantic:
 - `φ₁ = a ∨ b` (`b` is semantic)
 - `φ₂ = a` (`b` is NOT semantic)
 - `φ₁ ⊓ φ₂ = a` (`b` is NOT semantic)

TODO: prove equality holds if `Disjoint φ₁.semVars φ₂.semVars`
-/
@[simp]
theorem semVars_conj (φ₁ φ₂ : PropFun ν) : (φ₁ ⊓ φ₂).semVars ⊆ φ₁.semVars ∪ φ₂.semVars := by
  intro x
  simp only [Finset.mem_union, mem_semVars, satisfies_conj, not_and_or]
  aesop

/-- Semantic variable set of a conjunction is contained in
the union of each sub-prop's semantic variables.

Note that there aren't any obvious lower bounds on this set.
See [semVars_conj] for more details.
-/
@[simp]
theorem semVars_disj (φ₁ φ₂ : PropFun ν) : (φ₁ ⊔ φ₂).semVars ⊆ φ₁.semVars ∪ φ₂.semVars := by
  intro x
  simp only [Finset.mem_union, mem_semVars]
  aesop

@[simp]
theorem semVars_impl (φ₁ φ₂ : PropFun ν) : (φ₁ ⇨ φ₂).semVars ⊆ φ₁.semVars ∪ φ₂.semVars := by
  rw [himp_eq]
  have := semVars_disj (φ₁ᶜ) φ₂
  rw [sup_comm, semVars_neg] at this
  exact this

@[simp]
theorem semVars_biImpl (φ₁ φ₂ : PropFun ν)
    : (φ₁ ⇔ φ₂).semVars ⊆ φ₁.semVars ∪ φ₂.semVars := by
  apply subset_trans (semVars_conj _ _)
  apply Finset.union_subset
  . apply semVars_impl
  . rw [Finset.union_comm]
    apply semVars_impl

theorem setMany_satisfies_iff_inter_semVars (τ : PropAssignment ν) (vs τ' φ)
    : τ.setMany vs τ' ⊨ φ ↔ τ.setMany (vs ∩ φ.semVars) τ' ⊨ φ := by
  induction vs using Finset.induction generalizing τ
  · simp
  next x vs hx ih =>
  if h : x ∈ φ.semVars then
    rw [Finset.insert_eq, Finset.union_inter_distrib_right
        , Finset.singleton_inter_of_mem h]
    simp [setMany_union]; apply ih
  else
  simp [Finset.insert_eq, Finset.union_inter_distrib_right
      , Finset.singleton_inter_of_not_mem h
      , setMany_union]
  rw [← ih _, ← τ.set_setMany_comm _ _ _ _ hx]
  rw [not_mem_semVars] at h
  rw [h]

end semVars /- section -/


/-! ### Equivalence Over Sets -/

/-- Two functions φ₁ and φ₂ are equivalent over X when for every assignment τ, models of φ₁
extending τ over X are in bijection with models of φ₂ extending τ over X. -/
-- This is `sequiv` here: https://github.com/ccodel/verified-encodings/blob/master/src/cnf/encoding.lean
def equivalentOver (X : Set ν) (φ₁ φ₂ : PropFun ν) :=
  ∀ τ, (∃ (σ₁ : PropAssignment ν), σ₁.agreeOn X τ ∧ σ₁ ⊨ φ₁) ↔
       (∃ (σ₂ : PropAssignment ν), σ₂.agreeOn X τ ∧ σ₂ ⊨ φ₂)

-- NOTE: This is a better definition than `equivalentOver`. It would be nice to clean the proofs up
-- to use it, but it's not essential.
def extendsOver (X : Set ν) (φ₁ φ₂ : PropFun ν) :=
  ∀ (σ₁ : PropAssignment ν), σ₁ ⊨ φ₁ → ∃ (σ₂ : PropAssignment ν), σ₂.agreeOn X σ₁ ∧ σ₂ ⊨ φ₂

theorem equivalentOver_iff_extendsOver (X : Set ν) (φ₁ φ₂ : PropFun ν) :
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

theorem equivalentOver_refl (φ : PropFun ν) : equivalentOver X φ φ :=
  fun _ => ⟨id, id⟩
@[symm] theorem equivalentOver.symm : equivalentOver X φ₁ φ₂ → equivalentOver X φ₂ φ₁ :=
  fun e τ => (e τ).symm
@[trans] theorem equivalentOver.trans : equivalentOver X φ₁ φ₂ → equivalentOver X φ₂ φ₃ →
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

theorem equivalentOver_semVars [DecidableEq ν] {X : Set ν} : φ₁.semVars ⊆ X → φ₂.semVars ⊆ X →
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

/-! ### Extension Over Sets -/

/-- A function has the unique extension property from `X` to `Y` (both sets of variables) when any
satisfying assignment, if it exists, is uniquely determined on `Y` by its values on `X`. Formally,
any two satisfying assignments which agree on `X` must also agree on `Y`. -/
/- TODO: Model equivalence is expected to follow from this. For example:
equivalentOver φ₁.vars ⟦φ₁⟧ ⟦φ₂⟧ ∧ hasUniqueExtension φ₁.vars φ₂.vars ⟦φ₂⟧ →
{ σ : { x // x ∈ φ₁.vars} → Bool | σ ⊨ φ₁ } ≃ { σ : { x // x ∈ φ₂.vars } → Bool | σ ⊨ φ₂ } -/
def hasUniqueExtension (X Y : Set ν) (φ : PropFun ν) :=
  ∀ ⦃σ₁ σ₂ : PropAssignment ν⦄, σ₁ ⊨ φ → σ₂ ⊨ φ → σ₁.agreeOn X σ₂ → σ₁.agreeOn Y σ₂

theorem hasUniqueExtension_refl (X : Set ν) (φ : PropFun ν) : hasUniqueExtension X X φ :=
  by simp [hasUniqueExtension]

theorem hasUniqueExtension.subset_left : X ⊆ X' → hasUniqueExtension X Y φ →
    hasUniqueExtension X' Y φ :=
  fun hSub h _ _ h₁ h₂ hAgree => h h₁ h₂ (hAgree.subset hSub)

theorem hasUniqueExtension.subset_right : Y' ⊆ Y → hasUniqueExtension X Y φ →
    hasUniqueExtension X Y' φ :=
  fun hSub h _ _ h₁ h₂ hAgree => (h h₁ h₂ hAgree).subset hSub

@[trans]
theorem hasUniqueExtension.trans : hasUniqueExtension X Y φ → hasUniqueExtension Y Z φ →
    hasUniqueExtension X Z φ :=
  fun hXY hYZ _ _ h₁ h₂ hAgree => hAgree |> hXY h₁ h₂ |> hYZ h₁ h₂

theorem hasUniqueExtension.conj_right (ψ : PropFun ν) :
    hasUniqueExtension X Y φ → hasUniqueExtension X Y (φ ⊓ ψ) :=
  fun hXY _ _ h₁ h₂ hAgree => hXY (satisfies_conj.mp h₁).left (satisfies_conj.mp h₂).left hAgree

theorem hasUniqueExtension.conj_left (ψ : PropFun ν) :
    hasUniqueExtension X Y φ → hasUniqueExtension X Y (ψ ⊓ φ) :=
  fun hXY _ _ h₁ h₂ hAgree => hXY (satisfies_conj.mp h₁).right (satisfies_conj.mp h₂).right hAgree

theorem hasUniqueExtension_to_empty (X : Set ν) (φ : PropFun ν) : hasUniqueExtension X ∅ φ :=
  hasUniqueExtension_refl X φ |>.subset_right (Set.empty_subset X)

end PropFun

namespace PropForm

theorem equivalentOver_of_equivalent (X : Set ν) : φ₁ ≈ φ₂ → PropFun.equivalentOver X ⟦φ₁⟧ ⟦φ₂⟧ :=
  fun h => Quotient.sound h ▸ PropFun.equivalentOver_refl ⟦φ₁⟧

variable [DecidableEq ν]

theorem semVars_eq_of_equivalent {φ₁ φ₂ : PropForm ν}
    : φ₁ ≈ φ₂ → PropFun.semVars ⟦φ₁⟧ = PropFun.semVars ⟦φ₂⟧ :=
  fun h => Quotient.sound h ▸ rfl

@[simp]
theorem semVars_subset_vars (φ : PropForm ν) : PropFun.semVars ⟦φ⟧ ⊆ φ.vars := by
  simp only [PropFun.semVars, Set.Finite.toFinset_subset]
  exact PropFun.semVars'_subset_vars φ

theorem equivalentOver_vars {X : Set ν} : φ₁.vars ⊆ X → φ₂.vars ⊆ X →
    PropFun.equivalentOver X ⟦φ₁⟧ ⟦φ₂⟧ → equivalent φ₁ φ₂ :=
  fun h₁ h₂ h => Quotient.exact
    (PropFun.equivalentOver_semVars
      (subset_trans (semVars_subset_vars φ₁) h₁)
      (subset_trans (semVars_subset_vars φ₂) h₂)
      h)

end PropForm
