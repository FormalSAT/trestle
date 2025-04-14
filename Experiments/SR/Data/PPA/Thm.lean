/-
Copyright (c) 2025 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Trestle.Data.Cnf
import Trestle.Data.ICnf

import Trestle.Data.PPA.Defs

/-
  Persistent partial assignments (PPA).

  The data structure underlying the PPA is a resizable array that can be ``cleared''
  in O(1) time by bumping a generation number.
  Each cell in the array stores a generation number that determines if the
  cell is set (i.e. that it is above the data structure's generation number).
  Used to implement partial assignments by assuming that all
  variables are initially unset (PPA).
-/

namespace Trestle.PPA

open Trestle Model Nat
open LitVar ILit IVar LawfulLitVar
open PropFun

/-! ### Lemmas about `litValue?`, `varValue?` -/

@[simp]
theorem litValue?_negate (τ : PPA) (l : ILit) :
    τ.litValue? (-l) = (τ.litValue? l).map Bool.not := by
  aesop (add norm unfold litValue?)

theorem litValue?_eq_varValue?_none {τ : PPA} {l : ILit} :
    τ.litValue? l = none → τ.varValue? (toVar l) = none := by
  aesop (add norm unfold litValue?)

theorem litValue?_eq_varValue?_some {τ : PPA} {l : ILit} {b : Bool} :
    τ.litValue? l = some b → τ.varValue? (toVar l) = xor (!b) (polarity l) := by
  aesop (add norm unfold litValue?)

@[simp]
theorem litValue?_negate_none_iff {τ : PPA} {l : ILit} :
    τ.litValue? (-l) = none ↔ τ.litValue? l = none := by
  simp [litValue?_negate]

theorem lt_size_of_varValue?_some {τ : PPA} {v : IVar} {b : Bool} :
    τ.varValue? v = some b → v.index < τ.size := by
  intro hv
  simp [varValue?] at hv
  rcases Nat.lt_trichotomy v.index τ.size with (hlt | heq | hgt)
  · exact hlt
  · simp [heq] at hv
  · exfalso
    have : τ.assignment.size ≤ v.index := Nat.le_of_lt hgt
    simp [Array.getElem?_eq_none this] at hv

theorem lt_size_of_litValue?_some {τ : PPA} {l : ILit} {b : Bool} :
    τ.litValue? l = some b → l.index < τ.size := by
  simp [litValue?]
  rintro (⟨hv, _⟩ | ⟨hv, _⟩)
  <;> exact lt_size_of_varValue?_some hv

/-! ### `toPropFun` model -/

/-- The PropFun model for τ is the conjunctin of the variables it satisfies.
    Here, we map any variable set to true or false to the appropriate PropFun. -/
def varToPropFun (τ : PPA) (v : IVar) : PropFun IVar :=
  τ.varValue? v |>.map (if · then .var v else (.var v)ᶜ) |>.getD ⊤

/-- We can also calculate the model over just the indexes in range for τ. -/
def idxToPropFun (τ : PPA) (i : Nat) : PropFun IVar :=
  τ.varToPropFun (IVar.ofIndex i)

/-- We model the `PPA` as the conjunction of all its literals.
    Note that we cannot fully model the `PPA` as a `PropAssignment`
    because those are required to be total. -/
def toPropFun (τ : PPA) : PropFun IVar :=
  Fin.foldl τ.size (· ⊓ τ.idxToPropFun ·) ⊤

instance instCoeToPropFun : Coe PPA (PropFun IVar) := ⟨toPropFun⟩

instance instSemanticEntails : SemanticEntails (PropAssignment IVar) (PropFun IVar) where
  entails := PropFun.satisfies

theorem satisfies_iff {τ : PPA} {σ : PropAssignment IVar} :
    σ ⊨ ↑τ ↔ ∀ (i : Fin τ.size), σ ⊨ τ.idxToPropFun i := by
  constructor
  . intro hσ i
    have ⟨ϕ, hϕ⟩ := Fin.foldl_of_comm τ.size (· ⊓ τ.idxToPropFun ·) ⊤ i (by intros; simp; ac_rfl)
    rw [toPropFun, hϕ] at hσ
    simp_all
  . intro h
    unfold toPropFun
    apply Fin.foldl_induction' (hInit := PropFun.satisfies_tr)
    intro ϕ i hϕ
    simp [hϕ, h i]

theorem satisfies_iff_vars {τ : PPA} {σ : PropAssignment IVar} :
    σ ⊨ ↑τ ↔ ∀ ⦃v⦄ ⦃b⦄, τ.varValue? v = some b → σ v = b := by
  constructor
  . intro h ⟨v, hv⟩ b h'
    have := lt_size_of_varValue?_some h'
    let i : Fin τ.size := ⟨v - 1, this⟩
    have h := satisfies_iff.mp h i
    simp [idxToPropFun, varToPropFun, IVar.ofIndex,
        Nat.sub_add_cancel hv, Subtype.val, i, h'] at h
    cases b <;> simp_all
  . intro h
    apply satisfies_iff.mpr
    intro i
    unfold idxToPropFun varToPropFun
    cases' h' : (varValue? τ _) with b
    . simp
    . have := h h'
      cases b <;> simp_all

theorem satisfies_iff_lits {τ : PPA} {σ : PropAssignment IVar} :
    σ ⊨ ↑τ ↔ ∀ ⦃l⦄, τ.litValue? l = some true → σ ⊨ ↑l := by
  simp_rw [LitVar.satisfies_iff, litValue?]
  constructor
  . intro h l h'
    apply satisfies_iff_vars.mp h
    simp_all
  . intro h
    apply satisfies_iff_vars.mpr
    intro x b
    have := @h (mkPos x)
    have := @h (mkNeg x)
    cases b <;> simp_all

-- CC Note: we cannot add these to `defs` unless we shift `PropAssignment` to not depend on Mathlib

/-- A satisfying assignment for `toPropFun`.
This is an arbitrary extension of `τ` from its domain to all of `IVar`. -/
def toSatAssignment (τ : PPA) : PropAssignment IVar :=
  fun v => τ.varValue? v |>.getD false

-- Like the above def, except the default value given to other vars can be provided
def toSatAssignment' (τ : PPA) (b : Bool) : PropAssignment IVar :=
  fun v => τ.varValue? v |>.getD b

theorem toSatAssignment_satisfies (τ : PPA) : τ.toSatAssignment ⊨ ↑τ := by
  aesop (add norm unfold toSatAssignment, norm satisfies_iff_vars)

theorem toSatAssignment'_satisfies (τ : PPA) (b : Bool) : τ.toSatAssignment' b ⊨ ↑τ := by
  aesop (add norm unfold toSatAssignment', norm satisfies_iff_vars)

theorem toPropFun_ne_bot (τ : PPA) : τ.toPropFun ≠ ⊥ := by
  intro
  have := τ.toSatAssignment_satisfies
  simp_all only [not_satisfies_fls]

@[simp]
theorem varValue?_true_iff {τ : PPA} {v : IVar} :
    τ.varValue? v = some true ↔ τ.toPropFun ≤ .var v := by
  constructor
  · intro h
    apply PropFun.entails_ext.mpr
    simp_all [satisfies_iff_vars]
  · intro h
    have := (PropFun.entails_ext.mp h) _ (toSatAssignment_satisfies τ)
    simp [toSatAssignment] at this
    match hτ : varValue? τ v with
    | none =>       simp [hτ] at this
    | some false => simp [hτ] at this
    | some true =>  rfl

@[simp]
theorem varValue?_false_iff {τ : PPA} {v : IVar} :
    τ.varValue? v = some false ↔ τ.toPropFun ≤ (.var v)ᶜ := by
  constructor
  · intro h
    apply PropFun.entails_ext.mpr
    simp_all [satisfies_iff_vars]
  · intro h
    have := (PropFun.entails_ext.mp h) _ (toSatAssignment'_satisfies τ true)
    simp [toSatAssignment'] at this
    match hτ : varValue? τ v with
    | none =>       simp [hτ] at this
    | some false => rfl
    | some true =>  simp [hτ] at this

theorem not_mem_semVars_of_varValue?_none {τ : PPA} {v : IVar} :
    τ.varValue? v = none → v ∉ τ.toPropFun.semVars := by
  rw [not_mem_semVars]
  intro hv τ' b
  constructor
  all_goals (
    intro hτ'
    rw [satisfies_iff_vars] at hτ' ⊢
    intro v' b' hv'
    have h_ne : v ≠ v' := fun h => by rw [h, hv'] at hv; contradiction
    have := hτ' hv'
  )
  · rwa [PropAssignment.set_get_of_ne _ _ h_ne] at this
  · rwa [PropAssignment.set_get_of_ne _ _ h_ne]

-- CC: TODO: Clean up proof so less duplication?
@[simp]
theorem varValue?_none_iff {τ : PPA} {v : IVar} :
    τ.varValue? v = none ↔ ¬(τ.toPropFun ≤ .var v) ∧ ¬(τ.toPropFun ≤ (.var v)ᶜ) := by
  constructor
  · intro h_none
    constructor
    · intro h_lt
      let σ := τ.toSatAssignment.set v false
      have : σ.agreeOn τ.toPropFun.semVars τ.toSatAssignment := fun y hMem =>
        have : v ≠ y := fun h => τ.not_mem_semVars_of_varValue?_none h_none (h ▸ hMem)
        PropAssignment.set_get_of_ne _ _ this
      have hσ : σ ⊨ τ.toPropFun := (agreeOn_semVars this).mpr τ.toSatAssignment_satisfies
      have : σ ⊭ .var v := by
        simp only [satisfies_var, PropAssignment.set_get, not_false_eq_true, σ]
        trivial
      exact this (entails_ext.mp h_lt σ hσ)
    · intro h_lt
      let σ := τ.toSatAssignment.set v true
      have : σ.agreeOn τ.toPropFun.semVars τ.toSatAssignment := fun y hMem =>
        have : v ≠ y := fun h => τ.not_mem_semVars_of_varValue?_none h_none (h ▸ hMem)
        PropAssignment.set_get_of_ne _ _ this
      have hσ : σ ⊨ τ.toPropFun := (agreeOn_semVars this).mpr τ.toSatAssignment_satisfies
      have : σ ⊭ (.var v)ᶜ := by
        simp only [PropFun.satisfies_neg, satisfies_var, PropAssignment.set_get, not_true_eq_false,
          not_false_eq_true, σ]
      exact this (entails_ext.mp h_lt σ hσ)
  · rintro ⟨h₁, h₂⟩
    match hτ : varValue? τ v with
    | none =>       rfl
    | some true =>  exact absurd (varValue?_true_iff.mp hτ) h₁
    | some false => exact absurd (varValue?_false_iff.mp hτ) h₂

-- CC: Should the standard form be ≤ or ` ⊓ = ⊥`?

@[simp]
theorem litValue?_true_iff {τ : PPA} {l : ILit} :
    τ.litValue? l = some true ↔ τ.toPropFun ≤ l := by
  simp [litValue?, LitVar.toPropFun]
  cases polarity l <;>
    simp (config := {contextual := true}) [varValue?_false_iff, varValue?_true_iff]

@[simp]
theorem litValue?_false_iff {τ : PPA} {l : ILit} :
    τ.litValue? l = some false ↔ τ.toPropFun ≤ (↑l)ᶜ := by
  simp [litValue?, LitVar.toPropFun]
  cases polarity l <;>
    simp (config := {contextual := true}) [varValue?_false_iff, varValue?_true_iff]

-- CC: Not `simp` because generates two not-too-useful things
theorem litValue?_none_iff {τ : PPA} {l : ILit} :
    τ.litValue? l = none ↔ ¬(τ.toPropFun ≤ l) ∧ ¬(τ.toPropFun ≤ (↑l)ᶜ):= by
  simp [litValue?, LitVar.toPropFun]
  cases (polarity l) <;>
    simp (config := {contextual := true}) [varValue?_none_iff]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

-- CC: TODO these belong elsewhere. `PropFun.lean`?

/-
theorem inf_eq_of_varValue?_true {τ : PPA} {v : IVar} :
    τ.varValue? v = some true → τ.toPropFun ⊓ (.var v) = τ := by
  simp only [varValue?_true_iff, inf_eq_left, imp_self]

theorem inf_eq_of_varValue?_false {τ : PPA} {v : IVar} :
    τ.varValue? v = some false → τ.toPropFun ⊓ (.var v)ᶜ = τ := by
  simp only [varValue?_false_iff, inf_eq_left, imp_self]

theorem inf_eq_of_litValue?_true {τ : PPA} {l : ILit} :
    τ.litValue? l = some true → τ.toPropFun ⊓ ↑l = τ := by
  simp only [litValue?_true_iff, inf_eq_left, imp_self]

theorem inf_eq_of_litValue?_false {τ : PPA} {l : ILit} :
    τ.litValue? l = some false → τ.toPropFun ⊓ (↑l)ᶜ = τ := by
  simp only [litValue?_false_iff, inf_eq_left, imp_self]
-/

/-! ## Setting values in the PPA -/

@[simp]
theorem setVar_eq_setVarFor (τ : PPA) (v : IVar) (b : Bool) :
    τ.setVar v b = τ.setVarFor v b 0 := by
  simp [setVar, setVarFor]

theorem setVarUntil_eq_setVarFor (τ : PPA) (v : IVar) (b : Bool) (gen : Nat) :
    gen ≥ τ.generation → τ.setVarUntil v b gen = τ.setVarFor v b (gen - τ.generation) := by
  intro hgen
  simp [setVarUntil, setVarFor, ← Nat.add_sub_assoc hgen]
  congr
  · rw [← Nat.add_sub_assoc hgen, Nat.add_comm, Nat.add_sub_cancel]
  · have h := Int.mul_add (-1) ((gen : Int) - (τ.generation : Int)) τ.generation
    simp_rw [sub_add_cancel, neg_mul, one_mul] at h
    rw [h]
    aesop

@[simp]
theorem setLit_eq_setLitFor (τ : PPA) (l : ILit) :
    τ.setLit l = τ.setLitFor l 0 := by
  simp [setLit, setLitFor, setVar_eq_setVarFor]

theorem setNegatedClause_eq_setNegatedClauseFor (τ : PPA) (C : IClause) :
    τ.setNegatedClause C = τ.setNegatedClauseFor C 0 := by
  simp [setNegatedClause, setNegatedClauseFor, setLit_eq_setLitFor]

@[simp]
theorem setNegatedClause_empty (τ : PPA) : τ.setNegatedClause #[] = τ := by
  simp [setNegatedClause]

@[simp]
theorem setNegatedClauseUntil_empty (τ : PPA) (gen : Nat) :
    τ.setNegatedClauseUntil #[] gen = τ := by
  simp [setNegatedClauseUntil]

@[simp]
theorem setNegatedClauseFor_empty (τ : PPA) (extraBumps : Nat) :
    τ.setNegatedClauseFor #[] extraBumps = τ := by
  simp [setNegatedClauseFor]

@[simp]
theorem setNegatedClauseFor_cons (τ : PPA) (l : ILit) (ls : List ILit) (bumps : Nat) :
    τ.setNegatedClauseFor { toList := l :: ls } bumps =
      (τ.setLitFor (-l) bumps).setNegatedClauseFor { toList := ls } bumps := by
  simp_rw [setNegatedClauseFor, Array.foldl_cons]

-- CC: Already proved in `PPA.Defs`
-- @[simp] theorem setNegatedClause_cons (τ : PPA) (l : ILit) (ls : List ILit) :

/-! ### Lemmas about `reset` -/

theorem lt_reset_generation (τ : PPA) : ∀ i ∈ τ.reset.assignment, i.natAbs < τ.reset.generation := by
  dsimp [reset]
  intro i h
  have := τ.le_maxGen i h
  linarith

@[simp]
theorem varValue?_reset (τ : PPA) (v : IVar) : τ.reset.varValue? v = none := by
  unfold varValue?
  split
  . rfl
  . split
    . next n hn h =>
      have : n ∈ τ.reset.assignment := by
        rw [Array.getElem?_eq_some_iff] at hn
        rcases hn with ⟨hv, rfl⟩
        exact Array.getElem_mem hv
      have := τ.lt_reset_generation n this
      omega
    . rfl

@[simp]
theorem litValue?_reset (τ : PPA) (l : ILit) : (τ.reset).litValue? l = none := by
  simp [litValue?, varValue?_reset]

@[simp]
theorem toPropFun_reset (τ : PPA) : τ.reset.toPropFun = ⊤ := by
  ext; simp [satisfies_iff_vars]

/-! ### Lemmas about `setVar`, `setLit` -/

-- CC: The `simp` normal form should use `setVarFor`, so we omit proofs about `setVar`

@[simp]
theorem varValue?_setVarFor (τ : PPA) (v : IVar) (b : Bool) (bumps : Nat)
    : (τ.setVarFor v b bumps).varValue? v = some b := by
  unfold varValue? setVarFor
  cases b <;> simp
  · omega
  · have := τ.generation.property
    omega

theorem varValue?_setVarFor_of_ne {v v' : IVar} : v ≠ v' →
    ∀ (τ : PPA) (b : Bool) (bumps : Nat), (τ.setVarFor v b bumps).varValue? v' = τ.varValue? v' := by
  unfold varValue? setVarFor
  intro hNe τ b
  simp [Array.getElem?_setF, hNe]
  by_cases hv : v.index < τ.assignment.size
  <;> simp [hv]
  by_cases hv' : v'.index < τ.assignment.size
  <;> simp [hv']
  by_cases hvv' : v'.index < v.index
  <;> simp [hvv']
  <;> rw [Array.getElem?_eq_none (Nat.le_of_not_lt hv')]

@[simp]
theorem varValue?_setLitFor (τ : PPA) (l : ILit) (bumps : Nat)
    : (τ.setLitFor l bumps).varValue? (toVar l) = some (polarity l) := by
  simp [setLitFor]

@[simp]
theorem litValue?_setLitFor (τ : PPA) (l : ILit) (bumps : Nat)
    : (τ.setLitFor l bumps).litValue? l = some true := by
  simp [litValue?]

theorem varValue?_setLitFor_of_ne {l : ILit} {v : IVar} :
    toVar l ≠ v → ∀ (τ : PPA) (bumps : Nat), (τ.setLitFor l bumps).varValue? v = τ.varValue? v := by
  intro h
  simp [setLitFor, varValue?_setVarFor_of_ne h]

theorem litValue?_setLitFor_of_ne {l l' : ILit} :
    toVar l ≠ toVar l' → ∀ (τ : PPA) (bumps : Nat), (τ.setLitFor l bumps).litValue? l' = τ.litValue? l' := by
  intro h
  simp [litValue?, varValue?_setLitFor_of_ne h]

/-! ### `toPropFun` model -/

theorem toPropFun_setVarFor_lt_of_none {τ : PPA} {v : IVar} :
    τ.varValue? v = none → ∀ (b : Bool) (bumps : Nat), (τ.setVarFor v b bumps).toPropFun ≤ τ := by
  intro h b bumps
  apply entails_ext.mpr
  intro σ hσ
  rw [satisfies_iff_vars] at hσ ⊢
  intro y b hy
  apply hσ
  rwa [varValue?_setVarFor_of_ne]
  intro hEq
  rw [hEq, hy] at h
  contradiction

theorem toPropFun_setLitFor_le_of_none {τ : PPA} {l : ILit} :
    τ.litValue? l = none → ∀ (bumps : Nat), (τ.setLitFor l bumps).toPropFun ≤ τ := by
  intro
  simp_all only [litValue?, Option.map_eq_none', varValue?_none_iff, setLitFor, not_false_eq_true,
    and_self, toPropFun_setVarFor_lt_of_none, implies_true]

@[simp]
theorem toPropFun_setLitFor_lt (τ : PPA) (l : ILit) (bumps : Nat) :
    (τ.setLitFor l bumps).toPropFun ≤ l := by
  apply entails_ext.mpr
  intro σ hσ
  rw [satisfies_iff_lits] at hσ
  apply hσ
  apply litValue?_setLitFor

@[simp]
theorem lt_toPropFun_setLitFor (τ : PPA) (l : ILit) (bumps : Nat) :
    τ.toPropFun ⊓ l ≤ (τ.setLitFor l bumps) := by
  apply entails_ext.mpr
  intro σ hσ
  have ⟨hσ, hσ'⟩ := satisfies_conj.mp hσ
  rw [satisfies_iff_vars] at hσ ⊢
  intro x b hx
  by_cases h : toVar l = x
  . simp_all [setLitFor, LitVar.satisfies_iff]
  . apply hσ
    rwa [τ.varValue?_setLitFor_of_ne h] at hx

theorem toPropFun_setLitFor_of_none {τ : PPA} {l : ILit} :
    τ.litValue? l = none → ∀ (bumps : Nat), (τ.setLitFor l bumps).toPropFun = τ.toPropFun ⊓ l := by
  intro h bumps
  refine le_antisymm ?_ (τ.lt_toPropFun_setLitFor l bumps)
  simp [toPropFun_setLitFor_le_of_none h, toPropFun_setLitFor_lt]

-- TODO: This spec isn't correct, and needs an assumption that τ and C don't overlap,
-- or that C isn't a tautology?
-- Or just write an updated setNegatedClause that evaluates the literals as they
-- come in and return a Bool or an option or something
/-theorem setNegatedClause_of_le {τ : PPA} {C : IClause} :
    τ.toPropFun ≤ C.toPropFun → τ.setNegatedClause C = τ.toPropFun ⊓ Cᶜ := by
  have ⟨C⟩ := C
  induction' C with l ls ih generalizing τ
  · simp
    done
  · simp
    intro h -/

/-@[simp]
theorem setNegatedClause_reset_toPropFun (τ : PPA) (C : IClause) :
    (τ.reset.setNegatedClause C).toPropFun = (C.toPropFun)ᶜ := by
  have ⟨C⟩ := C
  induction' C with l ls ih generalizing τ
  · simp [setNegatedClause]
  · simp [setNegatedClause] -/


/-! # SetFor judgment -/

section isSetFor

variable {τ : PPA} {v : IVar} {n : Nat}

def isSet (τ : PPA) (v : IVar) : Prop :=
  τ.varValue? v ≠ none

-- Says that the provided variable is set for n "bumps"
-- Add 1 because setting the variable sets its assignment value to τ.generation, so it's set for 1 bump
def isSetFor (τ : PPA) (v : IVar) (n : Nat) : Prop :=
  ((τ.assignment.getD v.index 0).natAbs + 1) - τ.generation.val = n

theorem isSet_of_isSetFor_pos : n > 0 → isSetFor τ v n → isSet τ v := by
  intro hn
  simp [isSet, isSetFor, varValue?]
  match hv : τ.assignment[v.index]? with
  | none => simp [hv]; aesop
  | some g =>
    simp [hv]
    rintro rfl
    exact le_of_lt_succ (Nat.lt_of_sub_pos hn)

theorem isSet_of_isSetFor_succ {n : Nat} {τ : PPA} {v : IVar} :
    isSetFor τ v (n + 1) → isSet τ v :=
  fun h => isSet_of_isSetFor_pos (succ_pos _) h

theorem varValue?_ne_none_of_isSetFor {τ : PPA} {v : IVar} {n : Nat} :
    n > 0 → isSetFor τ v n → τ.varValue? v ≠ none := by
  intro hn
  simp [isSetFor, varValue?]
  rintro rfl
  replace hn := Nat.lt_of_sub_pos hn
  match hv : τ.assignment[v.index]? with
  | none => simp [hv] at hn
  | some g =>
    simp [hv] at hn
    simp [le_of_lt_succ hn]

theorem varValue?_ne_none_of_isSetFor' {τ : PPA} {v : IVar} {n : Nat} :
    isSetFor τ v (n + 1) → τ.varValue? v ≠ none :=
  varValue?_ne_none_of_isSetFor (succ_pos _)

-- Cayden TODO: Think about whether should be succ or hypothesis (> 0)
theorem isSetFor_of_varValue?_ne_none {τ : PPA} {v : IVar} :
    τ.varValue? v ≠ none → ∃ (n : Nat), isSetFor τ v (n + 1) := by
  cases hv : τ.assignment[v.index]?
  <;> simp [varValue?, hv]
  rename Int => g
  intro hg
  use (Int.natAbs g - τ.generation)
  simp [isSetFor, hv, Nat.sub_add_comm hg]

@[simp]
theorem isSetFor_zero_iff {τ : PPA} {v : IVar} :
    isSetFor τ v 0 ↔ τ.varValue? v = none := by
  cases hv : τ.assignment[v.index]?
  <;> simp [isSetFor, varValue?, hv]
  · have := τ.generation.property
    omega
  · omega

@[simp]
theorem setVar_isSetFor (τ : PPA) (v : IVar) (b : Bool) : isSetFor (τ.setVar v b) v 1 := by
  simp [isSetFor, setVar]; cases b <;> simp

@[simp]
theorem setLit_isSetFor (τ : PPA) (l : ILit) : isSetFor (τ.setLit l) (toVar l) 1 :=
  setVar_isSetFor _ _ _

@[simp]
theorem setVarFor_isSetFor (τ : PPA) (v : IVar) (b : Bool) (extraBumps : Nat) :
    isSetFor (τ.setVarFor v b extraBumps) v (extraBumps + 1) := by
  simp [isSetFor, setVarFor]; cases b <;> simp
  · rw [← Int.neg_add, Int.natAbs_neg]
    have : Int.natAbs (extraBumps + τ.generation) = extraBumps + τ.generation := rfl
    rw [this, add_assoc, add_comm τ.generation.val 1, ← add_assoc, Nat.add_sub_cancel]
  · have : Int.natAbs (τ.generation + extraBumps) = τ.generation + extraBumps := rfl
    rw [this, add_comm τ.generation.val _, add_assoc, add_comm τ.generation.val 1, ← add_assoc, Nat.add_sub_cancel]

@[simp]
theorem setLitFor_isSetFor (τ : PPA) (l : ILit) (extraBumps : Nat) :
    isSetFor (τ.setLitFor l extraBumps) (toVar l) (extraBumps + 1) :=
  setVarFor_isSetFor _ _ _ _

theorem isSetFor_bump {τ : PPA} {v : IVar} {n : Nat} :
    isSetFor τ v n → isSetFor τ.bump v (n - 1) := by
  simp [isSetFor, bump]
  rintro rfl
  rw [← sub_add_eq, ← Nat.add_sub_add_right]

theorem isSetFor_reset (τ : PPA) (v : IVar) : isSetFor τ.reset v 0 :=
  isSetFor_zero_iff.mpr (varValue?_reset τ v)

end isSetFor /- section -/

/-! ## Unit propagation -/

inductive PropResult (τ τ' : PPA) (C : IClause) where
  | contradiction (h : C.toPropFun ⊓ τ.toPropFun = ⊥)
  /-- Under `τ`, `C` became a unit clause `[l]`.
  The assignment was extended by that literal, i.e., `τ' = τ ⊓ l`. -/
  -- Note: I didn't prove that `C' = [l]`.
  | extended      (l : ILit) (hl : l ∈ C)
                  (h₁ : τ'.toPropFun = l.toPropFun ⊓ τ.toPropFun)
                  (h₂ : τ.toPropFun ⊓ C.toPropFun ≤ l.toPropFun)
  /-- Clause became satisfied. -/
  | satisfied
  /-- Clause did not become unit, and was not satisfied. -/
  | notUnit

/-- If `C` is satisfied by `τ`, return `satisfied`.
Otherwise compute the reduced clause `C' = {l ∈ C | ¬l ∉ τ}`.
If `C' = [u]` is a unit, extend `τ` by `u` and return `extended`.
If `C'` has become empty (is falsified), return `contradiction`.
If `C'` is not a unit and not falsified, return `notUnit`. -/
def propagateUnit (τ : PPA) (C : IClause) : (τ' : PPA) × PropResult τ τ' C :=
  go 0 none Option.all_none (by simp only [not_lt_zero', IsEmpty.forall_iff, implies_true])
where
  /-- If `unit? = some u`, then `u` is a literal in the clause that is not falsified by `τ`.
  It may therefore be the case that `C' = [u]` -/
  go (i : Nat) (unit? : Option ILit) (hUnit : unit?.all fun u => u ∈ C ∧ τ.litValue? u = none)
      (hLits : ∀ (j : Fin C.size), j.val < i → unit? = some C[j] ∨ τ.toPropFun ≤ (C[j].toPropFun)ᶜ) :
      (τ' : PPA) × PropResult τ τ' C :=
    if hi : i < C.size then
      let l := C[i]'hi
      match hl : τ.litValue? l with
      | some true => ⟨τ, .satisfied⟩
      | some false =>
        -- TODO: lots of duplication here
        go (i+1) unit? hUnit (by
          simp [l] at hl
          intro j hj
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ.mp hj) with hj | hj
          . exact hLits j hj
          . right
            apply litValue?_false_iff.mp
            simp [hj, hl])
      | none =>
        match hUnit : unit? with
        | .some u =>
          if hEq : u = l then
            go (i+1) (some l) (by simp [C.getElem_mem hi, hl, l]) (by
              intro j hj
              rcases Nat.lt_or_eq_of_le (Nat.lt_succ.mp hj) with hj | hj
              . exact hEq ▸ hLits j hj
              . apply Or.inl
                simp [hEq, hj, l])
          else
            ⟨τ, .notUnit⟩
        | .none =>
          go (i+1) (some l) (by simp [C.getElem_mem hi, hl, l]) (by
            intro j hj
            rcases Nat.lt_or_eq_of_le (Nat.lt_succ.mp hj) with hj | hj
            . apply Or.inr
              have := hLits j hj
              simpa using this
            . apply Or.inl
              simp [hj, l])
    else
      match unit? with
      | none =>
        ⟨τ, .contradiction (by
          apply le_bot_iff.mp
          apply entails_ext.mpr
          intro σ hσ
          exfalso
          rcases (satisfies_conj.mp hσ) with ⟨hσC, hστ⟩
          have ⟨l, hl, hσl⟩ := Clause.satisfies_iff.mp hσC
          rcases Array.mem_iff_getElem.mp hl with ⟨k, hk, rfl⟩
          rw [not_lt] at hi
          have := hLits ⟨k, hk⟩ (lt_of_lt_of_le hk hi)
          simp at this
          have := entails_ext.mp this _ hστ
          rw [PropFun.satisfies_neg] at this
          exact this hσl)⟩
      | some u =>
        ⟨τ.setLit u, .extended u
          (by simp at hUnit; tauto)
          (by
            simp at hUnit
            simp [τ.toPropFun_setLitFor_of_none hUnit.right, inf_comm])
          (by
            apply entails_ext.mpr
            intro σ hσ
            have ⟨hστ, hσC⟩ := satisfies_conj.mp hσ
            have ⟨l, hl, hσl⟩ := Clause.satisfies_iff.mp hσC
            rcases Array.mem_iff_getElem.mp hl with ⟨i, hi, rfl⟩
            have := hLits ⟨i, hi⟩ (by linarith)
            rcases this with hEq | hτl
            . cases hEq
              exact hσl
            . exfalso
              exact (satisfies_neg.mp <| entails_ext.mp hτl _ hστ) hσl)⟩
  termination_by C.size - i

section UP

@[simp]
theorem unitPropM.aux_nil (τ : PPA) (unit? : Option ILit) :
  unitPropM.aux τ { toList := [] } unit? = .ok unit? := by
  simp [unitPropM.aux, pure, Except.pure]

@[simp]
theorem unitPropM.aux_cons (τ : PPA) (l : ILit) (ls : List ILit) (unit? : Option ILit) :
  unitPropM.aux τ { toList := l :: ls } unit? =
    match τ.litValue? l with
    | some true => .error true
    | some false => unitPropM.aux τ { toList := ls } unit?
    | none =>
      match unit? with
      | none => unitPropM.aux τ { toList := ls } (some l)
      | some u =>
        if u = l then
          unitPropM.aux τ { toList := ls } unit?
        else
          .error false := by
  unfold unitPropM.aux pevalM
  simp only [List.length_cons, List.foldlM_toArray', List.foldlM_cons]
  match hl : τ.litValue? l with
  | some true => rfl
  | some false => rfl
  | none =>
    match h_unit : unit? with
    | none => rfl
    | some u =>
      by_cases hul : u = l
      <;> simp [hul] <;> rfl

@[simp]
theorem unitPropM.aux_some_ne_none (τ : PPA) (C : List ILit) (unit : ILit)
    : unitPropM.aux τ { toList := C } (some unit) ≠ .ok none := by
  induction C with
  | nil => simp
  | cons l ls ih =>
    simp
    match hl : τ.litValue? l with
    | some true => simp
    | some false => simp [ih]
    | none =>
      simp
      split
      · exact ih
      · intro h; injection h

theorem unitPropM.aux_some_eq (τ : PPA) (C : List ILit) (unit unit' : ILit)
    : unitPropM.aux τ { toList := C } (some unit) = .ok (some unit') → unit = unit' := by
  induction C with
  | nil => simp only [aux_nil, Except.ok.injEq, Option.some.injEq, imp_self]
  | cons l ls ih =>
    simp only [aux_cons]
    split
    · simp only [reduceCtorEq, IsEmpty.forall_iff]
    · exact ih
    · split
      · exact ih
      · simp only [reduceCtorEq, IsEmpty.forall_iff]

@[simp]
theorem unitProp.loop_nil (τ : PPA) (unit? : Option ILit) :
  unitProp.loop τ { toList := [] } 0 unit? =
    match unit? with
    | none => .falsified
    | some l => .unit l := by
  unfold unitProp.loop; simp; rfl

theorem unitProp.loop_cons_succ (τ : PPA) (l : ILit) (ls : List ILit) (n : Nat) (unit? : Option ILit) :
  ∀ {m : Nat}, m = ls.length - n →
    unitProp.loop τ { toList := l :: ls } (n + 1) unit? =
      unitProp.loop τ { toList := ls } n unit? := by
  intro m hm
  induction m generalizing n unit? with
  | zero =>
    unfold loop
    have : n ≥ ls.length := by exact Nat.le_of_sub_eq_zero (id (Eq.symm hm))
    simp [Nat.not_lt_of_ge this]
  | succ m ih =>
    unfold loop
    have hm' : m = ls.length - (n + 1) := by omega
    have hn : n < ls.length := by omega
    simp [hn, ih _ _ hm']

theorem unitProp.loop_of_ge_length (τ : PPA) (ls : List ILit) (n : Nat) (unit? : Option ILit) :
  n ≥ ls.length → unitProp.loop τ { toList := ls } n unit? =
      match unit? with
      | none => .falsified
      | some l => .unit l := by
  intro hn
  unfold loop
  simp [Nat.not_lt_of_le hn]
  rfl

theorem unitProp.loop_eq_unitPropM.aux (τ : PPA) (ls : List ILit) (n : Nat) (hn : n < ls.length) (unit? : Option ILit)
    : ∀ (m : Nat), m = ls.length - n →
        unitProp.loop τ { toList := ls } n unit? = unitPropM_Except (unitPropM.aux τ { toList := ls.drop n } unit?) := by
  intro m hm
  induction m generalizing n unit? with
  | zero =>
    unfold loop
    have : n = ls.length := by omega
    simp [this, unitPropM, unitPropM_Except, pure, Except.pure]
    cases unit? <;> rfl
  | succ m ih =>
    unfold loop
    have hm' : m = ls.length - (n + 1) := by omega
    simp [hn]
    rw [List.drop_eq_getElem_cons hn, unitPropM.aux_cons]
    match h : τ.litValue? ls[n] with
    | none =>
      simp only
      match h_unit : unit? with
      | none =>
        rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hn) with (h | h)
        · have := Nat.le_of_eq h.symm
          rw [unitProp.loop_of_ge_length τ ls (n + 1) _ this]
          rw [List.drop_of_length_le this]
          simp [unitPropM_Except]
        · exact ih _ h (some ls[n]) hm'
      | some u =>
        by_cases hul : u = ls[n]
        <;> simp [hul]
        · rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hn) with (h | h)
          · have := Nat.le_of_eq h.symm
            rw [unitProp.loop_of_ge_length τ ls (n + 1) _ this]
            rw [List.drop_of_length_le this]
            simp [unitPropM_Except]
          · exact ih _ h (some ls[n]) hm'
        · simp [unitPropM_Except]
    | some true => simp [unitPropM_Except]
    | some false =>
      rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hn) with (h | h)
      · have := Nat.le_of_eq h.symm
        rw [unitProp.loop_of_ge_length τ ls (n + 1) _ this]
        rw [List.drop_of_length_le this]
        cases unit? <;> simp [unitPropM_Except]
      · exact ih _ h unit? hm'

theorem unitProp_eq_unitPropM (τ : PPA) (C : IClause) :
    τ.unitProp C = τ.unitPropM C := by
  have ⟨C⟩ := C
  unfold unitProp unitPropM
  match C with
  | [] => simp [unitPropM_Except]
  | l :: ls =>
    exact unitProp.loop_eq_unitPropM.aux τ (l :: ls) 0 (by simp [List.length]) none (l :: ls).length rfl

/-! ### Correctness wrt the PropFun model -/

theorem unitPropM.aux_some_toPropFun (τ : PPA) (C : List ILit) (u : ILit)
    : τ.litValue? u = none
      → unitPropM.aux τ { toList := C } (some u) = .ok (some u)
        → Clause.toPropFun { toList := C } ⊓ τ ≤ u.toPropFun := by
  intro hu h
  induction C with
  | nil => simp
  | cons l ls ih =>
    simp [unitPropM.aux_cons] at h
    match hl : τ.litValue? l with
    | some true => simp [hl] at h
    | some false =>
      simp [hl] at h
      rw [litValue?_false_iff, le_iff_inf_compl_eq_bot, compl_compl, inf_comm] at hl
      simp [inf_sup_right, hl, ih h]
    | none =>
      simp [hl] at h
      rw [litValue?_none_iff] at hl
      by_cases hul : u = l
      · subst_vars
        simp only at h
        simp [inf_sup_right]
        exact ih h
      · simp [hul] at h

theorem unitPropM.aux_none_none_toPropFun (τ : PPA) (C : List ILit)
    : unitPropM.aux τ { toList := C } none = .ok none
      → Clause.toPropFun { toList := C } ⊓ τ = ⊥ := by
  intro h
  induction C with
  | nil => simp
  | cons l ls ih =>
    simp [unitPropM.aux_cons] at h
    match hl : τ.litValue? l with
    | none
    | some true => simp [hl] at h
    | some false =>
      simp [hl] at h
      rw [litValue?_false_iff, le_iff_inf_compl_eq_bot, compl_compl, inf_comm] at hl
      simp [inf_sup_right, hl, ih h]

theorem unitPropM.aux_none_some_toPropFun (τ : PPA) (C : List ILit) (u : ILit)
    : unitPropM.aux τ { toList := C } none = .ok (some u)
        → u ∈ C ∧ τ.litValue? u = none ∧ Clause.toPropFun { toList := C } ⊓ τ = u.toPropFun ⊓ τ := by
  intro h
  induction C with
  | nil => simp at h
  | cons l ls ih =>
    simp [unitPropM.aux_cons] at h
    match hl : τ.litValue? l with
    | some true => simp [hl] at h
    | some false =>
      simp [hl] at h
      rw [litValue?_false_iff, le_iff_inf_compl_eq_bot, compl_compl, inf_comm] at hl
      rcases ih h with ⟨h₁, h₂, h₃⟩
      simp [h₁, h₂, inf_sup_right, h₃, hl]
    | none =>
      simp [hl] at h
      have := unitPropM.aux_some_eq τ ls l u h
      subst this
      simp [hl, inf_sup_right, unitPropM.aux_some_toPropFun τ ls l hl h]

theorem unitPropM_falsified (τ : PPA) (C : IClause)
    : unitPropM τ C = .falsified → C.toPropFun ⊓ τ = ⊥ := by
  have ⟨C⟩ := C
  unfold unitPropM unitPropM_Except
  split <;> try (intro; contradiction)
  simp only [forall_const]
  rename_i h
  exact unitPropM.aux_none_none_toPropFun τ C h

theorem unitPropM_unit (τ : PPA) (C : IClause) (l : ILit)
    : unitPropM τ C = .unit l
        → l ∈ C ∧ τ.litValue? l = none ∧ C.toPropFun ⊓ τ = l.toPropFun ⊓ τ := by
  have ⟨C⟩ := C
  unfold unitPropM unitPropM_Except
  split <;> try (intro; contradiction)
  simp only [UPResult.unit.injEq, Array.mem_toArray, ILit.toPropFun]
  rintro rfl
  rename_i u h
  exact unitPropM.aux_none_some_toPropFun τ C u h

theorem unitPropM_satisfied (τ : PPA) (C : IClause)
    : unitPropM τ C = .satisfied → τ ≤ C.toPropFun := by
  have ⟨C⟩ := C
  unfold unitPropM unitPropM_Except
  split <;> try (intro; contradiction)
  simp only [forall_const, ge_iff_le]
  rename_i h
  revert h
  generalize none = unit?
  induction C generalizing unit? with
  | nil => simp
  | cons l ls ih =>
    simp only [unitPropM.aux_cons, Clause.toPropFun_cons]
    match hl : τ.litValue? l with
    | some true =>
      rw [litValue?_true_iff] at hl
      simp only [le_sup_of_le_left hl, imp_self]
    | some false => exact fun h => le_sup_of_le_right (ih _ h)
    | none =>
      simp only
      match unit? with
      | none => exact fun h => le_sup_of_le_right (ih _ h)
      | some unit =>
        simp only
        split
        · subst_vars
          exact fun h => le_sup_of_le_right (ih _ h)
        · simp only [Except.error.injEq, Bool.false_eq_true, IsEmpty.forall_iff]

end UP /- section -/

end PPA
