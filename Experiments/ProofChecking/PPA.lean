/-

Persistent partial assignments (PPA).

The data structure underlying the PPA is a resizable array that can be ``cleared''
in O(1) time by bumping a generation number.
Each cell in the array stores a generation number that determines if the
cell is set (i.e. that it is above the data structure's generation number).
Used to implement partial assignments by assuming that all
variables are initially unset (PPA).

Authors: Cayden Codel, Wojciech Nawrocki, James Gallicchio
Carnegie Mellon University
-/

import LeanSAT.Data.Cnf
import LeanSAT.Data.Literal
import LeanSAT.Data.ICnf
import LeanSAT.Model.PropFun

import LeanSAT.Upstream.ToStd
import LeanSAT.Upstream.ToMathlib
import LeanSAT.Upstream.Array

import Mathlib.Data.Nat.Basic

open LeanSAT Model Nat
open LitVar ILit IVar LawfulLitVar
open PropFun

/-! # Concise PPA (single array) -/

/-- A Persistent Partial Assignment of truth values to propositional variables.

Assuming the linearity restriction (see below) is met,
the PPA provides a fast representation of partial assignments.
The PPA is allocation-free as long as you initialize it
with the actual maximum variable index in `PPA.new`.
Otherwise, the PPA automatically resizes when a variable out of range is given.
The PPA provides functions for unit propagation and tautology checking.

The PPA is meant to be used persistently and linearly,
i.e., you should keep around exactly one copy of this structure.
Note that ensuring linearity in large functions can be tricky,
especially when `do` notation is used.
The only reliable method at the moment
is to look at the dynamic behavior in a profiler
and ensure that PPA code does not spend lots of time in `lean_copy_expand_array`. -/
structure PPA where
  /-- For each variable, stores the generation value that variable is set for. -/
  assignment : Array Int
  /-- The generation counter is used to avoid clearing the assignment array
      when the assignment is reset.  Instead, we just bump the counter and
      interpret values in the array below the counter as unassigned. -/
  generation : PNat
  /-- The maximum absolute value of any entry in `assignments`. -/
  maxGen : Nat
  le_maxGen : ∀ i ∈ assignment.data, i.natAbs ≤ maxGen

instance : ToString PPA where
  toString τ := String.intercalate " ∧ "
    (τ.assignment.foldl (init := []) (f := fun acc a => s!"{a}" :: acc))

/-! ## Reading values from the PPA -/

namespace PPA

@[reducible] def size (τ : PPA) : Nat := τ.assignment.size

/-- The value of the given variable in the current assignment, if assigned.
    Assignment is determined by comparing the current generation (τ.generation)
    against the generation value stored at that variable's index.
    If not assigned, returns `none`. -/
def varValue? (τ : PPA) (v : IVar) : Option Bool :=
  match τ.assignment.get? v.index with
  | none => none
  | some n =>
    if τ.generation ≤ n.natAbs then
      some (0 < n)
    else
      none

/-- The value of the given literal in the current assignment, if assigned.
    Otherwise `none`. -/
def litValue? (τ : PPA) (l : ILit) : Option Bool :=
  τ.varValue? (toVar l) |>.map (xor !(polarity l))

/-! ### Lemmas about `litValue?`, `varValue?` -/

@[simp] theorem litValue?_negate (τ : PPA) (l : ILit) :
    τ.litValue? (-l) = (τ.litValue? l).map Bool.not := by
  aesop (add norm unfold litValue?)

theorem litValue?_eq_varValue?_none {τ : PPA} {l : ILit} :
    τ.litValue? l = none → τ.varValue? (toVar l) = none := by
  aesop (add norm unfold litValue?)

theorem litValue?_eq_varValue?_some {τ : PPA} {l : ILit} {b : Bool} :
    τ.litValue? l = some b → τ.varValue? (toVar l) = xor (!b) (polarity l) := by
  aesop (add norm unfold litValue?)

@[simp] theorem litValue?_negate_none_iff {τ : PPA} {l : ILit} :
    τ.litValue? (-l) = none ↔ τ.litValue? l = none := by
  simp [litValue?_negate]

theorem lt_size_of_varValue?_some {τ : PPA} {v : IVar} {b : Bool} :
    τ.varValue? v = some b → v.index < τ.size := by
  intro hv
  simp [varValue?, Array.get?] at hv
  rcases Nat.lt_trichotomy v.index τ.size with (hlt | heq | hgt)
  · exact hlt
  · simp [heq] at hv
  · simp [Nat.lt_asymm hgt] at hv

theorem lt_size_of_litValue?_some {τ : PPA} {l : ILit} {b : Bool} :
    τ.litValue? l = some b → (toVar l).index < τ.size := by
  simp [litValue?]
  rw [← toVar_index_eq_index]
  rintro (⟨hv, _⟩ | ⟨hv, _⟩)
  <;> exact lt_size_of_varValue?_some hv

/-! ### `toPropFun` model -/

/-- The PropFun model for τ is the conjunctin of the variables it satisfies.
    Here, we map any variable set to true or false to the appropriate PropFun. -/
def varToPropFun (τ : PPA) (v : IVar) : PropFun IVar :=
  τ.varValue? v |>.map (if · then .var v else (.var v)ᶜ) |>.getD ⊤

/-- We can also calculate the model over just the indexes in range for τ. -/
def idxToPropFun (τ : PPA) (i : Fin τ.size) : PropFun IVar :=
  τ.varToPropFun ⟨IVar.fromIndex i, succ_pos _⟩

/-- We model the `PPA` as the conjunction of all its literals.
    Note that we cannot fully model the `PPA` as a `PropAssignment`
    because those are required to be total. -/
def toPropFun (τ : PPA) : PropFun IVar :=
  Fin.foldl τ.size (· ⊓ τ.idxToPropFun ·) ⊤

instance : Coe PPA (PropFun IVar) := ⟨toPropFun⟩

instance : SemanticEntails (PropAssignment IVar) (PropFun IVar) where
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
  . rintro h ⟨v, hv⟩ b h'
    have := lt_size_of_varValue?_eq_some h'
    let i : Fin τ.size := ⟨v - 1, this⟩
    have h := satisfies_iff.mp h i
    dsimp [idxToPropFun, varToPropFun] at h
    simp_rw [IVar.fromIndex, Nat.sub_add_cancel hv, PNat.val, h'] at h
    simp only [Option.map_some', Option.getD_some] at h
    cases b <;> simp_all
  . intro h
    apply satisfies_iff.mpr
    intro i
    unfold idxToPropFun varToPropFun
    cases' h' : (varValue? τ _) with b
    . simp
    . have := h h'
      cases b <;> simp_all

#exit

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
  intro hv σ b hσ
  rw [satisfies_iff_vars] at hσ ⊢
  intro y b hy
  have : v ≠ y := fun h => by rw [h, hy] at hv; contradiction
  rw [PropAssignment.set_get_of_ne _ _ this]
  apply hσ hy

-- Cayden TODO: Clean up proof so less duplication?
theorem varValue?_none_iff {τ : PPA} {v : IVar} :
    τ.varValue? v = none ↔ ¬(τ.toPropFun ≤ .var v) ∧ ¬(τ.toPropFun ≤ (.var v)ᶜ) := by
  constructor
  · intro hNone
    constructor
    · intro hLt
      let σ := τ.toSatAssignment.set v false
      have : σ.agreeOn τ.toPropFun.semVars τ.toSatAssignment := fun y hMem =>
        have : v ≠ y := fun h => τ.not_mem_semVars_of_varValue?_none hNone (h ▸ hMem)
        PropAssignment.set_get_of_ne _ _ this
      have hσ : σ ⊨ τ.toPropFun := (agreeOn_semVars this).mpr τ.toSatAssignment_satisfies
      have : σ ⊭ .var v := by
        simp only [satisfies_var, PropAssignment.set_get, not_false_eq_true]
      exact this (entails_ext.mp hLt σ hσ)
    · intro hLt
      let σ := τ.toSatAssignment.set v true
      have : σ.agreeOn τ.toPropFun.semVars τ.toSatAssignment := fun y hMem =>
        have : v ≠ y := fun h => τ.not_mem_semVars_of_varValue?_none hNone (h ▸ hMem)
        PropAssignment.set_get_of_ne _ _ this
      have hσ : σ ⊨ τ.toPropFun := (agreeOn_semVars this).mpr τ.toSatAssignment_satisfies
      have : σ ⊭ (.var v)ᶜ := by
        simp only [PropFun.satisfies_neg, satisfies_var, PropAssignment.set_get, not_true_eq_false,
          not_false_eq_true]
      exact this (entails_ext.mp hLt σ hσ)
  · rintro ⟨h₁, h₂⟩
    match hτ : varValue? τ v with
    | none =>       rfl
    | some true =>  exact absurd (varValue?_true_iff.mp hτ) h₁
    | some false => exact absurd (varValue?_false_iff.mp hτ) h₂

theorem litValue?_true_iff {τ : PPA} {l : ILit} :
    τ.litValue? l = some true ↔ τ.toPropFun ≤ l := by
  simp [litValue?, LitVar.toPropFun]
  cases polarity l <;>
    simp (config := {contextual := true}) [varValue?_false_iff, varValue?_true_iff]

theorem litValue?_false_iff {τ : PPA} {l : ILit} :
    τ.litValue? l = some false ↔ τ.toPropFun ≤ (↑l)ᶜ := by
  simp [litValue?, LitVar.toPropFun]
  cases polarity l <;>
    simp (config := {contextual := true}) [varValue?_false_iff, varValue?_true_iff]

theorem litValue?_none_iff {τ : PPA} {l : ILit} :
    τ.litValue? l = none ↔ ¬(τ.toPropFun ≤ l) ∧ ¬(τ.toPropFun ≤ (↑l)ᶜ):= by
  simp [litValue?, LitVar.toPropFun]
  cases (polarity l) <;>
    simp (config := {contextual := true}) [varValue?_none_iff]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

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

-- ?? folded into the `PPA` structure for now (forever?)
--structure PPA.WF (ppa : PPA) where
  -- hGen: 0 < generation
  -- hMaxVal : ∀ x ∈ assignment, x.natAbs ≤ maxVal

/-! ## Setting values in the PPA -/

/-- Initialize to an empty partial assignment,
supporting variables in the range `[1, maxVar]`.

The assignment will resize dynamically if it's used with
a variable above the initial `maxVar`. -/
def new (maxVar : Nat) : PPA where
  assignment := Array.mkArray maxVar 0
  generation := ⟨1, Nat.one_pos⟩
  maxGen := 0
  le_maxGen i h := by simp_all [List.mem_replicate]

/-- Reset the assignment to an empty one. -/
def reset (τ : PPA) : PPA :=
  { τ with generation := ⟨τ.maxGen + 1, Nat.succ_pos _⟩ }

/-- Clear all temporary assignments at the current generation. -/
def bump (τ : PPA) : PPA :=
  { τ with generation := ⟨τ.generation + 1, Nat.succ_pos _⟩ }

/-- Helper theorem for `setVar*`. -/
theorem setVar_le_maxGen (τ : PPA) (i : Nat) (b : Bool) (gen : Nat) :
    let v : Int := if b then gen else -gen
    ∀ g ∈ (τ.assignment.setF i v 0).data, g.natAbs ≤ Nat.max τ.maxGen gen := by
  intro v g hg
  have := Array.mem_setF _ _ _ _ g hg
  rcases this with h | h | h
  . exact le_max_of_le_left (τ.le_maxGen _ h)
  . simp [h]
  . cases b <;> simp [h]

/-- Set the given variable to `b` for the current generation. -/
def setVar (τ : PPA) (v : IVar) (b : Bool) : PPA :=
  let g : Int := if b then τ.generation else -τ.generation
  { τ with
    assignment := τ.assignment.setF v.index g 0
    maxGen := Nat.max τ.maxGen τ.generation
    le_maxGen := setVar_le_maxGen τ v.index b τ.generation }

/-- Set the given literal to `true` for the current generation. -/
def setLit (τ : PPA) (l : ILit) : PPA :=
  τ.setVar (toVar l) (polarity l)

/-- Set the given variable to `b` for all generations until `gen`. -/
def setVarUntil (τ : PPA) (v : IVar) (b : Bool) (gen : Nat) : PPA :=
  let g : Int := if b then gen else -gen
  { τ with
    assignment := τ.assignment.setF v.index g 0
    maxGen := Nat.max τ.maxGen gen
    le_maxGen := setVar_le_maxGen τ v.index b gen }

/-- Set the given literal to `true` for all generations until `gen`. -/
def setLitUntil (τ : PPA) (l : ILit) (gen : Nat) : PPA :=
  τ.setVarUntil (toVar l) (polarity l) gen

def setVarFor (τ : PPA) (v : IVar) (b : Bool) (extraBumps : Nat) : PPA :=
  let g : Int := if b then τ.generation + extraBumps else -(τ.generation + extraBumps)
  { τ with
    assignment := τ.assignment.setF v.index g 0
    maxGen := Nat.max τ.maxGen (τ.generation + extraBumps)
    le_maxGen := setVar_le_maxGen τ v.index b (τ.generation + extraBumps) }

def setLitFor (τ : PPA) (l : ILit) (extraBumps : Nat) : PPA :=
  τ.setVarFor (toVar l) (polarity l) extraBumps

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

theorem setLit_eq_setLitFor (τ : PPA) (l : ILit) :
    τ.setLit l = τ.setLitFor l 0 := by
  simp [setLit, setLitFor, setVar_eq_setVarFor]

/-- Set `l ↦ ⊥` for each `l ∈ C` and leave the rest of the assignment untouched.
If the current assignment contains literals appearing in `C`, they will be overwritten. -/
def setNegatedClause (τ : PPA) (C : IClause) : PPA :=
  C.foldl (init := τ) (fun τ l => τ.setLit (-l))

def setNegatedClauseUntil (τ : PPA) (C : IClause) (gen : Nat) : PPA :=
  C.foldl (init := τ) (fun τ l => τ.setLitUntil (-l) gen)

def setNegatedClauseFor (τ : PPA) (C : IClause) (extraBumps : Nat) : PPA :=
  C.foldl (init := τ) (fun τ l => τ.setLitFor (-l) extraBumps)

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
    τ.setNegatedClauseFor { data := l :: ls } bumps =
      (τ.setLitFor (-l) bumps).setNegatedClauseFor { data := ls } bumps := by
  simp_rw [setNegatedClauseFor, Array.foldl_cons]

@[simp]
theorem setNegatedClause_cons (τ : PPA) (l : ILit) (ls : List ILit) :
    τ.setNegatedClause { data := l :: ls } =
      (τ.setLit (-l)).setNegatedClause { data := ls } := by
  rw [setNegatedClause_eq_setNegatedClauseFor]
  exact setNegatedClauseFor_cons _ _ _ _

/-! ### Lemmas about `reset` -/

theorem lt_reset_generation (τ : PPA) : ∀ i ∈ τ.reset.assignment.data, i.natAbs < τ.reset.generation := by
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
      have : n ∈ τ.reset.assignment.data := by
        simp_rw [Array.get?_eq_getElem?, Array.getElem?_eq_data_get?, List.get?_eq_some] at hn
        have ⟨_, hn⟩ := hn
        rw [← hn]
        apply List.get_mem
      have := τ.lt_reset_generation n this
      linarith
    . rfl

@[simp]
theorem litValue?_reset (τ : PPA) (l : ILit) : (τ.reset).litValue? l = none := by
  simp [litValue?, varValue?_reset]

@[simp]
theorem toPropFun_reset (τ : PPA) : τ.reset.toPropFun = ⊤ := by
  ext; simp [satisfies_iff_vars]

/-! ### Lemmas about `setVar`, `setLit` -/

@[simp]
theorem varValue?_setVar (τ : PPA) (v : IVar) (b : Bool) : (τ.setVar v b).varValue? v = some b := by
  unfold varValue? setVar
  cases b <;> simp [Array.getElem?_setF, τ.generation.property]

@[simp]
theorem varValue?_setVar_of_ne {v v' : IVar} :
    v ≠ v' → ∀ (τ : PPA) (b : Bool), (τ.setVar v b).varValue? v' = τ.varValue? v' := by
  unfold varValue? setVar
  intro hNe
  simp [Array.getElem?_setF' _ _ _ (index_ne_iff.mpr hNe)]

@[simp]
theorem varValue?_setLit (τ : PPA) (l : ILit) : (τ.setLit l).varValue? (toVar l) = some (polarity l) := by
  simp [setLit, varValue?_setVar]

@[simp]
theorem litValue?_setLit (τ : PPA) (l : ILit) : (τ.setLit l).litValue? l = some true := by
  simp [litValue?, setLit, varValue?_setVar]

@[simp]
theorem varValue?_setLit_of_ne {l : ILit} {v : IVar} :
    toVar l ≠ v → ∀ (τ : PPA), (τ.setLit l).varValue? v = τ.varValue? v := by
  intro h
  simp [setLit, varValue?_setVar_of_ne h]

@[simp]
theorem litValue?_setLit_of_ne {l l' : ILit} :
    toVar l ≠ toVar l' → ∀ (τ : PPA), (τ.setLit l).litValue? l' = τ.litValue? l' := by
  intro h
  simp [litValue?, varValue?_setLit_of_ne h]

/-! ### `toPropFun` model -/

theorem toPropFun_setVar_lt_of_none {τ : PPA} {v : IVar} :
    τ.varValue? v = none → ∀ (b : Bool), (τ.setVar v b).toPropFun ≤ τ := by
  intro h b
  apply entails_ext.mpr
  intro σ hσ
  rw [satisfies_iff_vars] at hσ ⊢
  intro y b hy
  apply hσ
  rwa [varValue?_setVar_of_ne]
  intro hEq
  rw [hEq, hy] at h
  contradiction

theorem toPropFun_setLit_lt_of_none {τ : PPA} {l : ILit} :
    τ.litValue? l = none → (τ.setLit l).toPropFun ≤ τ := by
  intro
  simp_all only [litValue?, setLit, Option.map_eq_none', toPropFun_setVar_lt_of_none]

theorem toPropFun_setLit_lt (τ : PPA) (l : ILit) :
    (τ.setLit l).toPropFun ≤ l := by
  apply entails_ext.mpr
  intro σ hσ
  rw [satisfies_iff_lits] at hσ
  apply hσ
  apply litValue?_setLit

theorem lt_toPropFun_setLit (τ : PPA) (l : ILit) :
    τ.toPropFun ⊓ l ≤ (τ.setLit l) := by
  apply entails_ext.mpr
  intro σ hσ
  have ⟨hσ, hσ'⟩ := satisfies_conj.mp hσ
  rw [satisfies_iff_vars] at hσ ⊢
  intro x b hx
  by_cases h : toVar l = x
  . simp_all [setLit, LitVar.satisfies_iff]
  . apply hσ
    rwa [τ.varValue?_setLit_of_ne h] at hx

theorem toPropFun_setLit_of_none {τ : PPA} {l : ILit} :
    τ.litValue? l = none → (τ.setLit l).toPropFun = τ.toPropFun ⊓ l := by
  intro h
  refine le_antisymm ?_ (τ.lt_toPropFun_setLit l)
  simp [toPropFun_setLit_lt_of_none h, toPropFun_setLit_lt]

-- TODO: This spec isn't correct, and needs an assumption that τ and C don't overlap,
-- or that C isn't a tautology?
-- Or just write an updated setNegatedClause that evaluates the literals as they
-- come in and return a Bool or an option or something
theorem setNegatedClause_of_le {τ : PPA} {C : IClause} :
    τ.toPropFun ≤ C.toPropFun → τ.setNegatedClause C = τ.toPropFun ⊓ Cᶜ := by
  have ⟨C⟩ := C
  induction' C with l ls ih generalizing τ
  · simp
  · simp
    done
  done
#exit
@[simp]
theorem setNegatedClause_reset_toPropFun (τ : PPA) (C : IClause) :
    (τ.reset.setNegatedClause C).toPropFun = (C.toPropFun)ᶜ := by
  have ⟨C⟩ := C
  induction' C with l ls ih generalizing τ
  · simp [setNegatedClause]
  · rw [setNegatedClause, Array.foldl_eq_foldl_data]
    simp
    done

  done

#exit

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

theorem isSetFor_zero_iff {τ : PPA} {v : IVar} :
    isSetFor τ v 0 ↔ τ.varValue? v = none := by
  cases hv : τ.assignment[v.index]?
  <;> simp [isSetFor, varValue?, hv]
  · exact τ.generation.property
  · exact succ_le

theorem setVar_isSetFor (τ : PPA) (v : IVar) (b : Bool) : isSetFor (τ.setVar v b) v 1 := by
  simp [isSetFor, setVar]; cases b <;> simp

theorem setLit_isSetFor (τ : PPA) (l : ILit) : isSetFor (τ.setLit l) (toVar l) 1 :=
  setVar_isSetFor _ _ _

theorem setVarFor_isSetFor (τ : PPA) (v : IVar) (b : Bool) (extraBumps : Nat) :
    isSetFor (τ.setVarFor v b extraBumps) v (extraBumps + 1) := by
  simp [isSetFor, setVarFor]; cases b <;> simp
  · rw [← Int.neg_add, Int.natAbs_neg]
    have : Int.natAbs (extraBumps + τ.generation) = extraBumps + τ.generation := rfl
    rw [this, add_assoc, add_comm τ.generation.val 1, ← add_assoc, Nat.add_sub_cancel]
  · have : Int.natAbs (τ.generation + extraBumps) = τ.generation + extraBumps := rfl
    rw [this, add_comm τ.generation.val _, add_assoc, add_comm τ.generation.val 1, ← add_assoc, Nat.add_sub_cancel]

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

end isSetFor

/-! ## Tautology checking -/

/-- Check if the given clause is a tautology.
The current partial assignment is ignored,
and the returned assignment is unspecified. -/
def checkTauto (τ : PPA) (C : IClause) : PPA × { b : Bool // b ↔ C.toPropFun = ⊤ } :=
  go 0 ⟨τ.reset, by simp [Clause.toPropFun]⟩
where
  go (i : Nat) (τ : { τ : PPA // τ.toPropFunᶜ = Clause.toPropFun ⟨C.data.take i⟩ })
    : PPA × { b : Bool // b ↔ C.toPropFun = ⊤ } :=
  if hLt : i < C.size then
    let l := C[i]'hLt
    have hCl : Clause.toPropFun ⟨C.data.take (i+1)⟩ = Clause.toPropFun ⟨C.data.take i⟩ ⊔ l := by
      simp [List.take_succ, List.get?_eq_get hLt, Array.getElem_eq_data_get]
    match h : τ.val.litValue? l with
    | some true =>
      (τ.val, ⟨true, by
        have : τ.val.toPropFun ≤ l := litValue?_true_iff.mp h
        have : (↑l)ᶜ ≤ τ.val.toPropFunᶜ := compl_le_compl this
        have : (↑l)ᶜ ≤ C.toPropFun := by
          apply le_trans this
          rw [τ.property]
          apply C.toPropFun_take_lt
        have : l ≤ C.toPropFun := C.toPropFun_getElem_lt _
        have : ⊤ ≤ C.toPropFun := by
          rw [← sup_compl_eq_top (x := l.toPropFun)]
          apply sup_le <;> assumption
        simp only [top_le_iff.mp this]⟩)
    | some false =>
      go (i + 1) ⟨τ.val.setLit (-l), by
        have : (τ.val.setLit (-l)).toPropFun ≤ τ.val.toPropFun := by
          apply entails_ext.mpr
          intro σ hσ
          rw [satisfies_iff_vars] at hσ ⊢
          intro x b hx
          apply hσ
          by_cases hEq : toVar (-l) = x
          . aesop (add norm unfold litValue?, norm unfold setLit)
          . rwa [τ.val.varValue?_setLit_of_ne hEq]
        have := τ.val.toPropFun_setLit_lt (-l)
        have : (τ.val.setLit (-l)).toPropFun = τ.val.toPropFun ⊓ (-l).toPropFun := by
          refine le_antisymm ?_ (τ.val.lt_toPropFun_setLit _)
          simp_all only [le_inf_iff, and_self]
        simp [*, τ.property]⟩
    | none =>
      go (i + 1) ⟨τ.val.setLit (-l), by
        have : (τ.val.setLit (-l)).toPropFun = τ.val.toPropFun ⊓ (-l).toPropFun := by
          apply toPropFun_setLit_of_none
          simp [τ.val.litValue?_negate l, h]
        simp [*, τ.property]⟩
  else
    (τ.val, ⟨false, by
      simp only [false_iff]
      intro h
      apply τ.val.toPropFun_ne_bot
      have hEq := τ.property
      have : C.data.length ≤ i := by rw [not_lt] at hLt; exact hLt
      have that : C = { data := C.data } := rfl
      simp_rw [C.data.take_length_le this, ← that, h, compl_eq_top] at hEq
      assumption⟩)
termination_by go i τ => C.size - i

/-! ## Unit propagation -/

-- Cayden's alternate formulation of | extended
-- | extended      (l : ILit)
--                (τ' : PPA)
--                (h₁ : C.toPropFun ⊓ τ.toPropFun = τ'.toPropFun)
--                (h₂ : τ.litValue? l = none ∧ τ'.litValue? l = some true)

inductive UPResult (τ τ' : PPA) (C : IClause) where
  | contradiction (h : C.toPropFun ⊓ τ.toPropFun = ⊥)
  /-- Under `τ`, `C` became a unit clause `[l]`.
  The assignment was extended by that literal, i.e., `τ' = τ ⊓ l`. -/
  -- Note: I didn't prove that `C' = [l]`.
  | extended      (l : ILit) (hl : l ∈ C.data)
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
def propagateUnit (τ : PPA) (C : IClause) : (τ' : PPA) × UPResult τ τ' C :=
  go 0 none Option.all_none (by simp only [not_lt_zero', IsEmpty.forall_iff, implies_true])
where
  /-- If `unit? = some u`, then `u` is a literal in the clause that is not falsified by `τ`.
  It may therefore be the case that `C' = [u]` -/
  go (i : Nat) (unit? : Option ILit) (hUnit : unit?.all fun u => u ∈ C.data ∧ τ.litValue? u = none)
      (hLits : ∀ (j : Fin C.size), j.val < i → unit? = some C[j] ∨ τ.toPropFun ≤ (C[j].toPropFun)ᶜ) :
      (τ' : PPA) × UPResult τ τ' C :=
    if hi : i < C.size then
      let l := C[i]'hi
      match hl : τ.litValue? l with
      | some true => ⟨τ, .satisfied⟩
      | some false =>
        -- TODO: lots of duplication here
        go (i+1) unit? hUnit (by
          intro j hj
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ.mp hj) with hj | hj
          . exact hLits j hj
          . apply Or.inr
            apply litValue?_false_iff.mp
            simp [hj, hl])
      | none =>
        match hUnit : unit? with
        | .some u =>
          if hEq : u = l then
            go (i+1) (some l) (by simp [C.getElem_mem_data hi, hl]) (by
              intro j hj
              rcases Nat.lt_or_eq_of_le (Nat.lt_succ.mp hj) with hj | hj
              . exact hEq ▸ hLits j hj
              . apply Or.inl
                simp [hEq, hj])
          else
            ⟨τ, .notUnit⟩
        | .none =>
          go (i+1) (some l) (by simp [C.getElem_mem_data hi, hl]) (by
            intro j hj
            rcases Nat.lt_or_eq_of_le (Nat.lt_succ.mp hj) with hj | hj
            . apply Or.inr
              have := hLits j hj
              simpa using this
            . apply Or.inl
              simp [hj])
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
          have ⟨k, hk⟩ := Array.mem_data_iff.mp hl
          rw [not_lt] at hi
          have := hLits k (lt_of_lt_of_le k.is_lt hi)
          simp only [false_or] at this
          have := entails_ext.mp this _ hστ
          rw [PropFun.satisfies_neg] at this
          exact this (hk ▸ hσl))⟩
      | some u =>
        ⟨τ.setLit u, .extended u
          (by simp at hUnit; tauto)
          (by
            simp at hUnit
            simp [τ.toPropFun_setLit_of_none hUnit.right, inf_comm])
          (by
            apply entails_ext.mpr
            intro σ hσ
            have ⟨hστ, hσC⟩ := satisfies_conj.mp hσ
            have ⟨l, hl, hσl⟩ := Clause.satisfies_iff.mp hσC
            have ⟨i, hi⟩ := Array.mem_data_iff.mp hl
            have := i.is_lt
            have := hLits i (by linarith)
            rcases this with hEq | hτl
            . cases hEq
              rwa [hi]
            . exfalso
              exact (satisfies_neg.mp <| entails_ext.mp hτl _ hστ) (hi ▸ hσl))⟩
  termination_by go i _ _ _ => C.size - i

-- Cayden's alternate implementation of unit propagation (TODO: Compare for efficiency)

section monadic

-- Because unit prop might just want the result of C against τ, and no modify τ,
-- the updated assignment is not returned in the unit case.
inductive MUPResult where
  | falsified
  | satisfied
  | unit (l : ILit)
  | multipleUnassignedLiterals

inductive MUPDone where
  | satisfied
  | multipleUnassignedLiterals

open ResultT MUPResult MUPDone

abbrev UPBox := ResultT MUPDone (Option ILit)

def pevalUP (τ : PPA) (unit? : Option ILit) (l : ILit) : UPBox :=
  match τ.litValue? l with
  | some true => done .satisfied
  | some false => ok unit?
  | none =>
    match unit? with
    | none => ok l
    | some u =>
      if u = l then ok unit?
      -- Assume tautology cannot occur in clause, so two unassiged literals exits early
      else done .multipleUnassignedLiterals

def foldUP (τ : PPA) (C : IClause) := C.foldlM (pevalUP τ) none

def unitProp (τ : PPA) (C : IClause) : MUPResult :=
  match foldUP τ C with
  | ok none => .falsified
  | ok (some lit) => .unit lit
  | done .satisfied => .satisfied
  | done .multipleUnassignedLiterals => .multipleUnassignedLiterals

def motive_fn (τ : PPA) (C : IClause) : ℕ → Option ILit → Prop
  | idx, none => ∀ ⦃i : Fin C.size⦄, i < idx → τ.litValue? C[i] = some false
  | idx, some lit => lit ∈ C.data ∧ τ.litValue? lit = none ∧
      (∀ ⦃j : Fin C.size⦄, j < idx → C[j] ≠ lit → τ.litValue? C[j] = some false)

theorem SatisfiesM_UP (τ : PPA) (C : IClause) :
    SatisfiesM (fun
      -- If there are no unassigned literals, then all should be false
      | none => ∀ l ∈ C.data, τ.litValue? l = some false
      | some lit => lit ∈ C.data ∧ τ.litValue? lit = none ∧
          (∀ l ∈ C.data, l ≠ lit → τ.litValue? l = some false)) (foldUP τ C) := by
  have := C.SatisfiesM_foldlM (init := (none : Option ILit)) (f := pevalUP τ)
    (motive := motive_fn τ C)
    (h0 := by simp [motive_fn]) -- Why do I have to define it right above? Putting it inline with (motive :=) had sorryAx problems
    (hf := by
      unfold motive_fn
      simp only [SatisfiesM_ResultT_eq, getElem_fin]
      intro i box ih
        -- Cayden question: Is this proof more compact if I use pattern-matching with intro?
      intro
      | none, hbox =>
        intro j hj
        unfold pevalUP at hbox
        cases h_tau : τ.litValue? C[i.val] with
        | none =>
          simp [h_tau] at hbox
          cases h_box : box with
          | none => simp [h_box] at hbox
          | some lit => by_cases h_lit : lit = C[i.val] <;> simp [h_box, h_lit] at hbox
        | some b =>
          cases h_box : box with
          | none =>
            subst h_box
            rcases lt_or_eq_of_le (le_of_lt_succ hj) with (h | h)
            · exact ih h
            · cases b
              · replace h := Fin.ext h; subst h; exact h_tau
              · simp [h_tau] at hbox
          | some lit => by_cases h_lit : lit = C[i.val] <;> cases b <;> simp [h_tau, h_box, h_lit] at hbox
      | some lit, hbox =>
        unfold pevalUP at hbox
        cases h_tau : τ.litValue? C[i.val] with
        | none =>
          simp [h_tau] at hbox
          cases h_box : box with
          | none =>
            subst h_box
            simp at hbox
            use Array.mem_data_iff.mpr ⟨i, hbox⟩, hbox ▸ h_tau
            intro j hj₁ hj₂
            rcases lt_or_eq_of_le (le_of_lt_succ hj₁) with (h | h)
            · exact ih h
            · simp at ih
              replace h := Fin.ext h; subst h; rw [hbox] at hj₂; contradiction
          | some l =>
            subst h_box
            by_cases hl : l = C[i.val]
            · simp [hl] at hbox
              rw [hbox] at hl
              subst hl
              rcases ih with ⟨hl₁, hl₂, ih⟩
              use hl₁, hl₂
              intro j hj₁ hj₂
              rcases lt_or_eq_of_le (le_of_lt_succ hj₁) with (h | h)
              · exact ih h hj₂
              · replace h := Fin.ext h; subst h; rw [hbox] at hj₂; contradiction
            · simp [hl] at hbox
        | some b =>
          cases b
          · simp [h_tau] at hbox
            subst hbox
            rcases ih with ⟨hlit₁, hlit₂, ih⟩
            use hlit₁, hlit₂
            intro j hj₁ hj₂
            rcases lt_or_eq_of_le (le_of_lt_succ hj₁) with (h | h)
            · exact ih h hj₂
            · replace h := Fin.ext h; subst h; exact h_tau
          · simp [h_tau] at hbox)
  apply SatisfiesM.imp this
  intro
  | none =>
    intro h l hl
    rcases Array.mem_data_iff.mp hl with ⟨i, rfl⟩
    exact h i.isLt
  | some lit =>
    simp [motive_fn]
    intro hlit₁ hlit₂ ih
    use hlit₁, hlit₂
    intro l hl₁ hl₂
    rcases Array.mem_data_iff.mp hl₁ with ⟨i, rfl⟩
    exact ih hl₂

-- Cayden TODO/Q: Allow for [pattern_match] on ResultT? What is [unbox]?
-- Cayden Q: when aesop can't solve something, why does [aesop?] not give anything?
theorem contradiction_of_UP_falsified {τ : PPA} {C : IClause} :
    τ.unitProp C = .falsified → τ.toPropFun ⊓ C.toPropFun ≤ ⊥ := by
  unfold unitProp
  intro h_falsified
  split at h_falsified
  <;> try simp at h_falsified
  clear h_falsified
  rename (foldUP τ C = ok none) => h
  refine entails_ext.mpr fun τ' hτ' => ?_
  rw [satisfies_conj] at hτ'
  rcases hτ' with ⟨hττ', hCτ'⟩
  have ⟨lit, hlit, hτ'lit⟩ := Clause.satisfies_iff.mp hCτ'
  have hlv := SatisfiesM_ResultT_eq.mp (SatisfiesM_UP τ C) none h lit hlit
  clear h hCτ' hlit
  have := satisfies_iff_vars.mp hττ'
  replace hτ'lit := LitVar.satisfies_iff.mp hτ'lit
  cases hpol : polarity lit
  <;> simp [hpol] at hτ'lit
  <;> simp [litValue?, hpol] at hlv
  <;> rw [this hlv] at hτ'lit
  <;> contradiction

-- Is it better to say that ¬(τ ≤ l), or that τ.litValue? l = none?
theorem extended_of_UP_unit {τ : PPA} {C : IClause} {l : ILit} :
    τ.unitProp C = .unit l →
      C.toPropFun ⊓ τ.toPropFun ≤ l.toPropFun
      ∧ ¬(τ.toPropFun ≤ l.toPropFun) -- Cayden: see litValue?_none_iff
      ∧ ¬(τ.toPropFun ≤ l.toPropFunᶜ) := by
  unfold unitProp
  intro h_unit
  split at h_unit
  <;> try simp at h_unit
  rename ILit => lit; subst h_unit
  rename (foldUP τ C = ok (some lit)) => h
  have hlv := SatisfiesM_ResultT_eq.mp (SatisfiesM_UP τ C) (some lit) h
  clear h
  rcases hlv with ⟨hlit, hτlit, ih⟩
  constructor
  · refine entails_ext.mpr fun τ' hτ' => ?_
    rw [satisfies_conj] at hτ'; rcases hτ' with ⟨hCτ', hττ'⟩
    rw [satisfies_iff_lits] at hττ'
    rw [Clause.satisfies_iff] at hCτ'; rcases hCτ' with ⟨m, hm, hmτ'⟩
    by_cases heq : m = lit
    · subst heq; exact hmτ'
    · replace ih := ih _ hm heq
      have := litValue?_negate τ m
      simp only [ih, Option.map_some', Bool.not_false] at this
      have := hττ' this
      simp at this
      exact absurd hmτ' this
  · exact litValue?_none_iff.mp hτlit

#exit

/-
theorem SatisfiesM_foldUPs (τ : PPA) (L : Array IClause) :
    SatisfiesM (fun τ' => (clauses_to_PropFun L) ⊓ τ ≤ τ') (foldUPs τ L) := by
  have := L.SatisfiesM_foldlM (init := (τ : PPA)) (f := applyUPHint)
    (motive := fun idx τ' => (clauses_to_PropFun (L.take idx)) ⊓ τ ≤ τ')
  done
-/

/-
def motive_fn (τ : PPA) (C : IClause) : ℕ → Option ILit → Prop
  | idx, none => ∀ ⦃i : Fin C.size⦄, i < idx → τ.litValue? C[i] = some false
  | idx, some lit => lit ∈ C.data ∧ τ.litValue? lit = none ∧
      (∀ ⦃j : Fin C.size⦄, j < idx → C[j] ≠ lit → τ.litValue? C[j] = some false)

    SatisfiesM (fun
      -- If there are no unassigned literals, then all should be false
      | none => ∀ l ∈ C.data, τ.litValue? l = some false
      | some lit => lit ∈ C.data ∧ τ.litValue? lit = none ∧
          (∀ l ∈ C.data, l ≠ lit → τ.litValue? l = some false)) (foldUP τ C) := by
  have := C.SatisfiesM_foldlM (init := (none : Option ILit)) (f := pevalUP τ)
    (motive := motive_fn τ C)
    (h0 := by simp [motive_fn])
-/

theorem SatisfiesM_foldUPs (τ : PPA) (L : Array IClause) :
    SatisfiesM (fun τ' => (clauses_to_PropFun L) ⊓ τ ≤ τ') (foldUPs τ L) := by
  have := L.SatisfiesM_foldlM (init := (τ : PPA)) (f := applyUPHint)
    (motive := fun idx τ' => ∀ ⦃i : Fin L.size⦄, i < idx → L[i].toPropFun ⊓ τ ≤ τ')
    (h0 := by
      sorry
      done)
    (hf := by
      sorry
      done)
  done

#exit

theorem foldUPs_correct {τ : PPA} {L : List IClause} :
    foldUPs τ L = done true → (clauses_to_PropFun L) ⊓ τ = ⊥ := by
  induction' L with C CS ih generalizing τ
  · simp [foldUPs]
  · intro h_UP
    rw [foldUPs] at h_UP
    rw [List.foldlM_eq_foldl] at h_UP
    simp at h_UP

    --simp [List.foldlM_cons, applyUPHint] at h_UP
    --split at h_UP <;> try simp at h_UP

    done
  done

#exit

theorem unit_of_foldUPs_cons_ok {τ τ' : PPA} {C : IClause} {L : List IClause} :
    foldUPs τ (C :: L) = ok τ' → ∃ (l : ILit) (τ'' : PPA), τ.unitProp C = unit l τ'' := by
  intro h
  rw [foldUPs, List.foldlM_cons, applyUPHint] at h
  cases hτ : τ.unitProp C <;> simp [hτ] at h <;> try contradiction
  exact ⟨_, _, rfl⟩

theorem foldUPs_cons_of_falsified {τ : PPA} {C : IClause} {L : List IClause} :
    τ.unitProp C = .falsified → foldUPs τ (C :: L) = done true := by
  intro h; simp [foldUPs, List.foldlM_cons, applyUPHint, h]; rfl

theorem foldUPs_ok {τ τ' : PPA} {L : List IClause} :
    foldUPs τ L = ok τ' → (clauses_to_PropFun L) ⊓ τ ≤ τ' := by
  induction' L with C CS ih generalizing τ
  · simp; rintro rfl; exact Eq.ge rfl
  · intro h
    rw [clauses_to_PropFun_cons, inf_comm, ← inf_assoc, inf_comm]
    rcases unit_of_foldUPs_cons_ok h with ⟨l, σ, hτ⟩
    rw [foldUPs_cons_of_unit hτ] at h
    apply le_trans _ (ih h)
    have := (extended_of_UP_unit hτ).1
    rw [inf_comm] at this
    exact inf_le_inf_left _ this

theorem foldUPs_true {τ : PPA} {L : List IClause} :
    foldUPs τ L = done true → (clauses_to_PropFun L) ⊓ τ ≤ ⊥ := by
  induction' L with C CS ih generalizing τ
  · simp
  · intro h
    rw [foldUPs, List.foldlM_cons, applyUPHint] at h
    split at h <;> try injection h <;> try contradiction
    · rename unitProp τ C = falsified => heq
      rw [clauses_to_PropFun_cons, inf_comm, ← inf_assoc]
      exact le_trans inf_le_left (contradiction_of_UP_falsified heq)
    · rename ILit => l
      rename PPA => τ'
      rename unitProp τ C = unit _ _ => heq
      have := (extended_of_UP_unit heq).1
      rw [inf_comm] at this
      rw [clauses_to_PropFun_cons, inf_comm, ← inf_assoc, inf_comm]
      apply le_trans (inf_le_inf_left (clauses_to_PropFun CS) this)
      apply ih
      rw [← h]
      rfl

#exit
    --(clauses_to_PropFun (C :: L)) ⊓ τ = ⊥ := by


end monadic

end PPA
