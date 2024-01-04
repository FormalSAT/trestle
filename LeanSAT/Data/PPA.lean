import Mathlib.Data.Nat.Basic

import LeanSAT.Data.Cnf
import LeanSAT.Data.ICnf
import LeanSAT.AuxDefs
import LeanSAT.Upstream.ToStd

open LeanSAT LeanSAT.Model Nat

/-- A Persistent Partial Assignment of truth values to propositional variables.

Assuming the linearity restriction (see below) is met,
the PPA provides a fast representation of partial assignments.
The PPA is allocation-free as long as you initialize it
with the actual maximum variable index in `PPA.new`.
The PPA provides functions for unit propagation and tautology checking.

The PPA is meant to be used persistently and linearly,
i.e., you should keep around exactly one copy of this structure.
Note that ensuring linearity in large functions can be tricky,
especially when `do` notation is used.
The only reliable method at the moment
is to look at the dynamic behavior in a profiler
and ensure that PPA code does not spend lots of time in `lean_copy_expand_array`. -/
structure PPA where
  assignment : Array Int
  /-- The generation counter is used to avoid clearing the assignment array
  when the assignment is reset.
  Instead, we just bump the counter and interpret values in the array
  below the counter as unassigned. -/
  generation : { g : Nat // 0 < g }
  /-- The maximum absolute value of any entry in `assignments`. -/
  maxGen : Nat
  le_maxGen : ∀ g ∈ assignment.data, g.natAbs ≤ maxGen

instance : ToString PPA where
  toString τ := String.intercalate " ∧ "
    (τ.assignment.foldl (init := []) (f := fun acc a => s!"{a}" :: acc))

/-! ## Reading values from the PPA -/

namespace PPA
open LitVar PropFun

@[reducible] def size (τ : PPA) : Nat := τ.assignment.size

def varValue? (τ : PPA) (v : IVar) : Option Bool :=
  match τ.assignment.get? (v - 1) with
  | none => none
  | some n =>
    if τ.generation.val ≤ n.natAbs then
      some (0 < n)
    else
      none

  -- Cayden: Alternative definition that uses a let, not a match:
  --let v := τ.assignment.getD ((toVar l).val - 1) 0
  --if τ.generation ≤ v.natAbs then
  --  some <| xor (v < 0) (polarity l)
  --else none

/-- The value of the given literal in the current assignment, if assigned.
Otherwise `none`. -/
def litValue? (τ : PPA) (l : ILit) : Option Bool :=
  τ.varValue? (toVar l) |>.map (fun b => xor (!b) (polarity l))

/-! ### Lemmas about `litValue?`, `varValue?` -/

theorem litValue?_negate (τ : PPA) (l : ILit) :
    τ.litValue? (-l) = (τ.litValue? l).map Bool.not := by
  aesop (add norm unfold litValue?)

theorem litValue?_eq_varValue?_none {τ : PPA} {l : ILit} :
    τ.litValue? l = none → τ.varValue? (toVar l) = none := by
  aesop (add norm unfold litValue?)

theorem litValue?_eq_varValue?_some {τ : PPA} {l : ILit} {b : Bool} :
    τ.litValue? l = some b → τ.varValue? (toVar l) = xor (!b) (polarity l) := by
  aesop (add norm unfold litValue?)

theorem lt_size_of_varValue?_eq_some {τ : PPA} {x : IVar} {b : Bool} :
    τ.varValue? x = some b → x - 1 < τ.size := by
  unfold varValue?
  split <;> simp
  intros
  sorry -- should be apply Array.lt_size_of_get?_eq_some (or Array.some_lemma)

theorem lt_size_of_litValue?_eq_some {τ : PPA} {l : ILit} {b : Bool} :
    τ.litValue? l = some b → ((toVar l) - 1) < τ.size := by
  simp only [litValue?, Option.map_eq_some']
  intro ⟨b, h⟩
  exact lt_size_of_varValue?_eq_some h.1

/-! ### `toPropFun` model -/

def varToPropFun (τ : PPA) (x : IVar) : PropFun IVar :=
  τ.varValue? x |>.map (if · then .var x else (.var x)ᶜ) |>.getD ⊤

def idxToPropFun (τ : PPA) (i : Fin τ.size) : PropFun IVar :=
  τ.varToPropFun ⟨i + 1, succ_pos _⟩

/-- We model the `PPA` as the conjunction of all its literals.
Note that we cannot fully model the `PPA` as just one `PropAssignment`
because those are required to be total. -/
/- NOTE: Possible alternative models:
- A `PropSubst` which acts as the identity on all variables not in the PPA.
  This has a natural notion of semantic entailment: substituting yields ⊤.
- A finite set of literals. This however doesn't seem to have a natural entailment;
  there are two, treating the set as either big conj or big disj.
  Furthermore a set can be inconsistent/tautological
  by containing complementary literals,
  and this case has to be handled in such a model,
  whereas the PPA cannot.
  The same issue appears with PropFun; see `toPropFun_ne_bot`. -/
def toPropFun (τ : PPA) : PropFun IVar :=
  Fin.foldl τ.size (· ⊓ τ.idxToPropFun ·) ⊤

theorem satisfies_iff {τ : PPA} {σ : PropAssignment IVar} :
    σ ⊨ τ.toPropFun ↔ ∀ (i : Fin τ.size), σ ⊨ τ.idxToPropFun i := by
  constructor
  . intro hσ i
    have ⟨ϕ, hϕ⟩ := Fin.foldl_of_comm τ.size (· ⊓ τ.idxToPropFun ·) ⊤ i (by intros; simp; ac_rfl)
    rw [toPropFun, hϕ] at hσ
    simp_all
  . intro h
    unfold toPropFun
    apply Fin.foldl_induction' (hInit := satisfies_tr)
    intro ϕ i hϕ
    simp [hϕ, h i]

theorem satisfies_iff_vars {τ : PPA} {σ : PropAssignment IVar} :
    σ ⊨ τ.toPropFun ↔ ∀ x b, τ.varValue? x = some b → σ x = b := by
  constructor
  . intro h x b h'
    have := lt_size_of_varValue?_eq_some h'
    let i : Fin τ.size := ⟨Subtype.val x - 1, this⟩
    have h := satisfies_iff.mp h i
    dsimp [idxToPropFun, varToPropFun] at h
    have : 1 ≤ Subtype.val x := x.property
    simp_rw [Nat.sub_add_cancel this, Subtype.eta, h'] at h
    simp only [Option.map_some', Option.getD_some] at h
    cases b <;> simp_all
  . intro h
    apply satisfies_iff.mpr
    intro i
    unfold idxToPropFun varToPropFun
    cases' h' : (varValue? τ _) with b
    . simp
    . have := h _ _ h'
      cases b <;> simp_all

theorem satisfies_iff_lits {τ : PPA} {σ : PropAssignment IVar} :
    σ ⊨ τ.toPropFun ↔ ∀ l, τ.litValue? l = some true → σ ⊨ LitVar.toPropFun l := by
  simp_rw [LitVar.satisfies_iff, litValue?]
  constructor
  . intro h l h'
    apply satisfies_iff_vars.mp h
    simp_all
  . intro h
    apply satisfies_iff_vars.mpr
    intro x b
    have := h (mkPos x)
    have := h (mkNeg x)
    cases b <;> simp_all

/-- A satisfying assignment for `toPropFun`.
This is an arbitrary extension of `τ` from its domain to all of `IVar`. -/
def toSatAssignment (τ : PPA) : PropAssignment IVar :=
  fun x => τ.varValue? x |>.getD false

theorem toSatAssignment_satisfies (τ : PPA) : τ.toSatAssignment ⊨ τ.toPropFun := by
  aesop (add norm unfold toSatAssignment, norm satisfies_iff_vars)

theorem toPropFun_ne_bot (τ : PPA) : τ.toPropFun ≠ ⊥ := by
  intro
  have := τ.toSatAssignment_satisfies
  simp_all only [not_satisfies_fls]

theorem varValue?_true (τ : PPA) (x : IVar) :
    τ.varValue? x = some true → τ.toPropFun ≤ .var x := by
  intro h
  apply PropFun.entails_ext.mpr
  simp_all [satisfies_iff_vars]

theorem varValue?_false (τ : PPA) (x : IVar) :
    τ.varValue? x = some false → τ.toPropFun ≤ (.var x)ᶜ := by
  intro h
  apply PropFun.entails_ext.mpr
  simp_all [satisfies_iff_vars]

theorem not_mem_semVars_of_varValue?_none (τ : PPA) (x : IVar) :
    τ.varValue? x = none → x ∉ τ.toPropFun.semVars := by
  rw [not_mem_semVars]
  intro hx σ b hσ
  rw [satisfies_iff_vars] at hσ ⊢
  intro y b hy
  have : x ≠ y := fun h => by rw [h, hy] at hx; contradiction
  rw [PropAssignment.set_get_of_ne _ _ this]
  apply hσ y b hy

theorem varValue?_none (τ : PPA) (x : IVar) :
    τ.varValue? x = none → ¬(τ.toPropFun ≤ .var x) := by
  intro hNone hLt
  let σ := τ.toSatAssignment.set x false
  have : σ.agreeOn τ.toPropFun.semVars τ.toSatAssignment := fun y hMem =>
    have : x ≠ y := fun h => τ.not_mem_semVars_of_varValue?_none x hNone (h ▸ hMem)
    PropAssignment.set_get_of_ne _ _ this
  have hσ : σ ⊨ τ.toPropFun := (agreeOn_semVars this).mpr τ.toSatAssignment_satisfies
  have : σ ⊭ .var x := by
    simp only [satisfies_var, PropAssignment.set_get, not_false_eq_true]
  exact this (entails_ext.mp hLt σ hσ)

theorem varValue?_none' (τ : PPA) (x : IVar) :
    τ.varValue? x = none → ¬(τ.toPropFun ≤ (.var x)ᶜ) := by
  intro hNone hLt
  let σ := τ.toSatAssignment.set x true
  have : σ.agreeOn τ.toPropFun.semVars τ.toSatAssignment := fun y hMem =>
    have : x ≠ y := fun h => τ.not_mem_semVars_of_varValue?_none x hNone (h ▸ hMem)
    PropAssignment.set_get_of_ne _ _ this
  have hσ : σ ⊨ τ.toPropFun := (agreeOn_semVars this).mpr τ.toSatAssignment_satisfies
  have : σ ⊭ (.var x)ᶜ := by
    simp only [PropFun.satisfies_neg, satisfies_var, PropAssignment.set_get, not_true_eq_false,
      not_false_eq_true]
  exact this (entails_ext.mp hLt σ hσ)

theorem litValue?_true (τ : PPA) (l : ILit) :
    τ.litValue? l = some true → τ.toPropFun ≤ LitVar.toPropFun l := by
  simp [litValue?, LitVar.toPropFun]
  cases polarity l <;>
    simp (config := {contextual := true}) [varValue?_false, varValue?_true]

theorem litValue?_false (τ : PPA) (l : ILit) :
    τ.litValue? l = some false → τ.toPropFun ≤ (LitVar.toPropFun l)ᶜ := by
  simp [litValue?, LitVar.toPropFun]
  cases polarity l <;>
    simp (config := {contextual := true}) [varValue?_false, varValue?_true]

theorem litValue?_none (τ : PPA) (l : ILit) :
    τ.litValue? l = none → ¬(τ.toPropFun ≤ LitVar.toPropFun l) := by
  simp [litValue?, LitVar.toPropFun]
  cases (polarity l) <;>
    simp (config := {contextual := true}) [varValue?_none, varValue?_none']

end PPA

-- ?? folded into the `PPA` structure for now (forever?)
--structure PPA.WF (ppa : PPA) where
  -- hGen: 0 < generation
  -- hMaxVal : ∀ x ∈ assignment, x.natAbs ≤ maxVal

/-! ## Setting values in the PPA -/

namespace PPA
  open LitVar PropFun

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
  def setVar (τ : PPA) (x : IVar) (b : Bool) : PPA :=
    let v : Int := if b then τ.generation else -τ.generation
    { τ with
      assignment := τ.assignment.setF (x - 1) v 0
      maxGen := Nat.max τ.maxGen τ.generation
      le_maxGen := setVar_le_maxGen τ (x - 1) b τ.generation
    }

  /-- Set the given literal to `true` for the current generation. -/
  def setLit (τ : PPA) (l : ILit) : PPA :=
    τ.setVar (toVar l) (polarity l)

  /-- Set the given variable to `b` for all generations until `gen`. -/
  def setVarUntil (τ : PPA) (x : IVar) (b : Bool) (gen : Nat) : PPA :=
    let v : Int := if b then gen else -gen
    { τ with
      assignment := τ.assignment.setF (x - 1) v 0
      maxGen := Nat.max τ.maxGen gen
      le_maxGen := setVar_le_maxGen τ (x - 1) b gen
    }

  /-- Set the given literal to `true` for all generations until `gen`. -/
  def setLitUntil (τ : PPA) (l : ILit) (gen : Nat) : PPA :=
    τ.setVarUntil (toVar l) (polarity l) gen

  /-- Set `l ↦ ⊥` for each `l ∈ C` and leave the rest of the assignment untouched.
  If the current assignment contains literals appearing in `C`, they will be overwritten. -/
  def setNegatedClause (τ : PPA) (C : IClause) : PPA :=
    C.foldl (init := τ) (fun τ l => τ.setLit (-l))

  def setNegatedClauseUntil (τ : PPA) (C : IClause) (gen : Nat) : PPA :=
    C.foldl (init := τ) (fun τ l => τ.setLitUntil (-l) gen)

  /-! ### Lemmas about `reset` -/

  theorem lt_reset_generation (τ : PPA) : ∀ i ∈ τ.reset.assignment.data, i.natAbs < τ.reset.generation := by
    dsimp [reset]
    intro i h
    have := τ.le_maxGen i h
    linarith

  @[simp]
  theorem varValue?_reset (τ : PPA) (x : IVar) : τ.reset.varValue? x = none := by
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
  theorem varValue?_setVar (τ : PPA) (x : IVar) (b : Bool) : (τ.setVar x b).varValue? x = some b := by
    unfold varValue? setVar
    cases b <;> simp [Array.getElem?_setF, τ.generation.property]

  @[simp]
  theorem varValue?_setVar_of_ne (τ : PPA) {x x' : IVar} (b : Bool) :
      x ≠ x' → (τ.setVar x b).varValue? x' = τ.varValue? x' := by
    unfold varValue? setVar
    intro hNe
    have : x.val - 1 ≠ x'.val - 1 := by
      intro h
      have hx : 1 ≤ x.val := by cases x; assumption
      have hx' : 1 ≤ x'.val := by cases x'; assumption
      have : x.val - 1 + 1 = x'.val - 1 + 1 := by simp_rw [h]
      rw [Nat.sub_add_cancel hx, Nat.sub_add_cancel hx'] at this
      exact hNe (PNat.coe_inj.mp this)
    simp [Array.getElem?_setF' _ _ _ this]

  @[simp]
  theorem varValue?_setLit (τ : PPA) (l : ILit) : (τ.setLit l).varValue? (toVar l) = some (polarity l) := by
    simp [setLit, varValue?_setVar]

  @[simp]
  theorem litValue?_setLit (τ : PPA) (l : ILit) : (τ.setLit l).litValue? l = some true := by
    simp [litValue?, setLit, varValue?_setVar]

  @[simp]
  theorem varValue?_setLit_of_ne (τ : PPA) (l : ILit) (x : IVar) :
      toVar l ≠ x → (τ.setLit l).varValue? x = τ.varValue? x := by
    intro h
    simp [setLit, varValue?_setVar_of_ne _ _ h]

  @[simp]
  theorem litValue?_setLit_of_ne (τ : PPA) (l l' : ILit) :
      toVar l ≠ toVar l' → (τ.setLit l).litValue? l' = τ.litValue? l' := by
    intro h
    simp [litValue?, varValue?_setLit_of_ne _ _ _ h]

  /-! ### `toPropFun` model -/

  theorem toPropFun_setVar_lt_of_none (τ : PPA) (x : IVar) (b : Bool) :
      τ.varValue? x = none → (τ.setVar x b).toPropFun ≤ τ.toPropFun := by
    intro h
    apply entails_ext.mpr
    intro σ hσ
    rw [satisfies_iff_vars] at hσ ⊢
    intro y b hy
    apply hσ
    rwa [varValue?_setVar_of_ne]
    intro hEq
    rw [hEq, hy] at h
    contradiction

  theorem toPropFun_setLit_lt_of_none (τ : PPA) (l : ILit) :
      τ.litValue? l = none → (τ.setLit l).toPropFun ≤ τ.toPropFun := by
    intro
    simp_all only [litValue?, setLit, Option.map_eq_none', toPropFun_setVar_lt_of_none]

  theorem toPropFun_setLit_lt (τ : PPA) (l : ILit) :
      (τ.setLit l).toPropFun ≤ LitVar.toPropFun l := by
    apply entails_ext.mpr
    intro σ hσ
    rw [satisfies_iff_lits] at hσ
    apply hσ
    apply litValue?_setLit

  theorem lt_toPropFun_setLit (τ : PPA) (l : ILit) :
      τ.toPropFun ⊓ LitVar.toPropFun l ≤ (τ.setLit l).toPropFun := by
    apply entails_ext.mpr
    intro σ hσ
    have ⟨hσ, hσ'⟩ := satisfies_conj.mp hσ
    rw [satisfies_iff_vars] at hσ ⊢
    intro x b hx
    by_cases h : toVar l = x
    . simp_all [setLit, LitVar.satisfies_iff]
    . apply hσ
      rwa [τ.varValue?_setLit_of_ne _ _ h] at hx

  theorem toPropFun_setLit_of_none (τ : PPA) (l : ILit) :
      τ.litValue? l = none → (τ.setLit l).toPropFun = τ.toPropFun ⊓ LitVar.toPropFun l := by
    intro h
    refine le_antisymm ?_ (τ.lt_toPropFun_setLit l)
    simp [toPropFun_setLit_lt_of_none _ _ h, toPropFun_setLit_lt]

  /-! ## Lemmas about `setNegatedClause` -/

  @[simp]
  theorem toPropFun_reset_setNegatedClause (τ : PPA) (C : IClause) :
      -- NOTE: We only get an equality if `C.toPropFun ≠ ⊤`.
      C.toPropFunᶜ ≤ (τ.reset.setNegatedClause C).toPropFun := by
    suffices (Clause.toPropFun { data := C.data.take C.size : IClause })ᶜ ≤ (τ.reset.setNegatedClause C).toPropFun by
      simpa using this
    unfold setNegatedClause
    apply Array.foldl_induction
      (motive := fun n acc => (Clause.toPropFun { data := C.data.take n : IClause })ᶜ ≤ PPA.toPropFun acc)
    . simp [Clause.toPropFun]
    . intro i τ ih
      refine le_trans (le_inf_iff.mpr ?_) (τ.lt_toPropFun_setLit (-C[i]))
      simp only [List.take_succ, Clause.of_append, Clause.toPropFun_append, compl_sup]
      constructor
      . exact inf_le_of_left_le ih
      . apply inf_le_of_right_le
        simp [List.get?_eq_get, Array.getElem_eq_data_get]

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
      have hCl : Clause.toPropFun ⟨C.data.take (i+1)⟩ = Clause.toPropFun ⟨C.data.take i⟩ ⊔ LitVar.toPropFun l := by
        simp [List.take_succ, List.get?_eq_get hLt, Array.getElem_eq_data_get]
      match h : τ.val.litValue? l with
      | some true =>
        (τ.val, ⟨true, by
          have : τ.val.toPropFun ≤ LitVar.toPropFun l := τ.val.litValue?_true l h
          have : (LitVar.toPropFun l)ᶜ ≤ τ.val.toPropFunᶜ := compl_le_compl this
          have : (LitVar.toPropFun l)ᶜ ≤ C.toPropFun := by
            apply le_trans this
            rw [τ.property]
            apply C.toPropFun_take_lt
          have : LitVar.toPropFun l ≤ C.toPropFun := C.toPropFun_getElem_lt i _
          have : ⊤ ≤ C.toPropFun := by
            rw [← sup_compl_eq_top (x := LitVar.toPropFun l)]
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
            . rwa [τ.val.varValue?_setLit_of_ne _ _ hEq]
          have := τ.val.toPropFun_setLit_lt (-l)
          have : (τ.val.setLit (-l)).toPropFun = τ.val.toPropFun ⊓ LitVar.toPropFun (-l) := by
            refine le_antisymm ?_ (τ.val.lt_toPropFun_setLit _)
            simp_all only [le_inf_iff, and_self]
          simp [*, τ.property]⟩
      | none =>
        go (i + 1) ⟨τ.val.setLit (-l), by
          have : (τ.val.setLit (-l)).toPropFun = τ.val.toPropFun ⊓ LitVar.toPropFun (-l) := by
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

  inductive UPResult (τ τ' : PPA) (C : IClause) where
    | contradiction (h : C.toPropFun ⊓ τ.toPropFun = ⊥)
    /-- Under `τ`, `C` became a unit clause `[l]`.
    The assignment was extended by that literal, i.e., `τ' = τ ⊓ l`. -/
    -- Note: I didn't prove that `C' = [l]`.
    | extended      (l : ILit) (hl : l ∈ C.data)
                    (h₁ : τ'.toPropFun = LitVar.toPropFun l ⊓ τ.toPropFun)
                    (h₂ : τ.toPropFun ⊓ C.toPropFun ≤ LitVar.toPropFun l)
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
        (hLits : ∀ (j : Fin C.size), j.val < i → unit? = some C[j] ∨ τ.toPropFun ≤ (LitVar.toPropFun C[j])ᶜ) :
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
              apply litValue?_false
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
              simp [τ.toPropFun_setLit_of_none u hUnit.right, inf_comm])
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

end PPA
