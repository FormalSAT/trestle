import LeanSAT.Data.Cnf
import LeanSAT.Data.ICnf
import LeanSAT.AuxDefs
import LeanSAT.Upstream.ToStd
import Mathlib.Data.Nat.Basic

open LeanSAT LeanSAT.Model Nat

/-- A persistent partial assignment of truth values to propositional variables.

It is meant to be kept around persistently and used linearly.
Assuming these restrictions are met,
the structure provides a fast and allocation-free representation
of partial assignments.
It provides functions for unit propagation and tautology checking. -/
structure PPA where
  assignment : Array Int
  /-- The generation counter is used to avoid clearing the assignment array.
  Instead, we just bump the counter and interpret values in the array
  below the counter as unassigned. -/
  generation : { g : Nat // 0 < g }
  /-- The maximum absolute value of any entry in `assignments`. -/
  maxGen : Nat
  le_maxGen : ∀ i ∈ assignment.data, i.natAbs ≤ maxGen

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
  sorry
  done

theorem lt_size_of_litValue?_eq_some {τ : PPA} {l : ILit} {b : Bool} :
    τ.litValue? l = some b → ((toVar l) - 1) < τ.size := by
  sorry
  done

/-! ### `toPropFun` model -/

def varToPropFun (τ : PPA) (x : IVar) : PropFun IVar :=
  τ.varValue? x |>.map (if · then .var x else (.var x)ᶜ) |>.getD ⊤

def idxToPropFun (τ : PPA) (i : Fin τ.size) : PropFun IVar :=
  τ.varToPropFun ⟨i + 1, succ_pos _⟩

/-- We model the `PPA` as the conjunction of all its literals.
Note that we cannot fully model the `PPA` as just one `PropAssignment`
because those are required to be total. -/
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
    apply Fin.foldl_induction (hInit := satisfies_tr)
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

  /-- Set the given variable to `b` for the current generation. -/
  def setVar (τ : PPA) (x : IVar) (b : Bool) : PPA :=
    let v : Int := if b then τ.generation else -τ.generation
    { τ with
      assignment := τ.assignment.setF (x - 1) v 0
      maxGen := Nat.max τ.maxGen τ.generation
      le_maxGen := sorry }

  /-- Set the given literal to `true` for the current generation. -/
  def setLit (τ : PPA) (l : ILit) : PPA :=
    τ.setVar (toVar l) (polarity l)

  /-- Set the given variable to `b` for all generations until `gen`. -/
  def setVarUntil (τ : PPA) (x : IVar) (b : Bool) (gen : Nat) : PPA :=
    let v : Int := if b then gen else -gen
    { τ with
      assignment := τ.assignment.setF (x - 1) v 0
      maxGen := Nat.max τ.maxGen gen
      le_maxGen := sorry }

  /-- Set the given literal to `true` for all generations until `gen`. -/
  def setLitUntil (τ : PPA) (l : ILit) (gen : Nat) : PPA :=
    τ.setVarUntil (toVar l) (polarity l) gen

  /-- Set `l ↦ ⊥` for each `l ∈ C` and leave the rest of the assignment untouched.
  If the current assignment contains literals appearing in `C`, they will be overwritten. -/
  -- NB: might be easier to verify if we make this always bump p.generation; it's only used before UP anyway
  -- left without bump but might result in harder theorem
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

-- TODO: below
#exit

  /-! ## Unit propagation -/

  -- Propagate Partial result
  inductive PPR where
    | satisfied
    | multipleUnassignedLiterals

  --
  inductive PropagateResult where
    | contradiction
    | extended (l : ILit) (τ : PPA)
    | satisfied
    | multipleUnassignedLiterals

  /-- A result of `propagateUnit` on inputs `τ` and `C`. -/
  inductive PropagateResultDep (τ : PPA) (C : IClause) where
    | contradiction (h : C.toPropFun ⊓ τ.toPropFun = ⊥)
    | extended      (l : ILit)
                    (τ' : PPA)
                    (h₁ : C.toPropFun ⊓ τ.toPropFun = τ'.toPropFun)
                    (h₂ : τ.litValue? l = none ∧ τ'.litValue? l = some true)
    | satisfied                    -- The clause was satisfied
    | multipleUnassignedLiterals   -- Multiple unassigned literals
 -- | err                          -- Something went wrong? Helps make proofs easier

  -- Note: ResultT is the Exception monad, renamed.
  open ResultT
  open PropagateResult PropagateResultDep

  abbrev Box := ResultT PPR (Option ILit)

  def propUnitFun (τ : PPA) (box : Option ILit) (lit : ILit) : Box :=
    match τ.litValue? lit with
    | some true  => done .satisfied
    | some false => ok box
    | none =>
        match box with
        | none => ok lit
        | some u =>
          if u != lit then
            done .multipleUnassignedLiterals
          else
            ok box

  def propagate (τ : PPA) (C : IClause) := C.foldlM (propUnitFun τ) none

  def propagateUnit (τ : PPA) (C : IClause) : PropagateResult :=
    match propagate τ C with
    | ok none => .contradiction
    | ok (some lit) => .extended lit (τ.setLit lit)
    | done .satisfied => .satisfied
    | done .multipleUnassignedLiterals => .multipleUnassignedLiterals

  theorem pu_sm2 (τ : PPA) (C : IClause) :
      SatisfiesM (fun
        | none => ∀ l ∈ C.data, τ.litValue? l = some false
        | some lit => lit ∈ C.data ∧ τ.litValue? lit = none ∧
          ∀ l ∈ C.data, l ≠ lit → τ.litValue? l = some false) (propagate τ C) := by
    -- Cayden TODO: Why do I have to supply the hypothesis here? And not C[i]?
    have := C.SatisfiesM_foldlM (init := none) (f := propUnitFun τ)
      (motive := fun
        | idx, none => ∀ ⦃i : Fin C.size⦄, i < idx → τ.litValue? (C[i.val]'i.isLt) = some false
        | idx, some lit => lit ∈ C.data ∧ τ.litValue? lit = none ∧
          ∀ ⦃j : Fin C.size⦄, j < idx → C[j.val]'j.isLt ≠ lit → τ.litValue? (C[j]'j.isLt) = some false)
      (h0 := by simp)
      (hf := by
        simp only [SatisfiesM_ResultT_eq, getElem_fin]
        intro i box ih
        -- Cayden question: Is this proof more compact if I use pattern-matching with intro?
        intro
        | none, hbox =>
          simp only
          intro j hj
          unfold propUnitFun at hbox
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
          unfold propUnitFun at hbox
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
      simp
      intro hlit₁ hlit₂ ih
      use hlit₁, hlit₂
      intro l hl₁ hl₂
      rcases Array.mem_data_iff.mp hl₁ with ⟨i, rfl⟩
      exact ih hl₂

  theorem propUnit_contradiction {τ : PPA} {C : IClause} :
      propagateUnit τ C = .contradiction → C.toPropFun ⊓ τ.toPropFun ≤ ⊥ := by
    intro hpu
    unfold propagateUnit at hpu
    cases hp : propagate τ C with
    | ok box =>
      cases box with
      | none =>
        clear hpu
        refine entails_ext.mpr fun σ hσ => ?_
        rw [satisfies_conj] at hσ
        rcases hσ with ⟨hσ₁, hσ₂⟩
        have ⟨lit, hlit, hσlit⟩ := Clause.satisfies_iff.mp hσ₁
        have hvar := satisfies_iff'.mp hσ₂ lit false (SatisfiesM_ResultT_eq.mp (pu_sm2 τ C) none hp lit hlit)
        simp [LitVar.satisfies_iff.mp hσlit] at hvar
        cases hpol : polarity lit <;> rw [hpol] at hvar <;> contradiction
      | some lit => simp [hp] at hpu
    | done ppr => cases ppr <;> simp [hp] at hpu

  theorem propUnit_extended {τ τ' : PPA} {C : IClause} {l : ILit} :
      propagateUnit τ C = .extended l τ' →
        C.toPropFun ⊓ τ.toPropFun ≤ τ'.toPropFun ∧
        τ.litValue? l = none ∧
        τ'.litValue? l = some true := by
    intro hpu
    unfold propagateUnit at hpu
    cases hp : propagate τ C with
    | ok box =>
      cases box with
      | none => simp [hp] at hpu
      | some lit =>
        simp [hp] at hpu
        rcases hpu with ⟨rfl, rfl⟩
        have ⟨hl₁, hl₂, hl₃⟩ := SatisfiesM_ResultT_eq.mp (pu_sm2 τ C) _ hp
        constructor
        · refine entails_ext.mpr fun σ hσ => ?_
          rw [satisfies_conj] at hσ
          rcases hσ with ⟨hσ₁, hσ₂⟩
          rw [satisfies_iff] at hσ₂
          -- Cayden TODO: rename these hypotheses
          rcases Clause.satisfies_iff.mp hσ₁ with ⟨m, hm₁, hm₂⟩
          rw [LitVar.satisfies_iff] at hm₂
          rw [satisfies_iff]
          intro v b hv
          by_cases hvl : v = (toVar lit)
          · rw [setLit_varValue_pos τ hvl] at hv
            injection hv with hv
            by_cases hlm : m = lit
            · subst hlm
              rw [← hvl, hv] at hm₂
              exact hm₂
            · have := litValue?_eq_varValue?_some (hl₃ m hm₁ hlm)
              simp [← hm₂] at this
              replace this := hσ₂ _ _ this
              -- Cayden question: Why can't `contradiction` work here?
              cases hs : σ (toVar m) <;> rw [hs] at this <;> contradiction
          · rw [setLit_varValue_neg τ (Ne.symm hvl)] at hv
            exact hσ₂ _ _ hv
        · use hl₂, setLit_pos _ _
    | done ppr => cases ppr <;> simp [hp] at hpu

  theorem propUnit_satisfied {τ : PPA} {C : IClause} :
      propagateUnit τ C = .satisfied →
        -- Cayden TODO: Better way to express that τ ⊨ C?
        ⊤ ≤ C.toPropFun ⊓ τ.toPropFun := by
    intro hpu
    refine entails_ext.mpr fun σ hσ => ?_
    clear hσ
    rw [satisfies_conj]
    --have := SatisfiesM_ResultT_
    constructor
    · sorry
      done
    sorry
    done

  def motive (τ : PPA) (C : IClause) : Nat → Option ILit → Prop := fun idx box =>
    (hidx : idx ≤ C.size) → box = none → ∀ ⦃i : Nat⦄, (hi : i < idx) → τ.litValue? (C.get ⟨i, lt_of_lt_of_le hi hidx⟩) = some false

  theorem propUnit_fold_satisfied {τ : PPA} {C : IClause} :
      C.foldlM (propUnitFun τ) none = ok none → ∀ (i : Fin C.size), τ.litValue? C[i] = false := by
    have : SatisfiesM (motive τ C C.size) (C.foldlM (propUnitFun τ) none) := by
      apply Array.SatisfiesM_foldlM
      · intro hidx _ i hi; contradiction
      · intro i box hmotive
        unfold propUnitFun
        cases h_tau : τ.litValue? C[i] with
        | none =>
          cases h_box : box with
          | none =>
            simp
            have : motive τ C (↑i + 1) (some C[↑i]) := by intro _ h; contradiction
            exact this
          | some lit =>
            by_cases hlit : lit = C[↑i]
            · simp [hlit]
              have : motive τ C (↑i + 1) (some C[↑i]) := by intro _ h; contradiction
              exact this
            · rw [getElem_fin] at hlit
              simp [hlit]
        | some b =>
          cases b
          · simp [h_tau]
            have : motive τ C (↑i + 1) box := by
              rintro hidx rfl j hj
              rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hj) with (rfl | h)
              · simp; exact h_tau
              · exact hmotive Fin.is_le' rfl h
            exact this
          · simp [h_tau]
    intro h_fold i
    unfold SatisfiesM at this
    rcases this with ⟨x, hx⟩
    rw [h_fold] at hx
    cases hx_type : x with
    | ok y =>
      subst hx_type
      rcases y with ⟨y, hy⟩
      cases y with
      | none => exact hy (le_refl _) rfl i.isLt
      | some l =>
        simp only [Applicative.toFunctor, Monad.toApplicative, instMonadResultT,
          ResultT.bind, Function.comp_apply, ok.injEq] at hx
    | done y =>
      subst hx_type
      contradiction

  #exit

  /-
  inductive UnitPropResultDep {α : Type} [BEq α] [Hashable α]
    (db : ClauseDb α) (σ : PartPropAssignment) (hints : Array α) where
  /-- A contradiction was derived. The contradiction is implied by the subset of the database
  used in hints as well as the initial assignment. -/
  | contradiction (h : db.toPropTermSub (· ∈ hints.data) ⊓ σ.toPropTerm ≤ ⊥)
  /-- The partial assignment was extended. The final assignment `σ'` is implied by the subset of
  the database used in hints as well as the initial assignment. -/
  | extended (σ' : PartPropAssignment)
             (h : db.toPropTermSub (· ∈ hints.data) ⊓ σ.toPropTerm ≤ σ'.toPropTerm)
  /-- The hint `C` at index `idx` did not become unit under `σ`. -/
  | hintNotUnit (idx : α) (C : IClause) (σ : PartPropAssignment)
  /-- The hint index `idx` points at a nonexistent clause. -/
 | hintNonexistent (idx : α)
  -/

  /-- If `C` is satisfied by `τ`, return `notUnit`.
  Otherwise compute the reduced clause `C' = {l ∈ C | ¬l ∉ τ}`.
  If `C' = [u]` is a unit, extend `τ` by `u` and return `extended`.
  If `C'` has become empty (is falsified), return `contradiction`.
  If `C'` is not a unit and not falsified, return `notUnit`. -/
  def propagateUnit (τ : PPA) (C : IClause) :
      PropagateResultDep τ C := Id.run do
    -- The candidate for a unit.
    -- The ILit is the value stored in the clause, while the Fin is the index in the clause to access it
    --let mut unit? : Option ((i : ILit) × { f : Fin C.size // C[f] = i }) := none
    --let mut unit? : Option ILit := none
    let mut unitIdx? : Option ({i : Fin C.size // τ.litValue? C[i] = none}) := none
    let mut idx : { idx : Fin (C.size + 1) //
      (unitIdx? = none → ∀ (i : Fin idx), τ.litValue? C[i] = some false) ∧
      (unitIdx? ≠ none → ∃ v : ({i : Fin C.size // τ.litValue? C[i] = none}),
        unitIdx? = some v ∧
        ∀ (i : Fin idx), i.val ≠ v.val.val → τ.litValue? C[i] = some false ) } :=
          ⟨0, sorry⟩

    for hi : i in [0:C.size] do
      have hi_lt : i < C.size := Membership.mem.upper hi
      let l := C[i]'hi_lt
      have hl : l ∈ C.data := Array.getElem_mem_data C _
      match hl_val : τ.litValue? l with
      | some true => return .notUnit
      | some false =>
          -- Maintain invariant

          continue
      | none =>
          match unitIdx? with
          | none => unitIdx? := ⟨some l, fun _ => ⟨l, hl, sorry⟩⟩
          | some ⟨j, h⟩ =>
            if i ≠ j.val then return .notUnit
      continue
          --if let .some ⟨j, h⟩ := unitIdx? then
          --  if i ≠ j.val then
          --    return .notUnit

      -- Update invariant



    if hIdx : idx.val = C.size then
      match unitIdx? with
      | none => return .contradiction
      | some ⟨i, h⟩ => return .extended C[i] (τ.setLit C[i])
    else
      return .err

#check List.foldl

#exit

/-
def unitPropWithHintsDep (db : ClauseDb α) (σ₀ : PartPropAssignment) (hints : Array α)
    : UnitPropResultDep db σ₀ hints := Id.run do
  let mut σ : {σ : PartPropAssignment //
      db.toPropTermSub (· ∈ hints.data) ⊓ σ₀.toPropTerm ≤ σ.toPropTerm } :=
    ⟨σ₀, inf_le_right⟩
  for h : i in [0:hints.size] do
    let hint := hints[i]'(Membership.mem.upper h)
    have hMem : hint ∈ hints.data := Array.getElem_mem_data hints _

    match hGet : db.getClause hint with
    | none => return .hintNonexistent hint
    | some C =>
      have hDbσ₀ :
          db.toPropTermSub (· ∈ hints.data) ⊓ σ₀.toPropTerm ≤ C.toPropTerm ⊓ σ.val.toPropTerm :=
        le_inf (inf_le_of_left_le (toPropTermSub_of_getClause_eq_some db hMem hGet)) σ.property
      match hRed : C.reduce σ.val with
      | some #[] =>
        have : db.toPropTermSub (· ∈ hints.data) ⊓ σ₀.toPropTerm ≤ ⊥ := by
          have : C.toPropTerm ⊓ σ.val.toPropTerm ≤ ⊥ :=
            IClause.reduce_eq_some _ _ _ hRed
          exact le_trans hDbσ₀ this
        return .contradiction this
      | some C' =>
        let some ⟨u, hU⟩ := checkIsUnit C'
          | return .hintNotUnit hint C σ.val
        have : db.toPropTermSub (· ∈ hints.data) ⊓ σ₀.toPropTerm ≤
            PartPropAssignment.toPropTerm (σ.val.insert u.var u.polarity) := by
          have hU : db.toPropTermSub (· ∈ hints.data) ⊓ σ₀.toPropTerm ≤ u.toPropTerm := by
            have h := IClause.reduce_eq_some _ _ _ hRed
            conv at h => rhs; rw [← hU]; simp [IClause.toPropTerm]
            exact le_trans hDbσ₀ h
          refine PropTerm.entails_ext.mpr fun τ hτ => ?_
          have hU : τ ⊨ u.toPropTerm :=
            PropTerm.entails_ext.mp hU τ hτ
          have hσ : τ ⊨ σ.val.toPropTerm :=
            PropTerm.entails_ext.mp σ.property τ hτ
          rw [PartPropAssignment.satisfies_iff] at hσ ⊢
          intro x p hFind
          by_cases hEq : x = u.var
          next =>
            rw [hEq, HashMap.find?_insert _ _ LawfulBEq.rfl] at hFind
            rw [ILit.satisfies_iff] at hU
            simp_all
          next =>
            rw [HashMap.find?_insert_of_ne _ _ (bne_iff_ne _ _ |>.mpr (Ne.symm hEq))] at hFind
            exact hσ _ _ hFind
        σ := ⟨σ.val.insert u.var u.polarity, this⟩
      | _ => return .hintNotUnit hint C σ.val
  return .extended σ.val σ.property
-/

end PPA
