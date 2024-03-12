/-

Persistent partial assignments and substitutions.

Resizable arrays that can be ``cleared'' in O(1) time by bumping a generation
number. Each cell in the array stores a generation number that determines if the
cell is set (i.e. that it is above the data structure's generation number).
Used to implement partial assignments and substitutions by assuming that all
variables are unset (PPA) or set to themselves (PS) at initialization.

Authors: Cayden Codel, Wojciech Nawrocki, James Gallicchio
Carnegie Mellon University
-/

import LeanSAT.Data.Cnf
import LeanSAT.Data.ICnf
import Mathlib.Data.Nat.Basic

import LeanSAT.Model.Subst
import LeanSAT.Model.PropFun

import LeanSAT.Upstream.ToStd
import LeanSAT.Upstream.ToMathlib

import Experiments.ProofChecking.PPA

open LeanSAT LeanSAT.Model Nat
open LitVar ILit IVar LawfulLitVar
open PropFun

/- The value contained in the partial substitution. Values can either be booleans
   (in LRAT/LPR, they are only booleans), or set to other variables, with sign.

  When set to other variables, the boolean indicates the sign (true is positive),
  and the ILit refers to the underlying literal this variable is set to.     -/
inductive PSVal where
  | tr : PSVal
  | fls : PSVal
  | lit (l : ILit) : PSVal

attribute [match_pattern] PSVal

/- A PSCell is the actual array cell in the substitution. The generation
   checks whether the cell is set (allowing for efficient clearing), and the val
   field stores the information of what the variable is set to (boolean or other literal). -/
structure PSCell where
  generation : Nat   /- The generation value for the cell. Compare against PS.generation -/
  val : PSVal

/-- A persistent partial assignment of truth values to propositional variables.

If used linearly, it is an efficient way of clearing out partial assignments
when doing proof checking, tautology checking, or unit propagation. -/
structure PS where
  assignment : Array PSCell
  /-- The generation counter is used to avoid clearing the assignment array.
  Instead, we just bump the counter and interpret values in the array
  below the counter as unassigned. -/
  generation : PNat
  /-- The maximum absolute value of any entry in `assignments`. -/
  maxGen : Nat
  le_maxGen : ∀ i ∈ assignment.data, i.generation ≤ maxGen

/-! ## Reading values from the PS -/

abbrev PSubst := (IVar → PropForm IVar)

namespace PSVal

@[simp, inline] def mkPosLit (idx : Nat) : PSVal := .lit (mkPos ⟨idx + 1, succ_pos _⟩)
@[simp, inline] def mkNegLit (idx : Nat) : PSVal := .lit (mkNeg ⟨idx + 1, succ_pos _⟩)
@[simp, inline] def mkFalse : PSVal := .fls

protected def negate : PSVal → PSVal
  | .tr => .fls
  | .fls => .tr
  | .lit l => .lit (LitVar.negate l)

@[simp] theorem negate_negate : PSVal.negate ∘ PSVal.negate = id := by
  ext r; cases r <;> simp [PSVal.negate]

@[simp] theorem negate_negate' (r : PSVal) :
    r.negate.negate = r := by
  cases r <;> simp [PSVal.negate]

theorem negate_rhs_eq_lhs_negate (r₁ r₂ : PSVal) :
    r₁.negate = r₂ ↔ r₁ = r₂.negate := by
  cases r₁ <;> cases r₂ <;> simp [PSVal.negate]; aesop

@[simp] def isBool : PSVal →  Bool
  | .tr => true
  | .fls => true
  | _ => false

@[simp] def isLit : PSVal → Bool
  | .lit _ => true
  | _ => false

@[simp] def getVar : PSVal → IVar
  | .tr => 1  -- Useless return value for non-.lit values
  | .fls => 1
  | .lit l => toVar l

@[simp] def getLit : PSVal → ILit
  | .tr => mkPos ⟨1, succ_pos _⟩
  | .fls => mkNeg ⟨1, succ_pos _⟩
  | .lit l => l

@[simp] def sign : PSVal → Bool
  | .tr => true
  | .fls => false
  | .lit l => polarity l

instance : ToString PSVal where
  toString v :=
    match v with
    | .tr => "t"
    | .fls => "f"
    | .lit l => s!"{l}"

end PSVal

namespace PSCell

/-
def mkCell (idx : Nat) (gen : Nat := 0) : PSCell := {
  generation := gen
  val := PSVal.mkVal idx
} -/

def mkEmptyCell : PSCell := {
  generation := 0
  val := PSVal.mkFalse
}

-- Checks whether the cell is set against a provided generation value
@[simp, inline] def isSet (c : PSCell) (gen : Nat) : Bool := (c.generation ≥ gen)
@[simp, inline] def isBool (c : PSCell) : Bool := c.val.isBool
@[simp, inline] def isLit (c : PSCell) : Bool := c.val.isLit
@[simp, inline] def getVar (c : PSCell) : IVar := c.val.getVar
@[simp, inline] def getLit (c : PSCell) : ILit := c.val.getLit
@[simp, inline] def sign (c : PSCell) : Bool := c.val.sign
@[simp, inline] def isPointer (c : PSCell) (gen : Nat) : Bool := c.isSet gen && c.isLit

def varValue? (c : PSCell) (gen : Nat) : Option PSVal :=
  if c.isSet gen then
    some c.val
  else
    none

@[simp, inline] def clear (c : PSCell) : PSCell := { c with generation := 0 }

@[inline] def setToTrue (c : PSCell) (gen : Nat) : PSCell := { c with
  generation := gen
  val := PSVal.tr
}

@[inline] def setToFalse (c : PSCell) (gen : Nat) : PSCell := { c with
  generation := gen
  val := PSVal.fls
}

@[inline] def setToLit (c : PSCell) (l : ILit) (gen : Nat) : PSCell := { c with
  generation := gen
  val := PSVal.lit l
}

@[inline] def setLit (c : PSCell) (l : ILit) (gen : Nat) : PSCell :=
  if polarity l then
    c.setToTrue gen
  else
    c.setToFalse gen

section /- generation -/

variable (c : PSCell) (l : ILit) (gen : Nat)

@[simp] theorem mkEmptyCell_generation : mkEmptyCell.generation = 0 := rfl
@[simp] theorem setToTrue_generation : (c.setToTrue gen).generation = gen := rfl
@[simp] theorem setToFalse_generation : (c.setToFalse gen).generation = gen := rfl
@[simp] theorem setToLit_generation : (c.setToLit l gen).generation = gen := rfl
@[simp] theorem setLit_generation : (c.setLit l gen).generation = gen := by
  cases hpol : polarity l <;> simp [setLit, hpol]

end /- generation -/

instance : ToString PSCell where
  toString c := s!"({c.generation}, {c.val})"

end PSCell

/-! # PS -/

namespace PS

@[inline] def size (τ : PS) : Nat := τ.assignment.size

section /- Operations on Fin -/

variable (τ : PS) (i : Fin τ.size)

-- TODO: Or should these be abbrev?
@[simp, inline] def get : PSCell := τ.assignment.get i
@[simp, inline] def get? (i : Nat) : Option PSCell := τ.assignment.get? i

@[simp, inline] def isSet : Bool := (τ.get i).isSet τ.generation
@[simp, inline] def isLit : Bool := (τ.get i).isLit
@[simp, inline] def getVar : IVar := (τ.get i).getVar
@[simp, inline] def getLit : ILit := (τ.get i).getLit
@[simp, inline] def sign : Bool := (τ.get i).sign
@[simp, inline] def isPointer : Bool := (τ.get i).isPointer τ.generation

end /- section -/

section /- Operations on Nat -/

variable (τ : PS) (i : Nat)

-- TODO: Most elegant way to do Nats first? Monadic bind/map?
@[simp, inline] def isSet? : Option Bool := (PSCell.isSet · τ.generation) <$> (τ.get? i)
@[simp, inline] def isLit? : Option Bool := PSCell.isLit <$> (τ.get? i)
@[simp, inline] def isPointer? : Option Bool := (PSCell.isPointer · τ.generation) <$> (τ.get? i)
@[simp, inline] def getVar? : Option IVar := PSCell.getVar <$> (τ.get? i)
@[simp, inline] def getLit? : Option ILit := PSCell.getLit <$> (τ.get? i)
@[simp, inline] def sign? : Option Bool := PSCell.sign <$> (τ.get? i)

end /- section -/

instance : ToString PS where
  toString τ := String.intercalate " ∧ "
    (τ.assignment.foldl (init := []) (f := fun acc a => s!"{a}" :: acc))

end PS

/-! # WF: well-formed -/

/-
structure PSVal.WF (v : PSVal) (size : PNat) where
  h_index : v.getLit.index < size

structure PSCell.WF (c : PSCell) (size maxGen : PNat) where
  h_val : PSVal.WF c.val size
  h_gen : c.generation ≤ maxGen

structure PS.WF (τ : PS) where
  h_gen : τ.generation > 0
  h_cells : ∀ (i : Fin τ.size), PSCell.WF (τ.get i)
    ⟨τ.size, by match h : τ.size with
                | 0     => rw [h] at i; exact Fin.elim0' i
                | n + 1 => exact Nat.succ_pos _⟩ ⟨_, h_gen⟩ -/

namespace PS

/-! # varValue -/

-- Cayden: @[simp] attribute here?
def varValue (τ : PS) (v : IVar) : PSVal :=
  if hi : v.index < τ.size then
    match PSCell.varValue? (get τ ⟨v.index, hi⟩) τ.generation with
    | none => PSVal.lit (mkPos v)
    | some x => x
  else
    PSVal.lit (mkPos v)

@[inline] def litValue (τ : PS) (l : ILit) : PSVal :=
  if polarity l then
    varValue τ (toVar l)
  else
    PSVal.negate (varValue τ (toVar l))

-- TODO: Better name
def idxToSubst (σ : PS) (σ_built : PSubst) (i : Fin σ.size) : PSubst :=
  fun v =>
    if v.index = i.val then
      match PSCell.varValue? (σ.get i) v with
      | none => σ_built v
      | some .tr => .tr
      | some .fls => .fls
      | some (.lit l) => if polarity l then .var (toVar l)
                         else .neg (.var (toVar l))
    else σ_built v

def toSubst (σ : PS) : PSubst :=
  Fin.foldl σ.size (init := .var) (idxToSubst σ)

instance : Coe PS PSubst := ⟨toSubst⟩

theorem idxToSubst_comm (σ : PS) :
  ∀ (σ_built : PSubst) (idx₁ idx₂ : Fin σ.size),
    (idxToSubst σ) ((idxToSubst σ) σ_built idx₁) idx₂ =
    (idxToSubst σ) ((idxToSubst σ) σ_built idx₂) idx₁ := by
  intro σ_built idx₁ idx₂
  unfold idxToSubst
  apply funext
  intro v
  by_cases hidx : idx₁.val = idx₂.val
  <;> by_cases hv₁ : v.index = idx₁.val
  <;> by_cases hv₂ : v.index = idx₂.val
  <;> try simp [hv₁, hv₂, hidx]
  <;> try simp [hv₁, hv₂, hidx, Ne.symm hidx]

theorem toSubst_of_comm (σ : PS) {v : IVar} (hv : v.index < σ.size) :
    ∃ σ_built, σ.toSubst = idxToSubst σ σ_built ⟨v.index, hv⟩ :=
  Fin.foldl_of_comm σ.size (idxToSubst σ) .var ⟨v.index, hv⟩ (idxToSubst_comm σ)

/-
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
    simp [hϕ, h i] -/

instance : ToString PS where
  toString τ := String.intercalate " ∧ "
    (τ.assignment.foldl (init := []) (f := fun acc a =>
      match a.val with
        | .tr => s!"{a.generation}" :: acc
        | .fls => s!"-{a.generation}" :: acc
        | .lit l => s!"<{l}>" :: acc))

theorem litValue_negate (τ : PS) (l : ILit) :
    (τ.litValue (-l)) = PSVal.negate (τ.litValue l) := by
  cases hpol : polarity l <;> simp [hpol, litValue]

theorem litValue_eq_varValue_pos {l : ILit} :
    polarity l = true → ∀ (τ : PS), τ.litValue l = τ.varValue (toVar l) := by
  intro hl; simp [hl, litValue]

theorem litValue_eq_varValue_neg {l : ILit} :
    polarity l = false → ∀ (τ : PS), τ.litValue l = PSVal.negate (τ.varValue (toVar l)) := by
  intro hl; simp [hl, litValue]

theorem lt_size_of_varValue_of_not_id {τ : PS} {v : IVar} :
    τ.varValue v ≠ .lit (mkPos v) → v.index < τ.size := by
  intro hv
  by_contra
  rename (¬v.index < τ.size) => h_con
  simp [varValue, h_con] at hv

theorem lt_size_of_litValue_of_not_id {τ : PS} {l : ILit} :
    τ.litValue l ≠ .lit l → l.index < τ.size := by
  intro hv
  by_contra
  rename (¬l.index < τ.size) => h_con
  rcases mkPos_or_mkNeg l with (hl | hl)
  -- Cayden TODO: put this in one simp [] call. Why explicit typeclass LawfulLitVar lemmas?
  · simp [litValue, varValue, h_con] at hv
    rw [hl] at hv
    simp_rw [LawfulLitVar.polarity_mkPos, LawfulLitVar.toVar_mkPos] at hv
    simp at hv
  · simp [litValue, varValue, h_con, PSVal.negate] at hv
    rw [hl] at hv
    simp_rw [LawfulLitVar.polarity_mkNeg, LawfulLitVar.toVar_mkNeg] at hv
    simp at hv

theorem varValue_fls_iff {σ : PS} {v : IVar} :
    (σ.varValue v = .fls) ↔ (PropFun.substL ⟦v⟧ σ.toSubst) = ⊥ := by
  sorry
  done

theorem varValue_tr_iff {σ : PS} {v : IVar} :
    (σ.varValue v = .tr) ↔ (PropFun.substL ⟦v⟧ σ.toSubst) = ⊤ := by
  sorry
  done

theorem varValue_lit_iff {σ : PS} {v : IVar} {l : ILit} :
    (σ.varValue v = .lit l) ↔ (PropFun.substL ⟦v⟧ σ.toSubst) = (PropFun.substL l σ.toSubst) := by
  sorry
  done

theorem litValue_fls_iff {σ : PS} {l : ILit} :
    (σ.litValue l = .fls) ↔ (PropFun.substL l σ.toSubst) = ⊥ := by
  sorry
  done

theorem litValue_tr_iff {σ : PS} {l : ILit} :
    (σ.litValue l = .tr) ↔ (PropFun.substL l σ.toSubst) = ⊤ := by
  sorry
  done

theorem litValue_lit_iff {σ : PS} {l₁ l₂ : ILit} :
    (σ.litValue l₁ = .lit l₂) ↔ (PropFun.substL l₁ σ.toSubst) = l₂ := by
  sorry
  done

/-! # setLit -/

-- Cayden TODO: How to make setF more efficient when the value needs to be a cell?
-- Can an efficient implementation do this linearly? Ow will run out of memory?
-- One idea is to use a .setF' that takes a function : (Option α → α) instead of value v : α
-- That way, if the cell exists, its value can be mapped

-- This is a more efficient version
/-
def setLit (τ : PS) (l : ILit) : PS := { τ with
  assignment :=
    if hidx : l.index < τ.size then
      τ.assignment.set ⟨l.index, hidx⟩ ((τ.get ⟨l.index, hidx⟩).setLit l τ.generation)
    else
      τ.assignment.setF l.index (PSCell.mkEmptyCell.setLit l τ.generation) PSCell.mkEmptyCell
  maxGen := max τ.maxGen τ.generation
}
-/

theorem setVar_le_maxGen (τ : PS) (i : Nat) (c : PSCell) :
    ∀ cell ∈ (τ.assignment.setF i c PSCell.mkEmptyCell).data, cell.generation ≤ max τ.maxGen c.generation := by
  sorry
  done

-- This is a more functional version
/-- Set the given literal to `true` for the current generation in the PS. -/
def setLit (τ : PS) (l : ILit) : PS := { τ with
  assignment := τ.assignment.setF l.index (PSCell.mkEmptyCell.setLit l τ.generation) PSCell.mkEmptyCell
  maxGen := max τ.maxGen τ.generation
  le_maxGen := by
    have := setVar_le_maxGen τ l.index (PSCell.mkEmptyCell.setLit l τ.generation)
    rwa [PSCell.setLit_generation PSCell.mkEmptyCell l ↑τ.generation] at this
}

/-- Set the given literal to `true` for all generations until `gen`. -/
def setLitUntil (τ : PS) (l : ILit) (gen : Nat) : PS := { τ with
  assignment := τ.assignment.setF l.index (PSCell.mkEmptyCell.setLit l gen) PSCell.mkEmptyCell
  maxGen := max τ.maxGen gen
  le_maxGen := by
    have := setVar_le_maxGen τ l.index (PSCell.mkEmptyCell.setLit l gen)
    rwa [PSCell.setLit_generation PSCell.mkEmptyCell l gen] at this
}

def setVarToLit (τ : PS) (v : IVar) (l : ILit) : PS := { τ with
  assignment := τ.assignment.setF v.index (PSCell.mkEmptyCell.setLit l τ.generation) PSCell.mkEmptyCell
  maxGen := max τ.maxGen τ.generation
  le_maxGen := by
    have := setVar_le_maxGen τ v.index (PSCell.mkEmptyCell.setLit l τ.generation)
    rwa [PSCell.setLit_generation PSCell.mkEmptyCell l τ.generation] at this
}

def setVarToLitUntil (τ : PS) (v : IVar) (l : ILit) (gen : Nat) : PS := { τ with
  assignment := τ.assignment.setF v.index (PSCell.mkEmptyCell.setLit l gen) PSCell.mkEmptyCell
  maxGen := max τ.maxGen gen
  le_maxGen := by
    have := setVar_le_maxGen τ v.index (PSCell.mkEmptyCell.setLit l gen)
    rwa [PSCell.setLit_generation PSCell.mkEmptyCell l gen] at this
}

@[simp, inline] def setLitToLit (τ : PS) (l l_target : ILit) : PS :=
  if polarity l then
    τ.setVarToLit (toVar l) l_target
  else
    τ.setVarToLit (toVar l) (-l_target)

@[simp, inline] def setLitToLitUntil (τ : PS) (l l_target : ILit) (gen : Nat) : PS :=
  if polarity l then
    τ.setVarToLitUntil (toVar l) l_target gen
  else
    τ.setVarToLitUntil (toVar l) (-l_target) gen

def setVars (σ : PS) (A : Array (IVar × ILit)) : PS :=
  A.foldl (init := σ) (fun σ ⟨v, l⟩ => σ.setVarToLit v l)

def setLits (σ : PS) (A : Array ILit) : PS :=
  A.foldl setLit σ

/- Lemmas -/

@[simp] theorem setLit_size (τ : PS) (l : ILit) : (τ.setLit l).size = max τ.size (l.index + 1) := by
  simp [setLit, size]

-- Cayden TODO: Figure out which things are @[simp] in def vs. @[simp] theorems.
theorem litValue_setLit_pos (τ : PS) (l : ILit) : (τ.setLit l).litValue l = .tr := by
  by_cases hpol : polarity l
  <;> by_cases hl : l.index < τ.size
  <;> simp [litValue, varValue, size, setLit, PSCell.setLit, PSCell.setToTrue, PSCell.setToFalse,
        hpol, hl, PSCell.varValue?, PSVal.negate, Array.getElem_setF]

theorem litValue_setLit_neg (τ : PS) {l₁ l₂ : ILit} :
    l₁ ≠ l₂ → (τ.setLit l₁).litValue l₂ = τ.litValue l₂ := by
  intro hne
  by_cases hpol₁ : polarity l₁
  · by_cases hpol₂ : polarity l₂
    · simp [hpol₁, hpol₂, litValue]
      sorry
    sorry
  /-by_cases hpol : polarity l₂
  · simp [litValue, hpol, setLit, Array.size_setF, -Array.get_eq_getElem]
    by_cases hl₂ : l₂.index < τ.size
    · rw [size] at hl₂
      have : l₂.index < τ.assignment.size ∨ l₂.index < l₁.index + 1 := Or.inl hl₂
      simp [hl₂, this, -Array.get_eq_getElem]
      by_cases hpol₁ : polarity l₁
      · rw [Array.getElem_setF' τ.assignment l₁.index ⟨τ.generation, PSVal.tr⟩ PSCell.mkEmptyCell]

      done
    done
  --by_cases hpol : polarity l₂
  --<;> by_cases hl₂ : l₂.index < τ.size
  --<;> simp [litValue, setLit, hpol,
  --    hl₂, Or.inl hl₂, Array.size_setF, PSCell.varValue?, PSVal.negate] -/
  sorry
  done

/-! # New -/

/-- Initialize to an empty partial assignment,
supporting variables in the range `[1, maxVar]`.

The assignment will resize dynamically if it's used with
a variable above the initial `maxVar`. -/

def new (n : Nat) : PS where
  assignment := Array.mkArray n PSCell.mkEmptyCell
  generation := ⟨1, Nat.one_pos⟩
  maxGen := 0
  le_maxGen := by simp_all [List.mem_replicate]

/-
theorem new_WF (n : Nat) : (new n).WF := by
  simp [new]
  constructor
  · intro i
    sorry
  · simp only [gt_iff_lt, zero_lt_one] -/

/-! # Reset -/

/-- Reset the assignment to an empty one. -/
def reset (τ : PS) : PS :=
  { τ with
    generation := ⟨τ.maxGen + 1, Nat.succ_pos _⟩ }

/-! # Bump -/

/-- Clear all temporary assignments at the current generation. -/
def bump (τ : PS) : PS :=
  { τ with generation := τ.generation + 1 }


section monadic

/-! # Unit propagation -/

/-

Cayden note 1/8: In SR checking, the substitution witness σ is provided in the proof line,
  and then never modified. Instead, a partial assignment α is produced and modified.

To save memory and time, the substitution and partial assignments use the "generation bumping" strategy
to clear out their computations after each proof line/group of hints.

Since unit propagation is never done/evaluated against a substitution, proving its correctness is moot.
But! We do need to compute a clause's reduction under a substitution, and so we need a theory for that.
We also need to think about an efficient way to either compute a reduction OR make reduction and evaluation
against a partial assignment happen in the same step (possibly using another "PPA" structure off to the side
to record which literals have been seen in the reduction, so a tautology can be detected)

-/

inductive UPResult where
  | falsified
  | satisfied
  | unit (l : ILit) (τ : PS) -- Updated substitution and unit literal l
  | multipleUnassignedLiterals

inductive UPDone where
  | satisfied
  | multipleUnassignedLiterals

abbrev UPBox := Except UPDone (Option ILit)

open Except UPResult UPDone PPA

def sevalUP (σ : PS) (unit? : Option ILit) (l : ILit) : UPBox :=
  match σ.litValue l with
  | .tr => error .satisfied
  | .fls => ok unit?
  | .lit lit =>
    match unit? with
    | none => ok lit
    | some u =>
      if u = lit then ok unit?
      -- Since σ is a substitution, tautology could occur
      else if u = -lit then error .satisfied
      else error .multipleUnassignedLiterals

def foldUP (σ : PS) (C : IClause) := C.foldlM (sevalUP σ) none

def unitProp (σ : PS) (C : IClause) : UPResult :=
  match foldUP σ C with
  | ok none => .falsified
  | ok (some lit) => .unit lit (σ.setLit lit)
  | error .satisfied => .satisfied
  | error .multipleUnassignedLiterals => .multipleUnassignedLiterals

def UP_motive_fn (σ : PS) (C : IClause) : ℕ → Option ILit → Prop
  | idx, none => ∀ ⦃i : Fin C.size⦄, i < idx → σ.litValue C[i] = .fls
  | idx, some lit => ∃ (i : Fin C.size), i < idx ∧ σ.litValue C[i] = .lit lit ∧
      (∀ ⦃j : Fin C.size⦄, j < idx → j ≠ i → (σ.litValue C[j] = .fls ∨ σ.litValue C[j] = .lit lit))

theorem SatisfiesM_UP (σ : PS) (C : IClause) :
    SatisfiesM (fun
      | none => ∀ l ∈ C.data, σ.litValue l = .fls
      | some lit => ∃ (l : ILit), l ∈ C.data ∧ σ.litValue l = .lit lit ∧
          (∀ l' ∈ C.data, l' ≠ l → (σ.litValue l' = .fls ∨ σ.litValue l' = .lit lit))) (foldUP σ C) := by
  have := C.SatisfiesM_foldlM (init := (none : Option ILit)) (f := sevalUP σ)
    (motive := UP_motive_fn σ C)
    (h0 := by simp [UP_motive_fn])
    (hf := by
      unfold UP_motive_fn
      simp only [SatisfiesM_Except_eq, getElem_fin]
      -- Cayden question: is the proof more compact if I use pattern-matching with intro?
      intro i box ih
      intro
      | none, hbox =>
        intro j hj
        unfold sevalUP at hbox
        match hσ : σ.litValue C[i.val] with
        | .tr => simp_rw [hσ] at hbox
        | .fls =>
          simp_rw [hσ, ok.injEq] at hbox; subst hbox
          rcases eq_or_lt_of_le (le_of_lt_succ hj) with (hj | hj)
          · rw [Fin.ext hj]; exact hσ
          · exact ih hj
        | .lit lit =>
          simp [hσ] at hbox
          match box with
          | none => simp at hbox
          | some u =>
            rcases eq_trichotomy u lit with (rfl | rfl | hvar)
            · simp at hbox
            · simp at hbox
            · simp [ne_of_toVar_ne hvar, ne_of_toVar_ne ((toVar_negate lit).symm ▸ hvar)] at hbox
      | some u, hbox =>
        rename ILit => lit
        unfold sevalUP at hbox
        match hσ : σ.litValue C[i.val] with
        | .tr => simp_rw [hσ] at hbox
        | .fls =>
          simp_rw [hσ, ok.injEq] at hbox; subst hbox
          rcases ih with ⟨idx, hidx_lt, hidxσ, hidx_fls⟩
          use idx, lt_succ_of_lt hidx_lt, hidxσ
          intro j hj
          rcases lt_or_eq_of_le (le_of_lt_succ hj) with (h | h)
          · exact hidx_fls h
          · replace h := Fin.ext h; subst h; intro _; exact Or.inl hσ
        | .lit lit' =>
          simp [hσ] at hbox
          match box with
          | none =>
            simp at hbox; subst hbox
            have : C[i.val] ∈ C.data := Array.getElem_mem_data C i.isLt
            use i, lt_succ_self _, hσ
            intro j hj
            rcases lt_or_eq_of_le (le_of_lt_succ hj) with (h | h)
            · intro _; exact Or.inl (ih h)
            · replace h := Fin.ext h; subst h; intro hcon; contradiction
          | some u =>
            rcases eq_trichotomy u lit' with (rfl | rfl | hvar)
            · simp at hbox; subst hbox
              rcases ih with ⟨idx, hidx_lt, hidxσ, hidx_fls⟩
              use idx, lt_succ_of_lt hidx_lt, hidxσ
              intro j hj
              rcases lt_or_eq_of_le (le_of_lt_succ hj) with (h | h)
              · exact hidx_fls h
              · replace h := Fin.ext h; subst h; intro _; exact Or.inr hσ
            · simp at hbox
            · simp [ne_of_toVar_ne hvar, ne_of_toVar_ne ((toVar_negate lit').symm ▸ hvar)] at hbox)
  apply SatisfiesM.imp this
  intro
  | none =>
    intro h l hl
    rcases Array.mem_data_iff_exists_fin.mp hl with ⟨i, rfl⟩
    exact h i.isLt
  | some lit =>
    simp [UP_motive_fn]
    intro i hi ih
    use C[i.val], Array.getElem_mem_data C i.isLt, hi
    intro l hl₁ hl₂
    rcases Array.mem_data_iff_exists_fin.mp hl₁ with ⟨j, rfl⟩
    apply ih
    exact ne_of_apply_ne (C[·]) hl₂

theorem contradiction_of_UP_falsified {σ : PS} {C : IClause} :
    σ.unitProp C = .falsified → (C.toPropFun).substL σ.toSubst ≤ ⊥ := by
  unfold unitProp
  intro h_falsified
  split at h_falsified <;> try simp at h_falsified
  clear h_falsified
  rename (foldUP σ C = ok none) => h
  refine entails_ext.mpr fun τ hτ => ?_
  rw [satisfies_substL] at hτ
  have ⟨lit, hlit, hτlit⟩ := Clause.satisfies_iff.mp hτ
  rw [← Array.mem_data] at hlit
  have := SatisfiesM_Except_eq.mp (SatisfiesM_UP σ C) none h lit hlit
  clear h hτ
  replace hτlit := satisfies_iff.mp hτlit
  cases hpol : polarity lit
  <;> simp [hpol, PropAssignment.subst] at hτlit
  · rw [litValue_eq_varValue_neg hpol, PSVal.negate_rhs_eq_lhs_negate, PSVal.negate,
          varValue_tr_iff, substL_distrib] at this
    rw [this] at hτlit
    contradiction
  · rw [litValue_eq_varValue_pos hpol, varValue_fls_iff, substL_distrib] at this
    rw [this] at hτlit
    exact hτlit

theorem extended_of_UP_unit {σ σ' : PS} {C : IClause} {l : ILit} :
    σ.unitProp C = .unit l σ' →
      (C.toPropFun).substL σ.toSubst ≤ l.toPropFun ∧
      (∃ lit ∈ C.data, σ.litValue lit = .lit l ∧ σ'.litValue l = .tr) := by
      -- Cayden question: how to express this in an abstract way? Perhaps with a bind (l.bind σ) or as a (. ∘ .) of two subs
  unfold unitProp
  intro h_unit
  split at h_unit <;> try simp at h_unit
  --clear h_unit
  rename ILit => lit
  rename (foldUP σ C = ok (some lit)) => h
  rcases h_unit with ⟨rfl, rfl⟩
  have hlv := SatisfiesM_Except_eq.mp (SatisfiesM_UP σ C) (some lit) h
  clear h
  rcases hlv with ⟨l, hl_mem, hσl, ih⟩
  constructor
  · refine entails_ext.mpr fun τ hτ => ?_
    rw [satisfies_substL] at hτ
    by_cases heq : l = lit
    · subst heq
      rw [Clause.satisfies_iff] at hτ; rcases hτ with ⟨l', hl'_mem, hl'⟩
      rw [← satisfies_substL] at hl'
      sorry -- Proof got stuck here. And we may not need unit propagaion after all
      done
    · sorry
      done
    done
  · exact ⟨l, hl_mem, hσl, litValue_setLit_pos _ _⟩
  done

-- We have to carry along a PPA to store the unset literals and check for tautologies (Cayden later comment: why??)

/-! # Reduction -/

-- We do something very similar to "unit propagation", except we don't modify σ

inductive ReductionResult where
  | falsified
  | satisfied
  | reduced
  | notReduced

abbrev RedBox := Except PPA (PPA × Bool × Bool)

open Except ReductionResult

def sevalRed (σ : PS) (p : PPA × Bool × Bool) (l : ILit) : RedBox :=
  let ⟨τ, reduced?, unassigned?⟩ := p
  match σ.litValue l with
  | .tr => error τ
  | .fls => ok ⟨τ, true, unassigned?⟩
  | .lit lit =>
    match τ.litValue? lit with
    | none => ok ⟨τ.setLit lit, reduced? || (l != lit), true⟩
    | some true => ok ⟨τ, reduced? || (l != lit), true⟩
    | some false => error τ

def foldRed (σ : PS) (τ : PPA) (C : IClause) := C.foldlM (sevalRed σ) ⟨τ.reset, false, false⟩

def reduced? (σ : PS) (τ : PPA) (C : IClause) : ReductionResult × PPA :=
  match foldRed σ τ C with
  | ok ⟨τ, true, false⟩  => (.falsified, τ)
  | ok ⟨τ, true, true⟩   => (.reduced, τ)
  | ok ⟨τ, false, true⟩  => (.notReduced, τ)
  | ok ⟨τ, false, false⟩ => (.notReduced, τ) -- Shouldn't get this case, except if C is empty
  | error τ => (.satisfied, τ)

theorem reduced?_satisfied_iff {σ : PS} {τ τ' : PPA} {C : IClause} :
    σ.reduced? τ C = (.satisfied, τ') ↔ (C.toPropFun).substL σ.toSubst = ⊤ := by
  sorry
  done

theorem reduced?_falsified_iff {σ : PS} {τ τ' : PPA} {C : IClause} :
    σ.reduced? τ C = (.falsified, τ') ↔ (C.toPropFun).substL σ.toSubst ≤ ⊥ := by
  sorry
  done

theorem reduced?_notReduced_iff {σ : PS} {τ τ' : PPA} {C : IClause} :
    σ.reduced? τ C = (.notReduced, τ') ↔ (C.toPropFun).substL σ.toSubst = ↑C := by
  sorry
  done

theorem reduced?_reduced {σ : PS} {τ τ' : PPA} {C : IClause} :
    σ.reduced? τ C = (.reduced, τ') →
      ((C.toPropFun).substL σ.toSubst ≠ ⊤ ∧ (C.toPropFun).substL σ.toSubst ≠ ⊥) := by
  sorry
  done

/- Reduction without tautology checking -/

def seval (σ : PS) (p : Bool × Bool) (l : ILit) : Except Unit (Bool × Bool) :=
  -- Has there been a non-id map, and has there been a literal that's unassigned
  let ⟨reduced?, unassigned?⟩ := p
  match σ.litValue l with
  | .tr => error ()
  | .fls => ok (true, unassigned?)
  | .lit lit => ok (reduced? || (l != lit), true)

def reduce (σ : PS) (C : IClause) : ReductionResult :=
  match C.foldlM (seval σ) (false, false) with
  | ok (true, true) => .reduced
  | ok (true, false) => .falsified
  | ok (false, true) => .notReduced
  | ok (false, false) => .notReduced -- Shouldn't get this, unless if C is empty
  | error () => .satisfied

-- TODO: It is possible only the forward directions are needed
theorem reduce_satisfied_iff {σ : PS} {C : IClause} :
    σ.reduce C = .satisfied ↔ (C.toPropFun).substL σ.toSubst = ⊤ := by
  sorry
  done

theorem reduce_falsified_iff {σ : PS} {C : IClause} :
    σ.reduce C = .falsified ↔ (C.toPropFun).substL σ.toSubst ≤ ⊥ := by
  sorry
  done

theorem reduce_notReduced_iff {σ : PS} {C : IClause} :
    σ.reduce C = .notReduced ↔ (C.toPropFun).substL σ.toSubst = ↑C := by
  sorry
  done

theorem reduce_reduced {σ : PS} {C : IClause} :
    σ.reduce C = .reduced ↔
      ((C.toPropFun).substL σ.toSubst ≠ ⊤ ∧ (C.toPropFun).substL σ.toSubst ≠ ⊥) := by
  sorry
  done

end monadic

end PS
