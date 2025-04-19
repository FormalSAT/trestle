/-
Copyright (c) 2025 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Experiments.SR.Data.PS.Defs
import Trestle.Model.Subst

namespace Trestle.PS

open Trestle Model Nat
open LitVar ILit IVar LawfulLitVar
open PropFun

-- CC: Maybe make the type `IVar → PropFun IVar`?
abbrev PSubst := (IVar → PropForm IVar)

-- CC: Defined here because we don't want to include `PropFun` in `Defs.lean`.
def PSV.toPropForm : PSV → PropForm IVar
  | Sum.inl l => LitVar.toPropForm l
  | Sum.inr true => .tr
  | Sum.inr false => .fls

-- CC: Defined here because we don't want to include `PropFun` in `Defs.lean`.
def PSV.toPropFun : PSV → PropFun IVar
  | Sum.inl l => LitVar.toPropFun l
  | Sum.inr true => ⊤
  | Sum.inr false => ⊥

@[simp]
theorem PSV.toPropForm_eq_toPropFun (p : PSV)
    : ⟦PSV.toPropForm p⟧ = PSV.toPropFun p := by
  match p with | .inl l | .inr true | .inr false => simp [PSV.toPropForm, PSV.toPropFun]

@[simp]
theorem PSV.negate_toPropFun (p : PSV)
    : PSV.toPropFun (PSV.negate p) = (PSV.toPropFun p)ᶜ := by
  match p with | .inl l | .inr true | .inr false => simp [PSV.negate, PSV.toPropFun]

def toSubst_fun (σ : PS) : PSubst → Fin σ.size → PSubst :=
  fun σ' idx => (fun v =>
    if v.index = idx.val then
      match σ.varValue v with
      | .inl l => toPropForm l
      | .inr true => PropForm.tr
      | .inr false => PropForm.fls
    else σ' v)

def toSubst (σ : PS) : PSubst :=
  Fin.foldl σ.size (init := .var) (toSubst_fun σ)

theorem toSubst_fun_comm (σ : PS) :
  ∀ (σ' : PSubst) (idx₁ idx₂ : Fin σ.size),
    (toSubst_fun σ) ((toSubst_fun σ) σ' idx₁) idx₂ =
    (toSubst_fun σ) ((toSubst_fun σ) σ' idx₂) idx₁ := by
  intro σ idx₁ idx₂
  unfold toSubst_fun
  apply funext
  intro v
  by_cases hidx : idx₁.val = idx₂.val
  <;> by_cases hv₁ : v.index = idx₁.val
  <;> by_cases hv₂ : v.index = idx₂.val
  <;> try simp [hv₁, hv₂, hidx]

theorem toSubst_of_comm (σ : PS) {v : IVar} (hv : v.index < σ.size) :
    ∃ σ', σ.toSubst = (toSubst_fun σ) σ' ⟨v.index, hv⟩ :=
  Fin.foldl_of_comm σ.size (toSubst_fun σ) .var ⟨v.index, hv⟩ (toSubst_fun_comm σ)

theorem toSubst_eq_of_ge {σ : PS} {v : IVar} :
    v.index ≥ σ.size → σ.toSubst v = v := by
  intro hv
  unfold toSubst
  apply Fin.foldl_induction' σ.size σ.toSubst_fun PropForm.var (· v = PropForm.var v) rfl
  intro σ' ⟨i, hi⟩ hv'
  rw [toSubst_fun]
  split
  <;> rename_i h_idx
  · omega
  · rw [hv']

instance : ToString PS where
  toString σ := String.intercalate " ∧ "
    (σ.mappings.foldl (init := []) (fun acc a => s!"{PSV.fromMappedNat a}" :: acc))

@[simp]
theorem fromMappedNat_IVarToMappedNat (v : IVar)
    : PSV.fromMappedNat (IVarToMappedNat v) = v := by
  have ⟨v, hv⟩ := v
  simp [IVarToMappedNat, PSV.fromMappedNat]
  split <;> try omega
  rename_i n h
  have : n % 2 = 0 := by omega
  simp [this]
  congr
  omega

-- CC: This proof can probably be simplified with lemmas relating `IVarToMapped` and `ILitToMapped`
@[simp]
theorem fromMappedNat_ILitToMappedNat (l : ILit)
    : PSV.fromMappedNat (ILitToMappedNat l) = l := by
  simp [PSV.fromMappedNat, ILitToMappedNat]
  by_cases hpol : polarity l
  <;> simp [hpol]
  · have ⟨l, hl⟩ := l
    split <;> try omega
    · rename_i h
      simp only [_root_.mul_eq_zero, Int.natAbs_eq_zero, OfNat.ofNat_ne_zero, or_false] at h
      exact absurd h hl
    · rename_i n h
      simp only [succ_eq_add_one] at h
      have : n % 2 = 0 := by omega
      simp only [this, ↓reduceIte, mkPos, ne_eq, Int.ofNat_eq_coe, cast_add,
        Int.ofNat_ediv, cast_ofNat, cast_one, Sum.inl.injEq]
      congr
      simp only [polarity, decide_eq_true_eq] at hpol
      omega
  · have ⟨l, hl⟩ := l
    split <;> try omega
    · rename_i h
      simp only [Nat.add_eq_right, _root_.mul_eq_zero, Int.natAbs_eq_zero,
        OfNat.ofNat_ne_zero, or_false] at h
      exact absurd h hl
    · rename_i n h
      simp only [succ_eq_add_one, Nat.add_left_inj] at h
      have : n % 2 = 1 := by omega
      simp only [this, one_ne_zero, ↓reduceIte, mkNeg, ne_eq,
        Int.ofNat_eq_coe, cast_add, Int.ofNat_ediv, cast_ofNat,
        cast_one, neg_add_rev, Int.reduceNeg, Sum.inl.injEq]
      congr
      simp only [polarity, decide_eq_true_eq, not_lt] at hpol
      omega

/-! # negate -/

-- CC: This is probably too much machinery/abstraction, but the ability to
--     return `Nat` rather than `ILit ⊕ Bool` gives nice speedups in practice

@[simp]
theorem negateMappedNat_negateMappedNat (n : ℕ)
    : negateMappedNat (negateMappedNat n) = n := by
  by_cases hn : n % 2 = 0
  <;> simp [negateMappedNat, hn]
  · simp [succ_mod_two_eq_one_iff.mpr hn]
  · have : (n - 1) % 2 = 0 := by omega
    simp only [this, ↓reduceIte]
    rw [Nat.sub_add_cancel (by omega)]

@[simp]
theorem litValue_Nat_negate (σ : PS) (l : ILit)
    : σ.litValue_Nat (-l) = negateMappedNat (σ.litValue_Nat l) := by
  cases hpol : polarity l <;> simp [hpol, litValue_Nat]

theorem PSV.negate_eq_iff_eq_negate {p₁ p₂ : PSV}
    : PSV.negate p₁ = p₂ ↔ p₁ = PSV.negate p₂ := by
  cases p₁ <;> cases p₂
  <;> simp [negate]
  · exact neg_eq_iff_eq_neg

@[simp]
theorem PSV.negate_bool (b : Bool) : PSV.negate (.inr b) = (.inr !b) :=
  rfl

@[simp]
theorem PSV.negate_mkPos (v : IVar)
    : PSV.negate (.inl (mkPos v)) = (.inl (mkNeg v)) :=
  rfl

@[simp]
theorem PSV.negate_mkNeg (v : IVar)
    : PSV.negate (.inl (mkNeg v)) = (.inl (mkPos v)) := by
  simp only [negate, neg_mkNeg]

@[simp]
theorem PSV.negate_neg (l : ILit) : PSV.negate (.inl l) = .inl (-l) :=
  rfl

@[simp]
theorem fromMappedNat_negateMappedNat (n : ℕ)
    : PSV.fromMappedNat (negateMappedNat n) = PSV.negate (PSV.fromMappedNat n) := by
  simp [negateMappedNat, PSV.fromMappedNat]
  match n with
  | 0 => simp only [zero_mod, ↓reduceIte, zero_add, PSV.negate_bool, Bool.not_true]
  | 1 => simp only [mod_succ, one_ne_zero, ↓reduceIte, tsub_self, PSV.negate_bool, Bool.not_false]
  | (n + 2) =>
    by_cases hn : (n + 2) % 2 = 0
    <;> simp [hn]
    -- CC: All these omega proofs make me sad
    · have : (n + 1) % 2 = 1 := by omega
      simp [this]
      have : n % 2 = 0 := by omega
      simp [this]
      have : (n + 1) / 2 + 1 = n / 2 + 1 := by omega
      simp [this]
    · have : n % 2 = 1 := by omega
      simp [this]
      split <;> try omega
      rename_i hn
      simp at hn
      subst hn
      rename_i n
      simp [succ_mod_two_eq_one_iff.mp this]
      have : (n + 1) / 2 + 1 = n / 2 + 1 := by omega
      simp [this]

@[simp]
theorem litValue_negate (σ : PS) (l : ILit) :
    (σ.litValue (-l)) = PSV.negate (σ.litValue l) := by
  cases hpol : polarity l
  <;> simp only [litValue, litValue_Nat_negate, fromMappedNat_negateMappedNat]

theorem litValue_eq_varValue_pos {l : ILit} :
    polarity l = true → ∀ (σ : PS), σ.litValue l = σ.varValue (toVar l) := by
  intro hl σ
  simp only [litValue, litValue_Nat, hl, ↓reduceIte, varValue]

theorem litValue_eq_varValue_neg {l : ILit} :
    polarity l = false → ∀ (σ : PS), σ.litValue l = PSV.negate (σ.varValue (toVar l)) := by
  intro hl
  simp only [litValue, litValue_Nat, hl, Bool.false_eq_true, ↓reduceIte,
    fromMappedNat_negateMappedNat, varValue, implies_true]

theorem litValue_eq_varValue_neg' {l : ILit}
    : polarity l = false → ∀ (σ : PS), σ.litValue (-l) = σ.varValue (toVar l) := by
  intro hl
  simp only [litValue, litValue_Nat, polarity_negate, hl, Bool.not_false,
    ↓reduceIte, toVar_negate, varValue, implies_true]

@[simp]
theorem litValue_mkPos (σ : PS) (v : IVar)
    : σ.litValue (mkPos v) = σ.varValue v := by
  apply litValue_eq_varValue_pos (by simp)

@[simp]
theorem litValue_mkNeg (σ : PS) (v : IVar)
    : σ.litValue (mkNeg v) = PSV.negate (σ.varValue v) := by
  have := litValue_eq_varValue_neg (l := mkNeg v)
  simp at this
  exact this σ

theorem lt_size_of_varValue_of_not_id {σ : PS} {v : IVar}
    : σ.varValue v ≠ .inl (mkPos v) → v.index < σ.size := by
  intro hv
  by_contra
  rename (¬v.index < σ.size) => h_con
  simp [varValue, varValue_Nat, h_con] at hv

theorem varValue_eq_of_ge {σ : PS} {v : IVar}
    : v.index ≥ σ.size → σ.varValue v = .inl (mkPos v) := by
  contrapose
  simp only [ge_iff_le, not_le]
  exact lt_size_of_varValue_of_not_id

theorem lt_size_of_litValue_of_not_id {σ : PS} {l : ILit} :
    σ.litValue l ≠ .inl l → l.index < σ.size := by
  intro h
  rw [← ILit.toVar_index]
  apply lt_size_of_varValue_of_not_id
  intro h_con
  rcases mkPos_or_mkNeg l with (hl | hl)
  · have hpol : polarity l = true := by rw [hl]; simp only [polarity_mkPos]
    rw [litValue_eq_varValue_pos hpol σ, hl] at h
    simp only [toVar_mkPos, h_con, ne_eq, not_true_eq_false] at h
  · have hpol : polarity l = false := by rw [hl]; simp only [polarity_mkNeg]
    rw [litValue_eq_varValue_neg hpol σ, hl] at h
    simp [h_con] at h

theorem litValue_eq_of_ge {σ : PS} {l : ILit}
    : l.index ≥ σ.size → σ.litValue l = .inl l := by
  contrapose
  simp only [ge_iff_le, not_le]
  exact lt_size_of_litValue_of_not_id

@[simp]
theorem varValue_eq_toSubst (σ : PS) (v : IVar)
    : PSV.toPropForm (σ.varValue v) = σ.toSubst v := by
  by_cases hv : v.index < σ.size
  · have ⟨σ', hσ'⟩ := toSubst_of_comm σ hv
    simp only [PSV.toPropForm, hσ', toSubst_fun, ↓reduceIte]
  · rw [not_lt] at hv
    simp only [PSV.toPropForm, varValue_eq_of_ge hv,
      toPropForm_mkPos, toSubst_eq_of_ge hv]

@[simp]
theorem varValue_eq {σ : PS} {v : IVar}
    : PSV.toPropFun (σ.varValue v) = PropFun.substL (.var v) σ.toSubst := by
  rcases Nat.lt_or_ge v.index σ.size with (h_lt | h_ge)
  · rcases toSubst_of_comm σ h_lt with ⟨σ', hσ'⟩
    simp [hσ', toSubst_fun]
    split
    <;> rename_i h
    <;> simp [h, PSV.toPropFun]
  · simp [varValue_eq_of_ge h_ge, toSubst_eq_of_ge h_ge, PSV.toPropFun]

@[simp]
theorem varValue_false_iff {σ : PS} {v : IVar}
    : σ.varValue v = .inr false ↔ PropFun.substL (.var v) σ.toSubst = ⊥ := by
  simp only [← varValue_eq, PSV.toPropFun]
  split <;> simp_all

-- CC: Similar proofs here. Dunno why I can't use `varValue_eq`...
@[simp]
theorem varValue_true_iff {σ : PS} {v : IVar}
    : σ.varValue v = .inr true ↔ PropFun.substL (.var v) σ.toSubst = ⊤ := by
  rcases Nat.lt_or_ge v.index σ.size with (h_lt | h_ge)
  · rcases toSubst_of_comm σ h_lt with ⟨σ', hσ'⟩
    simp [hσ', toSubst_fun, h_lt]
    split
    <;> rename_i hv
    <;> simp [hv]
  · simp [varValue_eq_of_ge h_ge, toSubst_eq_of_ge h_ge]

@[simp]
theorem varValue_lit_iff {σ : PS} {v : IVar} {l : ILit}
    : σ.varValue v = .inl l ↔ PropFun.substL (.var v) σ.toSubst = l := by
  rcases Nat.lt_or_ge v.index σ.size with (h_lt | h_ge)
  · rcases toSubst_of_comm σ h_lt with ⟨σ', hσ'⟩
    simp [hσ', toSubst_fun, h_lt]
    split
    <;> rename_i hv
    <;> simp [hv]
  · simp [varValue_eq_of_ge h_ge, toSubst_eq_of_ge h_ge]
    exact eq_comm

@[simp]
theorem litValue_eq {σ : PS} {l : ILit}
    : PSV.toPropFun (σ.litValue l) = PropFun.substL l σ.toSubst := by
  rcases exists_mkPos_or_mkNeg l with ⟨v, rfl | rfl⟩
  <;> simp

@[simp]
theorem litValue_false_iff {σ : PS} {l : ILit} :
    (σ.litValue l = .inr false) ↔ PropFun.substL l σ.toSubst = ⊥ := by
  rcases exists_mkPos_or_mkNeg l with ⟨v, rfl | rfl⟩
  <;> simp [PSV.negate_eq_iff_eq_negate]

theorem litValue_true_iff {σ : PS} {l : ILit} :
    (σ.litValue l = .inr true) ↔ PropFun.substL l σ.toSubst = ⊤ := by
  rcases exists_mkPos_or_mkNeg l with ⟨v, rfl | rfl⟩
  <;> simp [PSV.negate_eq_iff_eq_negate]

theorem litValue_lit_iff {σ : PS} {l₁ l₂ : ILit} :
    (σ.litValue l₁ = .inl l₂) ↔ PropFun.substL l₁ σ.toSubst = l₂ := by
  rcases exists_mkPos_or_mkNeg l₁ with ⟨v, rfl | rfl⟩
  <;> simp [PSV.negate_eq_iff_eq_negate, eq_compl_iff_compl_eq]


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

def setVars (σ : PS) (L : List (IVar × ILit)) : PS :=
  L.foldl (init := σ) (fun σ ⟨v, l⟩ => σ.setVarToLit v l)

def setVars' (σ : PS) (A : Array (IVar × ILit)) : PS :=
  A.foldl (init := σ) (fun σ ⟨v, l⟩ => σ.setVarToLit v l)

def setVarsUntil (σ : PS) (L : List (IVar × ILit)) (gen : Nat) : PS :=
  L.foldl (init := σ) (fun σ ⟨v, l⟩ => σ.setVarToLitUntil v l gen)

def setVarsUntil' (σ : PS) (A : Array (IVar × ILit)) (gen : Nat) : PS :=
  A.foldl (init := σ) (fun σ ⟨v, l⟩ => σ.setVarToLitUntil v l gen)

theorem setVars_eq_setVars' {L : List (IVar × ILit)} {A : Array (IVar × ILit)} :
  L = A.data → ∀ (σ : PS), σ.setVars L = σ.setVars' A := by sorry

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

--ofFn (fun (idx : Fin maxVar) => PSCell.mkCell idx 0)

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

abbrev UPBox := ResultT UPDone (Option ILit)

open ResultT UPResult UPDone PPA

def sevalUP (σ : PS) (unit? : Option ILit) (l : ILit) : UPBox :=
  match σ.litValue l with
  | .tr => done .satisfied
  | .fls => ok unit?
  | .lit lit =>
    match unit? with
    | none => ok lit
    | some u =>
      if u = lit then ok unit?
      -- Since σ is a substitution, tautology could occur
      else if u = -lit then done .satisfied
      else done .multipleUnassignedLiterals

def foldUP (σ : PS) (C : IClause) := C.foldlM (sevalUP σ) none

def unitProp (σ : PS) (C : IClause) : UPResult :=
  match foldUP σ C with
  | ok none => .falsified
  | ok (some lit) => .unit lit (σ.setLit lit)
  | done .satisfied => .satisfied
  | done .multipleUnassignedLiterals => .multipleUnassignedLiterals

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
      simp only [SatisfiesM_ResultT_eq, getElem_fin]
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
          rcases Order.lt_succ_iff_eq_or_lt.mp hj with (hj | hj)
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
            · simp [ne_of_var_ne hvar, ne_of_var_ne ((toVar_negate lit).symm ▸ hvar)] at hbox
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
            · simp [ne_of_var_ne hvar, ne_of_var_ne ((toVar_negate lit').symm ▸ hvar)] at hbox)
  apply SatisfiesM.imp this
  intro
  | none =>
    intro h l hl
    rcases Array.mem_data_iff.mp hl with ⟨i, rfl⟩
    exact h i.isLt
  | some lit =>
    simp [UP_motive_fn]
    intro i hi ih
    use C[i.val], Array.getElem_mem_data C i.isLt, hi
    intro l hl₁ hl₂
    rcases Array.mem_data_iff.mp hl₁ with ⟨j, rfl⟩
    apply ih
    exact ne_of_apply_ne (C[·]) hl₂

theorem contradiction_of_UP_falsified {σ : PS} {C : IClause} :
    σ.unitProp C = .falsified → (C.toPropFun).bind σ.toSubst ≤ ⊥ := by
  unfold unitProp
  intro h_falsified
  split at h_falsified <;> try simp at h_falsified
  clear h_falsified
  rename (foldUP σ C = ok none) => h
  refine entails_ext.mpr fun τ hτ => ?_
  rw [satisfies_bind] at hτ
  have ⟨lit, hlit, hτlit⟩ := Clause.satisfies_iff.mp hτ
  have := SatisfiesM_ResultT_eq.mp (SatisfiesM_UP σ C) none h lit hlit
  clear h hτ
  replace hτlit := satisfies_iff.mp hτlit
  cases hpol : polarity lit
  <;> simp [hpol, PropAssignment.preimage] at hτlit
  · rw [litValue_eq_varValue_neg hpol, PSVal.negate_rhs_eq_lhs_negate, PSVal.negate,
          varValue_tr_iff, bind_distrib] at this
    rw [this] at hτlit
    contradiction
  · rw [litValue_eq_varValue_pos hpol, varValue_fls_iff, bind_distrib] at this
    rw [this] at hτlit
    exact hτlit

theorem extended_of_UP_unit {σ σ' : PS} {C : IClause} {l : ILit} :
    σ.unitProp C = .unit l σ' →
      (C.toPropFun).bind σ.toSubst ≤ l.toPropFun ∧
      (∃ lit ∈ C.data, σ.litValue lit = .lit l ∧ σ'.litValue l = .tr) := by
      -- Cayden question: how to express this in an abstract way? Perhaps with a bind (l.bind σ) or as a (. ∘ .) of two subs
  unfold unitProp
  intro h_unit
  split at h_unit <;> try simp at h_unit
  --clear h_unit
  rename ILit => lit
  rename (foldUP σ C = ok (some lit)) => h
  rcases h_unit with ⟨rfl, rfl⟩
  have hlv := SatisfiesM_ResultT_eq.mp (SatisfiesM_UP σ C) (some lit) h
  clear h
  rcases hlv with ⟨l, hl_mem, hσl, ih⟩
  constructor
  · refine entails_ext.mpr fun τ hτ => ?_
    rw [satisfies_bind] at hτ
    by_cases heq : l = lit
    · subst heq
      rw [Clause.satisfies_iff] at hτ; rcases hτ with ⟨l', hl'_mem, hl'⟩
      rw [← satisfies_bind] at hl'
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

abbrev RedBox := ResultT PPA (PPA × Bool × Bool)

open ResultT ReductionResult

def sevalRed (σ : PS) (p : PPA × Bool × Bool) (l : ILit) : RedBox :=
  let ⟨τ, reduced?, unassigned?⟩ := p
  match σ.litValue l with
  | .tr => done τ
  | .fls => ok ⟨τ, true, unassigned?⟩
  | .lit lit =>
    match τ.litValue? lit with
    | none => ok ⟨τ.setLit lit, reduced? || (l != lit), true⟩
    | some true => ok ⟨τ, reduced? || (l != lit), true⟩
    | some false => done τ

def foldRed (σ : PS) (τ : PPA) (C : IClause) := C.foldlM (sevalRed σ) ⟨τ.reset, false, false⟩

def reduced? (σ : PS) (τ : PPA) (C : IClause) : ReductionResult × PPA :=
  match foldRed σ τ C with
  | ok ⟨τ, true, false⟩  => (.falsified, τ)
  | ok ⟨τ, true, true⟩   => (.reduced, τ)
  | ok ⟨τ, false, true⟩  => (.notReduced, τ)
  | ok ⟨τ, false, false⟩ => (.notReduced, τ) -- Shouldn't get this case, except if C is empty
  | done τ => (.satisfied, τ)

theorem reduced?_satisfied_iff {σ : PS} {τ τ' : PPA} {C : IClause} :
    σ.reduced? τ C = (.satisfied, τ') ↔ (C.toPropFun).bind σ.toSubst = ⊤ := by
  sorry
  done

theorem reduced?_falsified_iff {σ : PS} {τ τ' : PPA} {C : IClause} :
    σ.reduced? τ C = (.falsified, τ') ↔ (C.toPropFun).bind σ.toSubst ≤ ⊥ := by
  sorry
  done

theorem reduced?_notReduced_iff {σ : PS} {τ τ' : PPA} {C : IClause} :
    σ.reduced? τ C = (.notReduced, τ') ↔ (C.toPropFun).bind σ.toSubst = ↑C := by
  sorry
  done

theorem reduced?_reduced {σ : PS} {τ τ' : PPA} {C : IClause} :
    σ.reduced? τ C = (.reduced, τ') →
      ((C.toPropFun).bind σ.toSubst ≠ ⊤ ∧ (C.toPropFun).bind σ.toSubst ≠ ⊥) := by
  sorry
  done

/- Reduction without tautology checking -/

def seval (σ : PS) (p : Bool × Bool) (l : ILit) : ResultT Unit (Bool × Bool) :=
  -- Has there been a non-id map, and has there been an literal that's unassigned
  let ⟨reduced?, unassigned?⟩ := p
  match σ.litValue l with
  | .tr => done ()
  | .fls => ok (true, unassigned?)
  | .lit lit => ok (reduced? || (l != lit), true)

def reduce (σ : PS) (C : IClause) : ReductionResult :=
  match C.foldlM (seval σ) (false, false) with
  | ok (true, true) => .reduced
  | ok (true, false) => .falsified
  | ok (false, true) => .notReduced
  | ok (false, false) => .notReduced -- Shouldn't get this, unless if C is empty
  | done () => .satisfied

-- TODO: It is possible only the forward directions are needed
theorem reduce_satisfied_iff {σ : PS} {C : IClause} :
    σ.reduce C = .satisfied ↔ (C.toPropFun).bind σ.toSubst = ⊤ := by
  sorry
  done

theorem reduce_falsified_iff {σ : PS} {C : IClause} :
    σ.reduce C = .falsified ↔ (C.toPropFun).bind σ.toSubst ≤ ⊥ := by
  sorry
  done

theorem reduce_notReduced_iff {σ : PS} {C : IClause} :
    σ.reduce C = .notReduced ↔ (C.toPropFun).bind σ.toSubst = ↑C := by
  sorry
  done

theorem reduce_reduced {σ : PS} {C : IClause} :
    σ.reduce C = .reduced ↔
      ((C.toPropFun).bind σ.toSubst ≠ ⊤ ∧ (C.toPropFun).bind σ.toSubst ≠ ⊥) := by
  sorry
  done

end monadic /- section -/

end Trestle.PS
