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
theorem fromMappedNat_MAPPED_TRUE : PSV.fromMappedNat MAPPED_TRUE = .inr true :=
  rfl

@[simp]
theorem fromMappedNat_MAPPED_FALSE : PSV.fromMappedNat MAPPED_FALSE = .inr false :=
  rfl

@[simp]
theorem toMappedNat_fromMappedNat (n : ℕ)
    : PSV.toMappedNat (PSV.fromMappedNat n) = n := by
  simp [PSV.fromMappedNat, PSV.toMappedNat]
  match n with
  | 0 => simp [MAPPED_TRUE]
  | 1 => simp [MAPPED_FALSE]
  | (n + 2) =>
    simp only
    by_cases hn : n % 2 = 0
    <;> simp [hn, ILitToMappedNat, mkPos, mkNeg, polarity]
    <;> split
    <;> omega  -- I ♥ omega

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

@[simp]
theorem fromMappedNat_toMappedNat (p : PSV)
    : PSV.fromMappedNat (PSV.toMappedNat p) = p := by
  match p with
  | .inl l | .inr true | .inr false => simp [PSV.toMappedNat]

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
  · simp only [PSV.toPropFun, varValue_eq_of_ge h_ge, toPropFun_mkPos,
      substL_distrib, toSubst_eq_of_ge h_ge, mk_var]

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
  · simp only [varValue_eq_of_ge h_ge, reduceCtorEq, substL_distrib,
      toSubst_eq_of_ge h_ge, mk_var, var_ne_top]

@[simp]
theorem varValue_lit_iff {σ : PS} {v : IVar} {l : ILit}
    : σ.varValue v = .inl l ↔ PropFun.substL (.var v) σ.toSubst = l := by
  rcases Nat.lt_or_ge v.index σ.size with (h_lt | h_ge)
  · rcases toSubst_of_comm σ h_lt with ⟨σ', hσ'⟩
    simp [hσ', toSubst_fun, h_lt]
    split
    <;> rename_i hv
    <;> simp [hv]
  · simp only [varValue_eq_of_ge h_ge, Sum.inl.injEq, substL_distrib,
      toSubst_eq_of_ge h_ge, mk_var, var_eq_toPropFun_iff]
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

@[simp]
theorem setLit_size (σ : PS) (l : ILit)
    : (σ.setLit l).size = max σ.size (l.index + 1) := by
  simp only [size, setLit, Array.size_setF]

@[simp]
theorem litValue_setLit_self (σ : PS) (l : ILit) : (σ.setLit l).litValue l = .inr true := by
  simp only [litValue, litValue_Nat, varValue_Nat, toVar_index, setLit,
    Array.length_toList, Array.size_setF, lt_sup_iff, lt_add_iff_pos_right,
    lt_one_iff, pos_of_gt, or_true, ↓reduceDIte, Array.getElem_setF_self,
    ge_iff_le, _root_.le_refl, ↓reduceIte, toMappedNat_fromMappedNat]
  by_cases hl : l.index < σ.size
  <;> by_cases hpol : polarity l
  <;> simp [hpol]

@[simp]
theorem litValue_setLit_of_ne {l₁ l₂ : ILit} (h_ne : toVar l₁ ≠ toVar l₂) (σ : PS) :
    (σ.setLit l₁).litValue l₂ = σ.litValue l₂ := by
  simp [setLit, litValue, litValue_Nat, varValue_Nat]
  congr 1
  congr 1
  · by_cases hl₂ : l₂.index < σ.size
    <;> simp [hl₂]
    · have hl₂' : l₂.index < σ.mappings.size := by
        rw [← σ.sizes_eq]; exact hl₂
      simp [index_ne_of_var_ne h_ne,
        Array.getElem_setF_lt _ l₁.index _ _ _ hl₂,
        Array.getElem_setF_lt _ l₁.index _ _ _ hl₂']
    · intro hl₂'
      have hi : σ.size ≤ l₁.index := by omega
      simp [Array.getElem_setF_ge_lt _ _ hi _ _ _ (Nat.ge_of_not_lt hl₂) hl₂',
        index_ne_of_var_ne h_ne]
  · congr 1
    -- CC: Duplicate proof after this point
    by_cases hl₂ : l₂.index < σ.size
    <;> simp [hl₂]
    · have hl₂' : l₂.index < σ.mappings.size := by
        rw [← σ.sizes_eq]; exact hl₂
      simp [index_ne_of_var_ne h_ne,
        Array.getElem_setF_lt _ l₁.index _ _ _ hl₂,
        Array.getElem_setF_lt _ l₁.index _ _ _ hl₂']
    · intro hl₂'
      have hi : σ.size ≤ l₁.index := by omega
      simp [Array.getElem_setF_ge_lt _ _ hi _ _ _ (Nat.ge_of_not_lt hl₂) hl₂',
        index_ne_of_var_ne h_ne]

/-! # setVarToLit -/

@[simp]
theorem setVarToLit_size (σ : PS) (v : IVar) (l : ILit)
    : (σ.setVarToLit v l).size = max σ.size (v.index + 1) := by
  simp only [size, setVarToLit, Array.size_setF]

@[simp]
theorem varValue_setVarToLit_self (σ : PS) (v : IVar) (l : ILit)
    : (σ.setVarToLit v l).varValue v = .inl l := by
  simp only [varValue, varValue_Nat, setVarToLit, Array.length_toList,
    Array.size_setF, lt_sup_iff, lt_add_iff_pos_right, lt_one_iff, pos_of_gt,
    or_true, ↓reduceDIte, Array.getElem_setF_self, ge_iff_le, _root_.le_refl,
    ↓reduceIte, fromMappedNat_toMappedNat]

-- CC: Somewhat duplicated proof from `litValue_setLit_of_ne`
@[simp]
theorem varValue_setVarToLit_ne (σ : PS) {v₁ v₂ : IVar} (h : v₁ ≠ v₂) (l : ILit)
    : (σ.setVarToLit v₁ l).varValue v₂ = σ.varValue v₂ := by
  simp [setVarToLit, varValue, varValue_Nat]
  congr 1
  by_cases hv₂ : v₂.index < σ.size
  <;> simp [hv₂]
  · simp [h, Array.getElem_setF_lt _ v₁.index _ _ _ hv₂]
    congr 1
    have hv₂' : v₂.index < σ.mappings.size := by
      rw [← σ.sizes_eq]; exact hv₂
    simp only [Array.getElem_setF_lt _ v₁.index _ _ _ hv₂',
      index_eq_iff, h, ↓reduceIte]
  · intro hv₂'
    have hi : σ.size ≤ v₁.index := by omega
    simp [Array.getElem_setF_ge_lt _ _ hi _ _ _ (Nat.ge_of_not_lt hv₂) hv₂',
      index_eq_iff, h, ↓reduceIte]

/-! # reduction -/

@[simp]
theorem reduceM.aux_nil (σ : PS) (b : Bool)
    : reduceM.aux σ { toList := [] } b = .ok b := by
  simp [reduceM.aux, pure, Except.pure]

@[simp]
theorem reduceM.aux_cons (σ : PS) (l : ILit) (ls : List ILit) (b : Bool)
    : reduceM.aux σ { toList := l :: ls } b =
        match σ.litValue l with
        | .inr true => .error ()
        | .inr false => reduceM.aux σ { toList := ls } true
        | .inl lit => reduceM.aux σ { toList := ls } (if l ≠ lit then true else b) := by
  unfold reduceM.aux sevalM
  simp only [ne_eq, ite_not, List.size_toArray, List.length_cons, Nat.add_left_inj,
      List.foldlM_toArray', List.foldlM_cons, Bool.if_true_right]
  match hl : σ.litValue l with
  | .inr true => rfl
  | .inr false => rfl
  | .inl lit =>
    by_cases h : l = lit
    <;> simp [h, hl, bind, Except.bind]

@[simp]
theorem reduceM.aux_true_ne_false (σ : PS) (ls : List ILit)
    : reduceM.aux σ { toList := ls } true ≠ .ok false := by
  induction ls with
  | nil => simp
  | cons l ls ih =>
    simp only [aux_cons, ne_eq, ite_self]
    match hl : σ.litValue l with
    | .inr true
    | .inr false
    | .inl lit => simp [ih]

@[simp]
theorem reduce.loop_nil (σ : PS) (b : Bool)
    : reduce.loop σ { toList := [] } 0 b =
        if b then .reduced else .notReduced := by
  simp only [loop, List.size_toArray, List.length_nil, lt_self_iff_false, ↓reduceDIte]

-- CC: LOL same exact proof(s) as `PPA.unitProp.loop_cons_succ`
theorem reduce.loop_cons_succ (σ : PS) (l : ILit) (ls : List ILit) (n : Nat) (b : Bool)
    : ∀ {m : Nat}, m = ls.length - n →
        reduce.loop σ { toList := l :: ls } (n + 1) b
          = reduce.loop σ { toList := ls } n b := by
  intro m hm
  induction m generalizing n b with
  | zero =>
    unfold loop
    have : n ≥ ls.length := by exact Nat.le_of_sub_eq_zero (id (Eq.symm hm))
    simp [Nat.not_lt_of_ge this]
  | succ m ih =>
    unfold loop
    have hm' : m = ls.length - (n + 1) := by omega
    have hn : n < ls.length := by omega
    simp [hn, ih _ _ hm']

theorem reduce.loop_of_ge_length (σ : PS) (ls : List ILit) (n : Nat) (b : Bool)
    : n ≥ ls.length → reduce.loop σ { toList := ls } n b
                        = if b then .reduced else .notReduced := by
  intro hn
  unfold loop
  simp only [List.size_toArray, Nat.not_lt_of_le hn, ↓reduceDIte]

-- CC: A lot of repeat branches in this one
theorem reduce.loop_eq_reduceM.aux (σ : PS) (ls : List ILit)
      (n : Nat) (hn : n < ls.length) (b : Bool)
    : ∀ (m : Nat), m = ls.length - n →
        reduce.loop σ { toList := ls } n b = reduceM_Except (reduceM.aux σ { toList := ls.drop n } b) := by
  intro m hm
  induction m generalizing n b with
  | zero =>
    unfold loop
    have : n = ls.length := by omega
    simp [this, reduceM, reduceM_Except, pure, Except.pure]
    cases b <;> rfl
  | succ m ih =>
    unfold loop
    have hm' : m = ls.length - (n + 1) := by omega
    simp [hn]
    rw [List.drop_eq_getElem_cons hn, reduceM.aux_cons, seval]
    match h : σ.litValue ls[n] with
    | .inr true => simp [reduceM_Except]
    | .inr false =>
      rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hn) with (h | h)
      · have := Nat.le_of_eq h.symm
        simp only [reduce.loop_of_ge_length σ ls (n + 1) _ this]
        rw [List.drop_of_length_le this]
        cases b <;> simp [reduceM_Except]
      · exact ih _ h true hm'
    | .inl lit =>
      simp only
      by_cases h_lit : ls[n] = lit
      <;> simp [h_lit]
      · rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hn) with (h | h)
        · have := Nat.le_of_eq h.symm
          simp only [reduce.loop_of_ge_length σ ls (n + 1) _ this]
          rw [List.drop_of_length_le this]
          cases b <;> simp [reduceM_Except]
        · exact ih _ h b hm'
      · rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hn) with (h | h)
        · have := Nat.le_of_eq h.symm
          simp only [reduce.loop_of_ge_length σ ls (n + 1) _ this]
          rw [List.drop_of_length_le this]
          cases b <;> simp [reduceM_Except]
        · exact ih _ h true hm'

theorem reduce_eq_reduceM (σ : PS) (C : IClause) :
    σ.reduce C = σ.reduceM C := by
  have ⟨C⟩ := C
  unfold reduce reduceM
  match C with
  | [] => simp [reduceM_Except]
  | l :: ls =>
    exact reduce.loop_eq_reduceM.aux σ (l :: ls) 0 (by simp [List.length]) _ (l :: ls).length rfl

/-! ### reduction correctness wrt `PropFun` -/

theorem reduceM.aux_true {σ : PS} {C : List ILit} {b : Bool}
    : reduceM.aux σ { toList := C } b = .ok false
        → PropFun.substL (Clause.toPropFun { toList := C}) σ.toSubst = (Clause.toPropFun { toList := C }) := by
  intro h_aux
  induction C with
  | nil => simp
  | cons l ls ih =>
    simp only [aux_cons] at h_aux
    match hl : σ.litValue l with
    | .inr true => simp only [hl, reduceCtorEq] at h_aux
    | .inr false => simp only [hl, aux_true_ne_false] at h_aux
    | .inl lit =>
      simp only [hl, ne_eq, ite_not, Bool.if_true_right] at h_aux
      by_cases h_lit : l = lit
      <;> simp [h_lit] at h_aux
      subst h_lit
      have := litValue_lit_iff.mp hl
      simp [ih h_aux, this]

#exit
-- TODO: It is possible only the forward directions are needed
@[simp]
theorem reduce_satisfied_iff {σ : PS} {C : IClause} :
    σ.reduce C = .satisfied ↔ PropFun.substL C.toPropFun σ.toSubst = ⊤ := by
  have ⟨C⟩ := C
  induction C with
  | nil => simp
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

end PS

end Trestle
