/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Experiments.SR.Checker.SRChecker
import Experiments.SR.Data.PPA.Thm
import Experiments.SR.Data.PS.Thm
import Experiments.SR.Data.RangeArray.Thm
import Trestle.Model.PropFun
import Trestle.Data.Cnf.Basic
import Trestle.Data.ICnf.Basic

namespace Trestle.SR

open RangeArray PPA PS
open Trestle Trestle.Model PropFun
open Except

/-

  We model `RangeArray`s with a list of `Option (List ILit)` for the formula
  clauses and a `List ILit` for the candidate redudant clause.

  We need a way of converting those into `PropFun`. We manually define
  that transformation here.

  Note that we assume "empty"/deleted clauses are `⊤` instead of `⊥`.

-/

private def clauseAsListToPropFun (C : List ILit) : PropFun IVar :=
  Clause.toPropFun { toList := C }

private def cnfAsListToPropFun (Cs : List (Option (List ILit))) : PropFun IVar :=
  .all (Cs.map (fun C =>
    match C with
    | none => ⊤
    | some C => clauseAsListToPropFun C))

@[simp]
theorem clauseAsListToPropFun_eq_toPropFun (C : List ILit)
    : clauseAsListToPropFun C = Clause.toPropFun ({ toList := C } : IClause) :=
  rfl

-- To avoid the empty clause problem, we use `[1, ¬1]`.
theorem cnfAsListToPropFun_eq_toPropFun (Cs : List (Option (List ILit)))
    : cnfAsListToPropFun Cs = Cnf.toPropFun ({ toList := Cs.map (fun cl =>
        match cl with
        | none => { toList := [LitVar.mkPos 1, LitVar.mkNeg 1] }
        | some C => { toList := C }) } : ICnf) := by
  simp [cnfAsListToPropFun]
  induction Cs with
  | nil => simp
  | cons C Cs ih =>
    match C with
    | none => simp [ih]
    | some C => simp [← ih, PropFun.all]

@[simp]
theorem cnfAsListToPropFun_nil : cnfAsListToPropFun [] = ⊤ := by
  simp [cnfAsListToPropFun]

@[simp]
theorem cnfAsListToPropFun_cons_none (Cs : List (Option (List ILit))) :
  cnfAsListToPropFun (none :: Cs) = cnfAsListToPropFun Cs := by
  simp [cnfAsListToPropFun, all]

@[simp]
theorem cnfAsListToPropFun_cons_some (C : List ILit) (Cs : List (Option (List ILit))) :
  cnfAsListToPropFun (some C :: Cs) = clauseAsListToPropFun C ⊓ cnfAsListToPropFun Cs := by
  simp [cnfAsListToPropFun, all]

@[simp]
theorem cnfAsListToPropFun_cons (C : Option (List ILit)) (Cs : List (Option (List ILit))) :
  cnfAsListToPropFun (C :: Cs) =
    (match C with
    | none => ⊤
    | some C => clauseAsListToPropFun C) ⊓ cnfAsListToPropFun Cs := by
  cases C <;> simp

@[simp]
theorem cnfAsListToPropFun_append (Cs₁ Cs₂ : List (Option (List ILit))) :
  cnfAsListToPropFun (Cs₁ ++ Cs₂) = cnfAsListToPropFun Cs₁ ⊓ cnfAsListToPropFun Cs₂ := by
  induction Cs₁ with
  | nil => simp
  | cons C Cs₁ ih =>
    simp [List.append]
    cases C <;> simp [ih, inf_assoc]

@[simp]
theorem cnfAsListToPropFun_replicate_none (n : Nat) :
    cnfAsListToPropFun (List.replicate n none) = ⊤ := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [List.replicate]
    exact ih

theorem clausePropFun_ge_of_mem {C : List ILit} {l : ILit}
    : l ∈ C → l.toPropFun ≤ clauseAsListToPropFun C := by
  intro h
  rw [clauseAsListToPropFun_eq_toPropFun]
  apply Clause.toPropFun_mem_le
  simp only [Array.mem_toArray, h]

theorem cnfPropFun_le_of_mem {Cs : List (Option (List ILit))} {C : List ILit} {i : Nat}
      {hi : i < Cs.length} :
    Cs.get ⟨i, hi⟩ = some C → cnfAsListToPropFun Cs ≤ clauseAsListToPropFun C := by
  intro h
  simp [cnfAsListToPropFun_eq_toPropFun]
  induction Cs generalizing i with
  | nil => simp at hi
  | cons X Xs ih =>
    match X with
    | none =>
      match i with
      | 0 => simp at h
      | i + 1 =>
        simp at hi h
        simp [ih h]
    | some X =>
      match i with
      | 0 =>
        simp at h; subst h
        simp [clauseAsListToPropFun_eq_toPropFun]
      | i + 1 =>
        simp at h
        have := ih h
        apply le_trans _ this
        simp

theorem cnfPropFun_le_set_none {Cs : List (Option (List ILit))}
  {i : Nat} (hi : i < Cs.length) :
    cnfAsListToPropFun Cs ≤ cnfAsListToPropFun (Cs.set i none) := by
  induction Cs generalizing i with
  | nil => contradiction
  | cons C Cs ih =>
    cases i with
    | zero => simp [List.set]
    | succ i =>
      simp [List.set]
      simp at hi
      apply le_trans _ (ih hi)
      cases C <;> simp

theorem list_satisfies_iff {τ : PropAssignment IVar} {Cs : List (Option (List ILit))} :
    τ ⊨ cnfAsListToPropFun Cs ↔ ∀ {C : List ILit}, (some C) ∈ Cs → τ ⊨ clauseAsListToPropFun C := by
  simp [cnfAsListToPropFun_eq_toPropFun]
  induction Cs with
  | nil => simp
  | cons C Cs ih =>
    match C with
    | none => simp [ih]
    | some C =>
      simp at ih ⊢
      intro _
      exact ih

/-! # Correctness -/

theorem assumeNegatedCandidateFor.loop.aux {F : RangeArray ILit} {τ : PPA} {Ls : List (Option (List ILit))} {L : List ILit}
    (h_models : models F Ls L) {bumps : Nat} {i j : Nat}
  : j = L.length - i →
    assumeNegatedCandidateFor.loop F bumps (F.dsize + i) τ = assumeNegatedClauseFor.loop { toList := L } bumps i τ := by
  intro hj
  induction j generalizing τ i with
  | zero =>
    have h_le₁ := Nat.le_of_sub_eq_zero hj.symm
    have h_le₂ := h_models.h_size₂.symm ▸ h_le₁
    unfold assumeNegatedClauseFor.loop
    simp at h_le₂ ⊢
    simp [not_lt.mpr h_le₁]
    unfold assumeNegatedCandidateFor.loop
    simp [not_lt.mpr h_le₂]
    intro h
    omega
  | succ j ih =>
    unfold assumeNegatedClauseFor.loop
    have hi : i < List.length L := by
      apply Nat.lt_of_sub_pos
      rw [← hj]
      exact Nat.zero_lt_succ j
    simp [hi]
    have h_agree := h_models.h_uncommitted hi
    simp [uget] at h_agree
    have := h_models.h_size₂
    rw [← this, usize] at hi
    split <;> rename _ => h_get
    · rw [← @ih (setLitFor τ (-L[i]) bumps) (i + 1) (by omega)]
      rw [assumeNegatedCandidateFor.loop]
      have : F.dsize + i < F.data.size := by omega
      simp [this, hi, h_get, h_agree, Nat.add_assoc]
    · rw [← @ih τ _ (by omega)]
      rw [assumeNegatedCandidateFor.loop]
      split <;> rename _ => hi'
      · simp [h_agree, h_get, Nat.add_assoc]
      · have := h_models.h_size₂
        rw [usize] at this
        omega
    · rw [assumeNegatedCandidateFor.loop]
      split <;> rename _ => hi'
      · simp [h_agree, h_get]
      · omega

@[simp]
theorem assumeNegatedCandidateFor_eq_assumeNegatedClauseFor {F : RangeArray ILit}
      {Ls : List (Option (List ILit))} {L : List ILit} (τ : PPA) (bumps : Nat)
  : models F Ls L →
    assumeNegatedCandidateFor F τ bumps = assumeNegatedClauseFor τ ({ toList := L} : IClause) bumps := by
  intro h_models
  simp [assumeNegatedCandidateFor, assumeNegatedClauseFor]
  exact @assumeNegatedCandidateFor.loop.aux _ _ _ _ h_models bumps 0 F.usize h_models.h_size₂

theorem assumeRATClause.loop.aux {F : RangeArray ILit} {τ : PPA} {σ : PS}
    {Ls : List (Option (List ILit))} {L : List ILit} (h_models : models F Ls L)     -- models
    {i : Nat} (hi : i < F.size)                                                     -- Clause index
    {C : List ILit} (hC : Ls.get ⟨i, h_models.h_size₁ ▸ hi⟩ = some C)               -- Clause at i
    {j k : Nat}
  : k = C.length - j →
    match assumeRATClause.loop F i σ ((F.index i hi) + j) τ with
    -- If we exit early, then τ satisfies the clause under the substitution, and τ is unchanged
    | .error τ' => τ.toPropFun ≤ PropFun.substL (clauseAsListToPropFun ((C.drop j))) σ.toSubst ∧ extendsFor τ τ' 0
    -- If we make it to the end, then τ' has been assumed by the negated candidate under the substitution
    | .ok τ' => τ'.toPropFun = ↑τ ⊓ (PropFun.substL (clauseAsListToPropFun ((C.drop j))) σ.toSubst)ᶜ ∧ extendsFor τ τ' 0 := by
  intro hk
  have hiL := h_models.h_size₁ ▸ hi
  have hi' := h_models.h_sizes (hiL) hC
  induction k generalizing τ j with
  | zero =>
    have h_le₁ := Nat.le_of_sub_eq_zero hk.symm
    unfold assumeRATClause.loop
    have hj := hi' ▸ h_le₁
    simp [rsize] at hj
    rw [add_comm j] at hj
    simp [not_lt_of_ge hj, List.drop_eq_nil_iff.mpr h_le₁]
  | succ k ih =>
    unfold assumeRATClause.loop
    have hj_lt : j < C.length := by omega
    replace hk : k = C.length - (j + 1) := by omega
    have : F.index i hi + j < F.index! (i + 1) := by
      simp [rsize] at hi'
      omega
    have hF := h_models.h_agree hiL hC hj_lt
    rw [oget] at hF
    simp [this, hF]
    clear hF
    match hσ : σ.litValue C[j] with
    | .inr true =>
      simp [hσ]
      have := List.mem_drop_iff_getElem.mpr ⟨0, (by rw [Nat.zero_add]; exact hj_lt), rfl⟩
      simp [Nat.zero_add] at this
      have := substL_le_of_le (Clause.toPropFun_mem_list_le this) σ.toSubst
      apply le_trans _ this
      simp [PS.litValue_true_iff.mp hσ]
    | .inr false =>
      simp [hσ]
      replace ih := ih (τ := τ) hk
      split <;> rename_i h_loop
      <;> simp [h_loop, ← Nat.add_assoc] at ih
      · rcases ih with ⟨hτ, h_extends⟩
        constructor
        · have := Clause.toPropFun_drop_le_drop_of_ge C (Nat.le_succ j)
          exact le_trans hτ (substL_le_of_le this _)
        · exact h_extends
      · rename PPA => τ''
        rcases ih with ⟨h_eq, h_extends⟩
        constructor
        · rw [h_eq, ← List.getElem_cons_drop_succ_eq_drop hj_lt, Clause.toPropFun_cons]
          simp [litValue_false_iff.mp hσ]
        · exact h_extends
    | .inl l' =>
      simp [PSV.toMappedNat]
      match hτ : τ.litValue? l' with
      | none =>
        simp
        replace ih := ih (τ := τ.setLitFor (-l') 0) hk
        have h_neg := litValue?_negate_none_iff.mpr hτ
        have hτ_le := PPA.toPropFun_setLitFor_le_of_none h_neg 0
        rw [← List.getElem_cons_drop_succ_eq_drop hj_lt, Clause.toPropFun_cons]
        simp [← litValue_eq, hσ, PSV.toPropFun]
        split <;> rename_i h_loop
        <;> simp [h_loop, ← Nat.add_assoc] at ih
        <;> rcases ih with ⟨h_eq, h_extends⟩
        · constructor
          · simp [toPropFun_setLitFor_of_none h_neg] at h_eq
            exact inf_compl_le_iff_le_sup.mp h_eq
          · have := extendsFor_setLitFor_of_none h_neg 0
            exact extendsFor_trans this h_extends
        · constructor
          · simp [h_eq, toPropFun_setLitFor_of_none h_neg, inf_assoc]
          · have := extendsFor_setLitFor_of_none h_neg 0
            exact extendsFor_trans this h_extends
      | some b =>
        cases b <;> simp
        -- false branch
        · replace ih := ih (τ := τ) hk
          split <;> rename_i h_loop
          <;> simp [h_loop, ← Nat.add_assoc] at ih
          <;> simp [ih.2]
          · have := Clause.toPropFun_drop_le_drop_of_ge C (Nat.le_succ j)
            exact le_trans ih.1 (substL_le_of_le this _)
          · simp [ih.1]
            clear ih
            rw [← List.getElem_cons_drop_succ_eq_drop hj_lt, Clause.toPropFun_cons]
            simp [← litValue_eq, hσ, PSV.toPropFun]
            have := litValue?_false_iff.mp hτ
            have :  τ.toPropFun ⊓ (LitVar.toPropFun l')ᶜ = τ.toPropFun := by
              simp [this]
            rw [← inf_assoc, this]
        -- true branch
        · have := Clause.toPropFun_mem_list_le (List.mem_drop_iff_getElem.mpr ⟨0, (by rw [Nat.zero_add]; exact hj_lt), rfl⟩)
          simp [Nat.add_zero] at this
          have := litValue?_true_iff.mp hτ
          rw [← List.getElem_cons_drop_succ_eq_drop hj_lt, Clause.toPropFun_cons]
          simp [← litValue_eq, hσ, PSV.toPropFun]
          exact le_sup_of_le_left this

theorem assumeRATClause_result {F : RangeArray ILit} {τ : PPA} {σ : PS}
    {Ls : List (Option (List ILit))} {L : List ILit} (h_models : models F Ls L)     -- models
    {i : Nat} (hi : i < F.size)                                                     -- Clause index
    {C : List ILit} (hC : Ls.get ⟨i, h_models.h_size₁ ▸ hi⟩ = some C)               -- Clause at c_idx
  : match assumeRATClause F i hi σ τ with
    | .error τ' => τ.toPropFun ≤ PropFun.substL (clauseAsListToPropFun C) σ.toSubst ∧ extendsFor τ τ' 0
    | .ok τ' => τ'.toPropFun = ↑τ ⊓ (PropFun.substL (clauseAsListToPropFun C) σ.toSubst)ᶜ ∧ extendsFor τ τ' 0 := by
  simp [assumeRATClause]
  exact @assumeRATClause.loop.aux _ _ _ _ _ h_models i hi C hC 0 (C.length) rfl

def unit_to_option (n : Int) : Option ILit :=
  if hn : n = 0 then none else some ⟨n, hn⟩

@[simp] theorem unit_to_option_zero : unit_to_option 0 = none := by simp [unit_to_option]

theorem unitProp.loop.aux {F : RangeArray ILit} (τ : PPA)
  {Ls : List (Option (List ILit))} {L : List ILit} (h_models : models F Ls L)     -- models
  {i : Nat} (hi : i < F.size)                                                     -- Clause index
  {C : List ILit} (hC : Ls.get ⟨i, h_models.h_size₁ ▸ hi⟩ = some C)               -- Clause at i
  {j k : Nat} (unit : Int)
    : k = C.length - j
        → unitProp.loop τ F i (F.index i hi + j) unit = PPA.unitProp.loop τ { toList := C } j (unit_to_option unit) := by
  intro hk
  have hiL := h_models.h_size₁ ▸ hi
  have hi' := h_models.h_sizes (hiL) hC
  induction k generalizing τ j unit with
  | zero =>
    have hj_le := Nat.le_of_sub_eq_zero hk.symm
    unfold RangeArray.unitProp.loop
    unfold PPA.unitProp.loop
    have hj := hi' ▸ hj_le
    simp [rsize] at hj
    rw [add_comm j] at hj
    simp [not_lt_of_ge hj, not_lt_of_ge hj_le, List.drop_eq_nil_iff.mpr hj_le]
    split <;> rename _ => h_unit
    <;> simp [h_unit, unit_to_option]
  | succ k ih =>
    have hj_lt : j < C.length := by omega
    replace hk : k = C.length - (j + 1) := by omega
    have : F.index i hi + j < F.index! (i + 1) := by
      simp [rsize] at hi'
      omega
    have hF := h_models.h_agree hiL hC hj_lt
    rw [oget] at hF
    unfold RangeArray.unitProp.loop
    unfold PPA.unitProp.loop
    simp [this, hF, hj_lt]
    split
    rename_i lit h_lit hCj
    simp [hCj]
    rw [Nat.add_assoc]
    match hτ : τ.litValue? ⟨lit, h_lit⟩ with
    | none =>
      by_cases h_unit : unit = 0
      <;> simp [h_unit]
      · simp [unit_to_option, @ih τ (j + 1) lit hk, h_lit]
      · split <;> rename_i hul
        · subst hul
          simp [@ih τ (j + 1) unit hk, unit_to_option, h_lit]
        · simp [unit_to_option, hul, h_unit]
          intro h_con
          injection h_con
          contradiction
    | some b =>
      cases b <;> simp
      exact @ih τ (j + 1) unit hk

@[simp]
theorem unitProp_eq_unitProp {F : RangeArray ILit} {τ : PPA}
  {Ls : List (Option (List ILit))} {L : List ILit} (h_models : models F Ls L)     -- models
  {i : Nat} (hi : i < F.size)                                                     -- Clause index
  {C : List ILit} (hC : Ls.get ⟨i, h_models.h_size₁ ▸ hi⟩ = some C)               -- Clause at i
    : RangeArray.unitProp τ F i hi = PPA.unitProp τ { toList := C } := by
  simp [RangeArray.unitProp, PPA.unitProp]
  have := @unitProp.loop.aux _ τ _ _ h_models i hi C hC 0 (C.length) 0 rfl
  simp at this
  exact this

theorem applyUPHint_spec {F : RangeArray ILit} {τ : PPA}
    {Ls : List (Option (List ILit))} {L : List ILit} (h_models : models F Ls L)
    (hint bumps : Nat)
  : match applyUPHint F bumps τ hint with
    | ⟨_, .err⟩ => True
    | ⟨τ', .unit⟩  =>
      ∃ (hint : Nat) (h_hint : hint < Ls.length) (C : List ILit), Ls.get ⟨hint, h_hint⟩ = some C
        ∧ ∃ (lit : ILit), lit ∈ C ∧ τ.litValue? lit = none
        ∧ τ' = τ.setLitFor lit bumps
        ∧ (clauseAsListToPropFun C) ⊓ τ = lit.toPropFun ⊓ τ
        ∧ (cnfAsListToPropFun Ls) ⊓ τ ≤ τ'
    | ⟨τ', .contra⟩ =>
      ∃ (hint : Nat) (h_hint : hint < Ls.length) (C : List ILit), Ls.get ⟨hint, h_hint⟩ = some C
        ∧ τ' = τ
        ∧ (clauseAsListToPropFun C) ⊓ τ = ⊥ := by
  simp [applyUPHint]
  by_cases h_hint : hint < Ls.length
  · have h_hint' := h_models.h_size₁ ▸ h_hint
    simp [h_hint']
    by_cases h_del : F.isDeleted hint h_hint'
    <;> simp [h_del]
    simp at h_del
    rcases (h_models.h_some h_hint).mp h_del with ⟨C, hC⟩
    rw [unitProp_eq_unitProp h_models h_hint' hC]
    match h_up : τ.unitProp { toList := C } with
    | .multipleUnassignedLiterals => simp
    | .satisfied => simp
    | .unit ⟨unit, h_unit⟩ =>
      rw [unitProp_eq_unitPropM] at h_up
      rcases unitPropM_unit h_up with ⟨h_mem, h_none, hC_inf⟩
      simp at h_mem
      simp
      use hint, h_hint, C, hC, ⟨unit, h_unit⟩, h_mem, h_none
      simp [hC_inf, toPropFun_setLitFor_of_none h_none bumps]
      have := cnfPropFun_le_of_mem hC
      apply le_trans (inf_le_inf_right τ.toPropFun this)
      simp [Trestle.SR.clauseAsListToPropFun, hC_inf]
    | .falsified =>
      simp
      use hint, h_hint, C, hC
      rw [unitProp_eq_unitPropM] at h_up
      exact unitPropM_falsified h_up
  -- out-of-bounds error branch
  · have h_hint' := h_models.h_size₁ ▸ h_hint
    simp [h_hint']

@[simp]
theorem applyUPHints.nil (F : RangeArray ILit) (τ : PPA) (bumps : Nat)
  : applyUPHints F bumps τ { toList := [] } = ⟨τ, .unit⟩ := by
  simp [applyUPHints, applyUPHints.loop]

theorem applyUPHints.loop.cons_succ' (F : RangeArray ILit) (τ : PPA) (bumps hint : Nat)
    {hints : List Nat} {i j : Nat}
  : j = hints.length - i →
    applyUPHints.loop F bumps { toList := hint :: hints } (i + 1) τ = applyUPHints.loop F bumps { toList := hints } i τ := by
  intro hj
  induction j generalizing τ i with
  | zero =>
    have h_le := Nat.le_of_sub_eq_zero hj.symm
    unfold applyUPHints.loop
    simp [not_lt_of_ge h_le]
  | succ j ih =>
    have hi : i < hints.length := by
      apply Nat.lt_of_sub_pos
      rw [← hj]
      exact Nat.zero_lt_succ j
    have hj' : j = hints.length - (i + 1) := by omega
    unfold applyUPHints.loop
    simp [hi]
    match h_hint : applyUPHint F bumps τ hints[i] with
    | ⟨τ', .err⟩ => simp
    | ⟨τ', .unit⟩ => simp [ih (τ := τ') hj']
    | ⟨τ', .contra⟩ => simp [ih (τ := τ') hj']

@[simp]
theorem applyUPHints.loop.cons_succ (F : RangeArray ILit) (τ : PPA) (bumps hint i : Nat) {hints : List Nat}
  : applyUPHints.loop F bumps { toList := hint :: hints } (i + 1) τ = applyUPHints.loop F bumps { toList := hints } i τ := by
  exact @applyUPHints.loop.cons_succ' F τ bumps hint hints i (hints.length - i) (by omega)

theorem applyUPHints_spec {F : RangeArray ILit} {τ : PPA}
  {Ls : List (Option (List ILit))} {L : List ILit} (h_models : models F Ls L)
  (bumps : Nat)
  (hints : List Nat)
  : match applyUPHints F bumps τ { toList := hints } with
    | ⟨_, .err⟩ => True
    | ⟨τ', .unit⟩ => (cnfAsListToPropFun Ls) ⊓ τ ≤ τ' ∧ extendsFor τ τ' bumps
    | ⟨τ', .contra⟩ => (cnfAsListToPropFun Ls) ⊓ τ = ⊥ ∧ extendsFor τ τ' bumps
  := by
  unfold applyUPHints
  induction hints generalizing τ with
  | nil => simp [applyUPHints.loop]
  | cons hint hints ih =>
    unfold applyUPHints.loop
    simp
    match h_hint : applyUPHint F bumps τ hint with
    | ⟨τ', .err⟩ => simp
    | ⟨τ', .unit⟩ =>
      have h_spec := applyUPHint_spec (τ := τ) h_models hint bumps
      simp [h_hint] at h_spec
      rcases h_spec with ⟨hint, h_hint_lt, C, hC, lit, h_lit_mem, hτ_lit, hτ', hτ₁, hτ₂⟩
      simp
      match h_loop : applyUPHints.loop F bumps { toList := hints } 0 τ' with
      | ⟨τ'', .err⟩ => simp [h_loop]
      | ⟨τ'', .unit⟩ =>
        simp
        replace ih := ih (τ := τ')
        subst hτ'
        simp [h_loop] at ih
        rcases ih with ⟨ih₁, ih₂⟩
        constructor
        · have h : cnfAsListToPropFun Ls ⊓ (cnfAsListToPropFun Ls ⊓ τ.toPropFun)
                    ≤ cnfAsListToPropFun Ls ⊓ (τ.setLitFor lit bumps).toPropFun :=
              inf_le_inf (fun τ a => a) hτ₂
          have : cnfAsListToPropFun Ls ⊓ cnfAsListToPropFun Ls = cnfAsListToPropFun Ls := by simp
          rw [← inf_assoc, this] at h
          apply le_trans h ih₁
        · have := extendsFor_setLitFor_of_none hτ_lit bumps
          exact extendsFor_trans this ih₂
      | ⟨τ'', .contra⟩ =>
        simp
        replace ih := ih (τ := τ')
        subst hτ'
        simp [h_loop] at ih
        rcases ih with ⟨ih₁, ih₂⟩
        constructor
        · have := toPropFun_setLitFor_of_none hτ_lit bumps
          simp [this] at ih₁ hτ₂
          clear this h_hint h_loop
          have := litValue?_none_iff.mp hτ_lit
          apply le_bot_iff.mp
          simp [← ih₁, hτ₂]
        · have := extendsFor_setLitFor_of_none hτ_lit bumps
          exact extendsFor_trans this ih₂
    | ⟨τ', .contra⟩ =>
      simp
      have h_spec := applyUPHint_spec (τ := τ) h_models hint bumps
      simp [h_hint] at h_spec
      rcases h_spec with ⟨hint, h_hint_mem, C, hC, rfl, hC_inf⟩
      have := cnfPropFun_le_of_mem hC
      simp [hC_inf] at this
      simp [this]
      apply le_bot_iff.mp
      rw [← hC_inf]
      exact inf_le_inf_right τ'.toPropFun this

/-! # reduce -/

theorem reduce_loop_eq_reduceM_aux (F : RangeArray ILit) (σ : PS) (hint : Nat)
  (h_hint : hint < F.size)
  {Ls : List (Option (List ILit))} {L : List ILit} (h_models : models F Ls L)
  {C : List ILit} (hC : Ls.get ⟨hint, h_models.h_size₁ ▸ h_hint⟩ = some C)
  (b : Bool)
    {i j : Nat}
    : j = F.rsize hint h_hint - i →
        RangeArray.reduce.loop F hint σ.mappings σ.gens σ.generation σ.sizes_eq.symm (F.index hint h_hint + i) b =
        PS.reduce.loop σ { toList := C } i b := by
  intro hj
  induction j generalizing i b with
  | zero =>
    have h_le := Nat.le_of_sub_eq_zero hj.symm
    unfold RangeArray.reduce.loop
    unfold PS.reduce.loop
    have h_rsize := h_le
    have h_rsize' := h_models.h_sizes (h_models.h_size₁ ▸ h_hint) hC
    simp [rsize, Nat.add_comm i] at h_rsize
    simp [not_lt_of_ge h_rsize, ← h_rsize']
    intro h_con
    omega
  | succ j ih =>
    have hi : i < F.rsize hint h_hint := by omega
    have hi' := hi
    have hj' : j = F.rsize hint h_hint - (i + 1) := by omega
    simp [rsize] at hi'
    have : F.index hint h_hint + i < F.index! (hint + 1) := by omega
    have h_rsize' := h_models.h_sizes (h_models.h_size₁ ▸ h_hint) hC
    have hiC := h_rsize' ▸ hi
    unfold RangeArray.reduce.loop
    unfold PS.reduce.loop
    simp [← h_rsize', hi, this]
    have h_hint' := h_models.h_size₁ ▸ h_hint
    have h_Fget := h_models.h_agree h_hint' hC hiC
    simp [oget] at h_Fget
    simp [h_Fget]
    split_ifs

    · stop
      rename_i hC_index h_gen_index h_pol
      split
      · simp [seval]
        rename_i h_map
        unfold PS.litValue PS.litValue_Nat PS.varValue_Nat
        simp [h_pol, hC_index, LitVar.polarity, h_gen_index]
        simp [ILit.polarity] at h_pol
        split at h_pol
        rename_i lit h_lit h_lit_eq
        simp at h_pol
        simp [h_lit_eq] at h_map
        simp [h_lit_eq, h_pol, h_map]
      · simp [seval]
        rename_i h_map
        unfold PS.litValue PS.litValue_Nat PS.varValue_Nat
        simp [h_pol, hC_index, LitVar.polarity, h_gen_index]
        simp [ILit.polarity] at h_pol
        split at h_pol
        rename_i lit h_lit h_lit_eq
        simp at h_pol
        simp [h_lit_eq] at h_map
        simp [h_lit_eq, h_pol, h_map]
        rw [Nat.add_assoc]
        exact ih true hj'
      · stop
        rename_i h_map₀ h_map₁
        simp [ILit.polarity] at h_pol
        split at h_pol
        rename_i lit h_lit h_lit_eq
        simp at h_pol
        simp [h_lit_eq, ILit.index] at h_map₀ h_map₁
        simp [ILitToMappedNat, LitVar.polarity, h_lit_eq, h_pol, ILit.index, seval]
        unfold PS.litValue PS.litValue_Nat PS.varValue_Nat
        simp [ILitToMappedNat, LitVar.polarity, h_lit_eq, h_pol, ILit.index, seval, LitVar.toVar]
        simp [h_lit_eq, ILit.index] at hC_index h_gen_index
        simp [PSV.fromMappedNat, IVar.index, hC_index, h_gen_index]
        match h_map_val : σ.mappings[lit.natAbs - 1]'(σ.sizes_eq ▸ hC_index) with
        | 0 => contradiction
        | 1 => contradiction
        | m + 2 =>
          simp
          split
          · split
            · rename_i h
              split at h <;> try contradiction
              · clear h
                rename_i h; split at h <;> contradiction
              · split at h <;> contradiction
            · exact ih b hj'
            · rename_i h
              split at h <;> try contradiction
              · clear h
                rename_i h
                split at h <;> contradiction
              · split at h <;> try contradiction
                clear h
                rename_i h _
                split at h
                · injection h
                  rename_i h; subst h
                  rename_i h
                  simp [LitVar.mkPos] at h
                  rename_i h_m2 _ _ hm
                  simp [Int.natAbs] at h_m2
                  split at h_m2
                  · rename_i n
                    simp [Int.ofNat] at h
                    have : n = (m + 2) / 2 := by omega
                    simp at this
                    have : (⟨↑n, by omega⟩ : ILit) = ⟨↑m / 2 + 1, by omega⟩ := by
                      simp; omega
                    exact absurd this h
                  · omega
                · injection h
                  rename_i h; subst h
                  omega
          · split
            · rename_i h
              split at h
              · rename_i hm
                split at hm <;> contradiction
              · contradiction
              · split at h <;> simp at h <;> contradiction
            · rename_i h
              split at h <;> try contradiction
              split at h <;> simp at h <;> try contradiction
              clear h
              rename_i h; subst h
              rename_i h
              split at h
              · injection h; rename_i h; injection h; rename_i h; subst h; rename_i h
                simp [Int.natAbs] at h
                omega
              · injection h; rename_i h; injection h; rename_i h; subst h; rename_i h
                simp [Int.ofNat] at h_pol
                omega
              done
            · exact ih true hj'
    · split
      · stop
        rename_i hC_index h_gen_index h_pol n h_map₀
        simp [ILit.polarity] at h_pol
        split at h_pol
        rename_i lit h_lit h_lit_eq
        simp at h_pol
        simp [h_lit_eq, ILit.index] at h_map₀
        simp [ILitToMappedNat, LitVar.polarity, h_lit_eq, h_pol, ILit.index, seval]
        unfold PS.litValue PS.litValue_Nat PS.varValue_Nat
        simp [ILitToMappedNat, LitVar.polarity, h_lit_eq, h_pol, ILit.index, seval, LitVar.toVar]
        simp [h_lit_eq, ILit.index] at hC_index h_gen_index
        simp [PSV.fromMappedNat, IVar.index, hC_index, h_gen_index, not_lt_of_ge h_pol, negateMappedNat, h_map₀]
        exact ih true hj'
      · stop
        rename_i hC_index h_gen_index h_pol n h_map₁
        simp [ILit.polarity] at h_pol
        split at h_pol
        rename_i lit h_lit h_lit_eq
        simp at h_pol
        simp [h_lit_eq, ILit.index] at h_map₁
        simp [ILitToMappedNat, LitVar.polarity, h_lit_eq, h_pol, ILit.index, seval]
        unfold PS.litValue PS.litValue_Nat PS.varValue_Nat
        simp [ILitToMappedNat, LitVar.polarity, h_lit_eq, h_pol, ILit.index, seval, LitVar.toVar]
        simp [h_lit_eq, ILit.index] at hC_index h_gen_index
        simp [PSV.fromMappedNat, IVar.index, hC_index, h_gen_index, not_lt_of_ge h_pol, negateMappedNat, h_map₁]
        done
      · rename_i hC_index h_gen_index h_pol _ h_map₀ h_map₁
        simp [ILit.polarity] at h_pol
        split at h_pol
        rename_i lit h_lit h_lit_eq
        simp at h_pol
        simp [h_lit_eq, ILit.index] at h_map₀ h_map₁
        simp [ILitToMappedNat, LitVar.polarity, h_lit_eq, h_pol, ILit.index, seval]
        unfold PS.litValue PS.litValue_Nat PS.varValue_Nat
        simp [ILitToMappedNat, LitVar.polarity, h_lit_eq, h_pol, ILit.index, seval, LitVar.toVar]
        simp [h_lit_eq, ILit.index] at hC_index h_gen_index
        simp [PSV.fromMappedNat, IVar.index, hC_index, h_gen_index, not_lt_of_ge h_pol, negateMappedNat]
        match h_map_val : σ.mappings[lit.natAbs - 1]'(σ.sizes_eq ▸ hC_index) with
        | 0 => contradiction
        | 1 => contradiction
        | m + 2 =>
          by_cases h_natAbs : lit.natAbs * 2 + 1 = m + 2
          <;> simp only [h_natAbs]
          · simp
            done
          · simp
            split
            · rename_i h
              split at h
              done
            · rename_i h
              split at h <;> try contradiction
              simp at h; subst h
              rename_i h
              split at h <;> try contradiction
              split at h
              · injection h
                rename_i h
                simp [LitVar.mkPos] at h
                injection h
                rename_i h; subst h
                omega
              · simp [LitVar.mkNeg] at h
                injection h
                rename_i h; subst h
                rename_i n hn2 hn
                have : -(1 : Int) + -(↑n / 2) = -(1 + n / 2) := by omega
                split at hn2
                · simp [Int.natAbs] at h_natAbs
                  have : m + 1 = n := by omega
                  subst this
                  clear hn2
                  split at h_natAbs
                  ·
                    done
                  · rename_i h


                    done
                  done
                · omega
                  done
                done
              done
            done
          done
        done
      done
    done
  done

#exit

-- The SR rule
theorem eqsat_of_SR {F C : PropFun ν} :
    (∃ σ, F ⊓ Cᶜ ≤ subst (F ⊓ C) σ) → PropFun.EquiSat F (F ⊓ C) := by
  rintro ⟨σ, hSR⟩
  constructor
  · rintro ⟨τ, hτF⟩
    by_cases hτC : τ ⊨ C
    · use τ
      rw [satisfies_conj]
      exact ⟨hτF, hτC⟩
    · replace hSR := entails_ext.mp hSR τ
      simp [satisfies_conj, and_imp, -satisfies_substL] at hSR
      replace hSR := hSR hτF hτC
      use PropAssignment.subst σ τ
      rw [satisfies_conj]
      exact hSR
  · rintro ⟨τ, hτ⟩
    rw [satisfies_conj] at hτ
    exact ⟨τ, hτ.1⟩

theorem eqsat_of_SR' {F C : PropFun ν} :
    (∃ σ, F ⊓ Cᶜ ≤ substL (F ⊓ C) σ) → EquiSat F (F ⊓ C) := by
  rintro ⟨σ, hSR⟩
  stop
  constructor
  · rintro ⟨τ, hτF⟩
    by_cases hτC : τ ⊨ C
    · use τ
      rw [satisfies_conj]
      exact ⟨hτF, hτC⟩
    · replace hSR := entails_ext.mp hSR τ
      simp [satisfies_conj, and_imp, -satisfies_substL] at hSR
      replace hSR := hSR hτF hτC
      use PropAssignment.substL (liftSubstL σ) τ
      rw [satisfies_conj]
      simp [← subst_liftSubst_eq_substL] at hSR
      exact hSR
  · rintro ⟨τ, hτ⟩
    rw [satisfies_conj] at hτ
    exact ⟨τ, hτ.1⟩

theorem checkLine_spec {F : RangeArray ILit}
    {Ls : List (Option (List ILit))} {L : List ILit} (h_models : models F Ls L)
    (τ : PPA) (σ : PS) (line : Trestle.Parsing.SRAdditionLine)
  : match checkLine ⟨F, τ, σ⟩ line with
    | .error false => True
    | .error true => (cnfAsListToPropFun Ls) = ⊥
    | .ok ⟨F', τ', σ'⟩ =>
      F' = F.commit
      ∧ PropFun.EquiSat (cnfAsListToPropFun Ls) (cnfAsListToPropFun Ls ⊓ clauseAsListToPropFun L)
  := by
  -- structure SRAdditionLine where
  -- witnessLits : Array ILit     -- Maps literals to true/false
  -- witnessMaps : Array ILit     -- Maps variables to literals
  -- upHints : Array Nat          -- Already 0-indexed clause IDs into the accumulated formula
  -- ratHintIndexes : Array Nat   -- Already 0-indexed
  -- ratHints : Array (Array Nat) -- Already 0-indexed
  -- ratSizesEq : ratHintIndexes.size = ratHints.size
  -- witnessMapsMod : witnessMaps.size % 2 = 0
  --have ⟨witnessLists, witnessMaps, c, d, e, f, g⟩ := line
  unfold checkLine
  simp [assumeNegatedCandidateFor_eq_assumeNegatedClauseFor _ _ h_models]
  match hC : τ.reset.assumeNegatedClauseFor { toList := L } (line.ratHints.size + 1) with
  | .error τ' => simp
  | .ok τ' =>
    simp
    have := assumeNegatedClauseFor_spec τ.reset L (line.ratHints.size + 1)
    simp [hC] at this
    rcases this with ⟨hτ', hτ_extends⟩
    match h_hints : F.applyUPHints (line.ratHints.size + 1) τ' line.upHints with
    | ⟨τ'', .err⟩ => simp [h_hints]
    | ⟨τ'', .unit⟩ =>
      simp
      by_cases h_dsize : F.dsize < F.data.size
      <;> simp [h_dsize]
      -- Check that we have a nontrivial witness
      have h_usize : 0 < F.usize := by
        simp [usize]; exact h_dsize
      by_cases h_pivot : line.witnessLits[0]?.getD (F.uget 0 h_usize) = F.uget 0 h_usize
      <;> simp [h_pivot]
      split <;> try simp
      rename_i h_loop
      split at h_loop
      <;> try (injection h_loop; contradiction)
      · simp at h_loop
      rename_i F' τ' σ' h_loop
      split at h_loop
      <;> simp at h_loop
      -- Now check all the RAT/SR hints
      rcases h_loop with ⟨rfl, rfl, rfl⟩
      rename_i τ''' h_loop
      simp
      apply eqsat_of_SR'
      use (assumeWitness σ (F.uget 0 h_usize) line.witnessLits line.witnessMaps).toSubst

      done
    | ⟨τ'', .contra⟩ =>
      simp
      have := applyUPHints_spec (τ := τ') h_models (line.ratHints.size + 1) line.upHints.toList
      simp [h_hints] at this
      rcases this with ⟨h_hints₁, h_hints₂⟩
      by_cases h_usize : F.usize = 0
      -- Trivial branch: If the candidate is empty, we should have found contradiction by now
      · simp [h_usize]
        simp [h_models.h_size₂] at h_usize
        subst h_usize
        simp at hτ'
        simp [hτ'] at h_hints₁
        exact h_hints₁
      -- UP Contradiction branch: we return immediately; check for equisat
      · simp [h_usize]
        apply equisat_of_entails
        simp [hτ'] at h_hints₁
        exact le_iff_inf_compl_eq_bot.mpr h_hints₁
      done
    done
  done

end Trestle.SR
