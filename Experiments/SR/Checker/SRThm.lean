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
open Trestle Trestle.Model PropFun Trestle.Parsing

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
theorem cnfAsListToPropFun_cons_none (Cs : List (Option (List ILit)))
  : cnfAsListToPropFun (none :: Cs) = cnfAsListToPropFun Cs := by
  simp [cnfAsListToPropFun, all]

@[simp]
theorem cnfAsListToPropFun_cons_some (C : List ILit) (Cs : List (Option (List ILit)))
  : cnfAsListToPropFun (some C :: Cs) = clauseAsListToPropFun C ⊓ cnfAsListToPropFun Cs := by
  simp [cnfAsListToPropFun, all]

@[simp]
theorem cnfAsListToPropFun_cons (C : Option (List ILit)) (Cs : List (Option (List ILit)))
  : cnfAsListToPropFun (C :: Cs) =
    (match C with
    | none => ⊤
    | some C => clauseAsListToPropFun C) ⊓ cnfAsListToPropFun Cs := by
  cases C <;> simp

@[simp]
theorem cnfAsListToPropFun_append (Cs₁ Cs₂ : List (Option (List ILit)))
  : cnfAsListToPropFun (Cs₁ ++ Cs₂) = cnfAsListToPropFun Cs₁ ⊓ cnfAsListToPropFun Cs₂ := by
  induction Cs₁ with
  | nil => simp
  | cons C Cs₁ ih =>
    cases C <;> simp [ih, inf_assoc]

@[simp]
theorem cnfAsListToPropFun_replicate_none (n : Nat)
  : cnfAsListToPropFun (List.replicate n none) = ⊤ := by
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
  simp only [List.mem_toArray, h]

theorem cnfPropFun_le_of_mem {Cs : List (Option (List ILit))} {C : List ILit} {i : Nat}
      {hi : i < Cs.length}
    : Cs.get ⟨i, hi⟩ = some C → cnfAsListToPropFun Cs ≤ clauseAsListToPropFun C := by
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
        simp
      | i + 1 =>
        simp at h
        have := ih h
        apply le_trans _ this
        simp

theorem cnfPropFun_drop_le_of_le (Cs : List (Option (List ILit))) {n₁ n₂ : Nat}
  : n₁ ≤ n₂ → cnfAsListToPropFun (List.drop n₁ Cs) ≤ cnfAsListToPropFun (List.drop n₂ Cs) := by
  intro hn
  induction Cs generalizing n₁ n₂ with
  | nil => simp
  | cons C Cs ih =>
    cases n₁ with
    | zero =>
      cases n₂ with
      | zero => simp
      | succ n₂ =>
        replace ih := ih (Nat.zero_le n₂)
        simp at ih
        simp
        exact inf_le_of_right_le ih
    | succ n₁ =>
      cases n₂ with
      | zero => contradiction
      | succ n₂ =>
        replace ih := ih (Nat.le_of_succ_le_succ hn)
        simp [ih]

theorem cnfPropFun_drop_succ_of_none {Cs : List (Option (List ILit))} {n : Nat} (hn : n < Cs.length)
  : Cs[n] = none → cnfAsListToPropFun (List.drop (n + 1) Cs) = cnfAsListToPropFun (List.drop n Cs) := by
  intro h
  induction Cs generalizing n with
  | nil => simp at hn
  | cons C Cs ih =>
    cases n with
    | zero =>
      simp at h; subst h
      simp
    | succ n =>
      simp at h hn
      replace ih := ih hn h
      simp [ih]

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
    simp
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
      simp [this, h_get, h_agree, Nat.add_assoc]
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

/-! # iget -/

def iget {F : RangeArray ILit} {Ls} {L : List ILit} (h_models : models F Ls L) (i : Nat) (C : List ILit) : Prop :=
  if hi : i < F.size then Ls.get ⟨i, h_models.h_size₁ ▸ hi⟩ = some C else C = L

theorem iget_lt {F : RangeArray ILit} {Ls} {L : List ILit} {h_models : models F Ls L}
    {i : Nat} {C : List ILit} (h_iget : iget h_models i C) (hi : i < F.size)
  : Ls.get ⟨i, h_models.h_size₁ ▸ Nat.lt_of_not_ge (not_le.mpr hi)⟩ = some C := by
  simp [iget, hi] at h_iget
  exact h_iget

theorem iget_eq {F : RangeArray ILit} {Ls} {L : List ILit} {h_models : models F Ls L} {C : List ILit}
  : iget h_models F.size C → C = L := by
  simp [iget]

@[simp]
theorem iget_Fsize {F : RangeArray ILit} {Ls} {L : List ILit} (h_models : models F Ls L)
    : iget h_models F.size L := by
  simp [iget]

theorem iget_of_eq_some {F : RangeArray ILit} {Ls} {L C} (h_models : models F Ls L) {i} {hi : i < Ls.length}
    : Ls[i] = some C → iget h_models i C := by
  simp [iget, h_models.h_size₁ ▸ hi]

theorem assumeRATClause.loop.aux {F : RangeArray ILit} {τ : PPA} {σ : PS}
    {Ls : List (Option (List ILit))} {L : List ILit} (h_models : models F Ls L)
    {i : Nat} (hi : i ≤ F.size)
    {C : List ILit} (hC : iget h_models i C)
    {j k : Nat}
  : k = C.length - j →
    match assumeRATClause.loop F i hi σ ((F.index! i) + j) τ with
    -- If we exit early, then τ satisfies the clause under the substitution, and τ is unchanged
    | .error τ' => τ.toPropFun ≤ PropFun.substL (clauseAsListToPropFun ((C.drop j))) σ.toSubst ∧ extendsFor τ τ' 0
    -- If we make it to the end, then τ' has been assumed by the negated candidate under the substitution
    | .ok τ' => τ'.toPropFun = ↑τ ⊓ (PropFun.substL (clauseAsListToPropFun ((C.drop j))) σ.toSubst)ᶜ ∧ extendsFor τ τ' 0 := by
  intro hk
  have hiL := h_models.h_size₁ ▸ hi
  induction k generalizing τ j with
  | zero =>
    have h_le₁ := Nat.le_of_sub_eq_zero hk.symm
    unfold assumeRATClause.loop
    simp [List.drop_eq_nil_iff.mpr h_le₁]
    by_cases hi' : i = F.size
    · subst hi'
      have := iget_eq hC; subst this
      have := h_models.h_size₂
      rw [usize] at this
      have : F.dsize + j ≥ F.data.size := by omega
      simp [not_lt_of_ge this]
    · replace hi' := Nat.lt_of_le_of_ne hi hi'
      replace hC := iget_lt hC hi'
      have hiF := h_models.h_sizes (h_models.h_size₁ ▸ hi') hC
      have hj := hiF ▸ h_le₁
      simp [rsize] at hj
      rw [add_comm j] at hj
      simp [Nat.ne_of_lt hi']
      have : F.index! (i + 1) ≤ F.index! i + j := by
        conv => rhs; rw [index!]
        simp [hi']
        exact hj
      simp [not_lt_of_ge this]
  | succ k ih =>
    unfold assumeRATClause.loop
    have hj_lt : j < C.length := by omega
    replace hk : k = C.length - (j + 1) := by omega
    -- Do some non-finishing-tactic casework
    -- Adjust hypotheses based on whether we are processing the candidate or a formula clause
    by_cases hi' : i = F.size
    focus
      subst hi'
      have this := iget_eq hC; subst this; clear hC
      have hC := h_models.h_size₂
      simp [usize] at hC
      have hj : F.dsize + j < F.data.size := by omega
      have hFC := h_models.h_uncommitted hj_lt
      simp [uget] at hFC
      simp [hj, hFC]
      clear hFC hj hiL
    swap
    focus
      replace hi := Nat.lt_of_le_of_ne hi hi'
      replace hiL := h_models.h_size₁ ▸ hi
      replace hC := iget_lt hC hi
      have : F.index! i + j < F.index! (i + 1) := by
        have := h_models.h_sizes hiL hC
        simp [rsize] at this
        rw [index_eq_index!] at this
        omega
      have hF := h_models.h_agree hiL hC hj_lt
      simp_rw [oget, index_eq_index!] at hF
      simp [hi', this, hF]
      clear hF hiL this
    all_goals (
    match hσ : σ.litValue C[j] with
    | .inr true =>
      simp
      have := List.mem_drop_iff_getElem.mpr ⟨0, (by rw [Nat.zero_add]; exact hj_lt), rfl⟩
      simp at this
      have := substL_le_of_le (Clause.toPropFun_mem_list_le this) σ.toSubst
      apply le_trans _ this
      simp [PS.litValue_true_iff.mp hσ]
    | .inr false =>
      simp
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
        · rw [h_eq, ← List.getElem_cons_drop hj_lt, Clause.toPropFun_cons]
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
        rw [← List.getElem_cons_drop hj_lt, Clause.toPropFun_cons]
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
            rw [← List.getElem_cons_drop hj_lt, Clause.toPropFun_cons]
            simp [← litValue_eq, hσ, PSV.toPropFun]
            have := litValue?_false_iff.mp hτ
            have :  τ.toPropFun ⊓ (LitVar.toPropFun l')ᶜ = τ.toPropFun := by
              simp [this]
            rw [← inf_assoc, this]
        -- true branch
        · have := Clause.toPropFun_mem_list_le (List.mem_drop_iff_getElem.mpr ⟨0, (by rw [Nat.zero_add]; exact hj_lt), rfl⟩)
          simp at this
          have := litValue?_true_iff.mp hτ
          rw [← List.getElem_cons_drop hj_lt, Clause.toPropFun_cons]
          simp [← litValue_eq, hσ, PSV.toPropFun]
          exact le_sup_of_le_left this
    )

theorem assumeRATClause_spec {F : RangeArray ILit} (τ : PPA) (σ : PS)
    {Ls : List (Option (List ILit))} {L : List ILit} (h_models : models F Ls L)
    {i : Nat} (hi : i ≤ F.size)
    {C : List ILit} (hC : iget h_models i C)
  : match assumeRATClause F i hi σ τ with
    | .error τ' => τ.toPropFun ≤ PropFun.substL (clauseAsListToPropFun C) σ.toSubst ∧ extendsFor τ τ' 0
    | .ok τ' => τ'.toPropFun = ↑τ ⊓ (PropFun.substL (clauseAsListToPropFun C) σ.toSubst)ᶜ ∧ extendsFor τ τ' 0 := by
  simp [assumeRATClause]
  exact @assumeRATClause.loop.aux _ _ _ _ _ h_models i hi C hC 0 (C.length) rfl

theorem assumeRATClause_error {F : RangeArray ILit} {τ τ' : PPA} {σ : PS}
    {Ls : List (Option (List ILit))} {L : List ILit} (h_models : models F Ls L)
    {i : Nat} {hi : i ≤ F.size}
    {C : List ILit} (hC : iget h_models i C)
  : assumeRATClause F i hi σ τ = .error τ' →
    τ.toPropFun ≤ PropFun.substL (clauseAsListToPropFun C) σ.toSubst ∧ extendsFor τ τ' 0 := by
  intro h
  have := assumeRATClause_spec τ σ h_models hi hC
  simp [h] at this
  exact this

theorem assumeRATClause_ok {F : RangeArray ILit} {τ τ' : PPA} {σ : PS}
    {Ls : List (Option (List ILit))} {L : List ILit} (h_models : models F Ls L)
    {i : Nat} {hi : i ≤ F.size}
    {C : List ILit} (hC : iget h_models i C)
  : assumeRATClause F i hi σ τ = .ok τ' →
    τ'.toPropFun = ↑τ ⊓ (PropFun.substL (clauseAsListToPropFun C) σ.toSubst)ᶜ ∧ extendsFor τ τ' 0 := by
  intro h
  have := assumeRATClause_spec τ σ h_models hi hC
  simp [h] at this
  exact this

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
    simp [not_lt_of_ge hj, not_lt_of_ge hj_le]
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
        · simp [unit_to_option, h_unit]
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
    | ⟨τ', .contra⟩ => simp

@[simp]
theorem applyUPHints.loop.cons_succ (F : RangeArray ILit) (τ : PPA) (bumps hint i : Nat) {hints : List Nat}
  : applyUPHints.loop F bumps { toList := hint :: hints } (i + 1) τ = applyUPHints.loop F bumps { toList := hints } i τ := by
  exact @applyUPHints.loop.cons_succ' F τ bumps hint hints i (hints.length - i) (by omega)

theorem applyUPHints_spec {F : RangeArray ILit} (τ : PPA)
  {Ls : List (Option (List ILit))} {L : List ILit} (h_models : models F Ls L)
  (bumps : Nat)
  (hints : List Nat)
  : match applyUPHints F bumps τ { toList := hints } with
    | ⟨_, .err⟩ => True
    | ⟨τ', .unit⟩ => (cnfAsListToPropFun Ls) ⊓ τ ≤ τ' ∧ extendsFor τ τ' bumps
    | ⟨τ', .contra⟩ => (cnfAsListToPropFun Ls) ⊓ τ = ⊥ ∧ extendsFor τ τ' bumps := by
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
      | ⟨τ'', .err⟩ => simp
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
      simp
      apply le_bot_iff.mp
      rw [← hC_inf]
      exact inf_le_inf_right τ'.toPropFun (cnfPropFun_le_of_mem hC)

theorem applyUPHints_unit {F : RangeArray ILit} {τ τ' : PPA}
  {Ls : List (Option (List ILit))} {L : List ILit} (h_models : models F Ls L)
  {bumps : Nat} {hints : List Nat}
  : applyUPHints F bumps τ { toList := hints } = (τ', .unit)
    → (cnfAsListToPropFun Ls) ⊓ τ ≤ τ' ∧ extendsFor τ τ' bumps := by
  intro h
  have := applyUPHints_spec τ h_models bumps hints
  simp [h] at this
  exact this

theorem applyUPHints_contra {F : RangeArray ILit} {τ τ' : PPA}
  {Ls : List (Option (List ILit))} {L : List ILit} (h_models : models F Ls L)
  {bumps : Nat} {hints : List Nat}
  : applyUPHints F bumps τ { toList := hints } = (τ', .contra)
    → (cnfAsListToPropFun Ls) ⊓ τ = ⊥ ∧ extendsFor τ τ' bumps := by
  intro h
  have := applyUPHints_spec τ h_models bumps hints
  simp [h] at this
  exact this

/-! # reduce -/

theorem reduce_loop_eq_reduce_loop (F : RangeArray ILit) (σ : PS) (hint : Nat) (h_hint : hint ≤ F.size)
  {Ls : List (Option (List ILit))} {L : List ILit} (h_models : models F Ls L)
  {C : List ILit} (hC : iget h_models hint C)
  {i j : Nat} (b : Bool)
    : j = (if h_hint' : hint = F.size then F.usize else F.rsize hint (Nat.lt_of_le_of_ne h_hint h_hint')) - i →
        RangeArray.reduce.loop F hint h_hint σ.gens σ.mappings σ.generation σ.sizes_eq (F.index! hint + i) b =
        PS.reduce.loop σ ({ toList := C } : IClause) i b := by
  intro hj
  induction j generalizing i b with
  | zero =>
    have h_le := Nat.le_of_sub_eq_zero hj.symm
    unfold RangeArray.reduce.loop
    unfold PS.reduce.loop
    by_cases h_hint' : hint = F.size
    · subst h_hint'
      simp at hj h_le
      have := iget_eq hC; subst this; clear hC
      have : F.dsize + i ≥ F.data.size := by omega
      simp [not_lt_of_ge this]
      clear this
      have := h_models.h_size₂
      intro h_con
      omega
    · have h_hint_lt := Nat.lt_of_le_of_ne h_hint h_hint'
      replace hC := iget_lt hC h_hint_lt
      have h_rsize := h_models.h_sizes (h_models.h_size₁ ▸ h_hint_lt) hC
      simp [rsize, h_hint', index_eq_index!] at h_le hj h_rsize
      have : F.index! hint + i ≥ F.index! (hint + 1) := by omega
      simp [h_hint', not_lt_of_ge this]
      intro h_con
      omega
  | succ j ih =>
    unfold RangeArray.reduce.loop PS.reduce.loop
    simp [seval]
    rw [Nat.add_assoc]
    replace ih := fun b => ih (i := i + 1) b (by omega)
    by_cases hi' : hint = F.size
    focus
      -- Do some non-finishing-tactic casework
      -- Adjust hypotheses based on whether we are processing the candidate or a formula clause
      subst hi'
      have := iget_eq hC; subst this; clear hC
      simp [usize] at hj
      have hC_len := h_models.h_size₂
      simp [usize] at hC_len
      have hFC := h_models.h_uncommitted (i := i) (by omega)
      simp [uget] at hFC
      have hiC : i < C.length := by omega
      have : F.dsize + i < F.data.size := by omega
      simp [hFC, hiC, this]
      simp only [index!, lt_self_iff_false, ↓reduceDIte] at ih
    swap
    focus
      have h_hint' := Nat.lt_of_le_of_ne h_hint hi'
      replace hC := iget_lt hC h_hint'
      have hC_len := h_models.h_sizes (h_models.h_size₁ ▸ h_hint') hC
      simp [hi', rsize, index_eq_index!] at hj hC_len
      have hiC : i < C.length := by omega
      have hFC := h_models.h_agree (h_models.h_size₁ ▸ h_hint') hC hiC
      simp [oget, index_eq_index!] at hFC
      have : F.index! hint + i < F.index! (hint + 1) := by omega
      simp [hi', hiC, hFC, this]
    all_goals (
    match hσ : σ.litValue C[i] with
    | .inr true =>
      -- Satisfied case
      have h_size := lt_size_of_litValue_ne_id (σ := σ) (l := C[i]) (by simp [hσ])
      have h_gen := ge_gen_of_litValue_ne_id (σ := σ) (l := C[i]) (by simp [hσ])
      have h_map := mappings_eq_of_litValue_true hσ
      rw [PS.size] at h_size
      simp [h_size, h_gen, h_map]
      by_cases h_pol : LitVar.polarity C[i]
      <;> simp [h_pol, MAPPED_TRUE, MAPPED_FALSE]
    | .inr false =>
      -- Literal is falsified, we induct trivially
      have h_size := lt_size_of_litValue_ne_id (σ := σ) (l := C[i]) (by simp [hσ])
      have h_gen := ge_gen_of_litValue_ne_id (σ := σ) (l := C[i]) (by simp [hσ])
      have h_map := mappings_eq_of_litValue_false hσ
      rw [PS.size] at h_size
      simp [h_size, h_gen, h_map]
      by_cases h_pol : LitVar.polarity C[i]
      <;> simp [h_pol, MAPPED_TRUE, MAPPED_FALSE]
      <;> exact ih true
    | .inl lit =>
      by_cases h_lit : C[i] = lit
      -- Id-mapped case
      · simp [h_lit] at hσ ⊢
        unfold litValue litValue_Nat varValue_Nat at hσ
        by_cases h_pol : LitVar.polarity lit
        <;> simp [h_pol] at hσ
        · by_cases h_lt : lit.index < σ.gens.size
          <;> simp [h_lt] at hσ ⊢
          · by_cases h_gen : σ.generation ≤ σ.gens[lit.index]
            · simp [h_gen, PSV.fromMappedNat] at hσ ⊢
              split at hσ
              <;> try contradiction
              rename_i h_map
              split at hσ <;> rename_i n h_mod
              · simp at hσ
                subst hσ
                simp at h_map
                have : (n / 2 + 1) * 2 = n + 1 + 1 := by omega
                simp [h_map, IVarToMappedNat, this]
                exact ih b
              · simp at hσ
                subst hσ
                simp at h_pol
            · simp [h_gen]
              exact ih b
          · exact ih b
        · by_cases h_lt : lit.index < σ.gens.size
          <;> simp [h_lt] at hσ ⊢
          · by_cases h_gen : σ.generation ≤ σ.gens[lit.index]
            <;> simp [h_gen, PSV.fromMappedNat] at hσ ⊢
            · split at hσ
              <;> try contradiction
              rename_i n' h_map
              simp [h_map]
              split at hσ
              · rename_i h_mod
                simp at hσ
                subst hσ
                have : (n' / 2 + 1) * 2 = n' + 1 + 1 := by omega
                simp [IVarToMappedNat, this]
                exact ih b
              · simp at hσ
                subst hσ
                simp at h_pol
            · exact ih b
          · exact ih b
      · have h_size := lt_size_of_litValue_ne_id (σ := σ) (l := C[i]) (by simp [hσ]; exact Ne.symm h_lit)
        have h_gen := ge_gen_of_litValue_ne_id (σ := σ) (l := C[i]) (by simp [hσ]; exact Ne.symm h_lit)
        have h_map := mappings_eq_of_litValue_lit h_lit hσ
        rcases h_map with ⟨n, hn⟩
        simp [h_size, h_gen, hn, h_lit]
        unfold litValue litValue_Nat varValue_Nat at hσ
        simp [h_size, h_gen, hn] at hσ
        clear hn h_size h_gen
        rcases LitVar.mkPos_or_mkNeg C[i] with (hC | hC)
        · rw [hC] at hσ
          simp [PSV.fromMappedNat] at hσ
          split at hσ <;> simp at hσ
          · subst hσ
            rw [hC] at h_lit
            simp at h_lit
            simp [IVarToMappedNat]
            split <;> rename_i h
            · have : (LitVar.toVar C[i]).val = n / 2 + 1 := by omega
              apply absurd _ h_lit
              simp [← this]
            · exact ih true
          · rename_i h_mod
            subst hσ
            clear h_lit
            simp [IVarToMappedNat]
            split <;> rename_i h
            · omega
            · exact ih true
        · rw [hC] at hσ
          simp [PSV.fromMappedNat, negateMappedNat] at hσ
          split at hσ
          <;> try contradiction
          rename_i n' hn'
          split at hn'
          · rename_i h_mod
            simp at hn'; subst hn'
            have : (n + 1) % 2 ≠ 0 := by omega
            simp [this] at hσ; clear this
            subst hσ
            simp [IVarToMappedNat]
            split <;> rename_i h
            · have : (LitVar.toVar C[i]).val = (n + 1) / 2 + 1 := by omega
              apply absurd _ h_lit
              rw [hC]
              simp [← this]
            · exact ih true
          · rename_i h_mod
            simp at hn'; subst hn'
            simp at h_mod
            have : n' % 2 = 0 := by omega
            simp [this] at hσ; clear this
            subst hσ
            simp [IVarToMappedNat]
            split <;> rename_i h
            · omega
            · exact ih true
    ) /- end all_goals -/

theorem reduce_eq_reduce (F : RangeArray ILit) (σ : PS) (hint : Nat) (h_hint : hint ≤ F.size)
  {Ls : List (Option (List ILit))} {L : List ILit} (h_models : models F Ls L)
  {C : List ILit} (hC : iget h_models hint C)
    : RangeArray.reduce F hint h_hint σ = PS.reduce σ ({ toList := C } : IClause) := by
  unfold RangeArray.reduce PS.reduce
  have := @reduce_loop_eq_reduce_loop F σ hint h_hint _ _ h_models C hC 0
    (if h_hint' : hint = F.size then F.usize else F.rsize hint (Nat.lt_of_le_of_ne h_hint h_hint')) false rfl
  simp at this
  exact this

theorem checkLine.loop_true_aux {line : SRAdditionLine} {F : RangeArray ILit}
    {Ls : List (Option (List ILit))} {L : List ILit} (h_models : models F Ls L)
    {τ τ' : PPA} --(hτ : τ.toPropFun = (clauseAsListToPropFun L)ᶜ)
    {σ : PS} {i j cri bc : Nat} (hi : i ≤ F.size) :
  j = F.size - i →
  uniform τ (line.ratHints.size + 1 - bc) →
    checkLine.loop F line.witnessMaps line.ratHintIndexes line.ratHints line.ratSizesEq σ i hi cri bc τ = ⟨τ', true⟩ →
    ---- can probably be done in a suffices -----
      (∃ (b : Nat), b ≤ line.ratHints.size + 1 - bc ∧ uniform τ' b)
      ∧ τ'.toPropFun = τ.toPropFun
    ---- suffices -----
      ∧ (cnfAsListToPropFun Ls) ⊓ τ ≤ PropFun.substL (cnfAsListToPropFun (Ls.drop i)) σ.toSubst
      ∧ (cnfAsListToPropFun Ls) ⊓ τ ≤ PropFun.substL (clauseAsListToPropFun L) σ.toSubst := by
  intro hj h_uniform
  induction j generalizing τ i cri bc with
  | zero =>
    -- i = F.size, so we are checking the candidate clause
    have hi : i = F.size := by omega
    subst hi
    clear hj
    unfold loop
    simp [reduce_eq_reduce F σ F.size (Nat.le_refl _) h_models (iget_Fsize h_models)]
    match h_reduce : σ.reduce { toList := L } with
    | .notReduced => simp
    | .satisfied =>
      simp
      rintro rfl
      simp [reduce_satisfied h_reduce, h_models.h_size₁]
      exact ⟨_, le_refl _, h_uniform⟩
    | .reduced =>
      -- Casework on a successful RAT hint find and assumption
      simp
      split <;> rename_i h_bc
      <;> try simp
      have hbc : line.ratHints.size + 1 - bc = line.ratHints.size - (bc + 1) + 2 := by omega
      have h_uniform' := hbc ▸ h_uniform
      split
      <;> try simp
      rename_i ri h_rat h_find_rat_hint
      split <;> rename_i τ₃ h_assume_rat
      <;> try simp
      · rintro rfl
        rcases assumeRATClause_error h_models (iget_Fsize h_models) h_assume_rat with ⟨hτ_le, hτ_ext⟩
        rcases uniform_bump_of_uniform_of_extendsFor' h_uniform' hτ_ext with ⟨h_uniform', hτ₃⟩
        simp [← hτ₃, h_models.h_size₁]
        use ⟨_, by omega, h_uniform'⟩
        simp at hτ_le
        apply le_trans _ hτ_le
        exact inf_le_right
      · split <;> rename_i τ₄ h_up
        <;> try simp
        rintro rfl
        rcases assumeRATClause_ok h_models (iget_Fsize h_models) h_assume_rat with ⟨hτ_le, hτ_ext⟩
        rcases applyUPHints_contra h_models h_up with ⟨h_up_le, h_up_ext⟩
        replace h_up_ext := extendsFor_trans hτ_ext h_up_ext
        rcases uniform_bump_of_uniform_of_extendsFor' h_uniform' h_up_ext with ⟨h_uniform', hτ₄⟩
        simp [← hτ₄, h_models.h_size₁]
        use ⟨_, by omega, h_uniform'⟩
        simp at hτ_le h_up_le
        simp [hτ_le, ← inf_assoc] at h_up_le
        exact le_iff_inf_compl_eq_bot.mpr h_up_le
  | succ j ih =>
    have hi_lt : i < F.size := by omega
    have hi_lt' := h_models.h_size₁ ▸ hi_lt
    have hj' : j = F.size - (i + 1) := by omega
    unfold loop
    simp [hi_lt]
    -- Split on whether the ith clause is deleted
    split <;> rename_i h_del
    · -- It's deleted, so no change in the reduction at hint `i`
      intro h_loop
      rcases ih (Nat.succ_le_of_lt hi_lt) hj' h_uniform h_loop with ⟨hτ, hpf, hL, hC⟩
      refine ⟨hτ, hpf, ?_, hC⟩
      clear hτ hpf hC
      apply le_trans hL
      apply substL_le_of_le
      have := eq_none_of_models_of_deleted h_models hi_lt' h_del
      rw [cnfPropFun_drop_succ_of_none hi_lt' this]
    · -- Not deleted, so we split on the returned result from `reduce`
      simp at h_del
      rcases (h_models.h_some hi_lt').mp h_del with ⟨C, hC⟩
      have h_iget := iget_of_eq_some h_models hC
      simp [reduce_eq_reduce F σ i hi h_models h_iget]
      intro h_loop
      split at h_loop <;> rename_i h_reduce
      -- reduce: Satisfied
      · rcases ih (Nat.succ_le_of_lt hi_lt) hj' h_uniform h_loop with ⟨hτ, hpf, hL, hC⟩
        refine ⟨hτ, hpf, ?_, hC⟩
        clear hτ hpf hC
        replace h_reduce := reduce_satisfied h_reduce
        simp [← List.getElem_cons_drop hi_lt', hC, h_reduce, hL]
      -- reduce: not reduced
      · rcases ih (Nat.succ_le_of_lt hi_lt) hj' h_uniform h_loop with ⟨hτ, hpf, hL, hC⟩
        refine ⟨hτ, hpf, ?_, hC⟩
        clear ih hτ hpf hC
        replace h_reduce := reduce_notReduced h_reduce
        simp [← List.getElem_cons_drop hi_lt', hC, h_reduce, hL]
        apply le_trans _ (cnfPropFun_le_of_mem hC)
        exact inf_le_left
      -- reduce. We continue with the loop by running UP on the reduced clause
      · split at h_loop <;> rename_i h_bc
        <;> try simp at h_loop
        -- Do we successfully find a RAT hint?
        split at h_loop
        <;> try simp at h_loop
        rename_i ri h_ri h_find_hint
        -- What's the result of assuming the negation of the reduced clause?
        split at h_loop
        <;> rename_i τ'' h_assume
        · -- Error: the clause is satisfied by σ or τ
          have h_iget := iget_of_eq_some h_models hC
          rcases assumeRATClause_error h_models h_iget h_assume with ⟨hτ_le, hτ_ext⟩
          clear h_assume
          have : line.ratHints.size + 1 - bc = line.ratHints.size - (bc + 1) + 2 := by omega
          rcases uniform_bump_of_uniform_of_extendsFor' (this ▸ h_uniform) hτ_ext with ⟨h_uniform'', hτ''⟩
          clear this
          have : (line.ratHints.size - (bc + 1) + 1) = line.ratHints.size + 1 - (bc + 1) := by omega
          rw [this] at h_uniform''
          clear this
          rcases ih (Nat.succ_le_of_lt hi_lt) hj' h_uniform'' h_loop with ⟨⟨b, hb₁, hb₂⟩, hpf, hL, hC⟩
          rw [hτ''] at hτ_le ⊢
          refine ⟨⟨b, by omega, hb₂⟩, hpf, ?_, hC⟩
          clear ih h_find_hint h_loop b hb₁ hb₂ hpf hC
          simp [← List.getElem_cons_drop hi_lt', hC, hL]
          exact inf_le_of_right_le hτ_le
        · -- Ok: We have now assumed the negation of the clause under σ
          rcases assumeRATClause_ok h_models (iget_of_eq_some h_models hC) h_assume with ⟨hτ'', h_ext⟩
          clear h_assume
          -- We expect a UP contradiction under the new assignment
          split at h_loop
          <;> try simp at h_loop
          rename_i τ''' h_up
          rcases applyUPHints_contra h_models h_up with ⟨h_bot, h_ext₃⟩
          clear h_up
          have h_bc2 : (line.ratHints.size + 1 - bc) = (line.ratHints.size - (bc + 1) + 2) := by omega
          have h_ext₄ := extendsFor_trans h_ext h_ext₃
          rcases uniform_bump_of_uniform_of_extendsFor' (h_bc2 ▸ h_uniform) h_ext with ⟨h_uniform₃, hpf₃⟩
          clear h_uniform₃
          rcases uniform_bump_of_uniform_of_extendsFor' (h_bc2 ▸ h_uniform) h_ext₄ with ⟨h_uniform₄, hpf₄⟩
          have h_bc1 : (line.ratHints.size - (bc + 1) + 1) = line.ratHints.size + 1 - (bc + 1) := by omega
          rw [h_bc1] at h_uniform₄
          rw [hpf₄] at hτ'' ⊢
          rcases ih (Nat.succ_le_of_lt hi_lt) hj' h_uniform₄ h_loop with ⟨⟨b, hb₁, hb₂⟩, hpf₃, hL, hC⟩
          refine ⟨⟨b, by omega, hb₂⟩, hpf₃, ?_, hC⟩
          clear ih h_find_hint h_loop hpf₄ b hb₁ hb₂ hpf₃ hC
          simp [← List.getElem_cons_drop hi_lt', hC, hL]
          clear hC hL
          apply le_iff_inf_compl_eq_bot.mpr
          simp at hτ''
          rw [inf_assoc, ← hτ'']
          exact h_bot

theorem checkLine.loop_true {F : RangeArray ILit} {τ τ' : PPA}
    {Ls : List (Option (List ILit))} {L : List ILit} (h_models : models F Ls L)
    {σ : PS} {line : SRAdditionLine}
  : uniform τ (line.ratHints.size + 1) →
    checkLine.loop F line.witnessMaps line.ratHintIndexes line.ratHints line.ratSizesEq σ 0 (Nat.zero_le _) 0 0 τ
      = ⟨τ', true⟩ →
        (cnfAsListToPropFun Ls) ⊓ τ ≤ PropFun.substL (cnfAsListToPropFun Ls) σ.toSubst
      ∧ (cnfAsListToPropFun Ls) ⊓ τ ≤ PropFun.substL (clauseAsListToPropFun L) σ.toSubst := by
  intro h_uniform h_loop
  have : F.size = F.size - 0 := by exact Eq.symm (Nat.sub_zero F.size)
  conv at h_uniform => rhs; rw [← Nat.sub_zero (line.ratHints.size + 1)]
  rcases checkLine.loop_true_aux h_models (Nat.zero_le _) this h_uniform h_loop with ⟨hb, hτ', hL, hC⟩
  clear hb h_loop
  simp at hL
  exact ⟨hL, hC⟩

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

-- Alternative proof that uses the computational `substL` instead of the abstract `subst`.
theorem eqsatL_of_SR {F C : PropFun ν} :
    (∃ σ, F ⊓ Cᶜ ≤ substL (F ⊓ C) σ) → EquiSat F (F ⊓ C) := by
  rintro ⟨σ, hSR⟩
  constructor
  · rintro ⟨τ, hτF⟩
    by_cases hτC : τ ⊨ C
    · use τ
      rw [satisfies_conj]
      exact ⟨hτF, hτC⟩
    · replace hSR := entails_ext.mp hSR τ
      have hτFC : τ ⊨ F ⊓ Cᶜ := by
        simpa [satisfies_conj] using And.intro hτF hτC
      have hSubst : τ ⊨ substL (F ⊓ C) σ := hSR hτFC
      use τ.subst (⟦σ ·⟧)
      simpa [satisfies_substL] using hSubst
  · rintro ⟨τ, hτ⟩
    rw [satisfies_conj] at hτ
    exact ⟨τ, hτ.1⟩

theorem checkLine_spec {F : RangeArray ILit}
    {Ls : List (Option (List ILit))} {L : List ILit} (h_models : models F Ls L)
    (τ : PPA) (σ : PS) (line : Trestle.Parsing.SRAdditionLine)
  : match checkLine ⟨F, τ, σ⟩ line with
    | .error false => True
    | .error true => (cnfAsListToPropFun Ls) = ⊥
    | .ok ⟨F', _, _⟩ =>
      F' = F.commit
      ∧ PropFun.EquiSat (cnfAsListToPropFun Ls) (cnfAsListToPropFun Ls ⊓ clauseAsListToPropFun L)
  := by
  unfold checkLine
  simp [assumeNegatedCandidateFor_eq_assumeNegatedClauseFor _ _ h_models]
  -- Assume the negation of the candidate clause
  cases h_assume_negated : τ.reset.assumeNegatedClauseFor { toList := L } (line.ratHints.size + 1)
  <;> simp
  rename_i τ₂
  rcases assumeNegatedClauseFor_ok h_assume_negated with ⟨hτ₂, h_ext₂⟩
  clear h_assume_negated
  simp at hτ₂
  -- Apply global UP hints
  match h_hints : F.applyUPHints (line.ratHints.size + 1) τ₂ line.upHints with
  | ⟨τ₃, .err⟩ => simp
  | ⟨τ₃, .contra⟩ =>
    -- Contradiction. No SR check needed, was a RUP clause
    rcases applyUPHints_contra h_models h_hints with ⟨hτ₂_bot, h_ext⟩
    clear h_hints
    by_cases h_usize : F.usize = 0
    <;> simp [h_usize]
    -- The candidate is empty, meaning the formula is UNSAT.
    · simp [h_models.h_size₂] at h_usize
      subst h_usize
      simp at hτ₂
      simp [hτ₂] at hτ₂_bot
      exact hτ₂_bot
    -- The candidate is nonempty, meaning the candidate is RUP.
    · apply equisat_of_entails
      simp [hτ₂] at hτ₂_bot
      exact le_iff_inf_compl_eq_bot.mpr hτ₂_bot
  | ⟨τ₃, .unit⟩ =>
    -- We derived units, but no contradiction. SR checking continues.
    -- First: the candidate *must* be nonempty.
    by_cases h_usize : F.usize = 0
    <;> simp [h_usize]
    have h_usize' : 0 < F.usize := by omega
    -- Does the call to `loop` return an error?
    split
    <;> try exact True.intro
    all_goals (
      rename_i h_state
      -- Is the first witness literal the pivot?
      split at h_state
      <;> try simp at h_state
    )
    rename_i τ₄ h_loop
    rcases h_state with ⟨rfl, rfl, rfl⟩
    apply And.intro rfl
    rcases applyUPHints_unit h_models h_hints with ⟨hτ₃, h_ext₃⟩
    clear h_hints
    replace h_ext₃ := extendsFor_trans h_ext₂ h_ext₃
    have h_uniform₃ := uniform_of_extendsFor_reset h_ext₃
    rcases checkLine.loop_true h_models h_uniform₃ h_loop with ⟨hL₃, hC₃⟩
    clear h_loop h_uniform₃
    apply eqsatL_of_SR
    use (assumeWitness σ line.witnessLits line.witnessMaps).toSubst
    rw [substL_conj, le_inf_iff, ← hτ₂]
    have := inf_le_inf (le_refl (cnfAsListToPropFun Ls)) hτ₃
    rw [← inf_assoc, Std.min_self] at this
    exact ⟨le_trans this hL₃, le_trans this hC₃⟩

theorem checkLine_ok {F F' : RangeArray ILit}
    {Ls : List (Option (List ILit))} {L : List ILit} (h_models : models F Ls L)
    (τ τ' : PPA) (σ σ': PS) (line : Trestle.Parsing.SRAdditionLine)
  : checkLine ⟨F, τ, σ⟩ line = .ok ⟨F', τ', σ'⟩ →
    F' = F.commit
    ∧ PropFun.EquiSat (cnfAsListToPropFun Ls) (cnfAsListToPropFun Ls ⊓ clauseAsListToPropFun L) := by
  intro h
  have := checkLine_spec h_models τ σ line
  simp [h] at this
  exact this

theorem checkLine_error_true {F : RangeArray ILit}
    {Ls : List (Option (List ILit))} {L : List ILit} (h_models : models F Ls L)
    (τ : PPA) (σ : PS) (line : Trestle.Parsing.SRAdditionLine)
  : checkLine ⟨F, τ, σ⟩ line = .error true →
    (cnfAsListToPropFun Ls) = ⊥ := by
  intro h
  have := checkLine_spec h_models τ σ line
  simp [h] at this
  exact this

/-! # consumeDeletionLine correctness -/

theorem consumeDeletionLine.loop.cons_succ' (F : RangeArray ILit) {del : Nat} {dels : List Nat}
    {i j : Nat}
  : j = dels.length - i →
    consumeDeletionLine.loop { toList := del :: dels } (i + 1) F = consumeDeletionLine.loop { toList := dels } i F := by
  intro hj
  induction j generalizing F i with
  | zero =>
    have h_le := Nat.le_of_sub_eq_zero hj.symm
    unfold loop
    simp [not_lt_of_ge h_le]
  | succ j ih =>
    have hi : i < dels.length := by
      apply Nat.lt_of_sub_pos
      rw [← hj]
      exact Nat.zero_lt_succ j
    have hj' : j = dels.length - (i + 1) := by omega
    unfold consumeDeletionLine.loop
    simp [hi]
    -- Is the deletion ID in the formula?
    split
    <;> try rfl
    rename_i h_del_lt
    -- Has the clause already been deleted?
    split
    <;> try rfl
    rename_i h_not_deleted
    simp at h_not_deleted
    exact ih (F.delete dels[i] h_del_lt) hj'

@[simp]
theorem consumeDeletionLine.loop.cons_succ (F : RangeArray ILit) (del : Nat) (dels : List Nat) (i : Nat)
  : consumeDeletionLine.loop { toList := del :: dels } (i + 1) F = consumeDeletionLine.loop { toList := dels } i F := by
  exact @consumeDeletionLine.loop.cons_succ' F del dels i (dels.length - i) (by omega)

-- This is a rather weak theorem.
-- After all, this spec allows the function to return a formula with all clauses deleted.
-- A stronger version might specify that deleted clauses are either from `line` or are deleted in the original formula.
theorem consumeDeletionLine_ok {F F' : RangeArray ILit} {line : SRDeletionLine}
  {Ls : List (Option (List ILit))} {L : List ILit} (h_models : models F Ls L) :
    consumeDeletionLine F line = .ok F' →
      ∃ Ls', models F' Ls' L ∧
        cnfAsListToPropFun Ls ≤ cnfAsListToPropFun Ls' := by
  have ⟨clauses⟩ := line
  unfold consumeDeletionLine
  induction clauses generalizing F Ls with
  | nil =>
    rw [consumeDeletionLine.loop]
    simp
    rintro rfl
    use Ls
  | cons clauseId clauses ih =>
    unfold consumeDeletionLine.loop
    simp at ih ⊢
    intro h_loop
    -- Check that the clause ID to be deleted is in range
    split at h_loop
    <;> try simp at h_loop
    rename_i h_id_lt
    rw [h_models.h_size₁] at h_id_lt
    -- Check that the clause ID is not already deleted
    split at h_loop
    <;> try simp at h_loop
    rename_i h_not_deleted
    simp at h_not_deleted
    have := models_delete h_models h_id_lt
    rcases ih this h_loop with ⟨Ls', h_models', hpf⟩
    use Ls', h_models'
    exact le_trans (cnfPropFun_le_set_none h_id_lt) hpf

end Trestle.SR
