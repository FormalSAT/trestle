/-

Theory and implementation for the SR proof system and a checker.

Authors: Cayden Codel
Carnegie Mellon University

-/

import Trestle.Data.Cnf
import Trestle.Data.ICnf
import Trestle.Data.PPA
import Trestle.Data.PS
import Trestle.Model.PropFun
import Trestle.Model.Quantification

namespace SR

open Trestle Trestle.Model Nat
open PPA PS LitVar ILit IVar LawfulLitVar PropFun
open ResultT

inductive UPResult
  | checked : UPResult
  | error : UPResult

open UPResult

structure SRLine where
  clause : IClause
  witness_lits : Array ILit
  witness_maps : Array (IVar × ILit)
  up_hints : Array Nat
  rat_hints : Array (Nat × Array Nat)

structure SRState where
  F : ICnf
  τ : PPA
  σ : PS

-- Build τ from candidate redundant clause C. Resets from previous line.
def assumeNegatedClause (τ : PPA) (C : IClause) (offset : Nat) : PPA :=
  τ.reset.setNegatedClauseFor C offset

/-
theorem toPropFun_data_cons (l : L) (ls : List L) :
    toPropFun ({ data := (l :: ls) } : Clause L) = LitVar.toPropFun l ⊔ toPropFun ( { data := ls } : Clause L) := by
  rw [of_cons]; simp
-/

@[simp] theorem assumeNegatedClause_empty (τ : PPA) (offset : Nat) :
    assumeNegatedClause τ #[] offset = τ.reset := by
  simp [assumeNegatedClause]
  done

#exit

def applyUPHint (F : ICnf) (offset : Nat) (τ : PPA) (hint : Nat) : ResultT (PPA × UPResult) PPA :=
  if h_hint : hint < F.size then
    let C := F.get ⟨hint, h_hint⟩
    match τ.unitProp C with
    | .falsified => done ⟨τ, .checked⟩
    | .satisfied => done ⟨τ, .error⟩
    | .multipleUnassignedLiterals => done ⟨τ, .error⟩
    | .unit l => ok (τ.setLitFor l offset)
  else
    done ⟨τ, .error⟩

-- Cayden TODO: Way to combine this along with reduced? in the non-up-next-RAT clause case?
-- Returns true if (C|σ) is satisfied by τ, false otherwise
def evalsToTrueUnderWitness (C : IClause) (σ : PS) (τ : PPA) : Bool :=
  match C.foldlM (init := ()) (fun _ lit =>
    match σ.litValue lit with
    | .tr => done ()   -- Shouldn't get here
    | .fls => ok ()
    | .lit l =>
      match τ.litValue? l with
      | some true => done () -- τ satisfies the clause C, so we're done
      | some false => ok ()
      | none => ok ()) with
  | ok () => false
  | done () => true

-- Assuming that (C|σ) is reduced but not satisfied and that C is a RAT clause, sets τ ← τ ⊓ (C|σ)ᶜ
def assumeRATClause (C : IClause) (σ : PS) (τ : PPA) : ResultT Unit PPA :=
  C.foldlM (init := τ) (fun τ lit =>
    match σ.litValue lit with
    | .tr => done ()      -- (C|σ) isn't satisfied, so we shouldn't get here
    | .fls => ok τ        -- Ignore the literal
    | .lit l =>
      match τ.litValue? l with
      | some true => done ()   -- (C|σ)|τ is satisfied, so we're done (shouldn't happen)
      | some false => ok τ     -- Its negation is true in τ, so ignore the literal
      | none => ok (τ.setLit (-l)))

-- Set the witness substitution σ from the provided mapping, resetting σ first
def assumeWitness (σ : PS) (A₁ : Array ILit) (A₂ : Array (IVar × ILit)) : PS :=
  (A₁.foldl (init := σ.reset) (fun σ' l => σ'.setLit l)).setVars' A₂

def checkClause (F : ICnf) (σ : PS) (ratHints : Array (Nat × Array Nat))
    (p : PPA × Nat) (index : Fin F.size) (C : IClause) : ResultT Unit (PPA × Nat) :=
  let ⟨τ, ratIndex⟩ := p
  match σ.reduce C with
  | .satisfied => ok (τ, ratIndex)
  | .notReduced => ok (τ, ratIndex)
  | _ =>
    -- The clause was reduced but not satisfied, so we have a candidate RAT clause
    -- If the clause index doesn't match the current index, then the proof doesn't check
    if h_index : ratIndex < ratHints.size then
      let ⟨ratClauseIndex, ratClauseHints⟩ := ratHints.get ⟨ratIndex, h_index⟩
      if index.val != ratClauseIndex then
        -- The potential RAT clause can be satisfied by τ instead, so check that. If not, error.
        if evalsToTrueUnderWitness C σ τ then
          ok (τ, ratIndex)
        else
          done ()
      else
        match assumeRATClause C σ τ with
        -- If we early exit from assumeRATClause, then the RAT clause trivially checks
        | done _ => ok (τ.bump, ratIndex + 1)
        | ok τ =>
          match ratClauseHints.foldlM (init := τ) (applyUPHint F 0) with
          | done (τ, .checked) => ok (τ.bump, ratIndex + 1)
          | done (_, .error) => done ()
          -- We expect contradiction at the end of the hints
          | ok _ => done ()
    else
      done ()

def checkLine (S : SRState) (line : SRLine) : ResultT Bool SRState :=
  let ⟨F, τ, σ⟩ := S
  let ⟨C, w_tf, w_maps, UPhints, RAThints⟩ := line
  let τ := assumeNegatedClause τ.reset C RAThints.size

  -- Evaluate the UP hints
  match UPhints.foldlM (init := τ) (applyUPHint F RAThints.size) with
  | done ⟨τ, .checked⟩ =>
    if C = #[] then
      done true
    else
      ok ⟨F.addClause C, τ, σ⟩
  | done ⟨_, .error⟩ => done false
  -- Unit propagation didn't lead to contradiction, so continue
  | ok τ =>

  -- Now add the witness (unless C is empty, at which point we error)
  if C = #[] then done false else
  if C.get? 0 ≠ w_tf.get? 0 then done false else
  let σ := assumeWitness σ w_tf w_maps


  -- Go through each clause in the formula. If the witness reduces it, but
  -- doesn't satisfy it, try the next RAT hint
  match F.foldlIdxM (init := (⟨τ, 0⟩ : PPA × Nat)) (checkClause F σ RAThints) with
  | done () => done false
  | ok (τ, _) => ok ⟨F.addClause C, τ, σ⟩ -- The RAT hint checked, so we continue

def checkProof (F : ICnf) (proof : Array SRLine) : Bool :=
  let τ := PPA.new 100
  let σ := PS.new 100
  match proof.foldlM (init := ⟨F, τ, σ⟩) checkLine with
  | ok _ => false
  | done false => false
  | done true => true

-----------------------------------------

/-! # correctness -/

theorem applyUPHint_checked {F : ICnf} {offset : Nat} {τ : PPA} {hint : Nat} :
    applyUPHint F offset τ hint = .done (τ, .checked) → F.toPropFun ⊓ τ ≤ ⊥ := by
  intro h
  unfold applyUPHint at h
  split at h <;> simp at h
  split at h <;> simp at h
  rename hint < F.size => h_hint
  rename (unitProp τ _ = _) => h_up
  have := contradiction_of_UP_falsified h_up
  rw [inf_comm] at this
  have h_le : F.toPropFun ≤ F[hint].toPropFun := Cnf.ith_le ⟨hint, h_hint⟩
  exact le_trans (inf_le_inf_right τ.toPropFun h_le) this

theorem applyUPHint_checked_eq {F : ICnf} {offset : Nat} {τ τ' : PPA} {hint : Nat} :
    applyUPHint F offset τ hint = .done (τ', .checked) → τ = τ' := by
  sorry
  done

theorem applyUPHint_ok {F : ICnf} {offset : Nat} {τ τ' : PPA} {hint : Nat} :
    applyUPHint F offset τ hint = .ok τ' → F.toPropFun ⊓ τ ≤ τ' := by
  intro h
  unfold applyUPHint at h
  split at h <;> simp at h
  split at h <;> simp at h
  rename hint < F.size => h_hint
  rename (unitProp τ _ = _) => h_up
  subst h
  have := (extended_of_UP_unit h_up).1
  simp at this
  sorry
  --exact le_trans (inf_le_inf_right τ.toPropFun (Cnf.ith_le ⟨hint, h_hint⟩)) this

#check Array.foldl

theorem assumeNegatedClause_spec (τ : PPA) (C : IClause) (offset : Nat) :
    (assumeNegatedClause τ C offset).toPropFun = C.toPropFunᶜ ∧
    ∀ l ∈ C, τ.isSetFor (toVar l) (offset + 1) := by
  have ⟨C⟩ := C
  rw [assumeNegatedClause]
  induction' C with l ls ih generalizing τ
  · simp [setNegatedClauseFor]
  · simp only [setNegatedClauseFor, Array.size_mk, List.length_cons, Clause.toPropFun_data_cons,
    compl_sup]
    done
  sorry
  done

#exit

open Classical
-- TODO: How to write the spec for this?
-- Jeremy: Can write the computational version of this, but if it's only for a theorem,
--         no need to make this efficient
theorem assumeWitness_spec (σ : PS) (A₁ : Array ILit) (A₂ : Array (IVar × ILit)) :
    (assumeWitness σ A₁ A₂).toSubst =
      (fun v => if ∃ (l : ILit), (v, l) ∈ A₂ then l
        else if ∃ l ∈ A₁, (toVar l) = v then
          if isPos l then ⊤ else ⊥
        else v.toPropFun) := by
  sorry
  done

#exit

theorem fold_UP_checked {F : ICnf} {A : Array Nat} {offset : Nat} {τ τ' : PPA} :
    A.foldlM (init := τ) (applyUPHint F offset) = done (τ', .checked) →
    F.toPropFun ⊓ τ ≤ ⊥ := by
  have ⟨A⟩ := A
  rw [Array.foldlM_eq_foldlM_data]
  induction' A with n ns ih generalizing τ
  · simp
  · simp
    intro h
    match hn : applyUPHint F offset τ n with
    | done (τ₁, .checked) =>
      rw [← applyUPHint_checked_eq hn] at hn
      exact le_bot_iff.mp (applyUPHint_checked hn)
    | done (τ₁, .error) =>
      simp [hn] at h; injection h
      rename _ => h
      simp at h
      done
    | ok τ₁ =>
      simp [hn] at h
      have := ih h
      have := inf_le_inf_left F.toPropFun (applyUPHint_ok hn)
      rw [← inf_assoc, inf_idem] at this
      exact le_bot_iff.mp (le_trans this (ih h))

theorem fold_UP_ok {F : ICnf} {A : Array Nat} {offset : Nat} {τ τ' : PPA} :
    A.foldlM (init := τ) (applyUPHint F offset) = ok τ' →
    F.toPropFun ⊓ τ ≤ τ' := by
  have ⟨A⟩ := A
  rw [Array.foldlM_eq_foldlM_data]
  induction' A with n ns ih generalizing τ
  · simp [pure]; rintro rfl; exact inf_le_right
  · simp
    intro h
    match hn : applyUPHint F offset τ n with
    | done (τ₁, .error)   => simp [hn] at h; injection h
    | done (τ₁, .checked) => simp [hn] at h; injection h
    | ok τ₁ =>
      simp [hn] at h
      have := ih h
      have := inf_le_inf_left F.toPropFun (applyUPHint_ok hn)
      rw [← inf_assoc, inf_idem] at this
      exact le_trans this (ih h)

--τ.toPropFun ≤ (PropFun.bind σ.toSubst C.toPropFun) ∧
-- TODO: Hypotheses about form of τ' wrt τ and SetFor judgment
theorem assumeRATClause_ok {C : IClause} {σ : PS} {τ τ' : PPA} :
    (PropFun.bind σ.toSubst C.toPropFun ≠ ⊤) →
    assumeRATClause C σ τ = ok τ' →
    τ'.toPropFun = τ.toPropFun ⊓ (PropFun.bind σ.toSubst C.toPropFun)ᶜ := by
  have ⟨C⟩ := C
  intro h_notSatisfied h
  rw [assumeRATClause, Array.foldlM_eq_foldlM_data] at h
  induction' C with l ls ih generalizing τ
  · rw [List.foldlM_nil] at h; injection h with h; subst h; simp
  · simp at h h_notSatisfied ⊢
    split at h <;> rename litValue _ _ = _ => hl <;> try simp [ResultT.bind, Bind.bind] at h
    · rw [litValue_fls_iff] at hl; simp [hl]
      apply ih (ne_top_right_of_disj_ne_top h_notSatisfied)
      rw [h]
    · rename ILit => lit
      split at h <;> try simp at h
      rename PPA => τ''
      rename _ = ok τ'' => h₁
      rw [litValue_lit_iff] at hl; simp [hl]
      have := @ih τ'' (ne_top_right_of_disj_ne_top h_notSatisfied)
      simp [h] at this
      split at h₁ <;> rename litValue? _ _ = _ => hlit <;> try simp at h₁
      · subst h₁
        rwa [← inf_assoc, inf_eq_of_litValue?_false hlit]
      · subst h₁
        rw [litValue?_none_iff_litValue?_negate_none] at hlit
        rwa [toPropFun_setLit_of_none hlit, toPropFun_neg, inf_assoc] at this

theorem assumeRATClause_done {C : IClause} {σ : PS} {τ : PPA} :
    (PropFun.bind σ.toSubst C.toPropFun ≠ ⊤) →
    assumeRATClause C σ τ = done () → τ.toPropFun ≤ (PropFun.bind σ.toSubst C.toPropFun) := by
  sorry
  done

/-
  have ⟨C⟩ := C
  intro h_notSatisfied h
  rw [assumeRATClause, Array.foldlM_eq_foldlM_data] at h
  induction' C with l ls ih generalizing τ
  · simp at h
  · split at h <;> try simp at h
    subst h; rename PPA => τ'; rename _ => ih
    rename List.foldlM _ _ _ = _ => h
    rw [Clause.toPropFun, List.foldr_cons, ← Clause.toPropFun, bind_disj] at h_notSatisfied
    rw [Clause.toPropFun, List.foldr_cons, ← Clause.toPropFun]
    have := Ne.lt_of_le h_notSatisfied le_top
    replace this := lt_of_le_of_lt le_sup_right this
    replace this := LT.lt.ne this
    simp at h
    split at h <;> rename litValue _ _ = _ => hl
    · rw [litValue_tr_iff] at hl; simp [hl] at h_notSatisfied
    · rw [litValue_fls_iff] at hl; simp [hl]
      replace ih := @ih τ this
      simp [ResultT.bind, Bind.bind] at h
      simp [h] at ih
      exact ih
    · rename ILit => lit
      rename PSVal => val
      rw [litValue_lit_iff] at hl; simp [hl]
      split at h <;> rename litValue? _ _ = _ => hlit
      · injection h with h; subst h
        rw [litValue?_true_iff] at hlit

        exact le_sup_of_le_left hlit
      · simp [ResultT.bind, Bind.bind] at h
        replace ih := @ih τ this
        simp [h] at ih
        exact le_sup_of_le_right ih
      · replace ih := @ih (τ.setLit (-lit)) this
        simp [ResultT.bind, Bind.bind] at h
        simp [h] at ih
        have hlit' : τ.litValue? (-lit) = none := by
          rw [litValue?_negate, hlit]; rfl
        rw [toPropFun_setLit_of_none hlit'] at ih
        rw [toPropFun_neg, helper, compl_compl] at ih
        exact ih -/


theorem evalsToTrueUnderWitness_true {C : IClause} {σ : PS} {τ : PPA} :
    (PropFun.bind σ.toSubst C.toPropFun ≠ ⊤) →
    evalsToTrueUnderWitness C σ τ = true →
    τ.toPropFun ≤ (PropFun.bind σ.toSubst C.toPropFun) := by
  have ⟨C⟩ := C
  intro h_notSatisfied
  rw [evalsToTrueUnderWitness, Array.foldlM_eq_foldlM_data]
  induction' C with l ls ih <;> simp
  intro h
  split at h <;> try contradiction
  rename _ => h; clear h
  rename _ => h
  simp at h_notSatisfied
  have := Ne.lt_of_le h_notSatisfied le_top
  replace this := lt_of_le_of_lt le_sup_right this
  replace this := LT.lt.ne this
  split at h <;> rename litValue _ _ = _ => hl
  · rw [litValue_tr_iff] at hl; simp [hl]
  · rw [litValue_fls_iff] at hl; simp [hl]
    simp [ResultT.bind, Bind.bind] at h
    apply ih this
    rw [h]
  · rename ILit => lit
    rename PSVal => val
    rw [litValue_lit_iff] at hl; simp [hl]
    split at h <;> rename litValue? _ _ = _ => hlit
    · rw [litValue?_true_iff] at hlit
      exact le_sup_of_le_left hlit
    -- Cayden TODO: These two proofs are duplicated
    · simp [ResultT.bind, Bind.bind] at h
      have := ih this
      simp [h] at this
      exact le_sup_of_le_right this
    · simp [ResultT.bind, Bind.bind] at h
      have := ih this
      simp [h] at this
      exact le_sup_of_le_right this

/-
theorem comps_eq_of_checkClause_ok_ratIndex {F : ICnf} {σ : PS} {rat_hints : Array (Nat × Array Nat)}
    {τ τ' β β' : PPA} {ratIndex : Nat} {index : Fin F.size} {C : IClause} :
    checkClause F σ rat_hints τ β ratIndex index

theorem ok_eq_of_checkClause_ok {F : ICnf} {σ : PS} {rat_hints : Array (Nat × Array Nat)}
    {τ τ' β β' : PPA} {ratIndex : Nat} {index : Fin F.size} {C : IClause} :
    checkClause F σ rat_hints τ β ratIndex index C = ok (τ', β', ratIndex) -/

theorem checkClause_ok {F : ICnf} {σ : PS} {ratHints : Array (Nat × Array Nat)}
    {τ τ' β β' : PPA} {ratIndex ratIndex' : Nat} {index : Fin F.size} {C : IClause} :
    F[index.1] = C →
    checkClause F σ ratHints ⟨τ, β, ratIndex⟩ index C = ok (τ', β', ratIndex') →
      (PropFun.bind σ.toSubst C.toPropFun) = ⊥ ∨
      F.toPropFun ⊓ τ ≤ PropFun.bind σ.toSubst C.toPropFun := by
  intro hFC h
  rw [checkClause] at h
  match hσC : σ.reduced? β C with
  | (.satisfied, _) => rw [reduced?_satisfied_iff] at hσC; simp [hσC]
  | (.notReduced, _) =>
    rw [reduced?_notReduced_iff] at hσC
    rw [hσC]
    -- Cayden TODO: What is the right kind of "mem" we should use here?
    have := F.getElem_mem_data index.isLt
    rw [hFC, Array.mem_data] at this
    exact Or.inr (le_trans inf_le_left (Cnf.toPropFun_le_mem this))
  | (.falsified, _) => rw [reduced?_falsified_iff, le_bot_iff] at hσC; simp [hσC]
  | (.reduced, β₂) =>
    right
    simp [hσC] at h
    replace hσC := reduced?_reduced hσC
    split at h <;> try contradiction
    -- Split into RAT clause/attempt to satisfy candidate RAT clause cases
    rename ratIndex < _ => hri
    split at h
      -- Actual RAT clause case
    · rename index.val = _ => hi
      split at h <;> rename assumeRATClause _ _ _ = _ => h_assume
      · exact le_trans inf_le_right (assumeRATClause_done hσC.1 h_assume)
      · rename PPA => τ₂
        have := assumeRATClause_ok hσC.1 h_assume
        split at h <;> rename Array.foldlM _ _ _ = _ => h_fold <;> try contradiction
        have := fold_UP_checked h_fold
        rwa [assumeRATClause_ok hσC.1 h_assume, ← inf_assoc, ← le_iff_inf_compl_le_bot] at this
        done
      -- Candidate RAT clause case, to satisfy
    · split at h
      · rename evalsToTrueUnderWitness _ _ _ = _ => h_eval
        exact le_trans inf_le_right (evalsToTrueUnderWitness_true hσC.1 h_eval)
      · contradiction

--  match F.foldlIdxM (init := (⟨τ, β, 0⟩ : PPA × PPA × Nat)) (checkClause F σ RAThints)
theorem fold_checkClause_ok {F : ICnf} {σ : PS} {ratHints : Array (Nat × Array Nat)}
    {τ τ' β β' : PPA} {ratIndex : Nat} :
    F.foldlIdxM (init := ⟨τ, β, 0⟩) (checkClause F σ ratHints) = ok (τ, β, ratIndex) →
      F.toPropFun ⊓ τ ≤ (PropFun.bind σ.toSubst F) := by
  have ⟨F⟩ := F
  simp [Array.foldlIdxM, pure, Bind.bind, ResultT.bind]
  rw [Array.foldlM_eq_foldlM_data]
  induction' F with C CS ih generalizing τ β ratIndex <;> simp
  intro h
  split at h <;> try contradiction
  rename (PPA × PPA × Nat) × Nat => acc
  rename _ = ok acc => heq
  simp at h
  split at heq <;> try contradiction
  rename (PPA × PPA × Nat) => acc'
  rename _ = ok acc' => h_check
  simp [h_check] at heq
  simp [Cnf.of_cons]
  have ⟨τ₂, β₂, ratIndex₂⟩ := acc'
  rcases checkClause_ok rfl h_check with (h | h)
  · stop

    done
  stop
  done

def checkClause_invariant (τ : PPA) (index : Nat) (hints : Array (Nat × Array Nat)) : Prop :=
  ∀ (v : IVar), isSet τ v → isSetFor τ v (hints.size - index)

theorem checkClause_ok' {F : ICnf} {σ : PS} {ratHints : Array (Nat × Array Nat)}
    {τ τ' β β' : PPA} {ratIndex ratIndex' : Nat} {index : Fin F.size}
    (h_inv : checkClause_invariant τ ratIndex ratHints) :
    checkClause F σ ratHints ⟨τ, β, ratIndex⟩ index (F.get index) = ok (τ', β', ratIndex') →
    (checkClause_invariant τ' ratIndex' ratHints ∧
     F.toPropFun ⊓ τ ≤ (PropFun.bind σ.toSubst (F.get index).toPropFun)) := by
  sorry
  done

theorem fold_checkClause_ok' {F : ICnf} {σ : PS} {ratHints : Array (Nat × Array Nat)}
    {τ β : PPA} {ratIndex : Nat}
    (h_inv : checkClause_invariant τ 0 ratHints) :
    F.foldlIdxM (init := (τ, β, 0)) (checkClause F σ ratHints) = ok (τ', β', ratIndex) →
      F.toPropFun ⊓ τ ≤ (PropFun.bind σ.toSubst F) := by
  sorry
  done


theorem SR_core' {F : ICnf} {C : IClause} :
    (∃ σ : (IVar → PropForm IVar), PropFun.bind σ C = ⊤ ∧ F.toPropFun ⊓ Cᶜ ≤ PropFun.bind σ F) →
    eqsat F (F ⊓ C.toPropFun) := by
  rintro ⟨σ, hC, hFC⟩
  constructor
  · rintro ⟨τ, hτF⟩
    by_cases hτC : τ ⊨ C.toPropFun
    · use τ
      rw [satisfies_conj]
      exact ⟨hτF, hτC⟩
    · replace hFC := entails_ext.mp hFC τ
      simp [satisfies_conj, and_imp, -satisfies_bind] at hFC
      replace hFC := hFC hτF hτC
      have : τ ⊨ PropFun.bind σ C := by rw [hC]; rfl
      simp at hFC this
      use PropAssignment.preimage (fun x => ⟦σ x⟧) τ
      rw [satisfies_conj]
      exact ⟨hFC, this⟩
  · rintro ⟨τ, hτ⟩
    rw [satisfies_conj] at hτ
    exact ⟨τ, hτ.1⟩

-- IClause × Array ILit × Array (IVar × ILit) × Array Nat × Array (Nat × Array Nat)
-- For the line to continue checking, the clause to be added must be redundant
theorem checkLine_ok {F : ICnf} {τ β : PPA} {σ : PS} {line : SRLine} {S : SRState}
    (hF : F ≠ #[]) : -- TODO remove hyp later? But we have to start with UNSAT formula
    checkLine ⟨F, τ, β, σ⟩ line = ok S → eqsat F.toPropFun (F.toPropFun ⊓ line.1) := by
  let ⟨C, w_tf, w_maps, up, rats⟩ := line
  simp [checkLine]
  split <;> try simp
  · by_cases hC : C = #[] <;> simp [hC]
    rename PPA => τ'
    rename Array.foldlM _ _ _ = _ => h_fold
    rintro rfl
    have := fold_UP_checked h_fold
    simp [assumeNegatedClause_spec τ.reset C rats.size] at this
    exact eqsat_of_entails (le_iff_inf_compl_eq_bot.mpr this)
  · rename PPA => τC
    rename _ => hτC_UP
    have hτC := fold_UP_ok hτC_UP
    simp [assumeNegatedClause_spec τ.reset C rats.size] at hτC
    by_cases hC : C = #[] <;> simp [hC]
    -- TODO: I want to use split here, but it renames the PPA's in the ok, and I can't rename τ' as a result
    --split <;> try simp
    match heq : F.foldlIdxM (checkClause F (assumeWitness σ w_tf w_maps) rats) (τC, β, 0) 0 F.size with
    | done _ => simp
    | ok (τ', β', index) =>
    simp
    split <;> try simp
    rename _ = w_tf[0]? => h_pivot
    rintro rfl
    apply SR_core'
    use (assumeWitness σ w_tf w_maps).toSubst
    constructor
    · sorry -- Need assumeWitness_spec for this, but because we check the pivot, this is an easy lemma
      done
    have h_inv : checkClause_invariant τC 0 rats := by
      --simp [checkClause_invariant]
      sorry
      done
    have : F.toPropFun ⊓ (F.toPropFun ⊓ C.toPropFunᶜ) ≤ F.toPropFun ⊓ τC := inf_le_inf_left (Cnf.toPropFun F) hτC
    rw [← inf_assoc, inf_idem] at this
    exact le_trans this (fold_checkClause_ok' h_inv heq)
    done

/--
    split <;> try simp
    rename _ = w_tf[0]? => h_pivot
    rintro rfl
    apply SR_core'
    use (assumeWitness σ w_tf w_maps).toSubst
    constructor
    · sorry -- Need assumeWitness_spec for this, but because we check the pivot, this is an easy lemma
      done
    --rename _ = ok _ => heq  -- Use when splitting
    have ⟨F⟩ := F
    rw [Array.foldlIdxM, Array.foldlM_eq_foldlM_data] at heq
    induction' F with C' CS ih generalizing τ β σ
    · simp at hF
    · match CS with
      | [] =>
        simp at heq

        have hC'_eq : C' = #[C'].get ⟨0, by simp⟩ := rfl
        --conv at heq => lhs; rhs; rw [hC'_eq]
        have := (checkClause_ok' h_inv heq).2
        simp at this hτC ⊢
        apply le_trans _ this
        have : C'.toPropFun = C'.toPropFun ⊓ C'.toPropFun := inf_idem.symm
        conv => lhs; lhs; rw [this]
        rw [inf_assoc]
        exact inf_le_inf_left (Clause.toPropFun C') hτC
        done
      | C'' :: CS =>
        clear hF
        simp at heq
        have : { data := C'' :: CS } ≠ #[] := by sorry
        have := ih this

        done

      done
    done
  done
  stop
  split at h_fold <;> try contradiction
  · rename _ => h
    rename Array.foldlM _ _ _ = _ => h_fold
    split at h <;> try contradiction
    · injection h with h
      injection h with hF hτ hβ hσ
      subst hF
      simp [le_iff_inf_compl_le_bot]
      have := fold_UP_checked h_fold
      rwa [assumeNegatedClause_spec, le_bot_iff] at this
  · rename _ => h
    rename PPA => τ₁
    rename Array.foldlM _ _ _ = _ => h_fold
    have := fold_UP_ok h_fold
    rw [assumeNegatedClause_spec] at this
    split at h <;> try contradiction
    stop
  stop
  done -/

-- For the line to finish checking, the empty clause must be derived
theorem checkLine_done_true {F : ICnf} {τ β : PPA} {σ : PS} {line : SRLine} :
    checkLine (SRState.mk F τ β σ) line = done true → F.toPropFun = ⊥ := by
  let ⟨C, w_tf, w_maps, up, rats⟩ := line
  simp [checkLine]
  split <;> try simp
  · by_cases hC : C = #[] <;> simp [hC]
    rename PPA => τ'
    rename _ = done (τ', checked) => heq
    have := fold_UP_checked heq
    simp [hC] at this
    sorry
    --exact this
  · by_cases hC : C = #[] <;> simp [hC]
    split
    --<;> simp
    sorry
    done

-- For the proof to check, the clause must be UNSAT
theorem checkProof_done_true {F : ICnf} {τ β : PPA} {σ : PS} {proof : Array SRLine} :
    proof.foldlM (init := SRState.mk F τ β σ) checkLine = done true → F.toPropFun = ⊥ := by
  have ⟨proof⟩ := proof
  rw [Array.foldlM_eq_foldlM_data]
  induction' proof with line lines ih generalizing F τ β σ
  <;> simp
  match h_line : checkLine (SRState.mk F τ β σ) line with
  | done false => intro h; injection h; contradiction
  | done true => exact (fun _ => checkLine_done_true h_line)
  | ok S' => exact (fun h => le_bot_iff.mp (ih h ▸ checkLine_ok h_line))

theorem checkProof_correct (F : ICnf) (proof : Array SRLine) :
    checkProof F proof = true → F.toPropFun = ⊥ := by
  simp only [checkProof]
  split <;> try simp
  rename _ => h
  exact checkProof_done_true h

#exit

def SRLine := IClause × List (IVar × ILit) × List IClause × List (IClause × List IClause)

-- Set up the partial assignment from the candidate clause
def step2 (τ : PPA) (C : IClause) (offset : Nat) : PPA := (τ.reset).setNegatedClauseFor C offset

-- Perform unit propagation
def step3UP (offset : Nat) (τ : PPA) (C : IClause) : ResultT Bool PPA :=
  match τ.unitProp' C offset with
  | .falsified => done true
  | .satisfied => done false
  | .unit _ τ' => ok τ'
  | .multipleUnassignedLiterals => done false

def step3 (τ : PPA) (L : List IClause) (offset : Nat) : ResultT Bool PPA :=
  L.foldlM (step3UP offset) τ

def step4 (σ : PS) (w : List (IVar × ILit)) : PS := (σ.reset).setVars w

def step5setup (σ : PS) (τ β : PPA) (C : IClause) : ResultT (PPA × PPA) (PPA × PPA × Bool) :=
  C.foldlM (init := ⟨τ, β, false⟩) (fun ⟨τ', β', b⟩ lit =>
    match σ.litValue lit with
    | .tr => done (τ', β')
    | .fls => ok (τ', β', true)
    | .lit l =>
      match β'.litValue? l with
      | some true => ok (τ', β', b)
      | some false => done (τ', β')
      | none =>
        match τ'.litValue? l with
        | some true => done (τ', β')
        | some false => ok ⟨τ', β'.setLit l, b || (lit = l)⟩
        | none => ok (τ'.setLit l, β'.setLit l, b || (lit = l)))

-- σ is the substitution from step 4
-- τ is the partial assignment initialized in step 2
-- β is the tautology PPA that is kept around each step 5, but reset each time
-- C is the candidate RAT clause
-- L is the list of hinted clauses that should lead to contradiction
def step5 (σ : PS) (τ β : PPA) (C : IClause) (L : List IClause) : ResultT (PS × PPA × PPA × Bool) PPA :=
  match step5setup σ τ.bump β.reset C with
  | done (τ', β') => done (σ, τ', β', true)
  | ok (τ', β', false) => done (σ, τ', β', true)
  | ok (τ', β', true) =>
    L.foldlM (init := τ') (fun τ' Cl =>
      match τ'.unitProp Cl with
      | .falsified => done (σ, τ', β', true)
      | .satisfied => done (σ, τ', β', false)
      | .multipleUnassignedLiterals => done (σ, τ', β', false)
      | .unit _ τ'' => ok τ'')

structure SRState where
  τ : PPA       -- α, or the partial assignment that is set to C each line and extended
  β : PPA       -- A helper data structure to check for tautology in (C∣σ)
  σ : PS        -- The substitution witness

inductive SRError
| malformedLine : String → SRError
| malformedAtom : String → SRError
| outOfBoundsId : Nat → SRError
| outOfBoundsLit : Nat → SRError
| idNotMonotonic : Nat → SRError
| doubleDeletion : Nat → SRError
| err : String → SRError

-- TODO: "Macro"-like functions for spot-modifying state?
-- TODO: Update CNF parsing logic to be more "monadic"
abbrev SRStateT := StateT SRState
abbrev SRCheckerM := SRStateT <| ResultT Bool


-- LineM (α) := SRState → ResultT (Bool × SRState) (α × SRState)
abbrev LineM := SRStateT <| ResultT (Bool × SRState)
abbrev ProofM := SRStateT <| ResultT Bool

--abbrev ereturn {β : Type u} (x : Bool) : ResultT (Bool × SRState) β := do done (x, ← get)

-- When we process the unit propagation hints, we can succeed on the line, or fail
-- If we get (done false), then we exit the proof checking at top level
-- If we get (done true), then the clause checks out, and we can skip the line
-- If we get (ok _), then we continue to RAT hints
def UPHintsToProof (m : LineM Unit) : ProofM Unit := do
  fun s =>
  match m s with
  | ok ⟨_, σ⟩ => ok ⟨(), σ⟩
  | done ⟨true, σ⟩ => ok ⟨(), σ⟩
  | done ⟨false, _⟩ => done false

-- When checking the RAT hints, we want to end each block having derived contradiction.
-- If we derive contradiction, then we should get back (done true).
-- If we get (done false), some RAT hint failed, so we forward that result.
-- If we get (done true), we derived contradiction. We switch to (ok _) to keep folding.
-- If we get (ok _), then we didn't derive contradiction, so we fail.
def RATBlock {α : Type _} (m : LineM α) : ProofM Unit := do
  fun s =>
  match m s with
  | ok _ => done false
  | done ⟨true, σ⟩ => ok ⟨(), σ⟩
  | done ⟨false, _⟩ => done false

-- At the very end of checking every line, we convert a LineM monad into a ProofM monad.
-- If we get (done false), then the proof didn't check at some point, and we forward that result.
-- If we get (done true), then we successfully validated the proof line containing the empty clause.
      -- Forward along the updated state to keep folding.
-- If we get (ok _), then every line checked, but we didn't find the empty clause. So we fail.
def LineToProof {α : Type _} (m : LineM α) : ProofM Unit := do
  fun s =>
  match m s with
  | ok ⟨_, _⟩ => done false
  | done ⟨true, σ⟩ => ok ⟨(), σ⟩
  | done ⟨false, _⟩ => done false

-- Build τ from candidate redundant clause C. Resets from previous line.
def assumeNegatedClause (C : IClause) (offset : Nat) : SRStateT Id Unit :=
  modify (fun st => { st with τ := st.τ.reset.setNegatedClauseFor C offset })

-- Perform unit propagation with τ on given clause. Expects contradiction or unit
def applyUPHint (offset : Nat) (C : IClause) : LineM Unit := do
  match (← get).τ.unitProp' C offset with
  | .falsified => done (true, ← get)      -- Cayden TODO: How to have function/macro so don't call (← get)?
  | .satisfied => done (false, ← get)
  | .unit _ τ' => modify (fun st => { st with τ := τ' })
  | .multipleUnassignedLiterals => done (false, ← get)


-- Cayden TODO: Figure out how can be made without | done b => done b
-- Try to derive contradiction through unit propagation hints.
-- Early exit with (done true) will get handled at top-level when checking the line
-- Early exit with (done false) causes the whole proof to stop
def applyUPHints (L : List IClause) (offset : Nat) : LineM Unit := do
  match L.foldlM (step3UP offset) (init := (← get).τ) with
  | ok τ' => modify (fun st => { st with τ := τ' })
  | done b => done (b, ← get)


-- An alternate definition that modifies each time rather than folding τ along
-- It does have a Unit as the accumulator...
-- Check which version is faster later
def applyUPHints' (L : List IClause) (offset : Nat) : LineM Unit :=
  L.foldlM (fun _ => applyUPHint offset) (init := ())

-- Set the witness substitution σ from the provided mapping, resetting σ first
def assumeWitness (w : List (IVar × ILit)) : SRStateT Id Unit :=
  modify (fun st => { st with σ := st.σ.setVars w })

-- Reduce C under σ, and then check for tautologies (via β) and evaluate under τ
-- If a literal is unassigned by τ, add it to τ for the RAT steps
-- If a literal evaluates to ⊤ under either σ or τ, the clause can be skipped
def reduceRATClause (C : IClause) : LineM Bool := do
  modify (fun st => { st with
    τ := st.τ.bump
    β := st.β.reset })
  C.foldlM (init := false) (fun b lit => do
    match (← get).σ.litValue lit with
    | .tr => done (true, ← get)
    | .fls => return true             -- Cayden TODO/Q: Why 'return' here?
    | .lit l =>
      match (← get).β.litValue? l with
      | some true => return b
      | some false => done (true, ← get)
      | none =>
        match (← get).τ.litValue? l with
        | some true => done (true, ← get)
        | some false =>
          modify (fun st => { st with β := st.β.setLit l })
          return (b || (lit = l))
        | none =>
          modify (fun st => { st with
            τ := st.τ.setLit l
            β := st.β.setLit l })
          return (b || (lit = l)))

-- σ is the substitution witness
-- τ is the partial assignment (negation of C)
-- β is the tautology PPA that is kept around each step 5, but reset each time
-- C is the candidate RAT clause
-- L is the list of hinted clauses that should lead to contradiction
-- Checks a pair of a RAT clause and a list of clause hints
def applyRATHint (C : IClause) (L : List IClause) : LineM Unit := do
  match ← reduceRATClause C with
  -- The witness σ doesn't reduce C, so we can skip the clause
  | false => done (true, ← get)
  -- The witness σ does reduce C
  | true =>
    -- Evaluate RAT hints with C loaded into the state
    L.foldlM (init := ()) (fun _ Cl => do
      match (← get).τ.unitProp Cl with
      -- Derived unit prop contradiction
      | .falsified => done (true, ← get)
      -- During unit prop, we should never find a hinted clause that is satisfied or not unit/contra
      | .satisfied => done (false, ← get)
      | .multipleUnassignedLiterals => done (false, ← get)
      -- If we find unit, extend the partial assignment
      | .unit _ τ' => modify (fun st => { st with τ := τ' }))

def McheckLine (l : SRLine) : ProofM Unit := do
  match l with
  | ⟨C, w, L, R⟩ =>
    let offset := R.length
    let _ := assumeNegatedClause C offset
    -- If we derive contradiction through UP hints and we exit early through monad,
    -- then we are done with the line
    let _ ← UPHintsToProof (applyUPHints' L offset)--
    -- Now we set up the witness
    let _ := assumeWitness w
    -- Now check all RAT hints, holding into the ProofM monad via ExpectDoneTrue
    let _ ← R.foldlM (init := ()) (fun _ ⟨Cl, H⟩ => RATBlock (applyRATHint Cl H))
    if C = #[] then done true else return

def McheckLines (lines : List SRLine) : Bool := --SRCheckerM Unit :=
  let state : SRState := {
    τ := PPA.new 100
    β := PPA.new 100
    σ := PS.new 100
  }

  match ((lines.foldlM (init := ()) (fun _ line => McheckLine line)) : ProofM Unit) |>.run state with
  -- If we end up with "okay", then we never validated the empty clause, so the proof didn't check
  | ok _ => false
  -- If we exited early with "true", then we validated the empty clause, so the proof checked out
  | done true => true
  -- If we exited early with "false", then there was a problem somewhere in the proof, so it didn't check
  | done false => false

theorem Mchecklines_correct (lines : List SRLine) :
  McheckLines lines = true →

/-

Overall: returns Bool

for each line:      (has type σ → ResultT Bool Unit, can drop state.
                     But since ignore "ok" case, could have SRCheckerM Unit := σ → ResultT Bool (Unit × σ))
  check line        (has type SRCheckerM Unit := σ → ResultT Bool (Unit × σ))
    step 2: set τ   (has type SRStateT Id Unit := σ → (Unit × σ))  (because can't fail)
    step 3: unit prop hints
                    (has type SRCheckerM Unit := σ → ResultT (Bool × σ) (Unit × σ))
                    (Can fail early (done false), but can't succeed early (except for the line))

-/

#exit

/-! # Unit propagation across many clauses -/

/-
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

-/

-- Cayden TODO: better name needed
-- Return true if contradiction reached. Otherwise, false
abbrev LineBox := ResultT Bool PPA

def toPF (F : PropFun IVar) (C : IClause) : PropFun IVar := F ⊓ C.toPropFun

@[simp] theorem toPF_top (C : IClause) : toPF ⊤ C = C.toPropFun := by
  rw [toPF, top_inf_eq]

def LtoPF (L : List IClause) : PropFun IVar := L.foldl toPF ⊤
def AtoPF (A : Array IClause) : PropFun IVar := A.foldl toPF ⊤

@[simp] theorem AtoPF_eq_LtoPF (A : Array IClause) : AtoPF A = LtoPF A.data :=
  Array.foldl_eq_foldl_data _ _ _

@[simp] theorem LtoPF_nil : LtoPF ([] : List IClause) = ⊤ := rfl

-- TODO: Make into a single simp?
theorem LtoPF_init (τ : PropFun IVar) (L : List IClause) :
    L.foldl toPF τ = τ ⊓ LtoPF L := by
  induction' L with C CS ih generalizing τ
  · simp
  · simp [ih]
    conv => rhs; rw [LtoPF]
    rw [List.foldl_cons, ih]
    simp [toPF, inf_assoc]

@[simp] theorem LtoPF_cons (C : IClause) (L : List IClause) :
    LtoPF (C :: L) = C.toPropFun ⊓ LtoPF L := by
  simp [LtoPF]
  rw [LtoPF_init, LtoPF]

def applyUPHint (τ : PPA) (C : IClause) : LineBox :=
  match τ.unitProp C with
  | .falsified => done true
  | .satisfied => done false
  | .unit _ τ' => ok τ'
  | .multipleUnassignedLiterals => done false

def AfoldUPs (τ : PPA) (A : Array IClause) := A.foldlM applyUPHint τ
def LfoldUPs (τ : PPA) (L : List IClause) := L.foldlM applyUPHint τ

@[simp] theorem Afold_eq_Lfold (τ : PPA) (A : Array IClause) : AfoldUPs τ A = LfoldUPs τ A.data :=
  Array.foldlM_eq_foldlM_data _ _ _

@[simp] theorem LfoldUPs_nil (τ : PPA) : LfoldUPs τ ([] : List IClause) = ok τ := rfl

theorem unit_of_LfoldUPs_cons_ok {τ τ' : PPA} {C : IClause} {L : List IClause} :
    LfoldUPs τ (C :: L) = ok τ' → ∃ (l : ILit) (τ'' : PPA), τ.unitProp C = unit l τ'' := by
  intro h
  rw [LfoldUPs, List.foldlM_cons, applyUPHint] at h
  cases hτ : τ.unitProp C <;> simp [hτ] at h <;> try contradiction
  exact ⟨_, _, rfl⟩

theorem LfoldUPs_cons_of_falsified {τ : PPA} {C : IClause} {L : List IClause} :
    τ.unitProp C = .falsified → LfoldUPs τ (C :: L) = done true := by
  intro h; simp [LfoldUPs, List.foldlM_cons, applyUPHint, h]; rfl

theorem LfoldUPs_cons_of_unit {l : ILit} {τ τ' : PPA} {C : IClause} {L : List IClause} :
    τ.unitProp C = unit l τ' → LfoldUPs τ (C :: L) = LfoldUPs τ' L := by
  intro h; simp [LfoldUPs, List.foldlM_cons, applyUPHint, h]; rfl

theorem LfoldUPs_ok {τ τ' : PPA} {L : List IClause} :
    LfoldUPs τ L = ok τ' → (LtoPF L) ⊓ τ ≤ τ' := by
  induction' L with C CS ih generalizing τ
  · simp; rintro rfl; exact Eq.ge rfl
  · intro h
    rw [LtoPF_cons, inf_comm, ← inf_assoc, inf_comm]
    rcases unit_of_LfoldUPs_cons_ok h with ⟨l, σ, hτ⟩
    rw [LfoldUPs_cons_of_unit hτ] at h
    apply le_trans _ (ih h)
    have := (extended_of_UP_unit hτ).1
    rw [inf_comm] at this
    exact inf_le_inf_left _ this

theorem LfoldUPs_true {τ : PPA} {L : List IClause} :
    LfoldUPs τ L = done true → LtoPF L ⊓ τ ≤ ⊥ := by
  induction' L with C CS ih generalizing τ
  · simp
  · intro h
    rw [LfoldUPs, List.foldlM_cons, applyUPHint] at h
    split at h <;> try injection h <;> try contradiction
    · rename unitProp τ C = falsified => heq
      rw [LtoPF_cons, inf_comm, ← inf_assoc]
      exact le_trans inf_le_left (contradiction_of_UP_falsified heq)
    · rename ILit => l
      rename PPA => τ'
      rename unitProp τ C = unit _ _ => heq
      have := (extended_of_UP_unit heq).1
      rw [inf_comm] at this
      rw [LtoPF_cons, inf_comm, ← inf_assoc, inf_comm]
      apply le_trans (inf_le_inf_left (LtoPF CS) this)
      apply ih
      rw [← h]
      rfl

theorem AfoldUPs_ok {τ τ' : PPA} {A : Array IClause} :
    AfoldUPs τ A = ok τ' → AtoPF A ⊓ τ ≤ τ' := by
  rw [Afold_eq_Lfold, AtoPF_eq_LtoPF]; exact LfoldUPs_ok

theorem AfoldUPs_true {τ : PPA} {A : Array IClause} :
    AfoldUPs τ A = done true → AtoPF A ⊓ τ ≤ ⊥ := by
  rw [Afold_eq_Lfold, AtoPF_eq_LtoPF]; exact LfoldUPs_true

abbrev RATBox := ResultT Bool PPA

def RATLine (τ : PPA) (R : List (List IClause)) : RATBox :=


end SR
