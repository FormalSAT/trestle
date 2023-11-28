import LeanSAT.Data.Cnf
import LeanSAT.Data.ICnf
import LeanSAT.AuxDefs
import LeanSAT.Upstream.ToStd
import Mathlib.Data.Nat.Basic

open LeanSAT LeanSAT.Model Nat

/-- A partial assignment of truth values to propositional variables.

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
  generation : { g : Nat // g > 0 }
  /-- The maximum absolute value of any entry in `assignments`. -/
  maxGen : Nat

namespace PPA
  open LitVar

@[reducible] def size (τ : PPA) : Nat := τ.assignment.size

  /-- The value of the given literal in the current assignment, if assigned.
  Otherwise `none`. -/
def litValue? (τ : PPA) (l : ILit) : Option Bool :=
  match τ.assignment.get? ((toVar l).val - 1) with
  | none => none
  | some n =>
    if τ.generation.val ≤ n.natAbs then
      some <| xor (n < 0) (polarity l)
    else
      none

  -- Cayden: Alternative definition that uses a let, not a match:
  --let v := τ.assignment.getD ((toVar l).val - 1) 0
  --if τ.generation ≤ v.natAbs then
  --  some <| xor (v < 0) (polarity l)
  --else none

def varValue? (τ : PPA) (v : IVar) : Option Bool :=
  τ.litValue? (mkPos v)

-- Cayden TODO: There's a far more elegant proof here
theorem litValue?_negate (τ : PPA) (l : ILit) :
    τ.litValue? l = Option.map Bool.not (τ.litValue? (-l)) := by
  unfold litValue?
  match hlit : Array.get? τ.assignment ((toVar l).val - 1) with
  | none => simp [hlit, -Array.get?_eq_getElem?]
  | some n =>
    simp [hlit, -Array.get?_eq_getElem?]
    by_cases hτ : τ.generation.val ≤ Int.natAbs n
    <;> cases polarity l <;> by_cases hn : (n < 0) <;> simp [hτ, hn]

theorem litValue?_eq_varValue?_none {τ : PPA} {l : ILit} :
    τ.litValue? l = none → τ.varValue? (toVar l) = none := by
  simp only [litValue?, varValue?]
  cases hlit : Array.get? τ.assignment ((toVar l).val - 1)
  <;> simp [hlit, -Array.get?_eq_getElem?]

theorem litValue?_eq_varValue?_some {τ : PPA} {l : ILit} {b : Bool} :
    τ.litValue? l = some b → τ.varValue? (toVar l) = xor (!b) (polarity l) := by
  simp only [litValue?, varValue?]
  cases hlit : Array.get? τ.assignment ((toVar l).val - 1) with
  | none => simp [hlit, -Array.get?_eq_getElem?]
  | some n =>
    simp [hlit, -Array.get?_eq_getElem?]
    by_cases hτ : τ.generation.val ≤ Int.natAbs n
    <;> cases polarity l <;> by_cases hn : (n < 0) <;> cases b <;> simp [hτ, hn]

theorem lt_size_of_litValue?_eq_some {τ : PPA} {l : ILit} {b : Bool} :
    τ.litValue? l = some b → ((toVar l).val - 1) < τ.size := by
  sorry
  done

def toPropFun_fun (τ : PPA) : PropFun IVar → Fin τ.size → ℤ → PropFun IVar :=
  fun acc idx a => acc ⊓
    (if τ.generation ≤ a then .var ⟨idx.val + 1, succ_pos _⟩
     else (.var ⟨idx.val + 1, succ_pos _⟩)ᶜ)

def toPropFun (τ : PPA) : PropFun IVar :=
  τ.assignment.foldlIdx (init := ⊤) (toPropFun_fun τ)

theorem toPropFun_fun_comm (τ : PPA) :
  ∀ (acc : PropFun IVar) (idx₁ idx₂ : Fin τ.size),
    (toPropFun_fun τ) ((toPropFun_fun τ) acc idx₁ (τ.assignment.get idx₁)) idx₂ (τ.assignment.get idx₂) =
    (toPropFun_fun τ) ((toPropFun_fun τ) acc idx₂ (τ.assignment.get idx₂)) idx₁ (τ.assignment.get idx₁) := by
  intro acc i j
  simp only [toPropFun_fun, Array.get_eq_getElem, ge_iff_le, le_inf_iff, inf_right_comm]

instance : ToString PPA where
  toString τ := String.intercalate " ∧ "
    (τ.assignment.foldl (init := []) (f := fun acc a => s!"{a}" :: acc))

end PPA

-- ??
--structure PPA.WF (ppa : PPA) where
  -- hGen: 0 < generation
  -- hMaxVal : ∀ x ∈ assignment, x.natAbs ≤ maxVal

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

  /-- Reset the assignment to an empty one. -/
  def reset (τ : PPA) : PPA :=
    { τ with generation := ⟨τ.maxGen + 1, Nat.succ_pos _⟩ }

  /-- Clear all temporary assignments at the current generation. -/
  def bump (τ : PPA) : PPA :=
    { τ with generation := ⟨τ.generation + 1, Nat.succ_pos _⟩ }

  /-- Set the given literal to `true` for the current generation
  in the assignment. -/
  def setLit (τ : PPA) (l : ILit) : PPA :=
    let v : Int := if polarity l then τ.generation else -τ.generation
    { τ with
      assignment := τ.assignment.setF ((toVar l).val - 1) v 0
      maxGen := Nat.max τ.maxGen τ.generation }

  /-- Set the given literal to `true` for all generations until `gen`. -/
  def setLitUntil (τ : PPA) (l : ILit) (gen : Nat) : PPA :=
    let v : Int := if polarity l then gen else -gen
    { τ with
      assignment := τ.assignment.setF ((toVar l).val - 1) v 0
      maxGen := Nat.max τ.maxGen gen }

  /-- Check if the given clause is a tautology.
  The current partial assignment is ignored,
  and the assignment afterwards is unspecified. -/
  def checkTauto (τ : PPA) (C : IClause) : PPA × Bool := Id.run do
    let mut τ := τ.reset
    for l in C do
      if let some false := τ.litValue? l then
        return (τ, true)
      τ := τ.setLit l
    return (τ, false)

  /-- Set `l ↦ ⊥` for each `l ∈ C` and leave the rest of the assignment untouched.
  If the current assignment contains literals appearing in `C`, they will be overwritten. -/
  -- NB: might be easier to verify if we make this always bump p.generation; it's only used before UP anyway
  -- left without bump but might result in harder theorem
  def setNegatedClause (τ : PPA) (C : IClause) : PPA :=
    C.foldl (init := τ) (fun τ l => τ.setLit (-l))

  def setNegatedClauseUntil (τ : PPA) (C : IClause) (gen : Nat) : PPA :=
    C.foldl (init := τ) (fun τ l => τ.setLitUntil (-l) gen)

  /-! # Lemmas -/

  theorem setLit_pos (τ : PPA) (l : ILit) : (τ.setLit l).litValue? l = some true := by
    rw [litValue?, setLit]
    cases polarity l
    <;> simp [Array.getElem?_setF]
    exact τ.generation.property

  theorem setLit_neg (τ : PPA) {l l' : ILit} :
      (toVar l) ≠ (toVar l') → (τ.setLit l).litValue? l' = τ.litValue? l' := by
    intro hl
    simp only [litValue?, setLit]
    have : (toVar l).val - 1 ≠ (toVar l').val - 1 := by
      rcases ILit.exists_succ_toVar l with ⟨n₁, hn₁⟩
      rcases ILit.exists_succ_toVar l' with ⟨n₂, hn₂⟩
      rw [hn₁, hn₂, Nat.add_sub_cancel, Nat.add_sub_cancel]
      -- TODO: How to use ≠ instead of ¬( = )?
      have := mt Subtype.ext hl
      have : ↑(toVar l) ≠ (toVar l').val := this
      simp [hn₁, hn₂] at this
      exact this
    cases polarity l
    <;> simp [Array.getElem?_setF' _ _ _ this]

  theorem setLit_varValue_pos (τ : PPA) {l : ILit} {v : IVar} :
      v = (toVar l) → (τ.setLit l).varValue? v = some (polarity l) := by
    intro hv
    rw [varValue?]
    have h_setLit := setLit_pos τ l
    cases hpol : polarity l
    · have : (mkPos v) = -l := by rw [hv]; ext <;> simp [hpol]
      rw [this]
      rw [litValue?_negate] at h_setLit
      match hlit : litValue? (setLit τ l) (-l) with
      | none => simp [hlit] at h_setLit
      | some b =>
        cases b with
        | true => simp [hlit] at h_setLit
        | false => rfl
    · have : (mkPos v) = l := by rw [hv]; ext <;> simp [hpol]
      rw [this]
      exact h_setLit

  theorem setLit_varValue_neg (τ : PPA) {l : ILit} {v : IVar} :
      (toVar l) ≠ v → (τ.setLit l).varValue? v = τ.varValue? v := by
    intro hv
    -- TODO: Why all the instances?
    rw [← @LawfulLitVar.toVar_mkPos ILit IVar LeanSAT.instLitVarILitIVar
      LeanSAT.instLawfulLitVarILitIVarInstLitVarILitIVar v] at hv
    exact setLit_neg τ hv

  #check PropFun.entails

  theorem satisfies_iff {τ : PPA} {σ : PropAssignment IVar} :
      σ ⊨ τ.toPropFun ↔ ∀ v b, τ.varValue? v = some b → σ v = b := by
    constructor
    · intro hσ v b hv
      rw [toPropFun] at hσ
      have := Array.foldlIdx_of_comm τ.assignment (toPropFun_fun τ) ⊤ (toPropFun_fun_comm τ)
      --have ⟨a, ha⟩ := ⊤.fold_of_mapsTo_of_comm
      --rw [toPropFun] at hσ

      --rw [satisfies_iff] at hσ
      sorry
      done
    · sorry

    /-
    where
  mp := fun h => by
    intro x p? hFind
    have ⟨φ, hφ⟩ := τ.fold_of_mapsTo_of_comm
      (init := ⊤) (f := fun acc x v => acc ⊓ if v then PropTerm.var x else (PropTerm.var x)ᶜ)
      hFind ?comm
    case comm =>
      intros
      dsimp
      ac_rfl
    rw [toPropTerm, hφ] at h
    aesop

  mpr := fun h => by
    apply HashMap.foldRecOn (hInit := satisfies_tr)
    intro φ x p hφ hFind
    rw [satisfies_conj]
    refine ⟨hφ, ?_⟩
    have := h _ _ hFind
    split <;> simp [*]
    -/

  theorem satisfies_iff' {τ : PPA} {σ : PropAssignment IVar} :
      σ ⊨ τ.toPropFun ↔ ∀ l b, τ.litValue? l = some b → σ (toVar l) = xor (!b) (polarity l) := by
    constructor
    · intro hσ l b hl
      have := satisfies_iff.mp hσ (toVar l) (xor (!b) (polarity l))
      cases b
      · simp at this
        simp
        apply this
        unfold varValue?
        sorry
      · sorry
    · sorry
    done

  /-! # Unit propagation -/

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
