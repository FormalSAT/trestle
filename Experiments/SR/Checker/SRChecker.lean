/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: Cayden Codel, Wojciech Nawrocki, James Gallicchio
-/

import Trestle.Data.ICnf.Defs
import Experiments.SR.Data.PPA.Defs
import Experiments.SR.Data.PS.Defs
import Experiments.SR.Data.RangeArray
import Experiments.SR.Parsing

/-!

  An LSR proof checker.

  Uses `RangeArray`s to efficiently implement CNF formulas with deletion.

-/

namespace Trestle

namespace RangeArray

/-

  We now add API-breaking versions of unit propagation, reduction,
  and assumption functions (see `PPA` and `PS`) on `RangeArray`s
  so the code goes fast.

-/

/--
  Assumes the negation of the candidate (uncommitted) clause.

  Returns an error if the clause is a tautology.
  Returns the updated `PPA` otherwise.
-/
def assumeNegatedCandidateFor (F : RangeArray ILit) (τ : PPA) (bumps : Nat) : Except PPA PPA :=
  let s := F.dsize
  let e := F.data.size
  let rec loop (i : Nat) (τ : PPA) : Except PPA PPA :=
    if hi : i < e then
      let l := F.get i hi
      let lv := τ.litValue?_8 l
      if lv = PPA.UNASSIGNED then
        loop (i + 1) (τ.setLitFor (-l) bumps)
      else if lv = PPA.FALSE then
        loop (i + 1) τ
       else -- lv = PPA.TRUE
        .error τ
    else  -- i ≥ e
      .ok τ
  termination_by F.data.size - i
  loop s τ


/--
  Assumes the negation of the RAT clause at the specified `index` for one bump.
  Negation occurs under the substitution `σ`.

  Returns an error if `C` is satisfied by either `σ`, or `τ` under `σ`.
-/
def assumeRATClause (F : RangeArray ILit) (idx : Nat) (h_idx : idx ≤ F.size)
      (σ : PS) (τ : PPA) : Except PPA PPA :=
  /- Instead of using `rsize` and substracting off `index i`,
     we calculate it directly. For whatever reason, this is faster.
     The performance improvement is about 8%. -/
  let s := F.index! idx
  let e := if idx = F.size then F.data.size else F.index! (idx + 1)

  let rec loop (i : Nat) (τ : PPA) : Except PPA PPA :=
    if hi : i < e then
      -- Hypothesis needed for termination argument
      have : e - (i + 1) < e - i := by omega

      let lit := F.get i (by
        simp only [e] at hi
        have := index!_le_dsize F (idx + 1)
        have := F.h_size

        by_cases h_eq : idx = F.size
        · simp [h_eq] at hi
          exact hi
        · simp [h_eq] at hi
          replace h_idx := Nat.lt_of_le_of_ne h_idx h_eq
          simp [index!] at hi
          split at hi <;> rename_i hi'
          · have := index!_le_dsize F (idx + 1)
            rw [index!] at this
            simp [hi'] at this
            omega
          · omega
      )

      let sv := σ.litValue_Nat lit
      if sv = PS.MAPPED_TRUE then
        .error τ
      else if sv = PS.MAPPED_FALSE then
        loop (i + 1) τ
      else -- sv = PS.UNASSIGNED
        let sLit := PS.ILitFromMappedNat sv
        let lv := τ.litValue?_8 sLit
        if lv = PPA.UNASSIGNED then
          loop (i + 1) (τ.setLit (-sLit))
        else if lv = PPA.FALSE then
          loop (i + 1) τ
        else
          .error τ
    else -- i ≥ e
      .ok τ
  termination_by (if idx = F.size then F.data.size else F.index! (idx + 1)) - i
  loop s τ

def unitProp (τ : PPA) (F : RangeArray ILit) (hint : Nat) (h_hint : hint < F.size) : PPA.UPResult :=
  /- Instead of using `rsize` and substracting off `index idx`,
     we calculate it directly. For whatever reason, this is faster.
     The performance improvement is about 8%. -/
  let s := F.index hint h_hint
  let e := F.index! (hint + 1)

  -- We store the unit in `unit`. If it's unmapped, it is `0`.
  let rec loop (i : Nat) (unit : Int) : PPA.UPResult :=
    if h : i < e then
      have : e - (i + 1) < e - i := by omega

      let ⟨lit, h_lit⟩ := F.get i (by
        simp [e] at h
        have := index!_le_dsize F (hint + 1)
        have := F.h_size
        omega
      )

      let lv := τ.litValue?_8 ⟨lit, h_lit⟩
      if lv = PPA.UNASSIGNED then
        if unit = 0 then
          loop (i + 1) lit
        else
          if unit = lit then
            loop (i + 1) unit
          else
            .multipleUnassignedLiterals
      else if lv = PPA.FALSE then
        loop (i + 1) unit
      else -- lv = PPA.TRUE
        .satisfied
    else -- i ≥ e
      if h_unit : unit = 0 then
        .falsified
      else
        .unit ⟨unit, by omega⟩
  termination_by (F.index! (hint + 1)) - i
  loop s 0


inductive HintResult where
  | unit
  | contra
  | err
deriving DecidableEq, Inhabited

def applyUPHint (F : RangeArray ILit) (bumps : Nat) (τ : PPA) (hint : Nat) : PPA × HintResult :=
  if h_hint : hint < F.size then
    if !F.isDeleted hint h_hint then
      match unitProp τ F hint h_hint with
      | .falsified => ⟨τ, .contra⟩
      | .satisfied => ⟨τ, .err⟩
      | .multipleUnassignedLiterals => ⟨τ, .err⟩
      | .unit l => (τ.setLitFor l bumps, .unit)
    else
      ⟨τ, .err⟩
  else
    ⟨τ, .err⟩

def applyUPHints (F : RangeArray ILit) (offset : Nat) (τ : PPA) (hints : Array Nat) : PPA × HintResult :=
  let rec loop (i : Nat) (τ : PPA) : PPA × HintResult :=
    if hi : i < hints.size then
      match applyUPHint F offset τ (hints[i]'hi) with
      | (τ, .unit) => loop (i + 1) τ
      | (τ, .contra) => (τ, .contra)
      | (τ, .err) => (τ, .err)
    else (τ, .unit)
  loop 0 τ

/--
  Reduction is the computational bottleneck for SR proof checking.
  The API-breaking version calculates the result of `σ.reduce` directly
  from the arrays, rather than boxing the result into an inductive datatype.
  The time savings are ~30%.
-/
def reduce (F : RangeArray ILit) (idx : Nat) (h_idx : idx ≤ F.size) (σ : PS) : PS.ReductionResult :=
  /- Instead of calculating `rsize` and then subtracting off `s`,
     we compute the ending manually as the start of the next index.
     The performance improvement is about ~8-10%.  -/
  let s := F.index! idx
  let e := if idx = F.size then F.data.size else F.index! (idx + 1)
  let ⟨gens, mappings, generation, _, sizes_eq, _⟩ := σ

  let rec loop (i : Nat) (reduced? : Bool) : PS.ReductionResult :=
    if hi : i < e then
      have : e - (i + 1) < e - i := by omega

      let lit := F.get i (by
        simp [e] at hi
        have := index!_le_dsize F (idx + 1)
        have := F.h_size
        by_cases h_eq : idx = F.size
        · simp [h_eq] at hi
          exact hi
        · simp [h_eq] at hi
          replace h_idx := Nat.lt_of_le_of_ne h_idx h_eq
          simp [index!] at hi
          split at hi <;> rename_i hi'
          · have := index!_le_dsize F (idx + 1)
            rw [index!] at this
            simp [hi'] at this
            omega
          · omega
      )

      if hlit : lit.index < gens.size then
        let gen := gens[lit.index]'hlit
        if gen ≥ generation then
          let n := mappings[lit.index]'(by rw [sizes_eq] at hlit; exact hlit)
          match n with
          | 0 =>
            if LitVar.polarity lit then .satisfied
            else loop (i + 1) true
          | 1 =>
            if LitVar.polarity lit then loop (i + 1) true
            else .satisfied
          | n =>
            -- Since we looked at `mappings` for `lit.index = var.index`,
            -- we compare the underlying mapping to the mapping for `lit`'s var.
            let n' := PS.IVarToMappedNat (LitVar.toVar lit)
            if n' = n then
              loop (i + 1) reduced?
            else
              loop (i + 1) true
        else
          loop (i + 1) reduced?
      else loop (i + 1) reduced?
    else -- i ≥ e
      if reduced? then .reduced else .notReduced
  termination_by (if idx = F.size then F.data.size else F.index! (idx + 1)) - i
  loop s false

end RangeArray


namespace SR

open Parsing

def scanRATHintIndexes (clauseId : Nat) (ratHintIndexes : Array Nat) : Option (Fin ratHintIndexes.size) :=
  let rec loop (i : Nat) : Option (Fin ratHintIndexes.size) :=
    if h : i < ratHintIndexes.size then
      if ratHintIndexes[i]'h = clauseId then some ⟨i, h⟩
      else loop (i + 1)
    else none
  loop 0

-- Finds the index for the (RAT clause ID + RAT hints) that matches the clauseId
def findRATHintIndex (ratIndex clauseId : Nat) (ratHintIndexes : Array Nat) : Option (Fin ratHintIndexes.size) :=
  -- If the RAT hints are sorted, then check the one under our "cached pointer" first
  if h_index : ratIndex < ratHintIndexes.size then
    let ratClauseIndex := ratHintIndexes[ratIndex]'h_index
    if ratClauseIndex = clauseId then
      some ⟨ratIndex, h_index⟩
    else
      scanRATHintIndexes clauseId ratHintIndexes
  else
    scanRATHintIndexes clauseId ratHintIndexes


/-- Set the witness substitution σ from the provided mapping, resetting σ first. -/
def assumeWitness (σ : PS) (tf_lits : Array ILit) (lit_maps : Array ILit) : PS :=
  ((σ.reset.setLits tf_lits).setVars' lit_maps)

structure SRState where
  F : RangeArray ILit
  τ : PPA
  σ : PS

def checkLine : SRState → SRAdditionLine → Except Bool SRState :=
  fun ⟨F, τ, σ⟩ ⟨witnessLits, witnessMaps, upHints, ratHintIndexes, ratHints, ratSizesEq, _⟩ =>
  match RangeArray.assumeNegatedCandidateFor F τ.reset (ratHints.size + 1) with
  | .error _ => .error false
  | .ok τ =>
    -- Evaluate the UP hints, with "# of RAT hints" as the offset
    match F.applyUPHints (ratHints.size + 1) τ upHints with
    | (_, .err) => .error false
    | (τ, .contra) =>
      -- dbg_trace s!"UP contra with {F.size} clauses"
      if F.usize = 0 then .error true  -- If the clause is empty, we have a successful contradiction proof
      else .ok ⟨F.commit, τ, σ⟩

    | (τ, .unit) =>
      -- If the clause is empty, we should have derived UP contradiction by now
      if hu : F.usize = 0 then
        .error false
      else
        have hu' : 0 < F.usize := by omega
        let σ := assumeWitness σ witnessLits witnessMaps
        -- dbg_trace s!"σ := {σ} {σ.gens}"

        -- Loop through each clause in the formula to check RAT conditions
        -- The Bool is true if the check succeeds on all clauses, false otherwise
        let Fsize := F.size
        let rec loop (i : Nat) (hi_le : i ≤ Fsize) (cachedRatHintIndex bumpCounter : Nat) (τ : PPA) : PPA × Bool :=
          if hi : i < Fsize then
            -- dbg_trace s!"RAT check on clause {i}"
            have : F.indexes.size - (i + 1) < F.indexes.size - i := by
              simp [Fsize, RangeArray.size] at hi
              omega

            have hi' := Nat.succ_le_of_lt hi

            if h_del : F.isDeleted i hi = true then
              loop (i + 1) hi' cachedRatHintIndex bumpCounter τ
            else
              -- First, check how the ith clause is reduced by σ
              match F.reduce i (Nat.le_of_lt hi) σ with
              | .satisfied
              | .notReduced => loop (i + 1) hi' cachedRatHintIndex bumpCounter τ
              | .reduced =>
                -- dbg_trace s!"Clause {i} is reduced under σ: {F.arrGet i}"
                if bumpCounter < ratHints.size then
                  -- Find the corresponding RAT hint
                  match findRATHintIndex cachedRatHintIndex i ratHintIndexes with
                  | none => ⟨τ, false⟩
                  | some ⟨ratIndex, hr⟩ =>
                    -- Assume the negation of the RAT clause
                    match F.assumeRATClause i (Nat.le_of_lt hi) σ τ with
                    | .error τ => loop (i + 1) hi' (ratIndex + 1) (bumpCounter + 1) τ.bump
                    | .ok τ =>
                      match F.applyUPHints 0 τ (ratHints[ratIndex]'(by rw [ratSizesEq] at hr; exact hr)) with
                      | (τ, .err) => ⟨τ, false⟩
                      | (τ, .unit) => ⟨τ, false⟩
                      | (τ, .contra) => loop (i + 1) hi' (ratIndex + 1) (bumpCounter + 1) τ.bump
                else ⟨τ, false⟩
          else
            -- The candidate clause might also be RAT
            match F.reduce F.size (by exact Nat.le_refl F.size) σ with
            | .satisfied => (τ, true)
            | .notReduced => (τ, false) -- Error: If the witness doesn't reduce it, we should just use RUP
            | .reduced =>
              if bumpCounter < ratHints.size then
                -- Find the corresponding RAT hint
                match findRATHintIndex cachedRatHintIndex i ratHintIndexes with
                | none => ⟨τ, false⟩
                | some ⟨ratIndex, hr⟩ =>
                  -- Assume the negation of the RAT clause
                  match F.assumeRATClause i hi_le σ τ with
                  | .error τ => (τ.bump, true)
                  | .ok τ =>
                    match F.applyUPHints 0 τ (ratHints[ratIndex]'(by rw [ratSizesEq] at hr; exact hr)) with
                    | (τ, .err) => ⟨τ, false⟩
                    | (τ, .unit) => ⟨τ, false⟩
                    | (τ, .contra) => (τ.bump, true)
              else ⟨τ, false⟩
        termination_by F.size - i

        match loop 0 (Nat.zero_le _) 0 0 τ with
        | ⟨_, false⟩ => .error false
        | ⟨τ, true⟩ => .ok ⟨F.commit, τ, σ⟩

--@[inline, always_inline]
def consumeDeletionLine (F : RangeArray ILit) (line : SRDeletionLine) : Except Unit (RangeArray ILit) :=
  let clausesSize := line.size
  let rec loop (i : Nat) (F : RangeArray ILit) : Except Unit (RangeArray ILit) :=
    if hi : i < clausesSize then
      let clauseId := line[i]'hi
      if hc : clauseId < F.size then
        if F.isDeleted clauseId hc then
          .error ()
        else
          loop (i + 1) (F.delete clauseId hc)
      else .error ()
    else .ok F
  termination_by line.size - i
  loop 0 F

end SR

end Trestle
