/-

An LSR proof checker, with proof of correctness.

Uses `RangeArray`s to efficiently implement CNF formulas with deletion.

Author: Cayden Codel
Carnegie Mellon University

-/

import Experiments.ProofChecking.RangeArray
import Experiments.ProofChecking.RangeArrayThm
import Experiments.ProofChecking.Parsing.Defs
import Experiments.ProofChecking.PPA
import Experiments.ProofChecking.PS

import LeanColls
open LeanColls

open RangeArray
open LeanSAT LeanSAT.Model
open PPA PS
open Except
open PropFun
open Parsing

namespace RangeArray

-- Returns the updated PPA. Returns `error` if `C` is a tautology, `ok` if not
def uAssumeNegatedForM (F : RangeArray ILit) (τ : PPA) (bumps : Nat) : Except PPA PPA :=
  let usize := F.usize
  let rec loop (i : Nat) (τ : PPA) : Except PPA PPA :=
    if h : i < usize then
      let l := F.ugetFin ⟨i, h⟩
      match τ.litValue? l with
      | none       => loop (i + 1) (τ.setLitFor (-l) bumps)
      | some false => loop (i + 1) τ
      | some true  => .error τ
    else
      .ok τ
  termination_by F.usize - i
  loop 0 τ

/-- Assumes into `τ` the negation of RAT clause `C` under the substitution `σ` for one "bump."
    Errors if `C` is satisfied by either `σ` or `τ` under `σ`. -/
def assumeRATClauseM (F : RangeArray ILit) (index : Fin F.size) (σ : PS) (τ : PPA) : Except PPA PPA :=
  let rsize := F.rsizeFin index
  let rec loop (i : Nat) (τ : PPA) : Except PPA PPA :=
    if h : i < rsize then
      let lit := F.ogetFin index ⟨i, h⟩
      match σ.litValue lit with
      | Sum.inr true => error τ       -- (C|σ) is satisfied, so return early to report satisfied
      | Sum.inr false => loop (i + 1) τ         -- Ignore the literal
      | Sum.inl l =>
        match τ.litValue? l with
        | some true => error τ        -- (C|σ)|τ is satisfied, so return early to report satisfied
        | some false => loop (i + 1) τ          -- Its negation is true in τ, so ignore the literal
        | none => loop (i + 1) (τ.setLit (-l))
    else
      ok τ
  termination_by F.rsizeFin index - i
  loop 0 τ


-- A tail-recursive implementation that breaks the API to go faster
-- We prove that these two implementations are equal
def assumeRATClauseDirect (F : RangeArray ILit) (index : Fin F.size) (σ : PS) (τ : PPA) : Except PPA PPA :=
  let s := F.indexFin index
  /- CC: Instead of calculating `rsizeFin` and then subtracting off `s`,
        we compute the ending manually as the start of the next index.
        The performance improvement is about ~8-10%.  -/
  let e :=
    if h_index : index.val + 1 < F.size then
      F.indexFin ⟨index.val + 1, h_index⟩
    else
      F.dsize
  let rec loop (i : Nat) (τ : PPA) : Except PPA PPA :=
    if h : i < e then
      let lit := F.getFin ⟨i, by
        simp only [e, indexFin_eq_index] at h
        split at h
        · have := lt_of_lt_of_le h (F.index_le_dataSize (index.val + 1))
          exact lt_of_lt_of_le this F.h_size
        · exact lt_of_lt_of_le h F.h_size⟩

      match σ.litValue lit with
      | Sum.inr true => error τ
      | Sum.inr false => loop (i + 1) τ
      | Sum.inl l =>
        match τ.litValue? l with
        | some true => error τ
        | some false => loop (i + 1) τ
        | none => loop (i + 1) (τ.setLit (-l))
    else
      ok τ
  termination_by
    (if h_index : index.val + 1 < F.size then
      F.indexFin ⟨index.val + 1, h_index⟩
    else
      F.dsize) - i
  loop s τ

def unitProp (τ : PPA) (F : RangeArray ILit) (hint : Fin F.size) : PPA.UPResult :=
  let rsize := F.rsizeFin hint
  let rec loop (i : Nat) (unit? : Option ILit) : PPA.UPResult :=
    if hi : i < rsize then
      let lit := F.ogetFin hint ⟨i, hi⟩
      match τ.litValue? lit with
      | some true => .satisfied
      | some false => loop (i + 1) unit?
      | none =>
        match unit? with
        | none => loop (i + 1) (some lit)
        | some u =>
          if u = lit then loop (i + 1) unit?
          else .multipleUnassignedLiterals
    else
      match unit? with
      | none => .falsified
      | some l => .unit l
  termination_by F.rsizeFin hint - i
  loop 0 none

--@[inline]
def unitPropDirect (τ : PPA) (F : RangeArray ILit) (hint : Fin F.size) : PPA.UPResult :=
  let s := F.indexFin hint
  /- CC: Instead of calculating `rsizeFin` and then subtracting off `s`,
        we compute the ending manually as the start of the next index.
        The performance improvement is about ~8-10%.  -/
  let e :=
    if h_index : hint + 1 < F.size then
      F.indexFin ⟨hint + 1, h_index⟩
    else
      F.dsize
  let rec loop (i : Nat) (unit? : Option ILit) : PPA.UPResult :=
    if h : i < e then
      let lit := F.getFin ⟨i, by
        simp [e, indexFin_eq_index] at h
        split at h
        · have := lt_of_lt_of_le h (F.index_le_dataSize (hint + 1))
          exact lt_of_lt_of_le this F.h_size
        · exact lt_of_lt_of_le h F.h_size⟩
      match τ.litValue? lit with
      | some true => .satisfied
      | some false => loop (i + 1) unit?
      | none =>
        match unit? with
        | none => loop (i + 1) (some lit)
        | some u =>
          if u = lit then loop (i + 1) unit?
          else .multipleUnassignedLiterals
    else
      match unit? with
      | none => .falsified
      | some l => .unit l
  termination_by
    (if h_index : hint + 1 < F.size then
      F.indexFin ⟨hint + 1, h_index⟩
    else
      F.dsize) - i
  loop s none

inductive HintResult where
  | unit
  | contra
  | err
  deriving DecidableEq, Inhabited

--@[inline]
def applyUPHint (F : RangeArray ILit) (bumps : Nat) (τ : PPA) (hint : Nat) : PPA × HintResult :=
  if h_hint : hint < F.size then
    if !F.isDeletedFin ⟨hint, h_hint⟩ then
      match unitProp τ F ⟨hint, h_hint⟩ with
      | .falsified => ⟨τ, .contra⟩
      | .satisfied => ⟨τ, .err⟩
      | .multipleUnassignedLiterals => ⟨τ, .err⟩
      | .unit l => (τ.setLitFor l bumps, .unit)
    else
      ⟨τ, .err⟩
  else
    ⟨τ, .err⟩

--@[inline]
def applyUPHintDirect (F : RangeArray ILit) (bumps : Nat) (τ : PPA) (hint : Nat) : PPA × HintResult :=
  if h_hint : hint < F.size then
    if !F.isDeletedFin ⟨hint, h_hint⟩ then
      match unitPropDirect τ F ⟨hint, h_hint⟩ with
      | .falsified => ⟨τ, .contra⟩
      | .satisfied => ⟨τ, .err⟩
      | .multipleUnassignedLiterals => ⟨τ, .err⟩
      | .unit l => (τ.setLitFor l bumps, .unit)
    else
      ⟨τ, .err⟩
  else
    ⟨τ, .err⟩

--@[inline, always_inline]
def applyUPHints (F : RangeArray ILit) (offset : Nat) (τ : PPA) (hints : Array Nat) : PPA × HintResult :=
  let rec loop (i : Nat) (τ : PPA) : PPA × HintResult :=
    if hi : i < Size.size hints then
      match applyUPHint F offset τ (Seq.get hints ⟨i, hi⟩) with
      | (τ, .unit) => loop (i + 1) τ
      | (τ, .contra) => (τ, .contra)
      | (τ, .err) => (τ, .err)
    else (τ, .unit)
  termination_by Size.size hints - i
  loop 0 τ

--@[inline, always_inline]
def applyUPHintsDirect (F : RangeArray ILit) (offset : Nat) (τ : PPA) (hints : Array Nat) : PPA × HintResult :=
  let rec loop (i : Nat) (τ : PPA) : PPA × HintResult :=
    if hi : i < Size.size hints then
      match applyUPHintDirect F offset τ (Seq.get hints ⟨i, hi⟩) with
      | (τ, .unit) => loop (i + 1) τ
      | (τ, .contra) => (τ, .contra)
      | (τ, .err) => (τ, .err)
    else (τ, .unit)
  termination_by Size.size hints - i
  loop 0 τ

def reduce (σ : PS) (F : RangeArray ILit) (index : Fin F.size) : ReductionResult :=
  let rsize := F.rsizeFin index
  let rec loop (i : Nat) (reduced? : Bool) : ReductionResult :=
    if hi : i < rsize then
      let lit := F.ogetFin index ⟨i, hi⟩
      match seval' σ lit with
      | .satisfied => .satisfied
      | .reduced => loop (i + 1) true
      | .notReduced => loop (i + 1) reduced?
    else
      if reduced? then .reduced else .notReduced
  termination_by F.rsizeFin index - i
  loop 0 false

/--
Reduction is the computational bottleneck for SR proof checking.
The API-breaking version calculates the result of `σ.reduce` directly
from the arrays, rather than boxing the result into an inductive datatype.
The time savings are ~30%.
-/
def reduceBreak (σ : PS) (F : RangeArray ILit) (index : Fin F.size) : ReductionResult :=
  let s := F.indexFin index
  /- CC: Instead of calculating `rsizeFin` and then subtracting off `s`,
         we compute the ending manually as the start of the next index.
         The performance improvement is about ~8-10%.  -/
  let e :=
    if h_index : index.val + 1 < F.size then
      F.indexFin ⟨index.val + 1, h_index⟩
    else
      F.dsize
  let rec loop (i : Nat) (reduced? : Bool) : ReductionResult :=
    if h : i < e then
      let lit := F.getFin ⟨i, by
        simp [e, indexFin_eq_index] at h
        split at h
        · have := lt_of_lt_of_le h (F.index_le_dataSize (index.val + 1))
          exact lt_of_lt_of_le this F.h_size
        · exact lt_of_lt_of_le h F.h_size⟩
      if hlit : lit.index < σ.gens.size then
        let gen := σ.gens.get ⟨lit.index, hlit⟩
        if gen ≥ σ.generation then
          let n := σ.mappings.get ⟨lit.index, by rw [σ.sizes_eq] at hlit; exact hlit⟩
          match n with
          | 0 =>
            if LitVar.polarity lit then .satisfied
            else loop (i + 1) true
          | 1 =>
            if LitVar.polarity lit then loop (i + 1) true
            else .satisfied
          | n =>
            if PSV.toMapped' lit ≠ n then
              loop (i + 1) true
            else
              loop (i + 1) reduced?
        else loop (i + 1) reduced?
      else loop (i + 1) reduced?
    else
      if reduced? then .reduced else .notReduced
  termination_by
    (if h_index : index.val + 1 < F.size then
      F.indexFin ⟨index.val + 1, h_index⟩
     else
      F.dsize) - i
  loop s false

end RangeArray

namespace SR

-- Scans through the RAT hint clause IDs to find a matching ID
def scanRATHintIndexesM (clauseId : Nat) (ratHintIndexes : Array Nat) : Option (Fin ratHintIndexes.size) :=
  match ratHintIndexes.foldlM (init := 0) (fun counter hint =>
        if hint = clauseId then error counter
        else ok (counter + 1)) with
  | ok _ => none
  | error index =>
    if hi : index < Size.size ratHintIndexes then
      some ⟨index, hi⟩
    else
      none

def scanRATHintIndexes (clauseId : Nat) (ratHintIndexes : Array Nat) : Option (Fin ratHintIndexes.size) :=
  let rec loop (i : Nat) : Option (Fin ratHintIndexes.size) :=
    if h : i < Size.size ratHintIndexes then
      if Seq.get ratHintIndexes ⟨i, h⟩ = clauseId then some ⟨i, h⟩
      else loop (i + 1)
    else none
  termination_by Size.size ratHintIndexes - i
  loop 0

-- Finds the index for the (RAT clause ID + RAT hints) that matches the clauseId
def findRATHintIndex (ratIndex clauseId : Nat) (ratHintIndexes : Array Nat) : Option (Fin ratHintIndexes.size) :=
  -- If the RAT hints are sorted, then check the one under our "cached pointer" first
  if h_index : ratIndex < Size.size ratHintIndexes then
    let ratClauseIndex := Seq.get ratHintIndexes ⟨ratIndex, h_index⟩
    if ratClauseIndex = clauseId then
      some ⟨ratIndex, h_index⟩
    else
      scanRATHintIndexes clauseId ratHintIndexes
  else
    scanRATHintIndexes clauseId ratHintIndexes


/-- Set the witness substitution σ from the provided mapping, resetting σ first. -/
def assumeWitness (σ : PS) (pivot : ILit) (A₁ : Array ILit) (A₂ : Array ILit) : PS :=
  ((σ.reset.setLits A₁).setVars' A₂).setLit pivot

structure SRState where
  F : RangeArray ILit
  τ : PPA
  σ : PS

def checkLine : SRState → SRAdditionLine → Except Bool SRState := fun ⟨F, τ, σ⟩ line =>
  --let ⟨C, wL, wM, upHints, ratHintIndexes, ratHints, _, _⟩ := line
  match uAssumeNegatedForM F τ.reset (line.ratHints.size + 1) with
  | error _ =>
    error false
  | ok τ =>
    -- Evaluate the UP hints, with "# of RAT hints" as the offset
    match applyUPHintsDirect F (line.ratHints.size + 1) τ line.upHints with
    | (_, .err) =>
      error false
    | (τ, .contra) =>
      if F.usize = 0 then error true  -- If the clause is empty, we have a successful contradiction proof
      else ok ⟨F.commit, τ, σ⟩

    | (τ, .unit) =>
      -- If the clause is empty, we should have derived UP contradiction by now
      if hu : 0 < F.usize then
        let pivot : ILit := line.witnessLits.getD 0 (F.ugetFin ⟨0, hu⟩)
        if pivot != F.ugetFin ⟨0, hu⟩ then error false else
        let σ := assumeWitness σ pivot line.witnessLits line.witnessMaps

        -- Loop through each clause in the formula to check RAT conditions
        -- The Bool is true if the check succeeds on all clauses, false otherwise
        let Fsize := F.size
        let rec loop (i cachedRatHintIndex bumpCounter : Nat) (τ : PPA) : PPA × Bool :=
          if hi : i < Fsize then
            if h_del : F.isDeletedFin ⟨i, hi⟩ = true then
              loop (i + 1) cachedRatHintIndex bumpCounter τ
            else
              -- First, check how the ith clause is reduced by σ
              match reduceBreak σ F ⟨i, hi⟩ with
              | .satisfied => loop (i + 1) cachedRatHintIndex bumpCounter τ
              | .notReduced => loop (i + 1) cachedRatHintIndex bumpCounter τ
              | .reduced =>
                if bumpCounter < line.ratHints.size then
                  -- Find the corresponding RAT hint
                  match findRATHintIndex cachedRatHintIndex i line.ratHintIndexes with
                  | none => ⟨τ, false⟩
                  | some ⟨ratIndex, hr⟩ =>
                    -- Assume the negation of the RAT clause
                    match assumeRATClauseDirect F ⟨i, hi⟩ σ τ with
                    | error τ => loop (i + 1) (ratIndex + 1) (bumpCounter + 1) τ.bump
                    | ok τ =>
                      match applyUPHintsDirect F 0 τ (Seq.get line.ratHints ⟨ratIndex, by rw [line.ratSizesEq] at hr; exact hr⟩) with
                      | (τ, .unit) => ⟨τ, false⟩
                      | (τ, .contra) => loop (i + 1) (ratIndex + 1) (bumpCounter + 1) τ.bump
                      | (τ, .err) => ⟨τ, false⟩
                else ⟨τ, false⟩
          else ⟨τ, true⟩
        termination_by F.size - i

        match loop 0 0 0 τ with
        | ⟨_, false⟩ => error false
        | ⟨τ, true⟩ => ok ⟨F.commit, τ, σ⟩
      else error false

--@[inline, always_inline]
def consumeDeletionLine (F : RangeArray ILit) (line : SRDeletionLine) : Except Unit (RangeArray ILit) :=
  let clausesSize := Size.size line.clauses
  let rec loop (i : Nat) (F : RangeArray ILit) : Except Unit (RangeArray ILit) :=
    if hi : i < clausesSize then
      let clauseId := Seq.get line.clauses ⟨i, hi⟩
      if hc : clauseId < F.size then
        if F.isDeletedFin ⟨clauseId, hc⟩ then
          error ()
        else
          loop (i + 1) (F.deleteFin ⟨clauseId, hc⟩)
      else error ()
    else .ok F
  termination_by Size.size line.clauses - i
  loop 0 F

end SR
