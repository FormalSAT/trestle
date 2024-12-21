/-

An SR parser (and updated CNF formula parser).
Made general via a `SRParser.Formula` class.

Author: Cayden Codel
Carnegie Mellon University

-/

import LeanSAT.Solver.Dimacs
import Experiments.ProofChecking.RangeArray
import Experiments.ProofChecking.Parsing.Defs

open Batteries
open LeanSAT.Solver.Dimacs
open LeanSAT LeanSAT.Model ILit Except

namespace SRParser

open Parsing

variable {CNF : Type _} [Formula CNF]

-- Parses a single literal from a string.
-- CC: The double Except monad is used to stop folding across a list/array of atom strings
--     in case a 0 is encountered, since DIMACS doesn't require a clause to fit on a line.
@[inline, specialize]
def parseLitM (maxVar : Nat) (F : CNF) (s : String) : Except (Except String CNF) CNF := do
  match s.toInt? with
  | none => throw (throw s!"Literal is not a number: {s}")
  | some n =>
    if hn : n = 0 then
      throw (return F)
    else
      if n.natAbs > maxVar then
        throw (throw s!"Literal {n} is greater than the maximum variable {maxVar}")
      else
        return Formula.addLiteral F ⟨n, hn⟩

inductive DimacsParsingResult
  | ok         -- Parsing expects more input
  | done       -- Parsing expects to be done
  | err : String → DimacsParsingResult   -- Error encountered
  deriving Inhabited, DecidableEq

-- Parses a single literal from a string. Keeps track of whether a '0' has been found.
@[inline, specialize]
def parseLit (maxVar : Nat) (F : CNF) (s : String) : DimacsParsingResult × CNF :=
  match s.toInt? with
  | none => (.err s!"Literal '{s}' is not a number.", F)
  | some n =>
    if hn : n = 0 then
      (.done, F)
    else
      if n.natAbs > maxVar then
        (.err s!"Literal {n} is greater than the maximum variable {maxVar}.", F)
      else
        (.ok, Formula.addLiteral F ⟨n, hn⟩)

@[specialize]
def parseClauseM (maxVar : Nat) (F : CNF) (s : String) : Except String CNF :=
  match s.splitOn " " |>.foldlM (parseLitM maxVar) F with
  | ok _ => throw "Zero not encountered on this line"
  | error e => return Formula.commitClause (← e)

@[specialize]
def parseClause (maxVar : Nat) (F : CNF) (s : String) : DimacsParsingResult × CNF :=
  let rec loop (F : CNF) : List String → DimacsParsingResult × CNF
    | [] => (.err "0 not found before end of line", F)
    | atom :: atoms =>
      match parseLit maxVar F atom with
      | (.err str, F) => (.err str, F)
      | (.ok, F) => loop F atoms
      | (.done, F) =>
        if atoms.length = 0 then
          (.done, Formula.commitClause F)
        else
          (.err "0 found before end of line", F)
  loop F (s.splitOn " ")

-- Parses the CNF given a string and an empty formula to read the clauses into
@[specialize]
def parseFormulaM (s : String) (F : CNF) : Except String (CNF × Nat) := do
  match s.splitOn "\n" |>.filter (fun line => !line.startsWith "c" && line.any (!·.isWhitespace)) with
  | [] => throw "All lines are empty or comments"
  | (pLine :: clauseLines) =>
    let (nvars, ncls) ← parseHeader pLine
    let F ← clauseLines.foldlM (parseClauseM nvars) F
    if Formula.size F != ncls then
      throw s!"Expected {ncls} clauses, but found {Formula.size F}"
    else
      return (F, nvars)

@[inline, always_inline, specialize]
def parseClauses (nvars ncls : Nat) (F : CNF) : List String → Except String CNF
  | [] =>
    if Formula.size F != ncls then
      throw s!"Expected {ncls} clauses, but found {Formula.size F}"
    else
      ok F
  | c :: cs =>
    match parseClause nvars F c with
    | (.err str, _) => throw str
    | (_, F) => parseClauses nvars ncls F cs

-- CC: Because `parseFormula` is only called at top level once, it is okay to
--     have the return type be an `Except` monad. However, the functions called
--     by this function are the non-monadic versions.
@[specialize]
def parseFormula (s : String) (F : CNF) : Except String (CNF × Nat) :=
  match s.splitOn "\n" |>.filter (fun line => !line.startsWith "c" && line.any (!·.isWhitespace)) with
  | [] => throw "All lines are empty or comments"
  | (pLine :: clauseLines) =>
    match parseHeader pLine with
    | .error str => throw str
    | .ok (nvars, ncls) =>
      match parseClauses nvars ncls F clauseLines with
      | .ok F => ok (F, nvars)
      | .error str => throw str

def parseSRAtom (st : ParsingState CNF) (s : String) : ParsingState CNF :=
  -- No matter what, the string should be a number, so parse it as an int
  match s.toInt? with
  | none => { st with mode := .err s!"Atom {s} didn't parse to a number" }
  | some n => processSRAtom n st

-- CC: Because the parse line is called at top-level, it's okay for this to be Except.
-- Returns the line id, the updated formula (with the candidate clause loaded), and the line
def parseLSRLine (F : CNF) (s : String) : Except String (Nat × CNF × (SRAdditionLine ⊕ SRDeletionLine)) :=
  match s.splitOn " " with
  | [] => throw "Empty line"
  | [id] => throw s!"Single atom line: {s}, with id {id}"
  | (id :: hd :: tls) =>
    match id.toNat? with
    | none => throw s!"Line ID {id} is not a number"
    | some id =>
      match hd with
      | "d" =>
        -- Check to make sure the maxId is (non-strictly) monotonically increasing
        -- CC: We actually don't care about this, since we assume the proof is ordered.
        match tls.foldlM (fun arr str =>
          match str.toNat? with
          | none => throw (throw s!"{str} was not a number")
          | some 0 => throw (return arr)
          | some (n + 1) => return arr.push n) #[] with
        | ok _ => throw "Zero not found on deletion line"
        | error e => return ⟨id, F, .inr (SRDeletionLine.mk (← e))⟩
      | _ =>
        let F := Formula.commitClauseUntil F (id - 1)

      -- We have an addition line, so the maxId should strictly increase
        -- CC: Similarly, we don't care that the ID line is strictly increasing,
        --     only that the clause doesn't exist in the formula yet.
        match hd.toInt? with
        | none => throw "Pivot is not a number"
        | some n =>
          let line := SRAdditionLine.new
          let st :=
            if hn : n = 0 then
              ParsingState.mk .upHints none F line
            else
              ParsingState.mk .clause (some ⟨n, hn⟩) (Formula.addLiteral F ⟨n, hn⟩) line

          let rec loop (st : ParsingState CNF) : List String → ParsingState CNF
            | [] => st
            | atom :: atoms =>
              let ⟨mode, pivot, F, line⟩ := parseSRAtom st atom
              match mode with
              | .err _ => ⟨mode, pivot, F, line⟩
              | _ => loop ⟨mode, pivot, F, line⟩ atoms

          let ⟨mode, _, F, line⟩ := loop st tls
          match mode with
          | .err str => throw str
          | .lineDone => return ⟨id, F, .inl line⟩
          | _ => throw "Addition line didn't end with 0"

--------------------------------------------------------------------------------

def undoBinaryMapping (x : UInt64) : Int :=
  if x &&& 1 = 1 then
    ((((x >>> 1).toNat) : Int) * -1)
  else
    (((x >>> 1).toNat) : Int)

-- CC: This version is an attempt to get totality
/-
def readBinaryToken (A : ByteArray) (index : Nat) : Int × { i : Nat // i > index } :=
  let rec go (i : Nat) (acc : UInt64) (shift : UInt64) : Int × { idx : Nat // idx > i } :=
    if hi : i < A.size then
      let atom : UInt8 := A.get ⟨i, hi⟩
      let acc' : UInt64 := acc ||| ((atom &&& 127).toUInt64 <<< shift)
      if atom &&& 128 != 0 then
        match go (i + 1) acc' (shift + 7) with
        | ⟨a, ⟨b, hb⟩⟩ => ⟨a, ⟨b, Nat.le_of_succ_le hb⟩⟩
      else
        ⟨undoBinaryMapping acc', ⟨A.size, hi⟩⟩
    else
      ⟨undoBinaryMapping acc, ⟨i + 1, Nat.lt_succ_self _⟩⟩
  termination_by A.size - i
  go index 0 0
-/

-- Int is result, Nat is cached index into A
partial def readBinaryToken (A : ByteArray) (index : Nat) : Int × Nat :=
  let rec go (i : Nat) (acc : UInt64) (shift : UInt64) : Int × Nat :=
    if hi : i < A.size then
      let atom : UInt8 := A.get ⟨i, hi⟩
      let acc' : UInt64 := acc ||| ((atom &&& 127).toUInt64 <<< shift)
      if atom &&& 128 != 0 then
        go (i + 1) acc' (shift + 7)
      else
        ⟨undoBinaryMapping acc', i + 1⟩
    else
      ⟨undoBinaryMapping acc, A.size⟩
  let ⟨res, idx⟩ := go index 0 0
  -- dbg_trace s!"Pointer at index {index} moved to {idx}, parsed {res}"
  ⟨res, idx⟩

-- Bool: found a 0
-- Nat: updated index
partial def parseLSRDeletionLineBinary (A : ByteArray) (index : Nat) : Bool × Nat × SRDeletionLine :=
  let rec go (i : Nat) (acc : Array Nat) : Bool × Nat × SRDeletionLine :=
    if i < A.size then
      let (x, j) := readBinaryToken A i
      if x = 0 then
        ⟨true, j, SRDeletionLine.mk acc⟩
      else
        go j (acc.push (x.natAbs - 1))
    else
      ⟨false, A.size, SRDeletionLine.mk acc⟩
  go index #[]

instance : Inhabited (Nat × ParsingState CNF) :=
  ⟨⟨0, ParsingState.mk .clause none (Formula.empty) (SRAdditionLine.new)⟩⟩

@[specialize]
partial def parseLSRAdditionLineBinary (F : CNF) (A : ByteArray)
    (index : Nat) (pivot : Option ILit) : Nat × ParsingState CNF :=
  let rec go (i : Nat) (st : ParsingState CNF) : Nat × ParsingState CNF :=
    have : Inhabited (Nat × ParsingState CNF) := by infer_instance
    if i < A.size then
      let (n, j) := readBinaryToken A i
      let st := processSRAtom n st
      match st.mode with
      | .err _ => (j, st)
      | .lineDone => (j, st)
      | _ => go j st
    else
      ⟨A.size, st⟩

  let newLine := SRAdditionLine.new
  match pivot with
  | none => go index (ParsingState.mk .upHints none F newLine)
  | some p => go index (ParsingState.mk .clause (some p) (Formula.addLiteral F p) newLine)

-- First nat is cached index into arr, second is ID of new clause to add
partial def parseLSRLineBinary (F : CNF) (A : ByteArray) (index : Nat)
    : Except String (Nat × Nat × CNF × (SRAdditionLine ⊕ SRDeletionLine)) :=
  if hi : index + 1 < A.size then
    -- Check if we have an addition line or a deletion line
    let lineStart : UInt8 := A.get ⟨index, Nat.lt_of_succ_lt hi⟩
    let ⟨lineId, index⟩ := readBinaryToken A (index + 1)
    if lineId < 0 then error "Negative line ID" else

    -- Addition line
    if lineStart = 1 then
      let F := Formula.commitClauseUntil F (lineId.natAbs - 1)

      -- Check if we have a pivot
      if index < A.size then
        let ⟨pivot, index⟩ := readBinaryToken A index
        let ⟨index, st⟩ :=
          if hp : pivot = 0 then
            parseLSRAdditionLineBinary F A index none
          else
            parseLSRAdditionLineBinary F A index (some ⟨pivot, hp⟩)
        match st.mode with
        | .err str => throw str
        | .lineDone => ok (index, lineId.natAbs, st.F, .inl st.line)
        | _ => error "Addition line didn't end with 0"
      else
        error "Line ended early"
    else if lineStart = 2 then
      match parseLSRDeletionLineBinary A index with
      | ⟨true, index, line⟩ => ok (index, lineId.natAbs, F, .inr line)
      | ⟨false, _, _⟩ => error "Deletion line didn't end with 0"
    else
      error "Start of line wasn't addition (1) or deletion (2)"

  else
    error "No more string!"

#exit

/- Correctness -/
-- parseLSRLine (F : CNF) (s : String) : Except String (Nat × CNF × (SRAdditionLine ⊕ SRDeletionLine))
-- CC: We trust that parsing is successful, so we only prove that there
--     exists a clause that `F` models on a successful parse
open RangeArray in
theorem parseLSRLine_ok_inl {F F' : RangeArray ILit} {s : String} {id : Nat} {addLine : SRAdditionLine} {Ls : List (Option (List ILit))} :
  parseLSRLine F s = Except.ok (id, F', Sum.inl addLine) →
    models F Ls [] →
    ∃ C, models F' (Ls ++ (List.replicate (id - Ls.length) none)) C := by
  sorry
  done

theorem parseLSRLine_ok_inr {F F' : RangeArray ILit} {s : String} {id : Nat} {delLine : SRDeletionLine} :
    parseLSRLine F s = Except.ok (id, F', Sum.inr delLine) → F = F' := by
  sorry
  done

end SRParser
