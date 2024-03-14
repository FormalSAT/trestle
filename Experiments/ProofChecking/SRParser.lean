/-

A parser for the LSR proof format.

Authors: Cayden Codel
Carnegie Mellon University

-/

import LeanSAT.Solver.Dimacs
import Experiments.ProofChecking.RangeArray
import Experiments.ProofChecking.SRChecker

import Std

open Std
open LeanSAT.Solver.Dimacs
open LeanSAT LeanSAT.Model ILit

namespace SRParser

open Except
open SR

structure ArrayParseRes where
  vars : Nat
  clauses : ICnf

structure RAPraseRes where
  vars : Nat
  formula : FlatCnf

def parseLit (maxVar : Nat) (F : FlatCnf) (s : String) : Except (Except String FlatCnf) FlatCnf := do
  match s.toInt? with
  | none => throw (throw s!"Literal is not a number: {s}")
  | some n =>
    if hn : n = 0 then
      throw (return F.cap)
    else
      if n.natAbs > maxVar then
        throw (throw s!"Literal {n} is greater than the maximum variable {maxVar}")
      else
        if n < 0 then
          return F.push ⟨n, hn⟩
        else
          return F.push ⟨n, hn⟩

def parseClause (maxVar : Nat) (F : FlatCnf) (s : String) : Except String FlatCnf :=
  match s.splitOn " " |>.foldlM (parseLit maxVar) F with
  | ok _ => throw "Zero not encountered on this line"
  | error e => return ← e

def parseFormula (s : String) : Except String FlatCnf := do
  let ⟨pLine, clauseLines⟩ ←
    s.splitOn "\n"
    |>.filter (fun line => !line.startsWith "c" && line.any (!·.isWhitespace))
    |>.expectNonempty fun () => "All lines are empty or comments"
  let (nvars, ncls) ← parseHeader pLine
  let F ← clauseLines.foldlM (parseClause nvars) RangeArray.empty
  if RangeArray.caps F != ncls then
    throw s!"Expected {ncls} clauses, but found {F.size}"
  else
    return F

inductive LPRCheckingMode
| Clause   : LPRCheckingMode
| Witness  : LPRCheckingMode
| Reducing : LPRCheckingMode
| DoneWithLine : LPRCheckingMode
deriving BEq

inductive SRParsingMode
| clause
| witness_tf
| witness_mapped_ready
| witness_mapped_halfway : IVar → SRParsingMode
| up_hints
| rat_hints : Nat × Array Nat → SRParsingMode
| done_with_line -- Could be removed, in favor of Except (Except String SRLine), but this is arguably more elegant
deriving BEq

open SRParsingMode

structure SRDeletionLine where
  clauses : Array Nat

def parseSRAtom (pivot : Option ILit) (p : SRLine × SRParsingMode) (s : String) : Except String (SRLine × SRParsingMode) :=
  let ⟨line, mode⟩ := p
  -- No matter what, the string should be a number, so parse it as an int
  match s.toInt? with
  | none => throw s!"Atom {s} didn't parse to a number"
  | some n =>
    if hn : n = 0 then
      match mode with
      | .clause => return ⟨line, .up_hints⟩
      | .witness_tf => return ⟨line, .up_hints⟩
      | .witness_mapped_ready => return ⟨line, .up_hints⟩
      | .witness_mapped_halfway _ => throw s!"Only got half a substitution mapping when ending a witness"
      | .up_hints => return ⟨line, .done_with_line⟩
      | .rat_hints hints => return ⟨{ line with rat_hints := line.rat_hints.push hints }, .done_with_line⟩
      | .done_with_line => throw s!"Addition line continued after last ending 0"
    else
      match mode with
      | .clause =>
        match pivot with
        | none => throw "No pivot provided for the clause"
        | some pivot =>
          if n = pivot.val then
            -- Seeing the pivot again means we're parsing a witness
            return ⟨line, .witness_tf⟩
          else
            -- It's not the pivot (and it's not 0), so add it to the clause
            return ⟨{ line with clause := line.clause.push ⟨n, hn⟩ }, .clause⟩
      | .witness_tf =>
        match pivot with
        | none => throw "No pivot provided for the witness"
        | some pivot =>
          if n = pivot.val then
            -- Seeing the pivot again means we're parsing the substitution mappings
            return ⟨line, .witness_mapped_ready⟩
          else
            return ⟨{ line with witness_lits := line.witness_lits.push ⟨n, hn⟩ }, .witness_tf⟩
      | .witness_mapped_ready =>
        match pivot with
        | none => throw "No pivot provided for the witness"
        | some pivot =>
          if n = pivot.val then
            throw s!"Saw pivot again in substitution mapping"
          else
            if n < 0 then
              throw s!"First of a substitution mapping must be positive"
            else
              return ⟨line, .witness_mapped_halfway ⟨n.natAbs, Int.natAbs_pos.mpr hn⟩⟩
      | .witness_mapped_halfway v =>
        return ⟨{line with witness_maps := line.witness_maps.push ⟨v, ⟨n, hn⟩⟩ }, .witness_mapped_ready⟩
      | .up_hints =>
        if n < 0 then
          match pivot with
          | none => throw "Can't have RAT hints for empty clauses"
          | _ =>
            -- This is our first RAT hint - start building it
            return ⟨line, .rat_hints ⟨n.natAbs - 1, #[]⟩⟩
        else
          return ⟨{ line with up_hints := line.up_hints.push (n.natAbs - 1) }, .up_hints⟩
      | .rat_hints ⟨h, hints⟩ =>
        if n < 0 then
          -- This is a new RAT hint - add the old one
          return ⟨{ line with rat_hints := line.rat_hints.push ⟨h, hints⟩ }, .rat_hints ⟨n.natAbs - 1, #[]⟩⟩
        else
          return ⟨line, .rat_hints ⟨h, hints.push (n.natAbs - 1)⟩⟩
      | .done_with_line => throw s!"Addition line continued after last ending 0"

def parseLSRLine (p : Nat × Array (SRLine ⊕ SRDeletionLine)) (s : String) : Except String (Nat × Array (SRLine ⊕ SRDeletionLine)) :=
  let ⟨maxId, lines⟩ := p
  match s.splitOn " " with
  | [] => throw "Empty line"
  | [_] => throw s!"Single atom line: {s}, with id {maxId}"
  | (id :: hd :: tls) =>
    match hd with
    | "d" =>
      -- Check to make sure the maxId is (non-strictly) monotonically increasing
      match id.toNat? with
      | none => throw "Line ID is not a number"
      | some id =>
        if id < maxId then
          throw "Deletion line id is not increasing"
        else
          match tls.foldlM (fun arr str =>
            match str.toNat? with
            | none => throw (throw s!"{str} was not a number")
            | some 0 => throw (return arr)
            | some (n + 1) => return arr.push n) #[] with
          | ok _ => throw "Zero not found on deletion line"
          | error e => return ⟨max id maxId, lines.push (.inr (SRDeletionLine.mk (← e)))⟩
    | _ =>
      -- We have an addition line, so the maxId should strictly increase
      match id.toNat? with
      | none => throw "Line ID is not a number"
      | some id =>
        if id ≤ maxId then
          throw "Addition line id is not increasing"
        else
          match hd.toInt? with
          | none => throw "Pivot is not a number"
          | some n =>
            let line : SRLine := ⟨#[], #[], #[], #[], #[]⟩
            if hn : n = 0 then
              match tls.foldlM (parseSRAtom none) ⟨line, .up_hints⟩ with
              | error str => throw str
              | ok ⟨line, mode⟩ =>
                if mode != .done_with_line then
                  throw "Addition line for empty clause didn't end with 0"
                else
                  return ⟨id, lines.push (.inl line)⟩
            else
              match tls.foldlM (parseSRAtom (some ⟨n, hn⟩)) ⟨line, .clause⟩ with
              | error str => throw str
              | ok ⟨line, mode⟩ =>
                if mode != .done_with_line then
                  throw "Addition line didn't end with 0"
                else
                  return ⟨id, lines.push (.inl line)⟩

def parseLSRFile (formulaSize : Nat) (s : String) : Except String (Array (SRLine ⊕ SRDeletionLine)) :=
  match s.splitOn "\n"
    |>.filter (fun line => !line.startsWith "c" && line.any (!·.isWhitespace))
    |>.foldlM parseLSRLine ⟨formulaSize, #[]⟩ with
  | error e => throw e
  | ok ⟨_, lines⟩ => return lines


end SRParser

def main (args : List String) : IO Unit := do
  let cnfFile := args[0]!
  let lsrFile := args[1]!
  let contents ← IO.FS.withFile cnfFile .read (·.readToEnd)
  --let res ← fromFileEnc cnfFile
  let F ← IO.ofExcept <| SRParser.parseFormula contents
  IO.println s!"Formula has {RangeArray.caps F} clauses"

  let lsrContents ← IO.FS.withFile lsrFile .read (·.readToEnd)
  let lines ← IO.ofExcept <| SRParser.parseLSRFile (RangeArray.caps F) lsrContents
  IO.println s!"LSR file has {lines.size} lines"
  --IO.println s!"{F}"
