/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: Cayden Codel
-/

import Trestle.Data.ICnf
import Experiments.SR.Data.RangeArray

/-!

Definitions common to SAT proof checking parsers.

-/

namespace Trestle

namespace Parsing

class Formula (F : Type _) where
  empty : F
  addLiteral : F → ILit → F
  commitClause : F → F
  commitClauseUntil : F → Nat → F
  size : F → Nat

instance : Formula (RangeArray ILit) where
  empty := (RangeArray.empty : RangeArray ILit)
  addLiteral := RangeArray.push
  commitClause := RangeArray.commit
  commitClauseUntil := RangeArray.commitUntil
  size := RangeArray.size

instance : Formula (ICnf × IClause) where
  empty := (#[], #[])
  addLiteral := (fun ⟨F, C⟩ l => ⟨F, C.push l⟩)
  commitClause := (fun ⟨F, C⟩ => (F.push C, #[]))
  commitClauseUntil := (fun ⟨F, C⟩ _ => (F, C)) -- CC: TODO
  size := (fun ⟨F, _⟩ => F.size)

--------------------------------------------------------------------------------

structure SRAdditionLine where
  witnessLits : Array ILit     -- Maps literals to true/false
  witnessMaps : Array ILit     -- Maps variables to literals
  upHints : Array Nat          -- Already 0-indexed clause IDs into the accumulated formula
  ratHintIndexes : Array Nat   -- Already 0-indexed
  ratHints : Array (Array Nat) -- Already 0-indexed
  ratSizesEq : ratHintIndexes.size = ratHints.size
  witnessMapsMod : witnessMaps.size % 2 = 0
  -- CC: Technically, ratHints can be a RangeArray. Try later

def SRAdditionLine.new : SRAdditionLine := ⟨
  Array.mkEmpty 100,
  Array.mkEmpty 100,
  Array.mkEmpty 100,
  Array.mkEmpty 100,
  Array.mkEmpty 100,
  by simp, by simp⟩

instance : Inhabited SRAdditionLine := ⟨{
  witnessLits := #[],
  witnessMaps := #[],
  upHints := #[],
  ratHintIndexes := #[],
  ratHints := #[],
  ratSizesEq := by simp,
  witnessMapsMod := by simp
}⟩

abbrev SRDeletionLine := Array Nat

inductive SRParsingMode
  | clause
  | witnessLits
  | witnessMappedReady
  | witnessMappedHalfway : IVar → SRParsingMode
  | upHints
  | ratHints : Nat → Array Nat → SRParsingMode
  | lineDone
  | err : String → SRParsingMode
deriving BEq, DecidableEq, Inhabited

structure ParsingState (CNF : Type _) where
  mode : SRParsingMode
  F : CNF
  line : SRAdditionLine

section SRParsing

variable [Formula CNF] [Inhabited CNF]

@[inline, specialize]
def processSRAtom (atom pivot : Int) : ParsingState CNF → ParsingState CNF := fun ⟨mode, F, line⟩ =>
  if h_atom : atom = 0 then
    match mode with
    | .clause =>
      -- We don't have a witness, so we insert the pivot into the witness and continue, if the clause isn't empty
      if h_pivot : pivot = 0 then
        ⟨.upHints, F, line⟩
      else
        ⟨.upHints, F, { line with witnessLits := line.witnessLits.push ⟨pivot, h_pivot⟩ }⟩
    | .witnessLits => ⟨.upHints, F, line⟩
    | .witnessMappedReady => ⟨.upHints, F, line⟩
    | .witnessMappedHalfway _ => ⟨.err "Only got half a substitution mapping when ending a witness", F, line⟩
    | .upHints => ⟨.lineDone, F, line⟩
    | .ratHints index hints =>
        ⟨.lineDone, F, { line with
          ratHintIndexes := line.ratHintIndexes.push index,
          ratHints := line.ratHints.push hints,
          ratSizesEq := by simp; exact line.ratSizesEq }⟩
    | .lineDone => ⟨.err "Addition line continued after last ending 0", F, line⟩
    | .err str => ⟨.err str, F, line⟩
  else
    match mode with
    | .clause =>
      if h_pivot : pivot = 0 then
        ⟨.err "No pivot provided for the clause", F, line⟩
      else
        if atom = pivot then
          -- Seeing the pivot again means we're parsing a witness
          ⟨.witnessLits, F, { line with witnessLits := line.witnessLits.push ⟨pivot, h_pivot⟩ }⟩
        else
          -- It's not the pivot (and it's not 0), so add it to the clause
          ⟨.clause, Formula.addLiteral F ⟨atom, h_atom⟩, line⟩
    | .witnessLits =>
      if pivot = 0 then
        ⟨.err "No pivot provided for the witness", F, line⟩
      else
        if atom = pivot then
          -- Seeing the pivot again means we're parsing the substitution mappings
          ⟨.witnessMappedReady, F, line⟩
        else
          ⟨.witnessLits, F, { line with witnessLits := line.witnessLits.push ⟨atom, h_atom⟩ }⟩
    | .witnessMappedReady =>
      if pivot = 0 then
        ⟨.err "No pivot provided for the witness", F, line⟩
      else
        if atom = pivot then
          ⟨.err "Saw pivot again in substitution mapping", F, line⟩
        else
          if atom < 0 then
            ⟨.err "First of a substitution mapping must be positive", F, line⟩
          else
            ⟨.witnessMappedHalfway ⟨atom.natAbs, Int.natAbs_pos.mpr h_atom⟩, F, line⟩
    | .witnessMappedHalfway v =>
      ⟨.witnessMappedReady, F,
        { line with
          witnessMaps := line.witnessMaps.push v |>.push ⟨atom, h_atom⟩,
          witnessMapsMod := by simp [Nat.add_assoc, Nat.add_mod_right]; exact line.witnessMapsMod }⟩
    | .upHints =>
      if atom < 0 then
        if pivot = 0 then
          ⟨.err "Can't have RAT hints for empty clauses", F, line⟩
        else
          -- This is our first RAT hint - start building it
          ⟨.ratHints (atom.natAbs - 1) #[], F, line⟩
      else
        ⟨.upHints, F, { line with upHints := line.upHints.push (atom.natAbs - 1) }⟩
    | .ratHints index hints =>
      if atom < 0 then
        -- This is a new RAT hint - add the old one
        ⟨.ratHints (atom.natAbs - 1) #[], F,
          { line with
            ratHintIndexes := line.ratHintIndexes.push index,
            ratHints := line.ratHints.push hints,
            ratSizesEq := by simp; exact line.ratSizesEq }⟩
      else
        ⟨.ratHints index (hints.push (atom.natAbs - 1)), F, line⟩
    | .lineDone =>
      ⟨.err "Addition line continued after last ending 0", F, line⟩
    | .err str =>
      ⟨.err str, F, line⟩

end SRParsing /- section -/

def echoRangeArrayCNF (F : RangeArray ILit) : IO Unit := do
  let size := F.size
  let rec loop (i : Nat) : IO Unit := do
    if hi : i < size then

      let rsize := F.rsize i hi
      let rec innerLoop (j : Nat) : IO Unit := do
        if hj : j < rsize then
          let lit := F.oget i hi j hj
          IO.print <| s!"{lit} "
          innerLoop (j + 1)
        else
          IO.println "0"
          return
      termination_by F.rsize i hi - j

      innerLoop 0

      have : F.indexes.size - (i + 1) < F.indexes.size - i := by
        simp [size, RangeArray.size] at hi
        omega

      loop (i + 1)
    else
      return
  termination_by F.size - i
  loop 0

private def printArr {α : Type _} [ToString α] (arr : Array α) : IO Unit := do
  let rec loop (i : Nat) := do
    if hi : i < arr.size then
      IO.print s!"{arr[i]'hi} "
      loop (i + 1)
    else
      return
  loop 0

private def printArrSucc (arr : Array Nat) : IO Unit := do
  let rec loop (i : Nat) := do
    if hi : i < arr.size then
      IO.print s!"{arr[i]'hi + 1} "
      loop (i + 1)
    else
      return
  loop 0

def echoLSRLine (line : SRAdditionLine) : IO Unit := do
  if line.witnessLits.size > 1 || line.witnessMaps.size > 0 then
    printArr line.witnessLits
    if line.witnessMaps.size > 0 then
      IO.print s!"{line.witnessLits[0]!} "
      printArr line.witnessMaps

  IO.print "0 "

  printArrSucc line.upHints

  let rec loopRat (i : Nat) : IO Unit := do
    if hi : i < line.ratHintIndexes.size then
      IO.print s!"-{line.ratHintIndexes[i]'hi + 1} "
      printArrSucc <| line.ratHints[i]'(by rwa [← line.ratSizesEq])
      loopRat (i + 1)

  loopRat 0
  IO.println "0"

def echoRangeArrayLSRLine (F : RangeArray ILit) (id : Nat) (line : SRAdditionLine ⊕ SRDeletionLine) : IO Unit := do
  IO.print s!"{id} "

  match line with
  | Sum.inr delLine =>
    IO.print "d "
    printArrSucc delLine
    IO.println "0"

  | Sum.inl addLine =>
    let usize := F.usize
    let rec loop (i : Nat) : IO Unit := do
      if hi : i < usize then
        IO.print s!"{F.uget i hi} "
      else
        return
    loop 0

    echoLSRLine addLine

end Parsing

end Trestle
