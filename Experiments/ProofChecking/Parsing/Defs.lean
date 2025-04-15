import Experiments.ProofChecking.RangeArray
import LeanSAT.Data.ICnf

namespace Parsing

open LeanSAT LeanSAT.Model ILit

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

structure SRDeletionLine where
  clauses : Array Nat
deriving Inhabited

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
  pivot : Option ILit
  F : CNF
  line : SRAdditionLine

section SRParsing

variable [Formula CNF] [Inhabited CNF]

@[inline, specialize]
def processSRAtom (atom : Int) : ParsingState CNF → ParsingState CNF := fun ⟨mode, pivot, F, line⟩ =>
  if h_atom : atom = 0 then
    match mode with
    | .clause =>
      -- We don't have a witness, so we insert the pivot into the witness and continue, if the clause isn't empty
      match pivot with
      | none => ⟨.upHints, pivot, F, line⟩
      | some pivot => ⟨.upHints, pivot, F, { line with witnessLits := line.witnessLits.push pivot }⟩
    | .witnessLits => ⟨.upHints, pivot, F, line⟩
    | .witnessMappedReady => ⟨.upHints, pivot, F, line⟩
    | .witnessMappedHalfway _ => ⟨.err "Only got half a substitution mapping when ending a witness", pivot, F, line⟩
    | .upHints => ⟨.lineDone, pivot, F, line⟩
    | .ratHints index hints =>
        ⟨.lineDone, pivot, F, { line with
          ratHintIndexes := line.ratHintIndexes.push index,
          ratHints := line.ratHints.push hints,
          ratSizesEq := by simp; exact line.ratSizesEq }⟩
    | .lineDone => ⟨.err "Addition line continued after last ending 0", pivot, F, line⟩
    | .err str => ⟨.err str, pivot, F, line⟩
  else
    match mode with
    | .clause =>
      match pivot with
      | none => ⟨.err "No pivot provided for the clause", pivot, F, line⟩
      | some pivot =>
        if atom = pivot.val then
          -- Seeing the pivot again means we're parsing a witness
          ⟨.witnessLits, pivot, F, { line with witnessLits := line.witnessLits.push pivot }⟩
        else
          -- It's not the pivot (and it's not 0), so add it to the clause
          ⟨.clause, pivot, Formula.addLiteral F ⟨atom, h_atom⟩, line⟩
    | .witnessLits =>
      match pivot with
      | none => ⟨.err "No pivot provided for the witness", pivot, F, line⟩
      | some pivot =>
        if atom = pivot.val then
          -- Seeing the pivot again means we're parsing the substitution mappings
          ⟨.witnessMappedReady, pivot, F, line⟩
        else
          ⟨.witnessLits, pivot, F, { line with witnessLits := line.witnessLits.push ⟨atom, h_atom⟩ }⟩
    | .witnessMappedReady =>
      match pivot with
      | none => ⟨.err "No pivot provided for the witness", pivot, F, line⟩
      | some pivot =>
        if atom = pivot.val then
          ⟨.err "Saw pivot again in substitution mapping", pivot, F, line⟩
        else
          if atom < 0 then
            ⟨.err "First of a substitution mapping must be positive", pivot, F, line⟩
          else
            ⟨.witnessMappedHalfway ⟨atom.natAbs, Int.natAbs_pos.mpr h_atom⟩, pivot, F, line⟩
    | .witnessMappedHalfway v =>
      ⟨.witnessMappedReady, pivot, F,
        { line with
          witnessMaps := line.witnessMaps.push v |>.push ⟨atom, h_atom⟩,
          witnessMapsMod := by simp [add_assoc, Nat.add_mod_right]; exact line.witnessMapsMod }⟩
    | .upHints =>
      if atom < 0 then
        match pivot with
        | none => ⟨.err "Can't have RAT hints for empty clauses", pivot, F, line⟩
        | _ =>
          -- This is our first RAT hint - start building it
          ⟨.ratHints (atom.natAbs - 1) #[], pivot, F, line⟩
      else
        ⟨.upHints, pivot, F, { line with upHints := line.upHints.push (atom.natAbs - 1) }⟩
    | .ratHints index hints =>
      if atom < 0 then
        -- This is a new RAT hint - add the old one
        ⟨.ratHints (atom.natAbs - 1) #[], pivot, F,
          { line with
            ratHintIndexes := line.ratHintIndexes.push index,
            ratHints := line.ratHints.push hints,
            ratSizesEq := by simp; exact line.ratSizesEq }⟩
      else
        ⟨.ratHints index (hints.push (atom.natAbs - 1)), pivot, F, line⟩
    | .lineDone =>
      ⟨.err "Addition line continued after last ending 0", pivot, F, line⟩
    | .err str =>
      ⟨.err str, pivot, F, line⟩

end SRParsing /- section -/

def echoRangeArrayCNF (F : RangeArray ILit) : IO Unit := do
  let rec loop (i : Nat) : IO Unit := do
    if hi : i < F.size then
      let rec innerLoop (j : Nat) : IO Unit := do
        if hj : j < F.rsizeFin ⟨i, hi⟩ then
          let lit := F.ogetFin ⟨i, hi⟩ ⟨j, hj⟩
          IO.print <| s!"{lit} "
          innerLoop (j + 1)
        else
          IO.println "0"
          return
      termination_by F.rsizeFin ⟨i, hi⟩ - j
      innerLoop 0
      loop (i + 1)
    else
      return
  loop 0

private def printArr {α : Type _} [ToString α] (arr : Array α) : IO Unit := do
  let rec loop (i : Nat) := do
    if hi : i < arr.size then
      IO.print s!"{arr.get ⟨i, hi⟩} "
      loop (i + 1)
    else
      return
  loop 0

private def printArrSucc (arr : Array Nat) : IO Unit := do
  let rec loop (i : Nat) := do
    if hi : i < arr.size then
      IO.print s!"{arr.get ⟨i, hi⟩ + 1} "
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
      IO.print s!"-{line.ratHintIndexes.get ⟨i, hi⟩ + 1} "
      printArrSucc <| line.ratHints.get ⟨i, by rwa [← line.ratSizesEq]⟩
      loopRat (i + 1)

  loopRat 0
  IO.println "0"

def echoRangeArrayLSRLine (F : RangeArray ILit) (id : Nat) (line : SRAdditionLine ⊕ SRDeletionLine) : IO Unit := do
  IO.print s!"{id} "

  match line with
  | Sum.inr delLine =>
    IO.print "d "
    printArrSucc delLine.clauses
    IO.println "0"

  | Sum.inl addLine =>
    let usize := F.usize
    let rec loop (i : Nat) : IO Unit := do
      if hi : i < usize then
        IO.print s!"{F.ugetFin ⟨i, hi⟩} "
      else
        return
    loop 0

    echoLSRLine addLine

end Parsing
