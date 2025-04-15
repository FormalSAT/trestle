/-

A CNF and SR parser from buffered streams (`BStream`).

Author: Cayden Codel
Carnegie Mellon University

-/

import Experiments.ProofChecking.BStream
import Experiments.ProofChecking.UInt
import Experiments.ProofChecking.Parsing.Defs

import Lean.Exception
import LeanSAT.Solver.Dimacs
import Experiments.ProofChecking.RangeArray

open Batteries
open LeanSAT.Solver.Dimacs
open LeanSAT LeanSAT.Model ILit Except
open LeanColls

namespace BStreamParser

open IO.FS BStream Parsing

variable {CNF : Type _} [Formula CNF] [Inhabited CNF]

@[inline, specialize]
partial def parseClause (maxVar : Nat) (F : CNF) : BStreamM CNF := do
  -- Just keep parsing literals until 0 is encountered
  let lit ← readInt!
  if h_lit : lit = 0 then
    return Formula.commitClause F
  else
    if lit.natAbs > maxVar then
      panic! s!"Error: Literal {lit} exceeds maximum variable {maxVar}"
    else
      let F := Formula.addLiteral F ⟨lit, h_lit⟩
      parseClause maxVar F

@[inline, specialize]
partial def parseFormula : BStreamM (CNF × Nat) := do
  let F := Formula.empty
  --let problemLine ←
  let foundProblemLine ← scanMatch "p cnf"
  if !foundProblemLine then
    panic! "Error: Expected problem line"

  -- Get the number of vars and number of clauses
  let nVars ← readNat!
  let nClauses ← readNat!

  let rec loop (i : Nat) (F : CNF) : BStreamM CNF := do
    if i ≥ nClauses then
      return F
    else
      let F ← parseClause nVars F
      loop (i + 1) F

  let F ← loop 0 F

  if Formula.size F ≠ nClauses then
    panic! "Error: Expected {nClauses} clauses, but got {Formula.size F}"

  return (F, nVars)

partial def parseLSRDeletionline : BStreamM SRDeletionLine := do
  -- Read nats until 0 is encountered
  let rec loop (acc : Array Nat) := do
    let clauseId ← readNat!
    if clauseId = 0 then
      return { clauses := acc }
    else
      loop (acc.push (clauseId - 1))
  loop #[]

/-
instance : Inhabited (Nat × CNF × (SRAdditionLine ⊕ SRDeletionLine)) := ⟨0, Formula.empty, Sum.inl SRAdditionLine.new⟩
instance : Inhabited (BStreamM (Nat × CNF × (SRAdditionLine ⊕ SRDeletionLine))) := ⟨fun σ => return (⟨0, Formula.empty, Sum.inl SRAdditionLine.new⟩, σ)⟩
-/

@[specialize]
partial def parseLSRLine (F : CNF) : BStreamM (Nat × CNF × (SRAdditionLine ⊕ SRDeletionLine)) := do
  -- Keep parsing ints until a 0 is found
  let lineId ← readNat!
  ws

  -- Check whether a 'd' char indicates a deletion line
  let delCh? ← getc!
  if delCh? = 'd'.toUInt8 then
    let delLine ← parseLSRDeletionline
    return (lineId, F, Sum.inr delLine)
  else
    -- Addition line!
    ungetc delCh?
    let F := Formula.commitClauseUntil F (lineId - 1)

    -- Parse the clause (lits until a repeat of the pivot, or 0)
    let pivot ← readInt!
    let line := SRAdditionLine.new
    let state :=
      if h : pivot = 0 then
        ParsingState.mk .upHints none F line
      else
        ParsingState.mk .clause (some ⟨pivot, h⟩) (Formula.addLiteral F ⟨pivot, h⟩) line

    -- Process the line until we get .lineDone
    let rec loop (state : ParsingState CNF) := do
      let atom ← readInt!
      let ⟨mode, pivot, F, line⟩ := processSRAtom atom state
      match mode with
      | .lineDone => return (lineId, F, Sum.inl line)
      | .err s => panic! s!"LSR parsing error: {s}"
      | _ => loop ⟨mode, pivot, F, line⟩

    loop state

end BStreamParser
