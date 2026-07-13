/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: Cayden Codel
-/

import Experiments.SR.Parsing.Defs
import Experiments.SR.Data.ByteArray.Defs
import Experiments.SR.Data.ByteArray.Basic

/-!

LSR file parsing.

-/

namespace Trestle

namespace SRParser

open Parsing ByteArray

variable {CNF : Type _} [Formula CNF]

def consumeCommentLines (arr : ByteArray) (iter : USize) : USize :=
  let c : UInt8 := peek arr iter
  if c = 'c'.toUInt8 then
    consumeCommentLines arr <| line arr (iter + 1)
  else
    iter
termination_by arr.size.toUSize - iter
decreasing_by
  simp
  rw [← USize.lt_iff_toNat_lt]
  apply USize.sub_lt_sub_of_lt_of_le
  <;> rename_i h
  · have : c ≠ UInt8.EOF := by simp [h]; trivial
    replace := iter_lt_of_peek_ne_EOF this
    have h₁ := iter_le_line arr (iter + 1)
    exact USize.lt_of_lt_of_le (USize.lt_succ_of_lt this) h₁
  · apply line_le_of_le
    have : c ≠ UInt8.EOF := by simp [h]; trivial
    exact USize.succ_le_of_lt <| iter_lt_of_peek_ne_EOF this

/-! # parseClause -/

/--
  Parses a clause from the array `arr` starting at `iter`.
-/
@[specialize]
def parseClause (F : CNF) (arr : ByteArray) (maxVar : Nat) (iter : USize) : CNF × USize :=
  if _ : iter < arr.size.toUSize then
    match h_atom : ByteArray.readInt32 arr iter with
    | atom =>
    match h_iter' : ByteArray.skipInt arr iter with
    | iter' =>
    if h : atom = 0 then
      (Formula.commitClause F, iter')
    else
      -- Out of bounds variable
      if atom.natAbs > maxVar then
        let F' : CNF := panic! s!"Variable {atom.natAbs} in clause {Formula.size F + 1} exceeds maximum variable {maxVar}"
        (F', arr.size.toUSize)
      else
        parseClause (Formula.addLiteral F ⟨atom, by simp [h]⟩) arr maxVar iter'
  else
    (F, iter)
termination_by arr.size.toUSize - iter
decreasing_by
  subst h_iter' h_atom
  simp
  apply USize.lt_iff_toNat_lt.mp
  apply USize.sub_lt_sub_of_lt_of_le
  · exact iter_lt_skipInt_of_readInt32 h
  · apply skipInt_le_of_le
    exact USize.le_of_lt (by assumption)

-- @[simp]
-- private theorem iter_le_parseClause_iter (F : CNF) (arr : ByteArray) (iter : USize) (maxVar : Nat)
--     : iter ≤ (parseClause F arr maxVar iter).2 := by
--   unfold parseClause
--   stop
--   simp
--   split
--   · rename_i hi
--     split
--     · simp
--     · split
--       · simp
--         apply USize.le_of_lt (by assumption)
--       · apply USize.le_trans <| iter_le_readInt_iter (α := UInt32) (arr := arr) (iter := iter)
--         apply iter_le_parseClause_loop_iter
--   · simp
-- termination_by arr.size.toUSize - iter
-- decreasing_by
--   stop
--   simp
--   rw [← USize.lt_iff_toNat_lt]
--   apply USize.sub_lt_sub_of_lt_of_le
--   · apply iter_lt_readInt_iter_of_ne_zero (by assumption)
--   · apply readInt_iter_le_of_le
--     apply USize.le_of_lt (by assumption)

-- private theorem parseClause_loop_iter_le_of_le (F : CNF) (arr : ByteArray) (iter : USize) (maxVar : Nat)
--     : iter ≤ arr.size.toUSize → (parseClause F arr maxVar iter).2 ≤ arr.size.toUSize := by
--   intro hi
--   stop
--   unfold parseClause.loop
--   simp
--   split
--   · rename_i hi_lt
--     split
--     · simp
--       exact readInt_iter_le_of_le hi
--     · rename_i h_int
--       split
--       · simp
--       · apply parseClause_loop_iter_le_of_le
--         exact readInt_iter_le_of_le hi
--   · exact USize.le_iff_toBitVec_le.mpr hi
-- termination_by arr.size.toUSize - iter
-- decreasing_by
--   simp
--   stop
--   rw [← USize.lt_iff_toNat_lt]
--   apply USize.sub_lt_sub_of_lt_of_le
--   · apply iter_lt_readInt_iter_of_ne_zero (by assumption)
--   · apply readInt_iter_le_of_le
--     apply USize.le_of_lt (by assumption)

-- theorem parseClause_iter_le_of_le (F : CNF) (arr : ByteArray) (iter : USize) (maxVar : Nat)
--     : iter ≤ arr.size.toUSize → (parseClause F arr iter maxVar).2 ≤ arr.size.toUSize := by
--   intro hi
--   unfold parseClause
--   simp
--   apply parseClause_loop_iter_le_of_le
--   exact USize.le_iff_toBitVec_le.mpr hi

/-! # parseClauses -/

@[specialize]
partial def parseClauses (F : CNF) (arr : ByteArray) (iter : USize) (nVars nClauses : Nat) : Except String CNF := do
  let size := arr.size.toUSize
  let rec loop (F : CNF) (iter : USize) : Except String (CNF × USize) :=
    have : size = arr.size.toUSize := rfl
    let iter₂ := ws arr iter
    if _ : iter₂ < size then
      --let prevSize := Formula.size F
      match _ : parseClause F arr nVars iter₂ with
      | (F', iter₃) =>
      -- if Formula.uncommittedSize F' != 0 || Formula.size F' = prevSize then
      --   .error s!"Formula clause {Formula.size F' + 1} contained a parsing error"
      -- else if iter₃ = iter₂ then
      --   -- TODO(CC): Remove this branch by adding a theorem on `parseClause` that the iteraor *will* move forward
      --   .error s!"Iterator did not advance forward in formula clause {Formula.size F' + 1}"
      -- else
        loop F' iter₃
    else
      .ok (F, iter₂)
  -- termination_by arr.size.toUSize - iter
  -- decreasing_by
  --   simp_wf
  --   rw [← USize.lt_iff_toNat_lt]
  --   rename_i hp _ h_ne
  --   apply USize.sub_lt_sub_of_lt_of_le
  --   · have := iter_le_parseClause_iter F arr iter₂ nVars
  --     simp [hp] at this
  --     exact USize.lt_of_le_of_ne this (Ne.symm h_ne)
  --   · have := parseClause_iter_le_of_le F arr iter nVars
  --     simp [hp] at this
  --     exact this <| USize.le_of_lt (by assumption)

  let (F, _) ← loop F iter
  if Formula.size F != nClauses then
    throw s!"Expected {nClauses} clauses, but parsed {Formula.size F}"
  else
    .ok F

def parseHeader (arr : ByteArray) (iter : USize) : Except String (Nat × Nat × USize) := do
  let iter := consumeCommentLines arr iter

  -- Assumes that the first two non-whitespace tokens are "p" and "cnf"
  let iter := token arr iter
  let iter := token arr iter

  -- Now parse two nats
  let ⟨nVars, iter⟩    := readNat arr iter
  let ⟨nClauses, iter⟩ := readNat arr iter

  if nVars = 0 then
    throw s!"Invalid cnf header: The number of variables was 0"
  else if nClauses = 0 then
    throw s!"Invalid cnf header: The number of clauses was 0"
  else
    .ok (nVars, nClauses, iter)

@[specialize]
def parseCnf (arr : ByteArray) (F : CNF) : Except String (CNF × Nat) := do
  let ⟨nVars, nClauses, iter⟩ ← parseHeader arr 0
  dbgTrace s!"c Parsing formula with {nVars} variables, {nClauses} clauses" fun () => do
  let F ← parseClauses F arr iter nVars nClauses
  return (F, nVars)

-- CC: Because the parse line is called at top-level, it's okay for this to be Except.
-- Returns the line id, the updated formula (with the candidate clause loaded), and the line
@[specialize]
partial def parseLSRAdditionLine (F : CNF) (arr : ByteArray) (iter : USize) : Except String (USize × CNF × SRAdditionLine) :=
  -- Assume that `iter` is after the line ID, and that there is no `'d'`.
  -- Parse the first integer to get the pivot (or 0 for the empty clause)
  let size := arr.size.toUSize
  let line := SRAdditionLine.new
  let ⟨pivot, iter⟩ := ByteArray.readInt (α := UInt32) arr iter
  let st :=
    if hp : pivot = 0 then
      ParsingState.mk .upHints F line
    else
      ParsingState.mk .clause (Formula.addLiteral F ⟨pivot, hp⟩) line

  let rec loop (st : ParsingState CNF) (iter : USize) : Except String (USize × CNF × SRAdditionLine) :=
    if _ : iter < size then
      -- match _ : ByteArray.readInt64' arr iter with
      -- | ⟨atom, iter'⟩ =>
      let atom := ByteArray.readInt64 arr iter
      let iter' := ByteArray.skipInt arr iter
      have ⟨mode, F, line⟩ := processSRAtom atom pivot st
      match mode with
      | .err str => throw str
      | .lineDone => .ok (iter', F, line)
      | _ => loop ⟨mode, F, line⟩ iter'
    else
      throw "Line ended early"
  -- termination_by arr.size.toUSize - iter
  -- decreasing_by
  --   simp
  --   rw [← USize.lt_iff_toNat_lt]
  --   sorry

  loop st iter

@[specialize]
partial def parseDeletionLine (arr : ByteArray) (iter : USize) : Except String (Array Nat × USize) :=
  let iter := ByteArray.ws arr iter
  let size := arr.size.toUSize

  let rec loop (acc : Array Nat) (iter : USize) : Except String (Array Nat × USize) :=
    have : size = arr.size.toUSize := rfl
    if _ : iter < size then
      let atom := ByteArray.readInt64 arr iter
      let iter' := ByteArray.skipInt arr iter
      if atom = 0 then
        .ok ⟨acc, iter'⟩
      else
        loop (acc.push (atom - 1).toNat) iter'
    else
      throw "Line ended early"
  -- termination_by arr.size.toUSize - iter
  -- decreasing_by
  --   simp
  --   rw [← USize.lt_iff_toNat_lt]
  --   rename_i hi h_readNat h_ne
  --   stop
  --   simp at h_readNat
  --   apply USize.sub_lt_sub_of_lt_of_le
  --   · have : atom = (readNat arr iter).1 := by simp [h_readNat]
  --     rw [this] at h_ne
  --     have := iter_lt_readNat_of_ne_zero h_ne
  --     simp [h_readNat] at this
  --     exact this
  --   · have : iter' = (readNat (α := UInt64) arr iter).2 := by simp [h_readNat]
  --     rw [this]
  --     apply readNat_iter_le_of_le
  --     apply USize.le_of_lt hi

  loop #[] iter
