/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: Cayden Codel
-/

import Experiments.SR.Parsing.Defs
import Experiments.SR.Data.AsciiIterator

/-!

LSR file parsing.

-/

namespace Trestle

namespace SRParser

open Parsing

variable {CNF : Type _} [Formula CNF] [Inhabited CNF]

@[specialize]
def parseClause (maxVar : Nat) (F : CNF) (arr : ByteArray') (iter : USize) : Except Unit (CNF × USize) :=
  let size := arr.val.size.toUSize
  let rec loop (F : CNF) (iter : USize) : Except Unit (CNF × USize) :=
    if hi : iter < size then
      let ⟨atom, iter'⟩ := ByteArray.readInt arr iter

      if h_atom : atom = 0 then
        .ok (Formula.commitClause F, iter')
      else
        if atom.natAbs > maxVar then
          -- Out of bounds variable
          .error ()
        else
          have : (arr.val.size.toUSize - iter').toNat < (arr.val.size.toUSize - iter).toNat := by
            have := ByteArray.readInt_iter_gt hi
            sorry
            done
          loop (Formula.addLiteral F ⟨atom, h_atom⟩) iter'
    else
      .error ()
  termination_by arr.val.size.toUSize - iter

  loop F iter

--@[inline, always_inline, specialize]
@[specialize]
partial def parseClauses (nvars ncls : Nat) (F : CNF) (arr : ByteArray') (iter : USize) : Except String CNF :=
  let size := arr.val.size.toUSize
  let rec loop (F : CNF) (iter : USize) : Except String (CNF × USize) :=
    let iter := ByteArray.ws arr iter
    if _ : iter < size then
      match parseClause nvars F arr iter with
      | .error _ => .error "Clause parsing error"
      | .ok ⟨F, iter⟩ => loop F iter
    else
      .ok (F, iter)

  match loop F iter with
  | .ok (F, _) =>
    if Formula.size F != ncls then
      throw s!"Expected {ncls} clauses, but found {Formula.size F}"
    else
      .ok F
  | .error str => throw str

--@[inline]
def parseHeader (arr : ByteArray') (iter : USize) : Except String (Nat × Nat × USize) :=
  -- Assumes that the first two non-whitespace tokens are "p" and "cnf"
  let iter := ByteArray.skip arr iter
  let iter := ByteArray.skip arr iter

  -- Now parse two nats
  let ⟨nVars, iter⟩ := ByteArray.readNat arr iter
  let ⟨nCls, iter⟩ := ByteArray.readNat arr iter

  if nVars = 0 || nCls = 0 || iter >= arr.val.size.toUSize then
    throw s!"Invalid header: {nVars}, {nCls}, or iter out of bounds"
  else
    .ok (nVars, nCls, iter)

@[specialize]
def parseFormula (arr : ByteArray') (F : CNF) : Except String (CNF × Nat) :=
  match parseHeader arr 0 with
  | .error str => throw str
  | .ok (nvars, ncls, iter) =>
    match parseClauses nvars ncls F arr iter with
    | .ok F => .ok (F, nvars)
    | .error str => throw str

-- CC: Because the parse line is called at top-level, it's okay for this to be Except.
-- Returns the line id, the updated formula (with the candidate clause loaded), and the line
@[specialize]
partial def parseLSRAdditionLine (F : CNF) (arr : ByteArray') (iter : USize) : Except String (USize × CNF × SRAdditionLine) :=
  -- Assume that `iter` is after the line ID, and that there is no `'d'`.
  -- Parse the first integer to get the pivot (or 0 for the empty clause)
  let size := arr.val.size.toUSize
  let line := SRAdditionLine.new
  let ⟨pivot, iter⟩ := ByteArray.readInt arr iter
  let st :=
    if hp : pivot = 0 then
      ParsingState.mk .upHints F line
    else
      ParsingState.mk .clause (Formula.addLiteral F ⟨pivot, hp⟩) line

  let rec loop (st : ParsingState CNF) (iter : USize) : Except String (USize × CNF × SRAdditionLine) :=
    if _ : iter < size then
      let ⟨atom, iter⟩ := ByteArray.readInt arr iter
      have ⟨mode, F, line⟩ := processSRAtom atom pivot st
      match mode with
      | .err str => throw str
      | .lineDone => .ok (iter, F, line)
      | _ => loop ⟨mode, F, line⟩ iter
    else
      throw "Line ended early"

  loop st iter

@[specialize]
partial def parseDeletionLine (arr : ByteArray') (iter : USize) : Except String (Array Nat × USize) :=
  let iter := ByteArray.ws arr iter
  let size := arr.val.size.toUSize

  let rec loop (acc : Array Nat) (iter : USize) : Except String (Array Nat × USize) :=
    if _ : iter < size then
      let ⟨atom, iter⟩ := ByteArray.readNat arr iter
      if atom = 0 then
        .ok ⟨acc, iter⟩
      else
        loop (acc.push (atom - 1)) iter
    else
      throw "Line ended early"

  loop #[] iter

