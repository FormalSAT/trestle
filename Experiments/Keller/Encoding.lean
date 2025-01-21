/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Trestle.Encode
import Trestle.Solver.Impl.DimacsCommand
import Trestle.Upstream.IndexTypeInstances

open Trestle Encode

inductive Vars (n s : Nat)
-- coordinates of each of the 2^n clique nodes
| x (i : BitVec n) (j : Fin n) (k : Fin s)
deriving IndexType

def allBitVecs (n) : Array (BitVec n) := Array.ofFn (BitVec.ofFin)

section encoding
open EncCNF Model PropForm

-- ensure that each vertex has a defined coordinate on each dimension
def coordinates : EncCNF (Vars n s) Unit := do
  for i in allBitVecs n do
    for j in Array.finRange n do
      let vars := Array.ofFn (fun k => Literal.pos <| Vars.x i j k)
      -- at least one of the `c_ij-` variables is true
      addClause vars
      -- at most one of the `c_ij-` variables is true
      Cardinality.amoPairwise vars

-- ensure for all pairs where only one coordinate *must* be different,
-- that there is a second coordinate which is also different
def twoDiffs : EncCNF (Vars n s) Unit := do
  for i in allBitVecs n do
    for j in Array.finRange n do
      -- the bitvector which must be different only at coord `j`
      let i' : BitVec n := i ||| BitVec.shiftLeft 1 j
      -- when `j` bit is already high, `i = i'`, so filter that out
      if i < i' then
        Subtype.val <| Tseitin.encode (any (do
          let j' ← List.finRange n
          guard (j' ≠ j)
          let k ← List.finRange s
          return [propform| {Vars.x i j' k} ↔ ¬{Vars.x i' j' k} ]
        ))

-- true if `i` and `i'` on coord `j` are equal `mod s`
def hasSGapAt (i i' : BitVec n) (j : Fin n) : PropForm (Vars n s) :=
  all (do
    let k ← List.finRange s
    return [propform| {Vars.x i j k} ↔ {Vars.x i' j k}]
  )

-- ensures `i` and `i'` have a coord `j` on which they are equal `mod s`
def hasSGap (i i' : BitVec n) : EncCNF (Vars n s) Unit :=
  -- only can consider those `j` for which `i` and `i'` could have an `s`-gap
  let potentialJs := Array.finRange n |>.filter fun j => i[j] ≠ i'[j]
  withTemps n (do
    let temp : Fin n → Vars n s ⊕ Fin n := Sum.inr
    for j in potentialJs do
      Subtype.val <| Tseitin.encode [propform|
        {temp j} → {hasSGapAt i i' j |>.map Sum.inl}
      ]
    addClause (potentialJs |>.map (Literal.pos <| Sum.inr ·))
  )

def allSGap : EncCNF (Vars n s) Unit := do
  for i in allBitVecs n do
    for i' in allBitVecs n do
      if i < i' then
        hasSGap i i'

def fullEncoding (n s) : EncCNF (Vars n s) Unit := do
  coordinates
  twoDiffs
  allSGap

end encoding

#eval! show IO _ from do
  let enc := fullEncoding 3 4 |>.toICnf
  let () ← IO.FS.withFile "hi.icnf" .write <| fun handle => do
    Solver.Dimacs.printFormula (handle.putStr) enc
    handle.flush
