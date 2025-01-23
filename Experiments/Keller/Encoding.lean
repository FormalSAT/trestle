/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Trestle.Encode
import Trestle.Solver.Impl.DimacsCommand
import Trestle.Upstream.IndexTypeInstances
import Experiments.Keller.KellerGraph
import Experiments.Keller.G8_Clique

open Trestle Encode

inductive Vars (n s : Nat)
-- coordinates of each of the 2^n clique nodes
| x (i : BitVec n) (j : Fin n) (k : Fin s)
deriving IndexType, Hashable

def allBitVecs (n) : Array (BitVec n) := Array.ofFn (BitVec.ofFin)

section Base
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
        withTemps (Fin n × Fin s) (do
          for j' in List.finRange n do
            if j' ≠ j then
              for k in List.finRange s do
                let temp := Literal.neg (Sum.inr (j',k))
                addClause #[temp, Literal.pos <| Sum.inl (Vars.x i j' k), Literal.pos <| Sum.inl (Vars.x i' j' k)]
                addClause #[temp, Literal.neg <| Sum.inl (Vars.x i j' k), Literal.neg <| Sum.inl (Vars.x i' j' k)]
          addClause (Array.mk (do
            let j' ← List.finRange n
            guard (j' ≠ j)
            let k ← List.finRange s
            return Literal.pos (Sum.inr (j',k))
          ))
        )

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
  withTemps (Fin n) (do
    for j in potentialJs do
      for k in List.finRange s do
        addClause #[Literal.neg (Sum.inr j), Literal.pos (Sum.inl (.x i j k)), Literal.neg (Sum.inl (.x i' j k))]
        addClause #[Literal.neg (Sum.inr j), Literal.neg (Sum.inl (.x i j k)), Literal.pos (Sum.inl (.x i' j k))]
    addClause (potentialJs |>.map (Literal.pos <| Sum.inr ·))
  )

def allSGap : EncCNF (Vars n s) Unit := do
  for i in allBitVecs n do
    for i' in allBitVecs n do
      if i < i' then
        hasSGap i i'

def baseEncoding (n s) : EncCNF (Vars n s) Unit := do
  coordinates
  twoDiffs
  allSGap

end Base

section SymmBreaking
open EncCNF

open Vars in
def initialSymm (s) : EncCNF (Vars 7 (s+1)) Unit := do
  -- c0 = (0,0,0,0,0,0,0)
  unit (x 0 0 0)
  unit (x 0 1 0)
  unit (x 0 2 0)
  unit (x 0 3 0)
  unit (x 0 4 0)
  unit (x 0 5 0)
  unit (x 0 6 0)
  -- c1 = (s,1,0,0,0,0,0)
  unit (x 1 0 0)
  unit (x 1 1 1)
  unit (x 1 2 0)
  unit (x 1 3 0)
  unit (x 1 4 0)
  unit (x 1 5 0)
  unit (x 1 6 0)
  -- c2 = (s,s+1,*,*,1,1,1)
  unit (x 3 0 0)
  unit (x 3 1 1)
  unit (x 3 4 1)
  unit (x 3 5 1)
  unit (x 3 6 1)
where unit v := addClause #[Literal.pos v]

end SymmBreaking

def cliqueToAssn (kc : KellerCliqueData n s) : HashAssn (Literal (Vars n s)) := Id.run do
  let mut res := HashAssn.empty
  for i in allBitVecs n do
    let x := kc.vertices[i.toFin]
    for j in Array.finRange n do
      let k := x[j]
      res := res.insert (.x i j k) true
  return res

def fullEncoding (s) : EncCNF (Vars 7 s) Unit := do
  baseEncoding 7 s
  match s with
  | s+1 => initialSymm s
  | _ => pure ()

def main (args : List String) := show IO _ from do
  if args.length < 3 then
    IO.println "command arguments: <n> <s> <cnf file>"
    return
  let n := args[0]!.toNat!
  let s := args[1]!.toNat!
  let file := args[2]!
  IO.println s!"encoding G_{n}_{s}"
  let enc := baseEncoding n s |>.toICnf
  let () ← IO.FS.withFile file .write <| fun handle => do
    Solver.Dimacs.printFormula (handle.putStr) enc
    handle.flush
