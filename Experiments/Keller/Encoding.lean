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

open EncCNF in
section

-- ensure that each vertex has a defined coordinate on each dimension
def coordinates : EncCNF (Vars n s) Unit := do
  for h : i in [0:2^n] do
    let i : BitVec n := ⟨i,h.2⟩
    for h : j in [0:n] do
      let j : Fin n := ⟨j,h.2⟩
      let vars := Array.ofFn (fun k => Literal.pos <| Vars.x i j k)
      -- at least one of the `c_ij-` variables is true
      addClause vars
      -- at most one of the `c_ij-` variables is true
      Cardinality.amoPairwise vars

open Model.PropForm in
def twoDiffs : EncCNF (Vars n s) Unit := do
  for h : i in [0:2^n] do
    let i : BitVec n := ⟨i,h.2⟩
    for h : j in [0:n] do
      let j : Fin n := ⟨j,h.2⟩
      let i' : BitVec n := i + BitVec.shiftLeft 1 j
      if i < i' then
        Subtype.val <| Tseitin.encode (any (do
          let j' ← List.finRange n
          guard (j' ≠ j)
          let k ← List.finRange s
          return [propform| {Vars.x i j' k} ↔ ¬{Vars.x i' j' k} ]
        ))

open Model PropForm in
def hasSGapAt (i i' : BitVec n) (j : Fin n) : PropForm (Vars n s) :=
  all (
    List.finRange s |>.map fun k =>
      [propform| {Vars.x i j k} ↔ {Vars.x i' j k}]
  )

def hasSGap (i i' : BitVec n) : EncCNF (Vars n s) Unit :=
  withTemps n (do
    for h : j in [0:n] do
      let j : Fin n := ⟨j,h.2⟩
      Subtype.val <| Tseitin.encode (
        .impl
          (Sum.inr j : Vars n s ⊕ _)
          (hasSGapAt i i' j |>.map Sum.inl)
      )
    addClause (Array.finRange n |>.map (Literal.pos <| Sum.inr ·))
  )

def allSGap : EncCNF (Vars n s) Unit := do
  for h : i in [0:2^n] do
    let i : BitVec n := ⟨i,h.2⟩
    for h : i' in [0:2^n] do
      let i' : BitVec n := ⟨i',h.2⟩
      if i < i' then
        hasSGap i i'

def fullEncoding (n s) : EncCNF (Vars n s) Unit := do
  coordinates
  twoDiffs
  allSGap

#eval show IO _ from do
  let enc := fullEncoding 3 7 |>.toICnf
  let () ← IO.FS.withFile "hi.icnf" .write <| fun handle => do
    Solver.Dimacs.printFormula (handle.putStr) enc
    handle.flush
  (Solver.Impl.DimacsCommand "cadical").solve enc

end
