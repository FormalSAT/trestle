/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Trestle.Encode
import Trestle.Solver.Dimacs
import Trestle.Upstream.IndexTypeInstances
import Experiments.Keller.KellerGraph
import Experiments.Keller.SymmBreakSR

namespace Keller.Encoding

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
open EncCNF Vars

def triangle (L : List α) (n : Nat) : List (Vector α n) :=
  aux L n |>.map (·.reverse)
where aux (L : List α) (n : Nat) : List (Vector α n) :=
  match n with
  | 0 => [⟨#[], by simp⟩]
  | n+1 =>
    L.tails.flatMap (fun
      | []     => []
      | hd::tl =>
        aux (hd::tl) n |>.map (·.push hd)
    )

def canonicalColumn (start : Fin s) (len : Nat) : List (Vector (Fin s) len) :=
  aux start len |>.map (Vector.reverse)
where aux (start : Fin s) (len) : List (Vector (Fin s) len) :=
  have : NeZero s := ⟨fun h => (h ▸ start).elim0⟩
  match len with
  | 0 => [⟨#[],by simp⟩]
  | len+1 => do
    let tail := aux start len
    (List.range (start+1)).flatMap (fun hd =>
      let hd : Fin s := hd
      tail.map (·.push hd)) ++
    (aux (start+1) len).map (fun tl =>
      tl.push (Fin.ofNat' s (start+1)))

def canonicalColumns (n : Nat) (len : Nat) (hs : s > 0) : List (Vector (Vector (Fin s) len) n) :=
  let cols := canonicalColumn (s := s) ⟨0,hs⟩ len
  triangle cols n


def symmBreak (n s) : EncCNF (Vars n s) Unit := do
  if hs : s ≥ 2 then do
  if hn : n ≥ 2 then do
  -- c0 = (0,0,0,0,0,0,0)
  for hi : i in [0:n] do
    have : i < n := hi.2
    set 0 i 0
  -- c1 = (s,1,0,0,0,0,0)
  set 1 0 0
  set 1 1 1
  for hi : i in [2:n] do
    have : i < n := hi.2
    set 1 i 0
  if hn' : n ≥ 5 then do
    -- c3 = (s,s+1,1,1,1,*,*)
    set 3 0 0
    for hi : i in [1:5] do
      have : i < 5 := hi.2
      set 3 i 1
where set (a b c) (hb : b < n := by omega) (hc : c < s := by omega) :=
  unit <| .pos <| x a ⟨b,hb⟩ ⟨c,hc⟩

def symmBreakCubes (hn : n ≥ 5) (hs : s ≥ 4) : List (Clause <| Literal (Vars n s)) :=
  let matrixList := canonicalCases.toList
  let colsList := canonicalColumns (n-5) 4 (by omega)
  let idxs := #[3, 7, 11, 19]
  matrixList.flatMap fun m =>
    let matAssn := Array.mk <| List.flatten <|
      List.ofFn fun r => List.ofFn fun c =>
        let mval : Fin s := m.data[r][c].castLE (by omega)
        .pos (x idxs[r.succ] ⟨2+c, by omega⟩ mval)
    colsList.map fun cols =>
      matAssn ++ Array.flatten (
        Array.ofFn (n := 4) fun r => Array.ofFn (n := n-5) fun c =>
          .pos <| x idxs[r] ⟨c+5, by omega⟩ cols[c][r])

end SymmBreaking

def fullEncoding (n s) : EncCNF (Vars n s) Unit := do
  baseEncoding n s
  symmBreak n s
