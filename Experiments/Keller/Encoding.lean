/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Trestle.Encode
import Trestle.Solver.Dimacs
import Trestle.Upstream.IndexTypeInstances
import Experiments.Keller.KellerGraph
import Experiments.Keller.SymmBreak.Matrix

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
      Cardinality.amoSeqCounter vars

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
def hasSGap (i i' : BitVec n) : EncCNF (Vars n s) Unit := do
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

def c0_c1_c3 (n s) : EncCNF (Vars n s) Unit := do
  if hs : s ≥ 2 then do
  if hn : n ≥ 2 then do
  -- c0 = (0, 0, 0, 0, 0, 0*)
  for hi : j in [0:n] do
    have : j < n := hi.upper
    set 0 j 0
  -- c1 = (0, 1, 0, 0, 0, 0*)
  set 1 0 0
  set 1 1 1
  for hi : j in [2:n] do
    have : j < n := hi.upper
    set 1 j 0
  if hn' : n ≥ 5 then do
    -- c3 = (0, 1, 1, 1, 1, _*)
    set 3 0 0
    for hi : j in [1:5] do
      have : j < 5 := hi.upper
      set 3 j 1
    -- c7 = (0, 1, 1, _, _, _*)
    set 7 0 0; set 7 1 1; set 7 2 1
    -- c11 = (0, 1, _, 1, _, _*)
    set 11 0 0; set 11 1 1; set 11 3 1
    -- c19 = (0, 1, _, _, 1, _*)
    set 19 0 0; set 19 1 1; set 19 4 1
where set (a b c) (hb : b < n := by omega) (hc : c < s := by omega) :=
  unit <| .pos <| x a ⟨b,hb⟩ ⟨c,hc⟩

-- we are sorting each column with respect to an odd order of i's:
def iOfIdx : Equiv.Perm (BitVec n) :=
    Equiv.Perm.setAll [(0, 0), (1, 1), (2, 3), (3, 7), (4, 11), (5, 19)]


def slowIncreasingUnits (j : Fin n) (startIdx : BitVec n) (startColor : Fin s) : EncCNF (Vars n s) Unit := do
  -- Under iOfIdx ordering, the first six indices are all pretty low.
  -- so we can insert lots of units implied by the other symmetry breaking and slowIncreasingStrict
  for h : a in [0: (2^n - startIdx.toNat) ⊓ (s-startColor.val)] do
    have : a < min _ _ := h.upper
    let i := (iOfIdx ⟨startIdx.toNat+a, by omega⟩)
    for h : k in [startColor+a:s] do
      have : k < s := h.upper
      unit <| .neg <| x i j ⟨k, by omega⟩


def slowIncreasingStrict (j : Fin n) : EncCNF (Vars n s) Unit := do
  -- temporary `m_idx,k` is true when
  -- the max color in col `j` *prior* to `idx` is `≥ k`
  let TempTy := BitVec n × Fin s
  withTemps TempTy do
    -- the max starts out below 0, so all m_0,k are false
    for k in List.fins s do
      addClause #[.neg (.inr (0,k))]

    -- now we can define m_idx,k in terms of values to the left and above
    -- `m_idx+1,k ↔ x_i[idx],k ∨ m_idx,k ∨ m_idx+1,k+1`
    for idx in allBitVecs n do
      match idx.toFin.succ? with
      | none => pure ()
      | some idxsucc =>
      for k in List.fins s do
        let misk : Vars n s ⊕ TempTy := .inr (idxsucc,k)
        let xiik : Vars n s ⊕ TempTy := .inl (x (iOfIdx idx) j k)
        let mik  : Vars n s ⊕ TempTy := .inr (idx,k)
        match k.succ? with
        | none =>
          Subtype.val <| tseitin[ {misk} ↔ {xiik} ∨ {mik} ]
        | some ksucc =>
          let misks : Vars n s ⊕ (BitVec n × Fin s) := .inr (idxsucc,ksucc)
          Subtype.val <| tseitin[ {misk} ↔ {xiik} ∨ {mik} ∨ {misks}]

    -- now the symmetry breaking kicker: the max can only increase by one each i!
    for i in allBitVecs n do
      match i.toFin.succ? with
      | none => pure ()
      | some isucc =>
      for k in List.fins s do
        match k.succ? with
        | none => pure ()
        | some ksucc =>
          addClause #[.pos (.inr (i,k)), .neg (.inr (isucc,ksucc))]

def matrixCubes (hn : n ≥ 5) (hs : s ≥ 4) : List (Clause <| Literal (Vars n s)) :=
  let matrixList := SymmBreak.Matrix.canonicalCases.toList
  let idxs := #[7, 11, 19]
  matrixList.map fun m =>
    Array.mk <| List.flatten <|
      List.ofFn fun r : Fin 3 => List.ofFn fun c : Fin 3 =>
        let mval : Fin s := m.data[r][c].castLE (by omega)
        .pos (x idxs[r] ⟨2+c, by omega⟩ mval)

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

def lastColsCubes (hn : n ≥ 5) (hs : s ≥ 4) : List (Clause <| Literal (Vars n s)) :=
  let idxs := #[3, 7, 11, 19]
  let colsList := canonicalColumns (n-5) idxs.size (by omega)
  colsList.map fun cols =>
    let cube := Array.flatten (
      Array.ofFn fun r => Array.ofFn (n := n-5) fun c =>
        .pos <| x idxs[r] ⟨c+5, by omega⟩ cols[c][r])
    cube

end SymmBreaking

def fullEncoding (n s) : EncCNF (Vars n s) Unit := do
  baseEncoding n s
  c0_c1_c3 n s
  if hn : n ≥ 5 then
    if hn : s > 5 then
      slowIncreasingUnits ⟨0,by omega⟩ 6 ⟨2,by omega⟩
      slowIncreasingUnits ⟨1,by omega⟩ 6 ⟨3,by omega⟩
      slowIncreasingUnits ⟨2,by omega⟩ 6 ⟨5,by omega⟩
      slowIncreasingUnits ⟨3,by omega⟩ 6 ⟨5,by omega⟩
      slowIncreasingUnits ⟨4,by omega⟩ 6 ⟨5,by omega⟩
      for h : i in [5:n] do
        slowIncreasingUnits ⟨i,h.upper⟩ 2 ⟨2,by omega⟩


def allCubes : List (Clause <| Literal <| Vars n s) :=
  if hn : n ≥ 5 then
    if hs : s ≥ 4 then
      matrixCubes hn hs ×ˢ lastColsCubes hn hs
      |>.map (fun (a,b) => a ++ b)
    else []
  else []
