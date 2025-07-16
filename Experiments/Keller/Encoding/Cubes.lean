/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Trestle.Encode
import Trestle.Solver.Dimacs
import Trestle.Upstream.IndexTypeInstances

import Experiments.Keller.Encoding.SR

namespace Keller.Encoding

open Trestle Encode

namespace Cubes

abbrev CubeM (n s) := Prod <| Array (Cube (Literal (Vars n s)))
def CubeM.bind (x : CubeM n s α) (f : α → CubeM n s β) : CubeM n s β :=
  let (cubes1,a) := x
  let (cubes2,b) := f a
  (cubes1++cubes2,b)
def CubeM.pure (a : α) : CubeM n s α := (#[],a)
instance : Monad (CubeM n s) where
  bind := CubeM.bind
  pure := CubeM.pure

def CubeM.split (c : Cube (Literal (Vars n s))) (m : CubeM n s α) : CubeM n s α :=
  let (cubes,a) := m
  let cubes := if cubes.isEmpty then #[#[]] else cubes
  ( cubes.map (Array.append c ·)
  , a)

def CubeM.emit (c : Cube (Literal (Vars n s))) : CubeM n s Unit := (#[c],())
def CubeM.emitMany (cs : Array (Cube (Literal (Vars n s)))) : CubeM n s Unit := (cs,())

def CubeM.toCubing (c : CubeM n s Unit) : Cubing (Literal (Vars n s)) := c.1.toList

open Vars CubeM

def canonMats :=
  SR.matList.filter (·.snd.isNone)
  |>.map (·.fst)

/-- info: true -/
#guard_msgs in
#eval canonMats = [
  #v[true, true, false, true, false],
  #v[true, true, false, false, true],
  #v[true, true, false, false, false],
  #v[true, false, true, false, false],
  #v[true, false, false, true, false],
  #v[true, false, false, false, false],
  #v[false, false, false, false, false]
]

def matrixCubes (n s) :=
  if h : n ≥ 5 ∧ s ≥ 2 then
    let (easy, med, hard) :=
      ( []
      , [canonMats[0], canonMats[2], canonMats[3], canonMats[4], canonMats[5], canonMats[6]]
      , [canonMats[1]])
    let toCube := SR.mat_to_cube (n := n) (hn := by omega) (s := s) (hs := by omega)
    (easy.map toCube, med.map toCube, hard.map toCube)
  else
    (Cubing.unit, Cubing.unit, Cubing.unit)

def lastColsCubes (n s) : Cubing <| Literal (Vars n s) :=
  if h : n = 7 ∧ s > 1 then
    have : NeZero s := ⟨by omega⟩
    (show CubeM n s Unit from
      let rec iter (j : Nat) (last : Nat) := do
        if hj : j < n then
          for hi : i in [0:last+1] do
            let cube : Cube (Literal (Vars n s)) := #[
              .mk (x  3 ⟨j,hj⟩ 0) (i &&& 8 = 0)
            , .mk (x  7 ⟨j,hj⟩ 0) (i &&& 4 = 0)
            , .mk (x 11 ⟨j,hj⟩ 0) (i &&& 2 = 0)
            , .mk (x 19 ⟨j,hj⟩ 0) (i &&& 1 = 0)
            ]
            split cube (iter (j+1) i)
      iter 5 16
    ).toCubing
  else .unit

def extraSplits (n s) : Cubing <| Literal (Vars n s) :=
  if h : n = 7 ∧ s > 0 then
    have : NeZero s := ⟨by omega⟩
    let vars : List (Vars n s) := [
      (x 2 ⟨3,by omega⟩ 0),
      (x 2 ⟨4,by omega⟩ 0),
      (x 4 ⟨3,by omega⟩ 0),
      (x 4 ⟨4,by omega⟩ 0),
      (x 6 ⟨3,by omega⟩ 0),
      (x 6 ⟨4,by omega⟩ 0),
    ]
    vars.foldr (fun v => .prod [#[.pos v], #[.neg v]]) .unit
  else .unit

def allCubes (n s) : List (Clause <| Literal <| Vars n s) :=
  let (easyMats,medMats,hardMats) := matrixCubes n s
  let lastColsCubes := lastColsCubes n s

  let allCubes := easyMats
    ++ (medMats.prod lastColsCubes).prod (extraSplits n s)
    ++ (hardMats.prod lastColsCubes).prod (extraSplits n s)

  allCubes

end Cubes
