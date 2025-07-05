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

open Vars

def matrixCubes (n s) : Cubing <| Literal (Vars n s) :=
  if h : n ≥ 5 ∧ s ≥ 4 then
    let matrixList := (SR.canonicalMats.get 3).canonical.toList
    let idxs := #[7, 11, 19]
    let two : Fin n := ⟨2,by omega⟩
    let three : Fin n := ⟨3,by omega⟩
    let four : Fin n := ⟨4,by omega⟩
    have : NeZero s := ⟨by omega⟩
    matrixList.map fun m =>
      #[.pos (x 7  three (Fin.ofNat' _ m.data[0][1]))
      , .pos (x 7  four  (Fin.ofNat' _ m.data[0][2]))
      , .pos (x 11 two   (Fin.ofNat' _ m.data[1][0]))
      , .pos (x 11 four  (Fin.ofNat' _ m.data[1][2]))
      , .pos (x 19 two   (Fin.ofNat' _ m.data[2][0]))
      , .pos (x 19 three (Fin.ofNat' _ m.data[2][1]))
      ]
  else
    .unit

def lastColsCubes (n s) : Cubing <| Literal (Vars n s) :=
  if h : s > 1 then
    if h : n = 7 then
      let colorings := SR.col5n_colorings s (by omega) |>.filterMap (·.getLeft?)
      colorings.map fun coloring =>
        Array.flatten <| Array.ofFn (n := 2) fun col => Array.ofFn (n := 4) fun row =>
          .pos (x #v[3,7,11,19][row] (h ▸ #[5,6][col]) coloring[col][row])
    else if h : n = 6 then
      let colorings := SR.col5_colorings s (by omega) |>.filterMap (·.getLeft?)
      let js := List.finRange n |>.filter (·.val ≥ 5)
      let cubes : List (Cubing _) := js.map fun j =>
        colorings.map fun coloring =>
          Array.ofFn (n := 4) fun idx =>
            .pos (x #v[3,7,11,19][idx] j coloring[idx])
      cubes.foldl (·.prod ·) (.unit)
      else .unit
  else .unit

def allCubes (n s) : List (Clause <| Literal <| Vars n s) :=
  let matCubes := matrixCubes n s
  let lastColsCubes := lastColsCubes n s

  let allCubes := matCubes.prod lastColsCubes

  allCubes.filter (·.size > 0)

end Cubes
