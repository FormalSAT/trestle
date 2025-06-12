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
    matrixList.map fun m =>
      Array.mk <| List.flatten <|
        List.ofFn fun r : Fin 3 => List.ofFn fun c : Fin 3 =>
          let mval : Fin s := @Fin.ofNat' s (by apply NeZero.mk; omega) m.data[r][c]
          .pos (x idxs[r] ⟨2+c, by omega⟩ mval)
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
