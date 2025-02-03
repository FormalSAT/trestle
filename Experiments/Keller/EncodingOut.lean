/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.Encoding

import Trestle.Solver.IncCNF

import Cli

open Keller Trestle

def main (args : List String) := show IO _ from do
  if args.length < 3 then
    IO.println "command arguments: <n> <s> <cnf file>"
    return
  let n := args[0]!.toNat!
  let s := args[1]!.toNat!
  let file := args[2]!
  IO.println s!"encoding G_{n}_{s}"
  let ((), {cnf, vMap, ..}) := Encoding.fullEncoding n s |>.run
  if h : n ≥ 5 ∧ s ≥ 4 then
    let cubes := Encoding.symmBreakCubes (n := n) (s := s) h.1 h.2
    let cubes := cubes.map (·.map _ vMap)
    IO.println s!"writing incremental CNF to {file}"
    let () ← IO.FS.withFile file .write <| fun handle => do
      Solver.Dimacs.printIncCNF (handle.putStr) cnf cubes
      handle.flush
  else
    IO.println s!"writing CNF to {file}"
    let () ← IO.FS.withFile file .write <| fun handle => do
      Solver.Dimacs.printFormula (handle.putStr) cnf
      handle.flush
