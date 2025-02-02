/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.Encoding

import Trestle.Data.HashAssn

open Keller Trestle

def main (args : List String) := show IO _ from do
  if args.length < 3 then
    IO.println "command arguments: <n> <s> <cnf file>"
    return
  let n := args[0]!.toNat!
  let s := args[1]!.toNat!
  let file := args[2]!
  IO.println s!"encoding G_{n}_{s}"
  let enc := Encoding.fullEncoding n s |>.toICnf
  let () ← IO.FS.withFile file .write <| fun handle => do
    Solver.Dimacs.printFormula (handle.putStr) enc
    handle.flush
