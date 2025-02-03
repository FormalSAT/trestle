/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.Encoding

import Trestle.Solver.IncCNF

import Cli

open Keller Trestle Cli

def cnfCmd := `[Cli|
  "cnf" VIA runCnfCmd;
  "testCmd provides another example for a subcommand without flags or arguments that does nothing."

  FLAGS:
    inc;    "Output an incremental CNF (inccnf) with good cube split."

  ARGS:
    n : Nat;         "# dimensions of the Keller graph."
    s : Nat;         "# colors available."
    file : String;      "File path to output CNF."
]
where runCnfCmd (p : Parsed) := do
  let n := p.positionalArg! "n" |>.as! Nat
  let s := p.positionalArg! "s" |>.as! Nat
  let file := p.positionalArg! "file" |>.as! String
  let inc := p.hasFlag "inc"

  IO.println s!"encoding G_{n}_{s}"
  let ((), {cnf, vMap, ..}) := Encoding.fullEncoding n s |>.run
  if inc then
    let cubes ← (do
      IO.println s!"calculating cubes..."
      if h : n ≥ 5 ∧ s ≥ 4 then
        pure <| Encoding.symmBreakCubes (n := n) (s := s) h.1 h.2
      else pure []
    )
    let cubes := cubes.map (·.map _ vMap)
    IO.println s!"writing incremental CNF to {file}"
    IO.FS.withFile file .write <| fun handle => do
      Solver.Dimacs.printIncCNF (handle.putStr) cnf cubes
      handle.flush
  else
    IO.println s!"writing CNF to {file}"
    IO.FS.withFile file .write <| fun handle => do
      Solver.Dimacs.printFormula (handle.putStr) cnf
      handle.flush
  return 0

def kellerCmd : Cmd := `[Cli|
  keller NOOP; ["0.0.1"]
  "Keller conjecture SAT encoding formalization output."

  SUBCOMMANDS:
    cnfCmd

]

def main (args : List String) := show IO _ from do
  kellerCmd.validate args
