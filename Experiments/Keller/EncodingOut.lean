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
  "Generates a CNF whose unsatisfiability is equivalent to
  the Keller conjecture on Keller graph G_n,s."

  FLAGS:
    inc;        "Output an incremental CNF (inccnf) with good cube split."
    cube : Nat; "Output a CNF with the i'th cube from --inc."

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
  let cube := p.flag? "cube" |>.map (·.as! Nat)

  let inccnf ← do
    if inc && cube.isSome then
      IO.println "--inc flag ignored because --cube is set"
      pure false
    else
      pure inc

  IO.println s!"encoding G_{n}_{s}"
  let ((), {cnf, vMap, ..}) := Encoding.fullEncoding n s |>.run
  if inccnf then
    let cubes ← (do
      IO.println s!"calculating cubes..."
      return Encoding.allCubes
    )
    let cubes := cubes.map (·.map _ vMap)
    IO.println s!"writing incremental CNF to {file}"
    IO.FS.withFile file .write <| fun handle => do
      Solver.Dimacs.printIncCNF (handle.putStr) cnf.toICnf cubes
      handle.flush
  else
    let cube ← cube.bindM (fun idx => do
      let cubes ← (do
        IO.println s!"calculating cubes..."
        return Encoding.allCubes
      )
      if h : idx < cubes.length then
        return some <| cubes[idx].map ILit vMap
      else
        IO.println s!"Cube index {idx} out of bounds! ({cubes.length} cubes)"
        return none
    )
    IO.println s!"writing CNF to {file}"
    let cnf :=
      match cube with
      | none => cnf
      | some cube =>
        (show Array _ from cnf) ++ Array.map (RichCnf.Line.clause #[·]) cube
    IO.FS.withFile file .write <| fun handle => do
      Solver.Dimacs.printRichCnf (handle.putStr) cnf
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


-- #eval show IO _ from do
--   let cnf ← IO.FS.readFile "full.cnf"
--   let {clauses := full, ..} ← IO.ofExcept <| Solver.Dimacs.parseFormula cnf
--   let cnf ← IO.FS.readFile "combinedCores.cnf"
--   let {clauses := cores, ..} ← IO.ofExcept <| Solver.Dimacs.parseFormula cnf
--   let coreSet := cores.foldl (init := Std.HashSet.empty (capacity := 200000))
--     (fun set clause =>
--       let clause := clause.sortDedup (α := Subtype (α := Int) _)
--       set.insert clause)
--
--   IO.FS.withFile "full_in_core.cnf" .write fun handle =>
--     for clause in full do
--       if coreSet.contains <| clause.sortDedup (α := Subtype (α := Int) _) then
--         handle.putStrLn <| Solver.Dimacs.formatClause clause
