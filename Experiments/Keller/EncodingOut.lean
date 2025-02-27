/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.Encoding

import Trestle.Solver.IncCNF

import Cli

open Keller Trestle Cli

open Solver.Dimacs in
def formatSRLine (c : IClause) (pivot : ILit) (true_lits : List ILit) (substs : List (IVar × ILit)) : String :=
  s!"{c.toList.map formatLit |> String.intercalate " "} " ++
  s!"{formatLit pivot} {true_lits.map formatLit |> String.intercalate " "} " ++
  s!"{formatLit pivot} {substs.map (fun (v,l) => s!"{formatVar v} {formatLit l}") ++ ["0"] |> String.intercalate " "}"

def cnfCmd := `[Cli|
  "cnf" VIA runCnfCmd;
  "Generates a CNF whose unsatisfiability is equivalent to
  the Keller conjecture on Keller graph G_n,s.

  This command can output 3 files: CNF, SR, and cube.
  The CNF is proven equivalent to Keller conjecture on n,s.
  Then, the DSR proof provides significant further symmetry breaking,
  which can be mechanically verified by a DSR checker.
  Finally, the cube file provides a good cube split to speed up solving
  the formula with all symmetry breaking clauses."

  FLAGS:
    cnf  : String;   "File path to output CNF."
    dsr  : String;   "File path to output DSR proof."
    cube : String;   "File path to output cube file."

  ARGS:
    n : Nat;         "# dimensions of the Keller graph."
    s : Nat;         "# colors available."
]
where runCnfCmd (p : Parsed) := do
  let n := p.positionalArg! "n" |>.as! Nat
  let s := p.positionalArg! "s" |>.as! Nat
  let cnfFileArg := p.flag? "cnf" |>.map (·.as! String)
  let dsrFileArg := p.flag? "dsr" |>.map (·.as! String)
  let cubeFileArg := p.flag? "cube" |>.map (·.as! String)

  IO.println s!"encoding G_{n}_{s}"
  let {cnf, vMap, vNames, ..} :=
    Encode.EncCNF.runUnit (Encoding.fullEncoding n s)
    (names := List.flatten <| List.flatten <|
      .ofFn fun (i : Fin (2^n)) => .ofFn fun (j : Fin n) => .ofFn fun (k : Fin s) =>
      (Encoding.Vars.x i j k, s!"x{i},{j},{k}"))

  if let some cnfFile := cnfFileArg then
    IO.println s!"writing CNF to {cnfFile}"
    IO.FS.withFile cnfFile .write <| fun handle => do
      Solver.Dimacs.printRichCnf (handle.putStr) cnf
      handle.flush

  if let some dsrFile := dsrFileArg then
    IO.println s!"calculating reverse variable map"
    let avMap : Encoding.AllVars n s → IVar :=
      let revMap : Batteries.RBMap String IVar compare :=
        vNames.foldl (init := Batteries.RBMap.empty) (fun acc var name => acc.insert name var)
      fun v =>
        match revMap.find? (toString v) with
        | some k => k
        | none => panic! s!"reverse variable map does not include \"{toString v}\""
    IO.println s!"calculating SR lines..."
    let sr := Encoding.SR.all n s
    IO.println s!"writing DSR proof to {dsrFile}"
    IO.FS.withFile dsrFile .write <| fun handle => do
      for {c, pivot, true_lits, substs} in sr do
        let line := formatSRLine
            (c := c.map _ avMap)
            (pivot := LitVar.map avMap pivot)
            (true_lits := true_lits.map (LitVar.map avMap))
            (substs := substs.map (fun (v,l) => (avMap v, LitVar.map avMap l)))
        handle.putStrLn line
      handle.flush

  if let some cubeFile := cubeFileArg then
    IO.println s!"calculating cubes..."
    let cubes := Encoding.Cubes.allCubes |>.map (·.map _ vMap)
    IO.println s!"writing cubes to {cubeFile}"
    IO.FS.withFile cubeFile .write <| fun handle => do
      Solver.Dimacs.printCubes handle.putStr cubes
      handle.flush

  return 0

def filterCoreCmd : Cmd := `[Cli|
  "filter-core" VIA run;
  "Filter one CNF by another (usually the unsat core)."

  FLAGS:
    full : String;    "Filepath to full CNF."
    core : String;    "Filepath to the CNF on which to filter (usually unsat core)."
    out : String;     "Filepath to the output."
]
where run (p : Parsed) := do
  let fullFile : System.FilePath := p.flag! "full" |>.as! String
  let coreFile : System.FilePath := p.flag! "core" |>.as! String
  let outFile  : System.FilePath := p.flag! "out"  |>.as! String

  let {clauses := full, ..} ← IO.ofExcept <|
    Solver.Dimacs.parseFormula (← IO.FS.readFile fullFile)
  let {clauses := core, ..} ← IO.ofExcept <|
    Solver.Dimacs.parseFormula (← IO.FS.readFile coreFile)

  let coreSet := core.foldl (init := Std.HashSet.empty (capacity := 200000))
    (fun set line =>
      match line with
      | .clause clause =>
        let clause := clause.sortDedup (α := Subtype (α := Int) _)
        set.insert clause
      | _ => set)

  let filtered : RichCnf := full.filter (fun
    | .clause c => coreSet.contains (c.sortDedup (α := Subtype (α := Int) _))
    | _ => true)

  IO.FS.withFile outFile .write fun handle =>
    Solver.Dimacs.printRichCnf handle.putStr filtered

  return 0


def kellerCmd : Cmd := `[Cli|
  keller VIA run; ["0.0.1"]
  "Keller conjecture SAT encoding tools."

  SUBCOMMANDS:
    cnfCmd;
    filterCoreCmd
]
where run (p) := do
  Parsed.printHelp p
  return 0

def main (args : List String) : IO UInt32 :=
  kellerCmd.validate args
