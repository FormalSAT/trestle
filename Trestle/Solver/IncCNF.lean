/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Trestle.Solver.Dimacs

namespace Trestle.Solver.Dimacs

def parseCube (maxVar : Nat) (s : String) : Except String ICube := do
  if s.startsWith "a " then
    parseClause maxVar <| s.drop 2
  else
    .error s!"expected cube, but does not start with `a `: {s}"

def parseCubes (maxVar : Nat) (s : String) : Except String (List ICube) :=
  s.splitOn "\n"
  |>.map (·.trim)
  |>.filter (!·.isEmpty)
  |>.mapM (parseCube maxVar)

def printCubes [Monad m] (print : String → m Unit) (cubes : List IClause) : m Unit := do
  for cube in cubes do
    print <| "a " ++ formatClause cube ++ "\n"

def printIncCNF [Monad m] (print : String → m Unit) (fml : ICnf) (cubes : List IClause) : m Unit := do
  print <| s!"p inccnf\n"
  for c in fml do
    print <| formatClause c ++ "\n"
  printCubes print cubes
