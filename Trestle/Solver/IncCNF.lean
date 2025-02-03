/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Trestle.Solver.Dimacs

namespace Trestle.Solver.Dimacs

def printIncCNF [Monad m] (print : String → m Unit) (fml : ICnf) (cubes : List IClause) : m Unit := do
  print <| s!"p inccnf\n"
  for c in fml do
    print <| formatClause c ++ "\n"
  for cube in cubes do
    print <| "a " ++ formatClause cube ++ "\n"
