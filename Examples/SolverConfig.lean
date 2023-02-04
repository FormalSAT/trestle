import LeanSAT
open LeanSAT

/-
The examples require at least one solver present, which is
configured here. If you want to use a different solver,
change the instance declaration here and recompile.
-/

instance : Solver IO := Solver.Impl.DimacsCommand "cadical"