import Lake
open Lake DSL

package «trestle»

@[default_target]
lean_lib Trestle {
  globs := #[.andSubmodules `Trestle]
}

/- In the command line you can run the examples with
`lake exe Examples.<whatever>`
-/
lean_exe Examples.ApproxMC
lean_exe Examples.Cadical
lean_exe Examples.CakeLPR
lean_exe Examples.GraphColoring
lean_exe Examples.PigeonHole


require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "584f39cda63a699d6f7e417321885d5e452aa304"
