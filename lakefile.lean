import Lake
open Lake DSL

package «trestle»

@[default_target]
lean_lib Trestle {
  globs := #[.andSubmodules `Trestle]
}

lean_lib Examples {
  globs := #[.submodules `Examples]
}

/- In the command line you can run the examples with
`lake exe Examples.<whatever>`
-/
lean_exe Examples.ApproxMC
lean_exe Examples.Cadical
lean_exe Examples.CakeLPR
lean_exe Examples.GraphColoring
lean_exe Examples.PigeonHole


lean_lib Experiments {
  globs := #[.submodules `Experiments]
}

lean_exe keller {
  root := `Experiments.Keller.EncodingOut
  --moreLeancArgs := #["-UNDEBUG", "-Og", "-ggdb", "-g3", "-fno-omit-frame-pointer"]
}

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.15.0"
require Cli from git "https://github.com/leanprover/lean4-cli" @ "v4.15.0"
