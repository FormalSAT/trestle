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

lean_lib Experiments {
  globs := #[.submodules `Experiments]
}

lean_exe keller {
  root := `Experiments.Keller.EncodingOut
  --moreLeancArgs := #["-UNDEBUG", "-Og", "-ggdb", "-g3", "-fno-omit-frame-pointer"]
}

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.17.0"
require Cli from git "https://github.com/leanprover/lean4-cli" @ "v4.17.0"
