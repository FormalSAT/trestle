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
  root := `Experiments.Keller.Main
  --moreLeancArgs := #["-UNDEBUG", "-Og", "-ggdb", "-g3", "-fno-omit-frame-pointer"]
}

lean_exe srcheck {
  root := `Experiments.SR.Main
}

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.18.0"
require Cli from git "https://github.com/leanprover/lean4-cli" @ "v4.18.0"
