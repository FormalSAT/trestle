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

lean_exe keller {
  root := `Experiments.Keller.Encoding
}

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.15.0"
