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

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "584f39cda63a699d6f7e417321885d5e452aa304"
