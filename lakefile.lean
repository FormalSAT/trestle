import Lake
open Lake DSL

package «lean-sat»

@[default_target]
lean_lib LeanSAT

lean_lib Examples {
  globs := #[.submodules `Examples]
}

-- Note: `std` is not required so that Lake selects a version matching mathlib.
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "master"
