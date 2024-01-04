import Lake
open Lake DSL

package LeanSAT

-- Note: `std` is not required so that Lake selects a version matching mathlib.
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
lean_lib LeanSAT

@[default_target]
lean_lib Examples
lean_exe run_examples {
  root := `Examples
}
