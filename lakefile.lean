import Lake
open Lake DSL

package «lean-sat»

@[default_target]
lean_lib LeanSAT

@[default_target]
lean_lib Examples
lean_exe run_examples {
  root := `Examples
}

-- Note: `std` is not required so that Lake selects a version matching mathlib.
require waterfall from git "http://github.com/JamesGallicchio/waterfall.git" @ "main"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "master"
