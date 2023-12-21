import Lake
open Lake DSL

package «lean-sat» where
  moreLinkArgs := #["-L./.lake/packages/LeanCopilot/.lake/build/lib", "-lctranslate2"]

-- Note: `std` is not required so that Lake selects a version matching mathlib.
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "master"

require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot" @ "v1.0.0"
require Duper from git "https://github.com/leanprover-community/duper.git" @ "v0.0.5"

@[default_target]
lean_lib LeanSAT

@[default_target]
lean_lib Examples
lean_exe run_examples {
  root := `Examples
}
