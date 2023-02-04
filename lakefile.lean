import Lake
open Lake DSL

package «lean-sat»

@[default_target]
lean_lib LeanSAT

lean_lib Examples
lean_exe run_examples {
  root := `Examples
}

require Std from git "http://github.com/leanprover/std4.git"@"main"

