import Lake
open Lake DSL

package «lean-sat»

@[default_target]
lean_lib LeanSAT

lean_lib Examples
lean_exe run_examples {
  root := `Examples
}

require std from git "http://github.com/leanprover/std4.git" @ "main"
require waterfall from git "http://github.com/JamesGallicchio/waterfall.git" @ "main"
