import Lake
open System Lake DSL

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

-- lean_lib ByteArrayFFI {
--   globs := #[.submodules `Experiments.SR.Data.]
-- }

input_file byte_array_ffi_defs.c where
  path := "Experiments" / "SR" / "Data" / "ByteArray" / "FFI" / "byte_array_ffi_defs.c"
  text := true

input_file uint_ffi_defs.c where
  path := "Experiments" / "SR" / "Data" / "UInt" / "FFI" / "uint_ffi_defs.c"
  text := true

target byte_array_ffi_defs.o pkg : FilePath := do
  let srcJob ← byte_array_ffi_defs.c.fetch
  let oFile := pkg.buildDir / "c" / "byte_array_ffi_defs.o"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC"] "cc" getLeanTrace

target uint_ffi_defs.o pkg : FilePath := do
  let srcJob ← uint_ffi_defs.c.fetch
  let oFile := pkg.buildDir / "c" / "uint_ffi_defs.o"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC"] "cc" getLeanTrace

target libleanffi_static pkg : FilePath := do
  let ba_ffiO ← byte_array_ffi_defs.o.fetch
  let uint_ffiO ← uint_ffi_defs.o.fetch
  let name := nameToStaticLib "leanffi"
  buildStaticLib (pkg.staticLibDir / name) #[ba_ffiO, uint_ffiO]

lean_exe srcheck {
  root := `Experiments.SR.Main
  moreLinkObjs := #[libleanffi_static]
}

lean_exe test {
  root := `Test
}

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.28.0"
require Cli from git "https://github.com/leanprover/lean4-cli" @ "v4.28.0"
