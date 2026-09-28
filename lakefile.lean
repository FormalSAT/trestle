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

/-- Extra include paths for compiling the FFI bridges with `leanc`.

  `leanc` is the Lean's own C compiler, so it always builds for the toolchain's
  architecture -- unlike the system `cc`, which builds for the *host*'s
  architecture and breaks whenever the two differ (e.g. `x86_64` under
  Rosetta on Apple ARM silicon).

  The problem is that `leanc` passes `-nostdinc`, which omits the headers for
  the C standard library. On Linux and Windows the toolchain ships its own
  libc headers, but on macOS the headers live in the Xcode SDK, so they
  have to be added back manually. This function does that.
-/
def ffiIncludeArgs : IO (Array String) := do
  unless System.Platform.isOSX do return #[]
  let sdk ← match ← IO.getEnv "SDKROOT" with
    | some sdk => pure sdk
    | none => do
      let out ← IO.Process.output { cmd := "xcrun", args := #["--show-sdk-path"] }
      pure ((out.stdout.splitOn "\n").head?.getD "")
  if sdk.isEmpty then
    error "could not locate the macOS SDK; set SDKROOT or install Xcode command line tools"
  return #["-isystem", sdk ++ "/usr/include"]

target byte_array_ffi_defs.o pkg : FilePath := do
  let srcJob ← byte_array_ffi_defs.c.fetch
  let oFile := pkg.buildDir / "c" / "byte_array_ffi_defs.o"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString] ++ (← ffiIncludeArgs)
  buildO oFile srcJob weakArgs #["-fPIC"] "leanc" getLeanTrace

target uint_ffi_defs.o pkg : FilePath := do
  let srcJob ← uint_ffi_defs.c.fetch
  let oFile := pkg.buildDir / "c" / "uint_ffi_defs.o"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString] ++ (← ffiIncludeArgs)
  buildO oFile srcJob weakArgs #["-fPIC"] "leanc" getLeanTrace

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

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.33.1"
require Cli from git "https://github.com/leanprover/lean4-cli" @ "v4.33.0"
