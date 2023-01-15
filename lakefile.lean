import Lake
open Lake DSL

elab "#currDir" : term =>
  open Lean Elab in do
  return mkLit <| .strVal <| (← IO.currentDir).toString

def rootDir : FilePath := #currDir

/-- The directory where cadical submodule is -/
def cadicalDir := rootDir / "cadical"

/-- The directory where lean-llvm source is -/
def leanLlvmDir := rootDir / "lean-llvm"


package «lean-sat» {
  moreLeancArgs := #[ "--verbose" ]
  moreLinkArgs := #[
    "-L" ++ (cadicalDir / "build").toString,
    "-I" ++ (cadicalDir / "src").toString,
    "-lcadical"]
}

target leancadical.o (pkg : Package) : FilePath := do
  let oFile := pkg.buildDir / "c" / "leancadical.o"
  let srcFile ← inputFile <| pkg.dir / "ffi" / "leancadical.c"
  buildFileAfterDep oFile srcFile fun srcFile => do
    let flags := #[
      "-I" ++ (← getLeanIncludeDir).toString,
      "-I" ++ (cadicalDir / "src").toString,
      "-O3", "-fPIC"]
    compileO "leancadical.c" oFile srcFile flags "clang"


extern_lib libleancadical (pkg : Package) := do
  let libcadicalFile := cadicalDir / "build" / "libcadical.a"
  if not <| ← libcadicalFile.pathExists then
    initSubmodules
    buildCadical

  -- copy libcadical.so into build/lib
  IO.FS.createDirAll (pkg.buildDir / "lib")
  proc {
    cmd := "cp"
    args := #[
      libcadicalFile.toString,
      (pkg.buildDir / "lib" / "libcadical.a").toString ]
  }

  let name := nameToStaticLib "leancadical"
  let ffiO ← fetch <| pkg.target ``leancadical.o
  buildStaticLib (pkg.buildDir / "lib" / name) #[ffiO]
where
  initSubmodules : IO Unit := do
    let child ← IO.Process.spawn {
      cmd := "git"
      args := #["submodule", "update", "--init", "--recursive"]
    }
    if (← child.wait) ≠ 0 then
      throw <| .mkOtherError 1 s!"Error initializing LeanSAT subodules, aborting"

  buildCadical : IndexBuildM Unit := do  
    IO.println "Configuring cadical makefile..."
    let ⟨errNo, stdout, stderr⟩ ← IO.Process.output {
      cmd := s!"./configure"
      args := #["-fPIC"]
      env := #[ ("CXX", (rootDir / "clang++").toString) ]
      cwd := cadicalDir
    }
    if errNo > 0 then
      error s!"Error configuring cadical makefiles:\n{stdout}\n{stderr}"

    IO.println "Building cadical..."
    let ⟨errNo, stdout, stderr⟩ ← IO.Process.output {
      cmd := "make"
      cwd := cadicalDir
    }
    if errNo > 0 then
      error s!"Error building cadical:\n{stdout}\n{stderr}"

@[default_target]
lean_lib LeanSAT

lean_lib Examples
lean_exe run_examples {
  root := `Examples
}

require Std from git "http://github.com/leanprover/std4.git"@"main"
require Mathlib from git "http://github.com/leanprover-community/mathlib4.git"@"master"

