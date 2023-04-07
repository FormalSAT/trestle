import LeanSAT.Solver.Basic
import LeanSAT.Solver.Dimacs

namespace LeanSAT.Solver.Impl


/-- Command-line CMSGen solver

Lives in IO, since we need access to process invocation.
-/
def CMSGenCommand
  (cmd : String := "cmsgen") (flags : List String := []) : ModelSample IO :=
  ⟨fun fml sampleSet count =>
  if sampleSet.isSome then panic! "cmsgen does not support sample sets" else
  IO.FS.withTempFile (fun temp => do
  let child ← IO.Process.spawn {
    cmd := cmd
    args := flags.toArray ++ #[
      "--samplefile", temp.toString,
      "--samples", toString count]
    stdin := .piped
    stdout := .piped
  }
  let (stdin, child) ← child.takeStdin
  Dimacs.printFormula (stdin.putStr) fml
  stdin.flush
  let _ ← child.wait
  
  let sampleOutput ← IO.FS.readFile temp
  IO.ofExcept <| Dimacs.parseAssnLines fml.numVars sampleOutput
  )⟩
