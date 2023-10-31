import LeanSAT.Solver.Basic
import LeanSAT.Solver.Dimacs

namespace LeanSAT.Solver.Impl


/-- Command-line CMSGen solver

Lives in IO, since we need access to process invocation.
-/
def UniGenCommand
  (cmd : String := "unigen") (flags : List String := []) : ModelSample IO :=
  ⟨fun fml sampleSet count => do
  let child ← IO.Process.spawn {
    cmd := cmd
    args := flags.toArray ++ #[
      "--samples", toString count]
    stdin := .piped
    stdout := .piped
  }
  let (stdin, child) ← child.takeStdin
  for sampleSet in sampleSet do
    stdin.putStrLn (["c", "ind"] ++ sampleSet.map Dimacs.formatVar ++ ["0"] |> String.intercalate " ")
  Dimacs.printFormula (stdin.putStr) fml
  stdin.flush
  let output ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let _ ← child.wait
  let sampleOutput ← IO.ofExcept output.get
  IO.ofExcept <| Dimacs.parseAssnLines (fml.maxBy (·.maxBy (LitVar.toVar · |>.val) |>.getD 0) |>.getD 0) sampleOutput
  ⟩
