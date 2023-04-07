import LeanSAT.Solver.Basic
import LeanSAT.Solver.Dimacs

namespace LeanSAT.Solver.Impl


/-- Command-line CMSGen solver

Lives in IO, since we need access to process invocation.
-/
def UniGenCommand
  (cmd : String := "unigen") (flags : List String := []) : ModelSample IO :=
  ⟨fun fml count => do
  let child ← IO.Process.spawn {
    cmd := cmd
    args := flags.toArray ++ #[
      "--samples", toString count]
    stdin := .piped
    stdout := .piped
  }
  let (stdin, child) ← child.takeStdin
  Dimacs.printFormula (stdin.putStr) fml
  stdin.flush
  let output ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let _ ← child.wait
  let sampleOutput ← IO.ofExcept output.get
  IO.ofExcept <| parseOutput sampleOutput
  ⟩
where
  parseOutput (s : String) : Except String (List Assn) := do
    let assns ←
      s.splitOn "\n"
      |>.filter (fun line => !line.startsWith "c" && !line.all (·.isWhitespace))
      |>.mapM (fun line =>
        line.splitOn " "
        |>.mapM (fun num => do
          let i ← num.toInt?.expectSome fun () =>
            s!"Expected number, got {num} in line `{line}`"
          if i < 0 then
            return (i.natAbs, false)
          else
            return (i.natAbs, true)
        ))
    return assns.map (fun list => Std.HashMap.ofList list)
