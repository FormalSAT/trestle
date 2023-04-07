import LeanSAT.Solver.Basic
import LeanSAT.Solver.Dimacs

namespace LeanSAT.Solver.Impl


/-- Command-line CMSGen solver

Lives in IO, since we need access to process invocation.
-/
def CMSGenCommand
  (cmd : String := "cmsgen") (flags : List String := []) : ModelSample IO :=
  ⟨fun fml count =>
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
  match ←child.wait with
  | 0 =>
    let sampleOutput ← IO.FS.readFile temp
    IO.ofExcept <| parseOutput sampleOutput
  | x =>
    let output ← child.stdout.readToEnd
    IO.ofExcept <| .error
      s!"Non-zero return code ({x}) from command {cmd}:\n{output}"
  )⟩
where
  parseOutput (s : String) : Except String (List Assn) := do
    let assns ←
      s.splitOn "\n"
      |>.mapM (fun line =>
        line.splitOn " "
        |>.mapM (fun num => do
          let i ← num.toInt?.expectSome fun () =>
            s!"Expected number, got {num}"
          if i < 0 then
            return (i.natAbs, false)
          else
            return (i.natAbs, true)
        ))
    return assns.map (fun list => Std.HashMap.ofList list)
