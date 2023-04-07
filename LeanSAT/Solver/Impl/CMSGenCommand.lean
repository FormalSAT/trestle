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
  IO.ofExcept <| parseOutput sampleOutput
  )⟩
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
