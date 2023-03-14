import LeanSAT.Solver.Basic
import LeanSAT.Solver.Dimacs

namespace LeanSAT.Solver.Impl


/-- Command-line ApproxMC solver 

Lives in IO, since we need access to process invocation.
-/
def ApproxMCCommand
  (cmd : String := "approxmc") (flags : List String := []) : ApproxModelCount IO :=
  ⟨fun fml sampleSet => do
  let child ← IO.Process.spawn {
    cmd := cmd
    args := flags.toArray
    stdin := .piped
    stdout := .piped
  }
  let (stdin, child) ← child.takeStdin
  for sampleSet in sampleSet do
    stdin.putStrLn <| "c ind " ++
      (sampleSet.map Dimacs.formatVar ++ ["0"] |> String.intercalate " ")
  Dimacs.printFormula (stdin.putStr) fml
  stdin.flush
  let output ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  match ←child.wait with
  | 0 =>
    let outputStr ← IO.ofExcept output.get
    IO.ofExcept <| parseOutput outputStr
  | x =>
    IO.ofExcept <| .error s!"Non-zero return code ({x}) from command {cmd}:\n{output.get}"
  ⟩
where
  parseOutput (s : String) : Except String ApproxModelCount.Res := do
    let lines :=
      s.splitOn "\n"
      |>.filter (fun line => !line.startsWith "c" && line.any (!·.isWhitespace))
    match lines with
    | [] => .error s!"Expected outcome, got `{s}`"
    | satRes :: rest =>
    match satRes with
    | "s UNSATISFIABLE" =>
      return ⟨0,2,0⟩
    | "s SATISFIABLE" =>
      match rest with
      | [] | _ :: _ :: _ =>
        .error s!"Expected one content line after `s SATISFIABLE`, got `{rest}`"
      | [res] =>
      if !res.startsWith "s mc " then
        .error s!"Expected `s mc <count>`, got `{s}`"
      else
      let number := res.drop 5 |>.trim
      return ⟨← (number.toNat?.expectSome fun () => s!"Expected number, got {number}"), 2, 0⟩
    | _ => .error s!"Expected `s [UN]SATISFIABLE`, got {satRes}"
