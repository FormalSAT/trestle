import LeanSAT.Solver.Basic
import LeanSAT.Solver.Dimacs

namespace LeanSAT.Solver.Impl

/-- Command-line d4 interface.

d4 can perform exact model counting efficiently.

This solver lives in IO, since we need access to process invocation.
-/
def D4Command.ModelCount
  (cmd : String := "d4") (flags : List String := []) : Solver.ModelCount IO :=
  ⟨fun fml vars => do
  if vars.isSome then
    IO.ofExcept (.error "d4 does not support blocking variables (all must be blocking)")

  IO.FS.withTempFile (fun temp => do
    IO.FS.withFile temp .write (fun handle =>
      Dimacs.printFormula handle.putStr fml)
  
    let child ← IO.Process.spawn {
      cmd := cmd
      args := ("-mc" :: flags ++ [temp.toString]).toArray
      stdout := .piped
    }
    let output ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
    let _ ← child.wait
    let outputStr ← IO.ofExcept output.get

    let res ← IO.ofExcept do
      let lines :=
        outputStr.splitOn "\n"
        |>.filter (fun line => !line.startsWith "c" && line.any (!·.isWhitespace))
      match ←(lines.expectNonempty fun () => s!"Expected result, got `{outputStr}`") with
      | ⟨first, _⟩ =>
      match first.take 2 with
      | "s " =>
        let this := first.drop 2
        this.toNat?.expectSome fun () => s!"Expected number, got `{this}`" 
      | _ =>
        .error  "Expected `s <UNSATISFIABLE|SATISFIABLE>`, got `{first}`"
    
    return res
  )⟩
