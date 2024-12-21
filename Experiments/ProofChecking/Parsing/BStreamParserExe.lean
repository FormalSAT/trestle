import Experiments.ProofChecking.BStream
import Experiments.ProofChecking.RangeArray
import Experiments.ProofChecking.Parsing.Defs
import Experiments.ProofChecking.Parsing.BStreamParser

open LeanSAT LeanSAT.Model ILit Except IO.FS

def printUsage : IO Unit := do
  IO.println "Usage: ./BStreamParser <file_path> [cnf | lsr | clsr]"

def echoCNF (filePath : String) : IO Unit := do
  let bs ← BStream.ofFilePath filePath
  let ((F, nVars), _) ← @BStreamParser.parseFormula (RangeArray ILit) _ _ bs

  IO.println s!"p cnf {nVars} {F.size}"
  Parsing.echoRangeArrayCNF F

@[specialize]
partial def echoLSR (filePath : String) (F : RangeArray ILit) : IO Unit := do
  let bs ← BStream.ofFilePath filePath
  let rec loop (F : RangeArray ILit) : BStreamM (RangeArray ILit):= do
    BStream.ws
    let ch ← BStream.getc
    if ch = EOF then
      return F
    else
      BStream.ungetc ch.toUInt8
      let (lineId, F, line) ← BStreamParser.parseLSRLine F
      --Parsing.echoRangeArrayLSRLine F lineId line
      let F := F.commit
      loop F
  let t₁ ← IO.monoMsNow
  let (F, _) ← loop F bs
  let t₂ ← IO.monoMsNow
  IO.println s!"Number of addition lines parsed: {F.size}"
  IO.println s!"Time taken: {t₂ - t₁} ms"

def echoLSRBinary (filePath : String) : IO Unit := do
  IO.println "Not implemented"

def main : List String → IO Unit
  | [] => printUsage
  | filePath :: args => do
    match args with
    | [] => echoLSR filePath (RangeArray.empty)
    | ["cnf"] => echoCNF filePath
    | ["lsr"] => echoLSR filePath (RangeArray.empty)
    --| ["clsr"] => echoLSRBinary filePath
    | _ => printUsage
