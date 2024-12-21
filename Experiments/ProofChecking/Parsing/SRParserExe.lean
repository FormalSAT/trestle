/-

An executable for `SRParser.lean`.

A simple command-line tool for reading in CNF/LSR files.
What's read is echoed back to `stdout`.

Author: Cayden Codel
Carnegie Mellon University

-/

import Experiments.ProofChecking.Parsing.SRParser
import Experiments.ProofChecking.Parsing.Defs
import Experiments.ProofChecking.RangeArray

import LeanSAT.Data.Cnf
import LeanSAT.Data.ICnf
import LeanSAT.Data.Literal

open LeanSAT LeanSAT.Model Except Parsing

def printUsage : IO Unit := do
  IO.println "Usage: ./SRParserExe <file-path> [cnf | lsr | clsr]"
  IO.println ""
  IO.println "where"
  IO.println ""
  IO.println "  cnf: parses a CNF file."
  IO.println "  lsr: parses an LSR file (default behavior)."
  IO.println "  clsr: parses a compressed binary LSR file."
  IO.println ""
  IO.println "If no command-line arguments are given, prints this help message."
  IO.println "Parses the CNF/LSR file and echoes it to stdout."
  IO.println "Note that the output will be in text format, even if the input is binary."

def echoCnf (filePath : String) : IO Unit := do
  let contents ← IO.FS.withFile filePath .read (·.readToEnd)
  match SRParser.parseFormula contents (RangeArray.empty : RangeArray ILit) with
  | .error str => IO.println str
  | .ok (F, nVars) =>
    IO.println s!"p cnf {nVars} {F.size}"
    Parsing.echoRangeArrayCNF F

def echoLSR (filePath : String) (F : RangeArray ILit) : IO Unit := do
  let t₁ ← IO.monoMsNow
  let contents ← IO.FS.withFile filePath .read (·.readToEnd)
  let lines := contents.splitOn "\n"
  let F ← lines.foldlM (init := F) (fun F line => do
    -- Skip empty lines
    if line.length > 0 then
      match SRParser.parseLSRLine F line with
      | Except.error str =>
        panic! s!"Error encountered: {str}"
      | Except.ok ⟨id, F, pl⟩ =>
        -- Parsing.echoRangeArrayLSRLine F id pl
        return F.commit
    else return F)
  let t₂ ← IO.monoMsNow
  IO.println s!"Number of addition lines parsed: {F.size}"
  IO.println s!"Time taken: {t₂ - t₁} ms"

/-
partial def echoLSRBinary (filePath : String) : IO Unit := do
  let contents ← IO.FS.withFile filePath .read (·.readBinToEnd)
  let rec loop (index : Nat) : IO Unit :=
    if index < contents.size then
      match SRParser.parseLSRLineBinary (RangeArray.empty : RangeArray ILit) contents index with
      | .error str => IO.println str
      | .ok (index, id, F, pl) => do
        IO.print s!"{id} "
        match pl with
        | .inl addLine => echoLSRLine F id addLine
        | .inr delLine =>
          IO.print "d "
          IO.print <| delLine.clauses.foldl (fun str clause => str ++ s!"{clause + 1} ") ""
          IO.println "0"
        loop index
    else
      return
  loop 0 -/

partial def main : List String → IO Unit
  | [] => printUsage
  | filePath :: args => do
    match args with
    | [] => echoLSR filePath (RangeArray.empty)
    | ["cnf"] => echoCnf filePath
    | ["lsr"] => echoLSR filePath (RangeArray.empty)
    -- | ["clsr"] => echoLSRBinary filePath
    | _ => printUsage
