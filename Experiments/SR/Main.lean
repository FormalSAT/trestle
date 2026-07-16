import Experiments.SR.Checker.SRChecker
import Experiments.SR.Parsing.SRParser

open Trestle Parsing SRParser

def ASCII_D : UInt8 := 100
def ASCII_D32 : UInt32 := 100

def printUsage : IO Unit := do
  IO.println "Usage: ./SRCheckerExe <cnf> <pf> [-c] [-b]"
  IO.println ""
  IO.println "where"
  IO.println ""
  IO.println "  <cnf>  file path to the CNF file."
  IO.println "  <pf>   file path to the LSR proof file."
--  IO.println "  [-c]   optional option to indicate a compressed binary LSR file."
  IO.println "  [-b]   buffers parsing files, rather than read all in memory."
  IO.println ""
  IO.println "If no command-line arguments are given, prints this help message."

def parseCnfIf (cnfFile : System.FilePath) (buffered : Bool) : IO (RangeArray ILit × Nat) := do
  if buffered then
    let bs : BStream ← BStream.ofFilePath cnfFile
    parseCnfBS bs (RangeArray.empty : RangeArray ILit)
  else
    let cnfContents ← IO.FS.withFile cnfFile .read (·.readBinToEnd)
    IO.ofExcept <| parseCnf cnfContents (RangeArray.empty : RangeArray ILit)

partial def parseAndCheckBS (bs : BStream) (st : SR.SRState) : IO (Except Bool Unit) := do
  match st with
  | ⟨F, τ, σ⟩ => do
    let (_, bs) ← BStream.ws bs
    let (ch, bs) ← BStream.peek bs
    if ch = EOF then
      return .ok ()
    else
      let (lineId, bs) ← BStream.readNat bs
      let (_, bs) ← BStream.ws bs
      let (ch, bs) ← BStream.peek bs
      if ch = ASCII_D32 then
        let (_, bs) ← BStream.getc bs
        let ⟨clauseIds, bs⟩ ← parseDeletionLineBS (acc := #[]) bs
        match SR.consumeDeletionLine F clauseIds with
        | .error _ => return .error false
        | .ok F => parseAndCheckBS bs ⟨F, τ, σ⟩
      else
        let F := Formula.commitClauseUntil F (lineId - 1)
        let ⟨⟨F, line⟩, bs⟩ ← parseLSRAdditionLineBS F bs
        match SR.checkLine ⟨F, τ, σ⟩ line with
        | .error b => return .error b
        | .ok ⟨F, τ, σ⟩ => parseAndCheckBS bs ⟨F, τ, σ⟩

-- Checks, line by line
partial def parseAndCheck (bytes : ByteArray) (iter : USize := 0) (st : SR.SRState) : Except Bool Unit := do
  match st with
  | ⟨F, τ, σ⟩ => do
    if iter < bytes.size.toUSize then
      -- Parse a new line
      let ⟨lineId, iter⟩ := ByteArray.readNat bytes iter
      let iter := ByteArray.ws bytes iter
      let ch := ByteArray.peek bytes iter
      if ch = ASCII_D then
        let iter := ByteArray.token bytes iter
        match parseDeletionLine bytes iter with
        | .error _ => .error false
        | .ok ⟨clauseIds, iter⟩ =>
          match SR.consumeDeletionLine F clauseIds with
          | .error _ => .error false
          | .ok F => parseAndCheck bytes iter ⟨F, τ, σ⟩
      else
        let F := Formula.commitClauseUntil F (lineId - 1)
        match parseLSRAdditionLine F bytes iter with
        | .error _ => .error false
        | .ok ⟨iter, F, line⟩ =>
          match SR.checkLine ⟨F, τ, σ⟩ line with
          | .error b => .error b
          | .ok ⟨F, τ, σ⟩ => parseAndCheck bytes iter ⟨F, τ, σ⟩
    else
      .ok ()

partial def main : List String → IO Unit
  | [] => printUsage
  | [_] => printUsage
  | (cnfFile :: lsrFile :: options) => do

    let buffered := options.contains "-b"

    let (F, nVars) ← parseCnfIf cnfFile buffered
    let τ := PPA.new (nVars * 2)
    let σ := PS.new (nVars * 2)

    let result ← (do
      if buffered then
        let bs ← BStream.ofFilePath lsrFile
        parseAndCheckBS bs ⟨F, τ, σ⟩
      else
        let bytes ← IO.FS.withFile lsrFile .read (·.readBinToEnd)
        return parseAndCheck bytes 0 ⟨F, τ, σ⟩
    )

    match result with
    | .ok _ =>
      IO.println "c Proof is valid, but did not derive the empty clause."
      IO.println "s VALID"
    | .error true => do
      IO.println "c Proof derived the empty clause"
      IO.println "s VERIFIED UNSAT"
    | .error false => do
      IO.println "c Error or invalid proof"
      IO.println "s INVALID"
