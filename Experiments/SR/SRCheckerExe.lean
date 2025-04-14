import Experiments.SR.SRChecker
import Experiments.SR.Parsing.SRParser

open Trestle Parsing SRParser

def printUsage : IO Unit := do
  IO.println "Usage: ./SRCheckerExe <cnf> <pf> [c]"
  IO.println ""
  IO.println "where"
  IO.println ""
  IO.println "  <cnf>: file path to the CNF file."
  IO.println "  <pf>:  file path to the LSR proof file."
  IO.println "  [c]:   optional option to indicate a compressed binary LSR file."
  IO.println ""
  IO.println "If no command-line arguments are given, prints this help message."

partial def main : List String → IO Unit
  | [] => printUsage
  | [_] => printUsage
  | [cnfFile, lsrFile] => do

    let cnfContents ← IO.FS.withFile cnfFile .read (·.readBinToEnd)
    if hc : cnfContents.size ≥ USize.size then
      IO.println "c CNF file too large"
      return
    else
      let (F, nVars) ← IO.ofExcept <|
        SRParser.parseFormula ⟨cnfContents, Nat.not_le.mp hc⟩ (RangeArray.empty : RangeArray ILit)

      let bytes ← IO.FS.withFile lsrFile .read (·.readBinToEnd)
      if h_lsr : bytes.size ≥ USize.size then
        IO.println "c LSR file too large"
        return
      else

      let bytes : ByteArray' := ⟨bytes, Nat.not_le.mp h_lsr⟩
      let size := bytes.val.size.toUSize
      let τ := PPA.new (nVars * 2)
      let σ := PS.new (nVars * 2)
      let iter : USize := 0

      let rec loop (iter : USize) : SR.SRState → Except Bool (SR.SRState × USize)
      | ⟨F, τ, σ⟩ => do
        if iter < size then
          -- Parse a new line
          let ⟨lineId, iter⟩ := ByteArray.readNat bytes iter
          let iter := ByteArray.ws bytes iter
          let ch := ByteArray.peekc bytes iter
          -- 'd' = 100 in ASCII
          if ch = 100 then
            let iter := ByteArray.skip bytes iter
            match parseDeletionLine bytes iter with
            | .error _ => .error false
            | .ok ⟨clauseIds, iter⟩ =>
              match SR.consumeDeletionLine F clauseIds with
              | .error _ => .error false
              | .ok F => loop iter ⟨F, τ, σ⟩
          else
            let F := Formula.commitClauseUntil F (lineId - 1)
            match parseLSRAdditionLine F bytes iter with
            | .error _ => .error false
            | .ok ⟨iter, F, line⟩ =>
              match SR.checkLine ⟨F, τ, σ⟩ line with
              | .error b => .error b
              | .ok ⟨F, τ, σ⟩ => loop iter ⟨F, τ, σ⟩
        else
          .ok (⟨F, τ, σ⟩, iter)

      match loop iter ⟨F, τ, σ⟩ with
      | .ok _ =>
        IO.println "c Proof is valid, but did not derive the empty clause."
        IO.println "s VALID"
      | .error true => do
        IO.println "c Proof derived the empty clause"
        IO.println "s VERIFIED UNSAT"
      | .error false => do
        IO.println "c Error or invalid proof"
        IO.println "s INVALID"

  | _ => printUsage
