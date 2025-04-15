/-

A runner for `SRChecker.lean`.

Command-line tool for checking LSR files.

Author: Cayden Codel
Carnegie Mellon University

-/

import Experiments.ProofChecking.Parsing.SRParser
import Experiments.ProofChecking.SRChecker
import Experiments.ProofChecking.RangeArray

import LeanSAT.Data.Cnf
import LeanSAT.Data.ICnf
import LeanSAT.Data.Literal

open LeanSAT LeanSAT.Model RangeArray

def printUsage : IO Unit := do
  IO.println "Usage: ./SRChecker <cnf> <lsr> [c]"
  IO.println ""
  IO.println "where"
  IO.println ""
  IO.println "   [c] is an optional argument specifying that <lsr> is in binary compressed format."
  IO.println ""
  IO.println "If no command-line arguments are given, prints this help message."
  IO.println "Reads the CNF and LSR files and checks the LSR proof."

def checkProof (lines : List String) (F : RangeArray ILit) (τ : PPA) (σ : PS) : Except Bool SR.SRState := do
  lines.foldlM (init := SR.SRState.mk F τ σ) (fun (⟨F, τ, σ⟩ : SR.SRState) line =>
    match SRParser.parseLSRLine F line with
    | .error _ => .error false
    | .ok (_, F, pl) =>
      match pl with
      | .inl addLine =>
        SR.checkLine ⟨F, τ, σ⟩ addLine
      | .inr delLine =>
        match SR.consumeDeletionLine F delLine with
        | .ok F => .ok ⟨F, τ, σ⟩
        | .error _ => .error false)

/-
theorem checkProof_error_true {lines : List String}
    {F : RangeArray ILit} {Ls : List (Option (List ILit))} (h_models : models F Ls [])
    {τ : PPA} {σ : PS} :
    checkProof lines F τ σ = .error true → cnfListToPropFun Ls = ⊥ := by
  induction lines generalizing F Ls τ σ with
  | nil => simp [checkProof, pure, Except.pure]
  | cons line lines ih =>
    simp [checkProof]
    split
    · simp [bind, Except.bind]
    · rename_i lineId F' parsedLine parseRes
      split
      · rename_i addLine
        rcases SRParser.parseLSRLine_ok_inl parseRes h_models with ⟨C, hC⟩
        simp [bind, Except.bind]
        split
        · rename_i b h_checkLine
          cases b <;> simp
          have := SR.checkLine_error_true hC h_checkLine
          simp at this
          exact this
        · rename_i S h_checkLine
          rcases SR.checkLine_ok hC h_checkLine with ⟨⟨τ', σ', hS⟩, h₂⟩
          subst hS
          have h_models_commit := models_commit hC
          intro h
          have := ih h_models_commit h
          simp [LeanColls.Seq.snoc] at this
          simp at h₂
          exact (PropFun.eq_bot_iff_eq_bot_of_eqsat h₂).mpr this
      · rename_i delLine
        have := SRParser.parseLSRLine_ok_inr parseRes
        subst this
        split
        · rename_i F₂ h_consumeDeletionLine
          stop
          rcases SR.consumeDeletionLine_ok h_models h_consumeDeletionLine with ⟨Ls₂, h_models₂, h_toPropFun⟩
          intro h
          rw [ih h_models₂ h, le_bot_iff] at h_toPropFun
          exact h_toPropFun
        · simp [bind, Except.bind] -/

def interpretResult : Except Bool SRState → IO Unit
  | .ok _ => do
    IO.println "c Proof is valid, but did not derive the empty clause."
    IO.println "s VALID"
  | .error true => do
    IO.println "c Proof derived the empty clause"
    IO.println "s VERIFIED UNSAT"
  | .error false => do
    IO.println "c Error or invalid proof"
    IO.println "s INVALID"

partial def main : List String → IO Unit
  | [] => printUsage
  | [_] => printUsage
  | [cnfFile, lsrFile] => do
    let cnfContents ← IO.FS.withFile cnfFile .read (·.readToEnd)
    let (F, nvars) ← IO.ofExcept <| SRParser.parseFormula cnfContents (RangeArray.empty : RangeArray ILit)

    let lsrContents ← IO.FS.withFile lsrFile .read (·.readToEnd)
    let lines := lsrContents.splitOn "\n"
    interpretResult <| checkProof lines F (PPA.new (nvars * 2)) (PS.new (nvars * 2))

  | [cnfFile, lsrFile, "c"] => do
    let cnfContents ← IO.FS.withFile cnfFile .read (·.readToEnd)
    let (F, nvars) ← IO.ofExcept <| SRParser.parseFormula cnfContents (RangeArray.empty : RangeArray ILit)

    let bytes ← IO.FS.withFile lsrFile .read (·.readBinToEnd)
    let b_size := bytes.size
    let rec loop (index : Nat) : SR.SRState → Except Bool SR.SRState
    | ⟨F, τ, σ⟩ => do
      if index < b_size then
        match SRParser.parseLSRLineBinary F bytes index with
        | .error _ => .error false
        | .ok (index, _, F, pl) =>
          --let F := F.commitUntil (id - 1)
          match pl with
          | .inl addLine =>
            match SR.checkLine ⟨F, τ, σ⟩ addLine with
            | .ok st => loop index st
            | .error b => .error b
          | .inr delLine =>
            match SR.consumeDeletionLine F delLine with
            | .ok F => loop index ⟨F, τ, σ⟩
            | .error _ => .error false
      else .error false
    interpretResult <| loop 0 (SR.SRState.mk F (PPA.new (nvars * 2)) (PS.new (nvars * 2)))

  | _ => printUsage
