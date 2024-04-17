/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Cli

import ProofChecker.Checker.Parse
import ProofChecker.Checker.CheckerCore

def runCheckCmd (p : Cli.Parsed) : IO UInt32 := do
  let cnfFname := p.positionalArg! "cnf"
  let cpogFname := p.positionalArg! "cpog"
  let printFormula := p.hasFlag "print-cnf"
  let printProof := p.hasFlag "print-cpog"
  let count := p.hasFlag "count"
  printlnFlush "Parsing CNF.."
  let (cnf, nVars) ← ICnf.readDimacsFile cnfFname.value
  IO.println "done."
  if printFormula then
    IO.println "Parsed CNF:"
    IO.print (cnf.toDimacs nVars)
  printlnFlush "Parsing CPOG.."
  let pf ← CpogStep.readDimacsFile cpogFname.value
  IO.println "done."
  if printProof then
    IO.println "Parsed CPOG:"
    for step in pf do
      IO.println step.toDimacs
  printlnFlush "Checking proof.."
  match checkProof cnf nVars pf count with
  | .ok v =>
    IO.println "PROOF SUCCESSFUL"
    if count then
      IO.println s!"Model count: {v}"
    return 0
  | .error e =>
    IO.println s!"PROOF FAILED\n{e}"
    return 1
where
  printlnFlush (s : String) := do
    IO.println s
    (← IO.getStdout).flush

def checkCmd : Cli.Cmd := `[Cli|
  CheckCPOG VIA runCheckCmd; ["0.1.0"]
  "Check a CPOG proof."

  FLAGS:
    v, verbose;         "Print diagnostic information."
    c, count;           "Output the unweighted model count."
    "print-cnf";        "Reprint the parsed CNF formula."
    "print-cpog";       "Reprint the parsed CPOG proof."

  ARGS:
    cnf  : String;      "The CNF input file."
    cpog : String;      "The CPOG proof file."

  EXTENSIONS:
    Cli.author "Wojciech Nawrocki"
]

def main (args : List String) : IO UInt32 := do
  checkCmd.validate args
