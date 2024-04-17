/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import ProofChecker.Data.ICnf
import ProofChecker.Checker.CheckerCore

def Except.ofOption (e : ε) : Option α → Except ε α
  | none   => .error e
  | some x => .ok x

namespace Dimacs

inductive Token where
  | int (i : Int) | str (s : String)
  deriving Repr, BEq

instance : Coe String Token :=
  ⟨Token.str⟩

instance : Coe Int Token :=
  ⟨Token.int⟩

instance : ToString Token where
  toString := fun | .int v | .str v => toString v

def Token.getInt? : Token → Option Int
  | .int i => some i
  | .str _ => none

def Token.getStr? : Token → Option String
  | .int _ => none
  | .str s => some s

def tokenizeLines (lines : Array String) : Array (Array Token) := Id.run do
  let mut lns := #[]
  for ln in lines do
    let tks := ln.splitOn " " |>.filter (· ≠ "")
    if tks.isEmpty then continue
    if tks.head! == "c" then continue
    let mut ln := #[]
    for tk in tks do
      if let some i := tk.toInt? then
        ln := ln.push <| .int i
      else
        ln := ln.push <| .str tk
    lns := lns.push ln
  return lns

end Dimacs

open Dimacs

def Nat.ofToken : Token → Except String Nat
  | .int i =>
    if 0 ≤ i then .ok (Int.natAbs i)
    else .error s!"expected non-negative int at '{i}'"
  | .str s => .error s!"expected int at '{s}'"

def Var.ofToken : Token → Except String Var
  | .int i =>
    if h : 0 < i then .ok ⟨Int.natAbs i, Int.natAbs_pos.mpr (Int.ne_of_gt h)⟩
    else .error s!"expected positive int at '{i}'"
  | .str s => .error s!"expected int at '{s}'"

def ILit.ofToken : Token → Except String ILit
  | .int i =>
    if h : i ≠ 0 then .ok ⟨i, h⟩
    else .error s!"literal can't be zero at '{i}'"
  | .str s => .error s!"expected int at '{s}'"

def ILit.ofTokenBounded (bd : Nat) (tk : Token) : Except String ILit := do
  let l ← ILit.ofToken tk
  if l.var ≤ bd then
    return l
  else
    throw s!"literal {l} exceeds maximum variable index {bd}"

def IClause.ofTokens (tks : Array Token) : Except String IClause := do
  tks.mapM ILit.ofToken

def IClause.ofTokensBounded (bd : Nat) (tks : Array Token) : Except String IClause := do
  tks.mapM (ILit.ofTokenBounded bd)

/-- Return a CNF computed from the tokens of a DIMACS CNF file, together with the variable count
stored in the header. -/
def ICnf.ofLines (lns : Array (Array Token)) : Except String (ICnf × Nat) := do
  let some hdr := lns[0]? 
    | throw s!"expected at least one line"
  let #[.str "p", .str "cnf", nVars, .int nClauses] := hdr
    | throw s!"unexpected header {hdr}"
  let nVars ← Nat.ofToken nVars
  let mut clauses : ICnf := #[]
  for ln in lns[1:] do
    try
      let some (.int 0) := ln[ln.size - 1]?
        | throw s!"missing terminating 0"
      let lits := ln[:ln.size - 1]
      let clause ← IClause.ofTokensBounded nVars lits
      clauses := clauses.push clause
    catch e =>
      throw s!"error on line '{" ".intercalate <| ln.toList.map toString}': {e}"
  if Int.ofNat clauses.size ≠ nClauses then
    throw s!"expected {nClauses} clauses, but got {clauses.size}"
  return (clauses, nVars)

def ICnf.readDimacsFile (fname : String) : IO (ICnf × Nat) := do
  let lns ← IO.FS.lines fname
  let lns := Dimacs.tokenizeLines lns
  match ofLines lns with
  | .ok v => return v
  | .error e => throw <| IO.userError e
  
def ICnf.toDimacs (cnf : ICnf) (nVars : Nat) : String := Id.run do
  let mut s := s!"p cnf {nVars} {cnf.size}\n"
  for C in cnf do
    for l in C do
      s := s ++ toString l ++ " "
    s := s ++ "0\n"
  return s
  
/-- Return a proof step given a DIMACS line. -/
def CpogStep.ofTokens (tks : Array Token) : Except String CpogStep := do
  let toUpHints (tks : Array Token) : Except String (Array Nat) := do
    if let #[.str "*"] := tks then
      throw s!"got unhinted proof, but all hints need to be filled in"
    tks.mapM Nat.ofToken
  let (some fst, some snd) := (tks[0]?, tks[1]?)
    | throw s!"expected at least two tokens"
  let tks := tks[2:]
  match fst, snd with
  | idx, .str "a" =>
    let C := Array.takeWhile (· != Token.int 0) tks
    let some (.int 0) := tks[C.size]?
      | throw s!"missing terminating 0 in clause"
    let some (.int 0) := tks[tks.size-1]?
      | throw s!"missing terminating 0 in hints"
    let hints : Subarray Token := tks[C.size+1:tks.size-1]
    return .addAt (← Nat.ofToken idx) (← IClause.ofTokens C) (← toUpHints hints)
  | .str "dc", idx =>
    let some (.int 0) := tks[tks.size-1]?
      | throw s!"missing terminating 0 in hints"
    let hints : Subarray Token := tks[:tks.size-1]
    return .delAt (← Nat.ofToken idx) (← toUpHints hints)
  | idx, .str "p" =>
    let some x := tks[0]?
      | throw s!"missing product literal"
    let some (.int 0) := tks[tks.size-1]?
      | throw s!"missing terminating 0 in hints"
    let ls : Subarray Token := tks[1:tks.size-1]
    return .prod (← Nat.ofToken idx) (← Var.ofToken x) (← IClause.ofTokens ls)
  | idx, .str "s" =>
    let (some x, some l₁, some l₂) := (tks[0]?, tks[1]?, tks[2]?)
      | throw s!"missing sum parameters"
    let some (.int 0) := tks[tks.size-1]?
      | throw s!"missing terminating 0 in hints"
    let hints : Subarray Token := tks[3:tks.size-1]
    return .sum (← Nat.ofToken idx) (← Var.ofToken x) (← ILit.ofToken l₁) (← ILit.ofToken l₂)
      (← toUpHints hints)
  | .str "r", r =>
    return .root (← ILit.ofToken r)
  | .str "do", _ => throw s!"do command is not supported"
  | _, .str "i" => throw s!"i command is deprecated"
  | _, _ => throw s!"unexpected command"

def CpogStep.readDimacsFile (fname : String) : IO (Array CpogStep) := do
  let lns ← IO.FS.lines fname
  let lns := Dimacs.tokenizeLines lns
  let mut pf := #[]
  for ln in lns do
    match CpogStep.ofTokens ln with
    | .ok v => pf := pf.push v
    | .error e =>
      throw <| IO.userError s!"error on line '{" ".intercalate <| ln.toList.map toString}': {e}"
  return pf