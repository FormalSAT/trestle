/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Trestle.Encode.EncCNF
import Trestle.Solver.Basic

open Std

namespace Trestle.Solver.Dimacs

def formatVar : IVar → String
| n => s!"{n}"

def formatLit (l : ILit) : String :=
  if LitVar.polarity l then
    formatVar (LitVar.toVar l)
  else "-" ++ formatVar (LitVar.toVar l)

def formatClause : IClause → String
| ⟨lits⟩ => lits.map (formatLit ·) ++ ["0"] |> String.intercalate " "

def formatComment (s : String) : String :=
  s.splitOn (sep := "\n")
  |>.map ("c " ++ ·)
  |> String.intercalate "\n"

def formatFormula (f : ICnf) : String :=
  let vars := f.maxBy (·.maxBy (LitVar.toVar · |>.val) |>.getD 0) |>.getD 0
  let clauses := f.size
  s!"p cnf {vars} {clauses}\n" ++ (
    f.map formatClause |>.toList |> String.intercalate "\n" )

def printICnf [Monad m] (print : String → m Unit) (f : ICnf) (vars := f.maxVar) : m Unit := do
  let clauses := f.size
  print <| s!"p cnf {vars} {clauses}\n"
  for c in f do
    print <| formatClause c ++ "\n"

def printRichCnf [Monad m] (print : String → m Unit) (f : RichCnf) (vars := f.maxVar) : m Unit := do
  let clauses := f.foldl (· + match · with |.clause _ => 1 | _ => 0) 0
  print <| s!"p cnf {vars} {clauses}\n"
  for line in show Array _ from f do
    match line with
    | .clause c =>
      print <| formatClause c
      print "\n"
    | .comment s =>
      print <| formatComment s
      print "\n"

def toFile (file : System.FilePath) (cnf : ICnf) : IO Unit := do
  IO.FS.withFile file .write fun handle =>
    printICnf handle.putStr cnf

def toFileRich (file : System.FilePath) (cnf : RichCnf) : IO Unit := do
  IO.FS.withFile file .write fun handle =>
    printRichCnf handle.putStr cnf

def formatAssn (a : HashAssn ILit) : String :=
  a.fold (fun str v b =>
    if b then
      str.append s!" {v}"
    else
      str.append s!" -{v}")
    "v"

def printRes [Monad m] [MonadExcept ε m] [Inhabited ε] (print : String → m Unit) : Solver.Res → m Unit
| .sat assn => do
  print "s SATISFIABLE"
  print (formatAssn assn)
| .unsat => print "s UNSATISFIABLE"
| .error => throw default


structure DimacsParseRes where
  vars : Nat
  clauses : RichCnf

def parseVar (maxVar : Nat) (s : String) : Except String IVar := do
  let n ← liftM <| s.toNat?.expectSome fun () => s!"Expected variable; got non-Nat: `{s}`"
  if h : n > 0 then
    if n ≤ maxVar then
      return ⟨n,h⟩
    else
      throw s!"Variable {n} higher than max var {maxVar}"
  else
    throw s!"Expected variable; got zero: `{s}`"

def parseLit (maxVar : Nat) (s : String) : Except String ILit := do
  if s.startsWith "-" then
    parseVar maxVar (s.drop 1) |>.map (- ·)
  else
    parseVar maxVar s

def parseClause (maxVar : Nat) (s : String) : Except String IClause := do
  aux (s.splitOn " " |>.filter (!·.isEmpty)) #[]
where aux (L : List String) (acc : Array ILit) := do
  match L with
  | [] => throw s!"Line was empty? `{s}`"
  | [last] =>
    if last = "0" then
      return acc
    else throw s!"Expected last entry of line to be zero; got: `{s}`"
  | lit::rest =>
    let lit ← parseLit maxVar lit
    aux rest (acc.push lit)

def parseHeader (s : String) : Except String (Nat × Nat) := do
  match s.splitOn " " with
  | ["p", "cnf", vars, clauses] => do
    let vars ← vars.toNat?.expectSome     fun () => s!"Header line #vars: expected number, got `{vars}`"
    let clss ← clauses.toNat?.expectSome  fun () => s!"Header line #clauses: expected number, got `{clauses}`"
    return (vars, clss)
  | _ => .error s!"Expected header `p cnf <#vars> <#clauses>`; got `{s}`"

-- TODO(JG): currently this fails if the p line occurs after some comment lines. fix that.
def parseFormula (s : String) : Except String DimacsParseRes := do
  let ⟨pLine, clauseLines⟩ ←
    s.splitOn "\n"
    |>.map (·.trim)
    |>.filter (!·.isEmpty)
    |>.filter (!·.startsWith "c")
    |>.expectNonempty fun () => "Missing p line"
  let (nvars, _) ← parseHeader pLine
  let clauses ← clauseLines.toArray.mapIdxM (fun lineNum line =>
    if line.startsWith "c " then
      .ok (.comment (line.drop 2))
    else
      parseClause nvars line
      |>.map (.clause ·)
      |>.mapError (s!"line {lineNum+1}: {·}"))
  return {
    vars := nvars
    clauses := clauses
  }

def parseVLines (maxVar : Nat) (assn : HashAssn ILit) (s : String) : Except String (HashAssn ILit) := do
  match ← (s.splitOn " " |>.expectNonempty fun () => panic! "splitOn returned empty?? 645") with
  | ⟨"v", vars⟩ => do
    let forAssn ← vars.foldlM (fun assn x => do
      ForInStep.bind assn fun assn => do
        if x = "0" then
          return ForInStep.done assn
        else
          let l ← parseLit maxVar x
          return ForInStep.yield <| assn.set l
    ) (ForInStep.yield assn)
    return ForInStep.run forAssn
  | _ =>
    .error s!"Expected `v <lits>`, got `{s}`"

def parseResult (maxVar : Nat) (s : String) : Except String Solver.Res := do
  let lines :=
    s.splitOn "\n"
    |>.filter (fun line => !line.startsWith "c" && line.any (!·.isWhitespace))
  match ←(lines.expectNonempty fun () => s!"Expected result, got `{s}`") with
  | ⟨first, rest⟩ =>
  match first with
  | "s UNSATISFIABLE" => return .unsat
  | "s SATISFIABLE" =>
    let assn ←
      rest.foldlM (fun assn line => parseVLines maxVar assn line) (HashMap.emptyWithCapacity)
    return .sat assn
  | _ => .error  "Expected `s <UNSATISFIABLE|SATISFIABLE>`, got `{first}`"


/-- auxiliary for getting an EncCNF.State from a DIMACS cnf file -/
def fromFileEnc (cnfFile : String) : IO (Encode.EncCNF.State IVar) := do
  let contents ← IO.FS.withFile cnfFile .read (·.readToEnd)
  let {vars, clauses} ← IO.ofExcept <| Solver.Dimacs.parseFormula contents
  return {
    nextVar := vars.succPNat
    cnf := clauses
    vMap := id
    vNames := .empty
  }

def parseAssnLine (maxVar : Nat) (s : String) : Except String (HashAssn ILit) := do
  let nums := s.splitOn " "
  let mut assn : HashAssn ILit := .empty
  let mut seenZero := false
  for n in nums do
    if seenZero then throw s!"Expected end of line after 0, but got `{n}`"
    else
    if n = "0" then
      seenZero := true
    else
      let lit ← parseLit maxVar n
      assn := assn.set lit

  if !seenZero then throw s!"Expected `0`, got end of line"
  else return assn

def parseAssnLines (maxVar : Nat) (s : String) : Except String (List (HashAssn ILit)) := do
  let lines :=
      s.splitOn "\n"
    |>.filter (fun line => !line.startsWith "c" && line.any (!·.isWhitespace))
  lines.mapM (parseAssnLine maxVar)
