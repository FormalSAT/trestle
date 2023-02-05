import LeanSAT.Encode.EncCNF
import LeanSAT.Solver.Basic

open Std

namespace LeanSAT.Solver.Dimacs

def formatVar : Var → String
| (n : Nat) => s!"{n + 1}"

def formatLit : Literal → String
| .pos v => formatVar v
| .neg v => "-" ++ formatVar v

def formatClause : Clause → String
| ⟨lits⟩ => lits.map (formatLit ·) ++ ["0"] |> String.intercalate " "

def formatFormula (f : Formula) : String :=
  let (vars,clauses) := (f.numVars, f.clauses.length)
  s!"p cnf {vars} {clauses}\n" ++ (
    f.clauses.map formatClause |> String.intercalate "\n" )

def printFormula [Monad m] (print : String → m Unit) (f : Formula) : m Unit := do
  let (vars,clauses) := (f.numVars, f.clauses.length)
  print <| s!"p cnf {vars} {clauses}\n"
  for c in f.clauses do
    print <| formatClause c ++ "\n"

open Notation in
example : (printFormula PrinterM.putStr ((0 ∨ 1) ∧ 5) |>.run) =
"p cnf 6 2
1 2 0
6 0
" := rfl

def formatAssn (a : Assn) : String :=
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


def printEnc (s : Encode.EncCNF.State) : IO Unit := do
  for i in [0:s.nextVar] do
    for name in s.names.find? i do
      IO.println s!"c {Dimacs.formatVar i} {name}"

  Dimacs.printFormula IO.print ⟨s.clauses.reverse⟩





structure DimacsParseRes where
  vars : Nat
  clauses : List Clause

def parseVar (maxVar : Nat) (s : String) : Except String Var := do
  let n ← s.toNat?.expectSome fun () => s!"Expected variable; got non-Nat: `{s}`"
  match n with
  | 0   => throw s!"Expected variable; got zero: `{s}`"
  | v+1 =>
    if v < maxVar then
      return v
    else
      throw s!"Variable {v} higher than max var {maxVar}"

def parseLit (maxVar : Nat) (s : String) : Except String Literal := do
  if s.startsWith "-" then
    parseVar maxVar (s.drop 1) |>.map Literal.not
  else
    parseVar maxVar s

def parseClause (maxVar : Nat) (s : String) : Except String Clause := do
  let lits ← s.splitOn " " |>.mapM (parseLit maxVar)
  return ⟨lits⟩

def parseHeader (s : String) : Except String (Nat × Nat) := do
  match s.splitOn " " with
  | ["p", "cnf", vars, clauses] => do
    let vars ← vars.toNat?.expectSome     fun () => s!"Header line #vars: expected number, got `{vars}`"
    let clss ← clauses.toNat?.expectSome  fun () => s!"Header line #clauses: expected number, got `{clauses}`"
    return (vars, clss)
  | _ => .error s!"Expected header `p cnf <#vars> <#clauses>`; got `{s}`"

def parseFormula (s : String) : Except String DimacsParseRes := do
  let ⟨pLine, clauseLines⟩ ←
    s.splitOn "\n"
    |>.filter (fun line => !line.startsWith "c" && line.any (!·.isWhitespace))
    |>.expectNonempty fun () => "All lines are empty or comments"
  let (nvars, _) ← parseHeader pLine
  let clauses ← clauseLines.mapM (parseClause nvars)
  return {
    vars := nvars
    clauses := clauses
  }

def parseAssnLine (maxVar : Var) (assn : Assn) (s : String) : Except String Assn := do
  match ← (s.splitOn " " |>.expectNonempty fun () => panic! "splitOn returned empty?? 645") with
  | ⟨"v", vars⟩ => do
    let forAssn ← vars.foldlM (fun assn x => do
      ForInStep.bind assn fun assn => do
        if x = "0" then
          return ForInStep.done assn
        else
          let l ← parseLit maxVar x
          return ForInStep.yield <| assn.insertLit l
    ) (ForInStep.yield assn)
    return ForInStep.run forAssn
  | _ =>
    .error s!"Expected `v <lits>`, got `{s}`"

def parseResult (maxVar : Var) (s : String) : Except String Solver.Res := do
  let lines :=
    s.splitOn "\n"
    |>.filter (fun line => !line.startsWith "c" && line.any (!·.isWhitespace))
  match ←(lines.expectNonempty fun () => s!"Expected result, got `{s}`") with
  | ⟨first, rest⟩ =>
  match first with
  | "s UNSATISFIABLE" => return .unsat
  | "s SATISFIABLE" =>
    let assn ←
      rest.foldlM (fun assn line => parseAssnLine maxVar assn line) (HashMap.empty)
    return .sat assn
  | _ => .error  "Expected `s <UNSATISFIABLE|SATISFIABLE>`, got `{first}`"


def fromFileEnc (cnfFile : String) : IO Encode.EncCNF.State := do
  let contents ← IO.FS.withFile cnfFile .read (·.readToEnd)
  let {vars, clauses} ← IO.ofExcept <| Dimacs.parseFormula contents
  return {
    nextVar := vars
    clauses := clauses
    names := Id.run do
      let mut map : HashMap Var String := HashMap.empty
      for i in [0:vars] do
        map := map.insert i s!"DIMACS var {i}"
      return map
    varCtx := ""
  }
