import LeanSAT.CNF
import LeanSAT.AuxDefs

namespace LeanSAT.Dimacs

def formatVar : Var → String
| (n : Nat) => s!"{n + 1}"

def formatLit : Literal → String
| .pos v => formatVar v
| .neg v => "-" ++ formatVar v

def formatClause : Clause → String
| ⟨lits⟩ => lits.map (formatLit ·) |> String.intercalate " "

def calcDimacsHeader : Formula → Nat × Nat
| ⟨clauses⟩ =>
  ( clauses.map (·.lits.map (β := Nat) Literal.var |>.maximum?.getD 0) |>.maximum?.getD 0
  , clauses.length )

def formatFormula (f : Formula) : String :=
  let (vars,clauses) := calcDimacsHeader f
  s!"p cnf {vars} {clauses}\n" ++ (
    f.clauses.map formatClause |> String.intercalate "\n" )

def printFormula [Monad m] (print : String → m Unit) (f : Formula) : m Unit := do
  let (vars,clauses) := calcDimacsHeader f
  print <| s!"p cnf {vars} {clauses}\n"
  for c in f.clauses do
    print <| formatClause c ++ "\n"


structure DimacsParseRes where
  vars : Nat
  clauses : List Clause

def parseVar (maxVar : Nat) (s : String) : Except String Var := do
  let n ← s.toNat?.expectSome fun () => s!"Expected variable; got non-Nat: `{s}`"
  match n with
  | 0   => throw "Expected variable; got zero: `{s}`"
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
