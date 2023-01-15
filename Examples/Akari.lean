import LeanSAT

open LeanSAT

namespace Akari

inductive AkariSquare
| space | filled (num : Option (Fin 5))
deriving DecidableEq, Inhabited

structure AkariProblem where
  height : Nat
  width : Nat
  board : Fin height → Fin width → AkariSquare
deriving Inhabited

def AkariProblem.ofString (s : String) : Except String AkariProblem := do
  let lines := s.split (· = '\n') |>.toArray
  let height := lines.size
  if h_h : height = 0 then
    throw "board must have at least one line?"
  else
    let width := lines[0]'(Nat.pos_of_ne_zero h_h) |>.length
    let arr : Array (Σ' A : Array AkariSquare, A.size = width)
      ← lines.mapIdxM (fun i line => do
        if h_w : width = line.length then
          let A ← Array.initM width (fun j => do
            match line[h_w ▸ j] with
            | ' ' => return .space
            | 'X' => return .filled none
            | '0' => return .filled (some 0)
            | '1' => return .filled (some 1)
            | '2' => return .filled (some 2)
            | '3' => return .filled (some 3)
            | '4' => return .filled (some 4)
            | _ => throw s!"line {i} col {j} unknown character: `{line[h_w ▸ j]}`")
          have : A.size = width := sorry
          return ⟨A, this⟩
        else throw s!"line {i} has width {line.length}; expected {width}"
      )
    have : arr.size = height := sorry
    return ⟨height, width, fun i j => let ⟨A,h⟩ := arr.get (this ▸ i); A.get (h ▸ j)⟩

structure AkariVars extends AkariProblem where
  isLight : Fin height → Fin width → Var
deriving Inhabited

def encode : AkariProblem → EncCNF AkariVars
| ⟨height, width, board⟩ =>
  open EncCNF Constraint in do
  let varArr ←
    Array.initM height fun r =>
      Array.initM width fun c =>
        mkVar s!"{r},{c} lit"
  let isLight (i : Fin height) (j : Fin width) := varArr[i]![j]!
  
  /- For each row/column, at most one of each contiguous line
    of `space`s can be a light -/
  for r in List.fins height do
    for cs in List.fins width |>.splitOnP (board r · ≠ .space) do
      atMostOne (cs.map (isLight r ·))
  for c in List.fins width do
    for rs in List.fins height |>.splitOnP (board · c ≠ .space) do
      atMostOne (rs.map (isLight · c))
  
  for r in List.fins height do
    for c in List.fins width do
      match board r c with
      | .space =>
        /- Each space square must have a light somewhere in the
          vertical/horizontal sections it is in -/
        /- find rows "adjacent" to r,c -/
        let rs := List.fins height  |>.splitOnP (board · c ≠ .space)
                                    |>.find? (·.contains r) |>.getD []
        /- sim for columns -/
        let cs := List.fins width  |>.splitOnP (board r · ≠ .space)
                                    |>.find? (·.contains c) |>.getD []
        /- at least one of these spaces must be light (note the list
          contains `isLight r c` twice, but that is fine) -/
        addClause (
          rs.map (Literal.pos <| isLight · c) ∨
            cs.map (Literal.pos <| isLight r ·)
        )
      | .filled num =>
        /- filled is not light -/
        addClause <| ¬ isLight r c
        /- if `num = some k` then `k` of `r,c`'s neighbors should
          be light -/
        match num with
        | none => pure ()
        | some k =>
          let nbrs :=  [
              r.pred?.map (isLight · c),
              r.succ?.map (isLight · c),
              c.pred?.map (isLight r ·),
              c.succ?.map (isLight r ·)
            ].map (·.toList.map .pos) |>.join
          equalK nbrs.toArray k

  return ⟨⟨height, width, board⟩, isLight⟩

def solve (p : AkariProblem) :=
  let (v,enc) := EncCNF.new! (encode p)
  let varList :=
    List.fins _ |>.bind fun i =>
      List.fins _ |>.map fun j =>
        v.isLight i j
  match Solver.solve enc varList with
  | (_, .error) => IO.println "error"
  | (_, .unsat) => IO.println "unsat"
  | (_, .sat assn) =>
    for i in List.fins _ do
      for j in List.fins _ do
        match assn.find? (v.isLight i j) with
        | none => panic! "wtf"
        | some true => IO.print "O"
        | some false =>
          match v.board i j with
          | .space => IO.print " "
          | .filled none => IO.print "X"
          | .filled (some n) => IO.print s!"{n}"
      IO.println ""

def main := do
  match AkariProblem.ofString <|
    "    X    \n" ++
    "  0    1 \n" ++
    "    X    \n" ++
    "1 X   X  \n" ++
    "    0    \n" ++
    "  X   1  \n" ++
    "1   X   X\n" ++
    "         \n" ++
    "  1 X 1  "
  with
  | .error s => IO.println s
  | .ok a => solve a

end Akari