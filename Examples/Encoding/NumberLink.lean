import LeanSAT
import Examples.SolverConfig

open LeanSAT Encode

namespace NumberLink

structure NumberLinkProblem where
  width : Nat
  height : Nat
  nums : Nat
  poses : List (Fin nums × Fin height × Fin width)
deriving Inhabited

structure NumberLinkVars where
  problem : NumberLinkProblem
  piece_var : Fin problem.height → Fin problem.width → Fin problem.nums → Var
deriving Inhabited

def numberLink (prob : NumberLinkProblem) : EncCNF NumberLinkVars :=
  open EncCNF in do
  /- make variables -/
  let arr ← Array.initM prob.height fun i =>
    Array.initM prob.width fun j =>
      Array.initM prob.nums fun n =>
        mkVar s!"pos {i} {j} numbered {n}"

  /- helper function to get the i,j,n variable -/
  let piece_var : Fin prob.height → Fin prob.width → Fin prob.nums → Var := fun i j n =>
    arr[i]![j]![n]!

  /- helper function to get the neighbors of i j -/
  let neighbors (i j) : List (_ × _):= [
      i.pred?.map (⟨·, j⟩) |>.toList,
      i.succ?.map (⟨·, j⟩) |>.toList,
      j.pred?.map (⟨i, ·⟩) |>.toList,
      j.succ?.map (⟨i, ·⟩) |>.toList
    ].join

  for i in List.fins _ do
    for j in List.fins _ do
      /- check if the square is in the given positions -/
      match prob.poses.find? (fun elem => (i,j) = elem.2) with
      | none =>
        /- assign at most one color to square i,j -/
        atMostOne (List.fins _ |>.map fun n => piece_var i j n)
        /- if a color assigned to this square, exactly two neighbors
          must share that color -/
        for n in List.fins _ do
          condEqualK
            [piece_var i j n]
            (neighbors i j |>.map fun (i',j') => piece_var i' j' n).toArray
            2
      | some (n, _, _) =>
        /- assign the square to n -/
        for n' in List.fins _ do
          if n = n' then
            addClause <| piece_var i j n
          else
            addClause <| ¬piece_var i j n'
        /- exactly one neighbor must share this color -/
        equalK (neighbors i j |>.map fun (i',j') => piece_var i' j' n).toArray 1

  return ⟨prob, piece_var⟩

def main : IO Unit := do
  let prob : NumberLinkProblem := {
    width := 9
    height := 8
    nums := 8
    poses := [
      (1, 3, 3),
      (1, 4, 6),
      (2, 7, 0),
      (2, 2, 1),
      (3, 3, 1),
      (3, 4, 4),
      (4, 4, 3),
      (4, 3, 8),
      (5, 6, 2),
      (5, 6, 7),
      (6, 1, 4),
      (6, 1, 7),
      (7, 2, 4),
      (7, 3, 6),
      (8, 1, 1),
      (8, 2, 3)
    ]
  }
  let (vars, enc) := EncCNF.new! <| numberLink prob
--  enc.prettyPrintAux (IO.println)
  match ← Solver.solve enc.toFormula with
  | .error => IO.println "err"
  | .unsat => IO.println "unsat"
  | .sat assn =>
    for i in List.fins _ do
      for j in List.fins _ do
--        for n in List.fins _ do
--          if assn.find? (vars.piece_var i j n) = some true then
--            IO.println s!"{i},{j} is {n}"
        match (List.fins _).find? (fun n =>
          assn.find? (vars.piece_var i j n) |>.get!)
        with
        | none =>
          IO.print " "
        | some n =>
          IO.print n
      IO.println ""
