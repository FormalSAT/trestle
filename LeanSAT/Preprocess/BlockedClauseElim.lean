import LeanSAT.CNF
import Std.Data.HashMap
import LeanSAT.AuxDefs

namespace LeanSAT.Preprocess.BlockedClauseElim

open List

/-- Assuming x ∈ C1, returns (¬x ∈ C2 ∨ (resolving C1+C2 gives a tautology)) -/
def resolvesTaut (x : Literal) (C1 C2 : Clause) : Bool :=
  !(List.contains C2.lits x.not) ||
  List.any C1.lits (fun a =>
    x.var ≠ a.var ∧
    List.any C2.lits (fun b =>
      a = b.not))

private structure State where
  clauses : List Clause
  litMap : Std.HashMap Literal (List Clause)
  h_litMap_some : ∀ l, litMap.find? l = some CS → CS = clauses.filter (·.lits.contains l)
  h_litMap_none : ∀ l, litMap.find? l = none → [] = clauses.filter (·.lits.contains l)

private def stateOfFormula (f : Formula) : State :=
  let clauses := f.clauses
  let litMap := clauses.foldl (fun m c =>
    c.lits.foldl (fun m l =>
        match m.find? l with
        | none => m.insert l [c]
        | some c' => m.insert l (c::c'))
      m)
    Std.HashMap.empty
  ⟨clauses, litMap, sorry, sorry⟩

private def removeClause (c : Clause) (m : Std.HashMap Literal (List Clause)) :=
  c.lits.foldl (fun m l =>
    match m.find? l with
    | none => panic! "invariant violated: 1249850198"
    | some cs =>
      m.insert l (cs.filter (· ≠ c))) m

/-- Find and removed blocked clauses from the formula.
  Returns updated formula with no blocked clauses, and a list of eliminated (variable,clause) pairs -/
def blockedClauseElim (F : Formula) : Formula × List (Literal × Clause) :=
  let rec remBlocked (s : State) (acc : List (Literal × Clause))
    : List Clause × List (Literal × Clause) :=
    -- Find blocked clause & its blocked variable
    match s.clauses.partitionMap (fun C =>
        -- For a given clause, find an atom such that resolution is always taut
        match C.lits.find? (fun x =>
          s.litMap.find! x.not |>.all (fun C' =>
            C = C' ∨ resolvesTaut x C C'))
        with
        -- If such an atom doesn't exist, put clause in left group
        | none => Sum.inl C
        -- If this atom does exist, put clause in right group
        | some x => .inr (x,C))
    with
    -- No more blocked clauses, return
    | (CS', []) => (CS', acc)
    -- Found some blocked clauses
    | (CS', blocked) =>
      assert! CS'.length + blocked.length = s.clauses.length
      assert! CS'.length < s.clauses.length
      let s : State := {
        clauses := CS'
      , litMap := blocked.foldl (fun m (_,c) => removeClause c m) s.litMap
      , h_litMap_none := sorry
      , h_litMap_some := sorry
      }
      -- Iterate on remaining clauses
      remBlocked s (blocked ++ acc)
  let (CS, removed) := remBlocked (stateOfFormula F) []
  (⟨CS⟩, removed)
termination_by remBlocked A _ => A.clauses.length
