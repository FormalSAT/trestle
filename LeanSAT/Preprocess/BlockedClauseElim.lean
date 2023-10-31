import LeanSAT.Data.Cnf
import Std.Data.HashMap
import LeanSAT.AuxDefs

namespace LeanSAT.Preprocess.BlockedClauseElim

open List

/-- Assuming x ∈ C1, returns (¬x ∈ C2 ∨ (resolving C1+C2 gives a tautology)) -/
def resolvesTaut [LitVar L ν] [BEq L] [BEq ν] (x : L) (C1 C2 : Clause L) : Bool :=
  !(Array.contains C2 (-x)) ||
  Array.any C1 (fun a =>
    !(LitVar.toVar x == LitVar.toVar a) &&
    Array.any C2 (fun b =>
      a == (-b)))

private structure State (L) [BEq L] [Hashable L] where
  clauses : List (Clause L)
  litMap : Std.HashMap L (List (Clause L))
  h_litMap_some : ∀ l, litMap.find? l = some CS →
                      CS = clauses.filter (·.contains l)
  h_litMap_none : ∀ l, litMap.find? l = none →
                      [] = clauses.filter (·.contains l)

variable {L} [BEq L] [Hashable L] [LitVar L ν] [BEq ν]

private def stateOfFormula (f : Cnf L) : State L :=
  let litMap := f.foldl (fun m c =>
    c.foldl (fun m l =>
        match m.find? l with
        | none => m.insert l [c]
        | some c' => m.insert l (c::c'))
      m)
    Std.HashMap.empty
  { clauses := f.toList, litMap
    h_litMap_some := sorry
    h_litMap_none := sorry }

private def removeClause (c : Clause L) (m : Std.HashMap L (List (Clause L))) :=
  c.foldl (init := m) (fun m l =>
    match m.find? l with
    | none => panic! "invariant violated: 1249850198"
    | some cs =>
      m.insert l (cs.filter (! · == c)))

/-- Find and removed blocked clauses from the formula.
  Returns updated formula with no blocked clauses, and a list of eliminated (variable,clause) pairs -/
def blockedClauseElim (F : Cnf L) : Cnf L × List (L × Clause L) :=
  let rec remBlocked (s : State L) (acc : List (L × Clause L))
    : List (Clause L) × List (L × Clause L) :=
    -- Find blocked clause & its blocked variable
    match s.clauses.partitionMap (fun C =>
        -- For a given clause, find an atom such that resolution is always taut
        match C.find? (fun x =>
          s.litMap.find! (-x) |>.all (fun C' =>
            C == C' || resolvesTaut x C C'))
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
      let s : State L := {
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
