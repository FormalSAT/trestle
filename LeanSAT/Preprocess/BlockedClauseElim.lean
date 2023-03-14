import LeanSAT.CNF

namespace LeanSAT.Preprocess.BlockedClauseElim

/-- Assuming x ∈ C1, returns (¬x ∈ C2 ∨ (resolving C1+C2 gives a tautology)) -/
def resolvesTaut (x : Literal) (C1 C2 : Clause) : Bool :=
  !(List.contains C2.lits x.not) ||
  List.any C1.lits (fun a =>
    x.var ≠ a.var ∧
    List.any C2.lits (fun b =>
      a = b.not))

-- Returns formula with no blocked clauses
--   + list of eliminated (variable,clause) pairs
def blockedClauseElim (F : Formula) : Formula × List (Literal × Clause) :=
  let rec remBlocked (CS : List Clause) (acc : List (Literal × Clause))
    : List Clause × List (Literal × Clause) :=
    -- Find blocked clause & its blocked variable
    match CS.partitionMap (fun C =>
        -- For a given clause, find an atom such that resolution is always taut
        match C.lits.find? (fun x =>
          CS.all (fun C' =>
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
      assert! CS'.length + blocked.length = CS.length
      assert! CS'.length < CS.length
      -- Iterate on remaining clauses
      remBlocked CS' (blocked ++ acc)
  let (CS, removed) := remBlocked (F.clauses) []
  (⟨CS⟩, removed)
termination_by remBlocked A _ => A.length
