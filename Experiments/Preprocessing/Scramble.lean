import LeanSAT.Encode.EncCNF

namespace LeanSAT.Encode.EncCNF

def LawfulState.scramble (s : LawfulState L ν) : IO (LawfulState L ν) := do
  let clauseScrambled ← s.cnf.mapM fun clause => do
    return (← IO.randPerm clause.toList).toArray
  let cnf := (← IO.randPerm clauseScrambled.toList).toArray
  return { s with
    cnf
    -- TODO(JG): prove lemmas about `IO.randPerm`
    cnfVarsLt := sorry
    vMapLt := sorry
  }
