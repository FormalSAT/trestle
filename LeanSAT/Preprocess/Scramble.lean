def scramble (s : State L) : IO (State L) := do
  let clauseScrambled ← s.cnf.mapM fun clause => do
    return (← IO.randPerm clause.toList).toArray
  let cnf := (← IO.randPerm clauseScrambled.toList).toArray
  return { s with
    cnf
  }
