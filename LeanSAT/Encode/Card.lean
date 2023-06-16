import LeanSAT.Encode.EncCNF
import LeanSAT.Encode.Tseitin

namespace LeanSAT.Encode

open EncCNF Tseitin Tseitin.Notation

def amoPairwise (lits : List Literal) : EncCNF Unit := do
  -- for every pair x,y of literals in `lits`, they can't both be true
  lits.forDiagM (fun (x y : Literal) => do
    tseitin (¬(x ∧ y))
  )

def amoCut4 (lits : List Literal) : EncCNF Unit := do
  match lits with
  | []                      => return
  | l1 :: []                => amoPairwise [l1]
  | l1 :: l2 :: []          => amoPairwise [l1, l2]
  | l1 :: l2 :: l3 :: rlits =>
    let t ← mkTemp
    amoPairwise [t, l1, l2, l3]
    amoCut4 (.not t :: rlits)
termination_by _ lits => lits.length

def atMostOne (lits : List Literal) : EncCNF Unit :=
  if lits.length ≤ 5 then
    amoPairwise lits
  else
    amoCut4 lits

def partialSumsBlock (lits : Array Literal) (hl : lits.size > 0) (k : Nat) (hk : k > 1)
  : EncCNF (VarBlock [k, lits.size]) := do
  -- `temps[i][j]` ↔ i < ∑ j' ≤ j, `lits[j']`
  let temps ← mkTempBlock [k, lits.size]

  have : 0 < k := Nat.lt_trans (by simp) hk

  for i in List.fins k do
    for j in List.fins lits.size do
      match j.pred? with
      | none => -- `j = 0`
        if i = ⟨0,this⟩ then
          tseitin (temps[i][j] ↔ lits[j])
        else
          tseitin (¬temps[i][j])
      | some j' =>
        match i.pred? with
        | none =>
          tseitin (temps[i][j] ↔ (temps[i][j'] ∨ lits[j]))
        | some i' =>
          tseitin (temps[i][j] ↔ (temps[i][j'] ∨ temps[i'][j'] ∧ lits[j]))
 
  return temps

def partialSumsAtMostK (lits : Array Literal) (hl : lits.size > 0) (k : Nat) (hk : k > 0) : EncCNF Unit :=
  newCtx s!"pSums≤{k}" do
  let sumsBlock ← partialSumsBlock lits hl (k+1) (Nat.succ_le_succ hk)

  have : lits.size-1 < lits.size := Nat.sub_lt hl (by simp)

  -- ¬`sumsBlock[k][lits.size-1]`
  -- <=> ¬(k < ∑ j, lits[j])
  -- <=> k ≥ ∑ j, lits[j]
  tseitin (¬sumsBlock[k][lits.size-1])

def partialSumsAtLeastK (lits : Array Literal) (hl : lits.size > 0) (k : Nat) (hk : k > 1) : EncCNF Unit :=
  newCtx s!"pSums≥{k}" do
  let sumsBlock ← partialSumsBlock lits hl k hk

  have : k-1 < k := Nat.sub_lt (Nat.lt_trans (by simp) hk) (by simp)
  have : lits.size-1 < lits.size := Nat.sub_lt hl (by simp)

  -- `sumsBlock[k-1][lits.size-1]`
  -- <=> k-1 < ∑ j, lits[j]
  -- <=> k ≤ ∑ j, lits[j]
  addClause (sumsBlock[k-1][lits.size-1])

def partialSumsEqualK (lits : Array Literal) (hl : lits.size > 0) (k : Nat) (hk : k > 0) : EncCNF Unit :=
  newCtx s!"pSums={k}" do
  have : lits.size-1 < lits.size := Nat.sub_lt ‹_› (by simp)
  have : k-1 < k+1 := Nat.le_step <| Nat.sub_lt ‹_› (by simp)
  let sumsBlock ← partialSumsBlock lits hl (k+1) (Nat.succ_le_succ hk)

  -- `¬sumsBlock[k][lits.size-1]`
  -- <=> ¬(k < ∑ j, lits[j])
  -- <=> k ≥ ∑ j, lits[j]
  tseitin (¬sumsBlock[k][lits.size-1])

  -- `sumsBlock[k-1][lits.size-1]`
  -- <=> k-1 < ∑ j, lits[j]
  -- <=> k ≤ ∑ j, lits[j]
  tseitin (sumsBlock[k-1][lits.size-1])

mutual
def atMostK (lits : Array Literal) k :=
  newCtx s!"atMost{k}" do
  if hz : k = 0 then
    for l in lits do
      addClause l.not
  else if k = 1 then
    atMostOne lits.data
  else if habove : k ≥ lits.size then
    -- trivially true
    return
  else if lits.size-k < k then
    atLeastK (lits.map (·.not)) (lits.size-k)
  else
    have : k > 0 := Nat.pos_of_ne_zero hz
    have : lits.size > 0 := Nat.lt_trans ‹_› (Nat.lt_of_not_le habove)
    partialSumsAtMostK lits ‹_› k ‹_›

def atLeastK (lits : Array Literal) k :=
  newCtx s!"atLeast{k}" do
  if hz : k = 0 then
    -- trivially true
    return
  else if k = 1 then
    addClause lits.toList
  else if k = lits.size then
    -- ⋀{l ∈ lits} l
    for l in lits do
      addClause l
  else if habove : k > lits.size then
    -- trivially false
    tseitin .false
  else if lits.size-k < k then
    atMostK (lits.map (·.not)) (lits.size-k)
  else
    have : k > 0 := Nat.pos_of_ne_zero hz
    have : lits.size > 0 := Nat.lt_of_lt_of_le ‹_› (Nat.ge_of_not_lt habove)
    partialSumsAtMostK lits ‹_› k ‹_›
end

/-- ∑ᵢ lits[i] = k -/
def equalK (lits : Array Literal) (k : Nat) : EncCNF Unit :=
  newCtx s!"equal{k}" <| do
  if hl : lits.size < k then
    -- trivially false
    tseitin .false
  else if hk:k = 0 then
    for l in lits do
      addClause l.not
  else if k = 1 then
    addClause lits.toList
    atMostOne lits.toList
  else if lits.size - k < k then
    equalK (lits.map (·.not)) (lits.size - k)
  else
    have : k > 0 := Nat.pos_of_ne_zero hk
    have : lits.size > 0 := Nat.lt_of_lt_of_le this (Nat.ge_of_not_lt hl)
    partialSumsEqualK lits ‹_› k ‹_›
