import LeanSAT.Encode.EncCNF

namespace LeanSAT.Encode

open EncCNF Notation

def condAmoPairwise (cond lits : List Literal) : EncCNF Unit := do
  match lits with
  | []    => return
  | x::xs =>
    for y in xs do
      addClause ⟨cond.map (·.not) ++ [¬x, ¬y]⟩
    condAmoPairwise cond xs

def amoPairwise := condAmoPairwise []

def condAmoCut4 (cond lits : List Literal) : EncCNF Unit := do
  match lits with
  | []                      => return
  | l1 :: []                => condAmoPairwise cond [l1]
  | l1 :: l2 :: []          => condAmoPairwise cond [l1, l2]
  | l1 :: l2 :: l3 :: rlits =>
    let t ← mkTemp
    condAmoPairwise cond [t, l1, l2, l3]
    condAmoCut4 cond ((¬t) :: rlits)
termination_by _ lits => lits.length

def amoCut4 := condAmoCut4 []

def condAtMostOne (cond lits : List Literal) : EncCNF Unit :=
  if lits.length ≤ 5 then
    condAmoPairwise cond lits
  else
    condAmoCut4 cond lits

def atMostOne := condAtMostOne []


def partialSumsBlock (cond : List Literal) (lits : Array Literal) (k : Nat)
  : EncCNF (VarBlock [k, lits.size]) :=
  newCtx s!"pSums{k}" do
  let negCond := cond.map (·.not)

  -- `temps[i][j]` ↔ i < ∑ j' ≤ j, `lits[j']`
  let temps ← mkTempBlock [k, lits.size]

  match k with
  | 0 => return temps
  | k+1 =>
  if h:lits.size = 0 then
    return temps
  else
  have : 0 < lits.size := Nat.pos_of_ne_zero h

  -- `temps[i+1][j]` → `temps[i][j]`
  for h:i in [0:k] do
    have : i+1 < k+1 := Nat.succ_lt_succ h.2
    have : i < k+1 := Nat.lt_of_succ_lt this
    for h:j in [0:lits.size] do
      have : j < lits.size := h.2
      addClause ⟨negCond ++ [¬temps[i+1][j], temps[i][j]]⟩

  -- `temps[i][j]` → `temps[i][j+1]`
  for h:i in [0:k+1] do
    have : i < k+1 := h.2
    for h:j in [0:lits.size-1] do
      have : j+1 < lits.size := by simp at h; exact Nat.add_lt_of_lt_sub h.2
      have : j < lits.size := Nat.lt_of_succ_lt this
      addClause ⟨negCond ++ [¬temps[i][j], temps[i][j+1]]⟩

  -- ¬`temps[i][j]` → ¬`temps[i+1][j+1]`
  for h:i in [0:k] do
    have : i+1 < k+1 := Nat.succ_lt_succ h.2
    have : i < k+1 := Nat.lt_of_succ_lt this
    for h:j in [0:lits.size-1] do
      have : j+1 < lits.size := by simp at h; exact Nat.add_lt_of_lt_sub h.2
      have : j < lits.size := Nat.lt_of_succ_lt this
      addClause ⟨negCond ++ [(temps[i][j] : Literal), ¬temps[i+1][j+1]]⟩
  
  if h:1 < k+1 then
    addClause ⟨negCond ++ [¬temps[1][0]]⟩

  -- ¬`temps[i][j]` ∧ ¬`lits[j+1]` → ¬`temps[i][j+1]`
  for h:i in [0:k+1] do
    have : i < k+1 := h.2
    for h:j in [0:lits.size-1] do
      have : j+1 < lits.size := by simp at h; exact Nat.add_lt_of_lt_sub h.2
      have : j < lits.size := Nat.lt_of_succ_lt this
      addClause ⟨negCond ++ [.pos temps[i][j], lits[j+1], ¬temps[i][j+1]]⟩

  -- ¬`lits[0]` → ¬`temps[0][0]`
  addClause ⟨negCond ++ [lits[0], ¬temps[0][0]]⟩

  -- `temps[i][j]` ∧ `lits[j+1]` → `temps[i+1][j+1]`
  for h:i in [0:k] do
    have : i+1 < k+1 := Nat.succ_lt_succ h.2
    have : i < k+1 := Nat.lt_of_succ_lt this
    for h:j in [0:lits.size-1] do
      have : j+1 < lits.size := by simp at h; exact Nat.add_lt_of_lt_sub h.2
      have : j < lits.size := Nat.lt_of_succ_lt this
      addClause ⟨negCond ++ [¬temps[i][j], ¬lits[j+1], temps[i+1][j+1]]⟩

  -- `lits[j]` → `temps[0][j]`
  for h:j in [0:lits.size] do
    have : j < lits.size := h.2
    addClause ⟨negCond ++ [¬lits[j], temps[0][j]]⟩
  
  return temps

def condAtMostK (cond : List Literal) (lits : Array Literal) (k : Nat) : EncCNF Unit :=
  newCtx s!"atMost{k}" do
  let sumsBlock ← partialSumsBlock cond lits (k+1)

  -- ¬`sumsBlock[k][lits.size-1]`
  -- <=> ¬(k < ∑ j, lits[j])
  -- <=> k ≥ ∑ j, lits[j]
  if h:lits.size-1 < lits.size then
    addClause ⟨cond.map (·.not) ++ [¬sumsBlock[k][lits.size-1]]⟩

def atMostK := condAtMostK []

def condAtLeastK (cond : List Literal) (lits : Array Literal) (k : Nat) : EncCNF Unit :=
  newCtx s!"atLeast{k}" do
  let sumsBlock ← partialSumsBlock cond lits k

  -- `sumsBlock[k-1][lits.size-1]`
  -- <=> k-1 < ∑ j, lits[j]
  -- <=> k ≤ ∑ j, lits[j]
  if h:k = 0 then
    return -- trivially true
  else
  have : k-1 < k := Nat.sub_lt (Nat.pos_of_ne_zero h) (by simp)
  if h:lits.size = 0 then
    addClause ⟨cond.map (·.not)⟩ -- trivially false
  else
  have : lits.size-1 < lits.size := Nat.sub_lt (Nat.pos_of_ne_zero h) (by simp)
  addClause ⟨cond.map (·.not) ++ [.pos sumsBlock[k-1][lits.size-1]]⟩

def atLeastK := condAtLeastK []

def condEqualK (cond : List Literal) (lits : Array Literal) (k : Nat) : EncCNF Unit :=
  newCtx s!"equal{k}" <|
  let negCond := cond.map (·.not)
  if lits.size < k then do
    addClause ⟨negCond⟩ -- trivially false
  else if hk:k = 0 then do
    -- each lit should be false
    for l in lits do
      addClause ⟨negCond ++ [¬l]⟩
  else if hsize:lits.size - k < k then do
    condEqualK cond (lits.map (·.not)) (lits.size - k)
  else do
  have : 0 < k := Nat.pos_of_ne_zero hk
  have : 0 < lits.size := Nat.pos_of_ne_zero <| by intro; simp [*] at *
  have : lits.size-1 < lits.size := Nat.sub_lt ‹_› (by simp)
  have : k-1 < k+1 := Nat.le_step <| Nat.sub_lt ‹_› (by simp)
  let sumsBlock ← partialSumsBlock cond lits (k+1)

  -- ¬`sumsBlock[k][lits.size-1]`
  -- <=> ¬(k < ∑ j, lits[j])
  -- <=> k ≥ ∑ j, lits[j]
  addClause ⟨negCond ++ [¬sumsBlock[k][lits.size-1]]⟩

  -- `sumsBlock[k-1][lits.size-1]`
  -- <=> k-1 < ∑ j, lits[j]
  -- <=> k ≤ ∑ j, lits[j]
  addClause ⟨negCond ++ [.pos sumsBlock[k-1][lits.size-1]]⟩


def equalK := condEqualK []
