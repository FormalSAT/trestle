import LeanSAT.Encode.VEncCNF
import LeanSAT.Encode.Tseitin

namespace LeanSAT.Encode

open VEncCNF Model PropFun

variable [LitVar L ν] [LawfulLitVar L ν]
    [DecidableEq L] [DecidableEq ν] [Fintype ν]

def card (lits : List L) (τ : PropAssignment ν) : Nat :=
  lits.countP (τ ⊨ LitVar.toPropFun ·)

def cardPred (lits : List L) (P : Nat → Prop) [DecidablePred P] : PropFun ν :=
  .ofFun fun τ => P (card lits τ)

@[simp] theorem satisfies_cardPred (lits : List L) (P) [DecidablePred P] (τ)
  : τ ⊨ cardPred lits P ↔ P (card lits τ) := by
  unfold cardPred; simp

def amoPairwise (lits : Array L) : VEncCNF L Unit (cardPred lits.data (· ≤ 1)) :=
  -- for every pair x,y of literals in `lits`, they can't both be true
  (for_all (Array.ofFn id) fun (i : Fin lits.size) =>
    for_all (Array.ofFn id) fun (j : Fin lits.size) =>
      .guard (i ≠ j) fun _ =>
        addClause #[-lits[i], -lits[j]]
  ).mapProp (by
    rcases lits with ⟨list⟩
    ext τ
    simp [Clause.toPropFun, any, Array.getElem_eq_data_get]
    simp only [Array.size]
    by_cases h : card list τ = 0
    · simp [h]
      intro x y; split <;> simp
      simp [card, List.countP_eq_zero] at h
      apply Or.inl; apply h; rw [List.mem_iff_get]; simp
    · replace h : card list τ > 0 := Nat.pos_of_ne_zero h
      simp [card, List.countP_pos, List.mem_iff_get] at h
      rcases h with ⟨x,h⟩
      stop
      have := List.countP_mono_left (l := list)
      rw [Nat.le_iff_lt_or_eq, Nat.lt_one_iff]; simp [h]
      unfold card)

def amoCut4 (lits : Array ILit) : EncCNF Unit :=
  match h1 : lits.pop? with
  | none => return
  | some (lits', l1) =>
  match h2 : lits'.pop? with
  | none => amoPairwise [l1]
  | some (lits'', l2) =>
  match h3 : lits''.pop? with
  | none => amoPairwise [l1, l2]
  | some (lits''', l3) => do
  let t ← mkTemp
  amoPairwise [t, l1, l2, l3]
  have : lits.size = lits'''.size + 1 + 1 + 1 := by
    repeat rw [Array.size_pop? ‹_›]
  have : lits'''.size + 1 < lits.size := by simp [*]
  amoCut4 <| lits'''.push (-t)
termination_by _ lits => lits.size

def atMostOne (lits : Array ILit) : EncCNF Unit :=
  if lits.size ≤ 5 then
    amoPairwise lits.toList
  else
    amoCut4 lits

open Model.PropForm.Notation in
def partialSumsBlock (lits : Array ILit) (k : Nat) (hk : k > 1)
  : EncCNF (IVarBlock [k, lits.size]) := do
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
          addClause #[-temps[i][j]]
      | some j' =>
        match i.pred? with
        | none =>
          tseitin (temps[i][j] ↔ temps[i][j'] ∨ lits[j])
        | some i' =>
          tseitin (temps[i][j] ↔ temps[i][j'] ∨ temps[i'][j'] ∧ lits[j])

  return temps

def partialSumsAtMostK (lits : Array ILit) (hl : lits.size > 0) (k : Nat) (hk : k > 0) : EncCNF Unit :=
  newCtx s!"pSums≤{k}" do
  let sumsBlock ← partialSumsBlock lits (k+1) (Nat.succ_le_succ hk)

  have : lits.size-1 < lits.size := Nat.sub_lt hl (by simp)

  -- ¬`sumsBlock[k][lits.size-1]`
  -- <=> ¬(k < ∑ j, lits[j])
  -- <=> k ≥ ∑ j, lits[j]
  addClause #[ -sumsBlock[k][lits.size-1] ]

def partialSumsAtLeastK (lits : Array ILit) (hl : lits.size > 0) (k : Nat) (hk : k > 1) : EncCNF Unit :=
  newCtx s!"pSums≥{k}" do
  let sumsBlock ← partialSumsBlock lits k hk

  have : k-1 < k := Nat.sub_lt (Nat.lt_trans (by simp) hk) (by simp)
  have : lits.size-1 < lits.size := Nat.sub_lt hl (by simp)

  -- `sumsBlock[k-1][lits.size-1]`
  -- <=> k-1 < ∑ j, lits[j]
  -- <=> k ≤ ∑ j, lits[j]
  addClause #[ sumsBlock[k-1][lits.size-1] ]

open Model.PropForm.Notation in
def partialSumsEqualK (lits : Array ILit) (hl : lits.size > 0) (k : Nat) (hk : k > 0) : EncCNF Unit :=
  newCtx s!"pSums={k}" do
  have : lits.size-1 < lits.size := Nat.sub_lt ‹_› (by simp)
  have : k-1 < k+1 := Nat.le_step <| Nat.sub_lt ‹_› (by simp)
  let sumsBlock ← partialSumsBlock lits (k+1) (Nat.succ_le_succ hk)

  -- `¬sumsBlock[k][lits.size-1]`
  -- <=> ¬(k < ∑ j, lits[j])
  -- <=> k ≥ ∑ j, lits[j]
  tseitin (¬sumsBlock[k][lits.size-1])

  -- `sumsBlock[k-1][lits.size-1]`
  -- <=> k-1 < ∑ j, lits[j]
  -- <=> k ≤ ∑ j, lits[j]
  tseitin (sumsBlock[k-1][lits.size-1])

mutual
def atMostK (lits : Array ILit) k :=
  newCtx s!"atMost{k}" do
  if hz : k = 0 then
    for l in lits do
      addClause #[ -l ]
  else if k = 1 then
    atMostOne lits
  else if habove : k ≥ lits.size then
    -- trivially true
    return
  else if lits.size-k < k then
    atLeastK (lits.map (- ·)) (lits.size-k)
  else
    have : k > 0 := Nat.pos_of_ne_zero hz
    have : lits.size > 0 := Nat.lt_trans ‹_› (Nat.lt_of_not_le habove)
    partialSumsAtMostK lits ‹_› k ‹_›

def atLeastK (lits : Array ILit) k :=
  newCtx s!"atLeast{k}" do
  if hz : k = 0 then
    -- trivially true
    return
  else if k = 1 then
    addClause lits
  else if k = lits.size then
    -- ⋀{l ∈ lits} l
    for l in lits do
      addClause #[l]
  else if habove : k > lits.size then
    -- trivially false
    tseitin .fls
  else if lits.size-k < k then
    atMostK (lits.map (- ·)) (lits.size-k)
  else
    have : k > 0 := Nat.pos_of_ne_zero hz
    have : lits.size > 0 := Nat.lt_of_lt_of_le ‹_› (Nat.ge_of_not_lt habove)
    partialSumsAtMostK lits ‹_› k ‹_›
end

/-- ∑ᵢ lits[i] = k -/
def equalK (lits : Array ILit) (k : Nat) : EncCNF Unit :=
  newCtx s!"equal{k}" <| do
  if hl : lits.size < k then
    -- trivially false
    tseitin .fls
  else if hk:k = 0 then
    for l in lits do
      addClause #[ -l ]
  else if k = 1 then
    addClause lits
    atMostOne lits
  else if lits.size - k < k then
    equalK (lits.map (- ·)) (lits.size - k)
  else
    have : k > 0 := Nat.pos_of_ne_zero hk
    have : lits.size > 0 := Nat.lt_of_lt_of_le this (Nat.ge_of_not_lt hl)
    partialSumsEqualK lits ‹_› k ‹_›
