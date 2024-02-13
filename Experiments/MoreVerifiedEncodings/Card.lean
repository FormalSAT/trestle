import LeanSAT.Encode.VEncCNF
import LeanSAT.Encode.Tseitin

namespace LeanSAT.Encode

open VEncCNF Model PropFun

variable [LitVar L ν] [LawfulLitVar L ν]
    [DecidableEq L] [DecidableEq ν] [ErasedFintype ν]

def card (lits : Multiset L) (τ : PropAssignment ν) : Nat :=
  lits.countP (τ ⊨ LitVar.toPropFun ·)

noncomputable def cardPred (lits : Multiset L) (P : Nat → Prop) [DecidablePred P] :=
  have : Fintype ν := ErasedFintype.toFintype
  fun τ => P (card lits τ)

@[simp] theorem satisfies_cardPred (lits : Multiset L) (P) [DecidablePred P] (τ)
  : cardPred lits P τ ↔ P (card lits τ) := by
  let _ : Fintype ν := ErasedFintype.toFintype
  unfold cardPred; simp

noncomputable abbrev atMost (k : Nat) (lits : Multiset L) := cardPred lits (· ≤ k)
noncomputable abbrev atLeast (k : Nat) (lits : Multiset L) := cardPred lits (· ≥ k)

theorem ofList_eq_map_get (L : List α)
  : Multiset.ofList L = (Finset.univ.val.map fun i => L.get i) := by
  conv => lhs; rw [← List.finRange_map_get (l := L)]

@[inline]
def amoPairwise (lits : Array L) :
    VEncCNF L Unit (atMost 1 (Multiset.ofList lits.data)) :=
  -- for every pair x,y of literals in `lits`, they can't both be true
  (for_all (Array.ofFn id) fun (i : Fin lits.size) =>
    for_all (Array.ofFn (fun (j : Fin (lits.size - i.succ)) =>
        (Fin.addNat j i.succ).cast (by
          cases i; cases j; simp at *; apply Nat.sub_add_cancel; assumption)))
      fun (j : Fin lits.size) =>
        addClause #[-lits[i], -lits[j]]
  ).mapProp (by
    rcases lits with ⟨list⟩
    ext τ
    simp [Clause.toPropFun, any, Array.getElem_eq_data_get]
    simp [Array.mem_def, Array.size]
    simp_rw [← not_and_or, not_and]
    rw [ofList_eq_map_get, card, Multiset.countP_map]
    rw [← Finset.filter_val, ← Finset.card_def, Finset.card_le_one]
    simp
    constructor
    · rintro l ⟨i,hi⟩ hτi ⟨j,hj⟩ hτj
      simp; by_contra i_ne_j
      if i < j then
        apply l ⟨i,hi⟩ ⟨j-(i+1),_⟩ hτi
        · convert hτj
          simp
          omega
        · omega
      else
        have : j < i := by omega
        apply l ⟨j,hj⟩ ⟨i-(j+1),_⟩ hτj
        · convert hτi
          simp
          omega
        · omega
    · rintro r ⟨x,hx⟩ ⟨y,hy⟩ hτx hτy
      specialize r _ hτx _ hτy
      simp at r
      omega
  )

open EncCNF (WithTemps) in
/-- At-most-one cut4 encoding. The literals are divided into many small groups,
like `lits = L₁ ++ L₂ ++ ... ++ Lₙ`.
Then we add `n` auxiliary variables `tᵢ` representing whether a literal
to the left of `Lᵢ` is true.
Then we can encode "at most one of `lits`" as a conjunction:
- ∀ i, at most one of `[tᵢ] ++ Lᵢ ++ [¬tᵢ₊₁]`
-/
def amoCut4 (lits : Array L) (h : lits.size > 4) : VEncCNF L Unit (atMost 1 (Multiset.ofList lits.data)) :=
  let firstGrpSize := 3
  let middleGrps := (lits.size - 5) / 2
  let lastGrpSize := lits.size - firstGrpSize - 2 * middleGrps
  withTemps (middleGrps + 1) (
    seq[
      amoPairwise #[
        WithTemps.var (lits[0]'(by trans 4; decide; assumption))
      , WithTemps.var (lits[1]'(by trans 4; decide; assumption))
      , WithTemps.var (lits[2]'(by trans 4; decide; assumption))
      , WithTemps.temp 0
      ]
    , for_all (Array.ofFn id) (fun (i : Fin middleGrps) =>
        amoPairwise #[
          WithTemps.temp i.castSucc
        , WithTemps.var (lits[3 + 2 * i.val]'(by
            rcases i with ⟨i,hi⟩; simp (config := {zeta:=true}) at hi ⊢
            zify at hi ⊢; simp [Nat.cast_sub h] at hi; omega))
        , WithTemps.var (lits[4 + 2 * i.val]'(by
            rcases i with ⟨i,hi⟩; simp (config := {zeta:=true}) at hi ⊢
            zify at hi ⊢; simp [Nat.cast_sub h] at hi; omega))
        , WithTemps.temp i.succ
        ]
        )
    , amoPairwise <|
        #[WithTemps.temp <| Fin.last middleGrps] ++
        lits[lits.size-lastGrpSize:lits.size].toArray.map WithTemps.var
    ]
  )
  |>.mapProp (by
    ext τ; simp
    sorry)

def atMostOne (lits : Array L) : VEncCNF L Unit (atMost 1 <| Multiset.ofList lits.data) :=
  if h : lits.size ≤ 4 then
    amoPairwise lits
  else
    amoCut4 lits (by omega)

#exit

open Model.PropForm.Notation in
def partialSumsBlock (lits : Array L) (temps : Fin k → Fin lits.size → ν)
  : VEncCNF L Unit (fun τ =>
      ∀ i j, τ (temps i j) ↔ i < card (Multiset.ofList lits[0:j].toArray.toList) τ) :=
  -- `temps i j` ↔ i < (∑ `j' ≤ j`, `lits[j']`)
  (for_all (List.fins k) fun i =>
    for_all (List.fins lits.size) fun j =>
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
  ).mapProp (by
    sorry)


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
