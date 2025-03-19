/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.Autos

import Experiments.Keller.SymmBreak.IncSorted

namespace Keller.SymmBreak

/-! ## Matrix Symmetries

After all symmetry breaking up to `C3Zeros`,
we can still freely swap columns `j ≥ 2`
(so long as `c3[j'] = 1` for `2 ≤ j' ≤ j`).

So, we interpret the colors of the columns `2 ≤ j < m+2`
on the first `m` `cX` indices as an `m×m` matrix.
Then we calculate canonical representatives for each equivalence class
under column swaps and renumbering operations,
keeping track of the automorphism that evidences each element's
equivalence to the canonical representative.

In the encoding, we emit SR clauses that ban each non-canonical element,
using the automorphism as the SR witness.
-/

@[ext]
structure Matrix (m : Nat) where
  data : Vector (Vector Nat m) m
  /-- Each row should be bounded at 2+r (can always renumber into this state) -/
  bounds : ∀ r c : Fin m, data[r][c] ≤ 2 + r
  /-- Every index is 1 in either the data or the tranposed data -/
  transpose_one : ∀ r c : Fin m, data[r][c] = 1 ∨ data[c][r] = 1
deriving DecidableEq, Repr

namespace Matrix

nonrec def compare (x y : Matrix m) : Ordering := Id.run do
  for hs : step in [1:m] do
    let step : Fin m := ⟨step, hs.upper⟩
    -- check `col = step`
    for hr : row in [0:step] do
      let row : Fin m := ⟨row, Nat.lt_trans hr.upper step.isLt⟩
      let ord := aux x.data[row][step] y.data[row][step]
      if ord ≠ .eq then return ord

    -- check `row = step`
    for hc : col in [0:step] do
      let col : Fin m := ⟨col, Nat.lt_trans hc.upper step.isLt⟩
      let ord := aux x.data[step][col] y.data[step][col]
      if ord ≠ .eq then return ord

  return .eq
where aux (a b : Nat) : Ordering :=
  if a = b then .eq else
  if a = 1 then .lt else
  if b = 1 then .gt else
  compare a b

instance : Ord (Matrix m) where compare := compare

instance : BEq (Matrix m) := Ord.toBEq inferInstance

instance : LE (Matrix m) := leOfOrd
instance : DecidableRel (α := Matrix m) (· ≤ ·) := Ord.instDecidableRelLe
instance : LT (Matrix m) := ltOfOrd
instance : DecidableRel (α := Matrix m) (· < ·) := Ord.instDecidableRelLt


/-- Generate all possible values for the last row of the matrix extension.
`kBound` is the (exclusive) upper bound for elements. -/
def extend.lastRows (kBound : Nat) (len : Nat) : Array (Vector Nat len) :=
  match len with
  | 0 => #[#v[]]
  | len+1 =>
  extend.lastRows kBound len |>.flatMap (fun prefixArr =>
    Array.ofFn (n := kBound) fun i => prefixArr.push i)

theorem extend.lastRows_bounded : ∀ v ∈ lastRows kBound len, ∀ x ∈ v, x < kBound := by
  intro v v_mem_lastRows x x_mem_v
  replace v_mem_lastRows := Array.mem_def.mp v_mem_lastRows
  replace x_mem_v := Array.mem_def.mp x_mem_v.val
  induction len with
  | zero =>
    simp [lastRows] at v_mem_lastRows; subst v
    simp at x_mem_v
  | succ len ih =>
    simp [lastRows, -Array.mem_toList, List.mem_ofFn] at v_mem_lastRows
    rcases v_mem_lastRows with ⟨v_pre,v_pre_mem,y,rfl⟩
    specialize ih v_pre v_pre_mem
    clear v_pre_mem
    simp at x_mem_v
    aesop

/-- Given matrix `x` and extending last row `lastRow`,
returns array of possible values for row `row` extending `x`.
The notable complexity here is that when `lastRow[row] ≠ 1`,
we are forced to put a `1` in this row.
-/
def extend.fillRow (x : Matrix m) (lastRow : Vector Nat m) (row : Fin m) :
      Array (Vector Nat (m+1)) :=
  if lastRow[row] = 1 then
    Array.ofFn (n := row+3) fun lastVal =>
      x.data[row].push lastVal
  else
    #[ x.data[row].push 1 ]

def extend.fillLastCols (x : Matrix m) (lastRow : Vector Nat m)
      (upTo : Nat) (upTo_bound : upTo ≤ m) :
      Array <| Vector (Vector Nat (m+1)) upTo :=
  match upTo with
  | 0 => #[#v[]]
  | upTo+1 =>
    let prevs := fillLastCols x lastRow upTo (Nat.le_of_lt upTo_bound)
    let thisRow := extend.fillRow x lastRow ⟨upTo, upTo_bound⟩
    -- combine each `prev` possibility with each `thisRow` possibility
    prevs.flatMap (fun prev =>
      thisRow.map (prev.push)
    )

theorem extend.fillLastCols_bounded (x : Matrix m) (lastRow : Vector ℕ m)
  (prevs : Vector (Vector ℕ (m + 1)) m)
  (prevs_mem : prevs ∈ fillLastCols x lastRow m (Nat.le_refl _))
  (r c : Nat) (hr : r < m) (hc : c < m+1) :
  prevs[r][c] ≤ 2 + r := sorry

theorem extend.fillLastCols_transposeOne_1 (x : Matrix m) (lastRow : Vector ℕ m)
  (prevs : Vector (Vector ℕ (m + 1)) m)
  (prevs_mem : prevs ∈ fillLastCols x lastRow m (Nat.le_refl _))
  (r c : Nat) (hr : r < m) (hc : c < m) :
  prevs[r][c] = 1 ∨ prevs[c][r] = 1 := sorry

theorem extend.fillLastCols_transposeOne_2 (x : Matrix m) (lastRow : Vector ℕ m)
  (prevs : Vector (Vector ℕ (m + 1)) m)
  (prevs_mem : prevs ∈ fillLastCols x lastRow m (Nat.le_refl _))
  (r : Nat) (hr : r < m) :
  prevs[r][m] = 1 ∨ lastRow[r] = 1 := sorry

/-- Given a matrix `x` and an extending last row `lastRow`,
generate all viable matrices by filling in the last column.

Notably, in order to maintain the `transpose_one` invariant,
we check whether the last row's corresponding element is *not* one,
in which case we are forced to place a one in the last column instead.
-/
def extend.withLastRow (x : Matrix m) (lastRow : Vector Nat m)
  (lastRow_bounded : ∀ x ∈ lastRow, x < 2+m) : Array (Matrix (m+1)) :=
  let allButLastRow := fillLastCols x lastRow m (Nat.le_refl _)
  let datas := allButLastRow.map (·.push (lastRow.push 1))
  datas.pmap (P := fun _ => _ ∧ _) (fun data h => {
    data
    bounds := h.1
    transpose_one := h.2
  }) (by
    intro data data_mem
    simp +zetaDelta at data_mem
    rcases data_mem with ⟨prevRows,prevRows_mem,rfl⟩
    constructor
    · intro r c
      if r.val < m then
        simp [*]
        apply fillLastCols_bounded
        apply prevRows_mem
      else
        have : r.val = m := by omega
        simp [this]
        if c.val < m then
          simp [*]
          apply Nat.le_of_lt; apply lastRow_bounded
          apply Vector.Mem.mk; rw [← Vector.getElem_toArray]
          refine Array.getElem_mem ?_
          simp [*]
        else
          have : c.val = m := by omega
          simp [this]; omega
    · intro r c
      if r.val < m then
        simp [*]
        if c.val < m then
          simp [*]
          apply fillLastCols_transposeOne_1
          apply prevRows_mem
        else
          have : c.val = m := by omega
          simp [*]
          apply fillLastCols_transposeOne_2
          apply prevRows_mem
      else
        have : r.val = m := by omega
        simp [this]
        if c.val < m then
          simp [*]
          rw [or_comm]
          apply fillLastCols_transposeOne_2
          apply prevRows_mem
        else
          have : c.val = m := by omega
          simp [this]
  )

def extend (x : Matrix m) : Array (Matrix (m+1)) :=
  let lastRows : Array (Vector Nat m) := extend.lastRows (2+m) m
  lastRows.pmap (extend.withLastRow x)
    (by
      intro lastRow lastRow_mem
      simp [lastRows] at lastRow_mem
      apply extend.lastRows_bounded
      apply lastRow_mem
    )
  |>.flatten


#eval! extend {
  data := #v[#v[1,1],#v[2,1]]
  bounds := by decide
  transpose_one := by decide
} |>.map (·.data)

end Matrix
