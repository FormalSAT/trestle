/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.Autos

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




end Matrix
