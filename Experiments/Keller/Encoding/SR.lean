/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Trestle.Encode
import Experiments.Keller.SR

import Experiments.Keller.Encoding.Spec
import Experiments.Keller.SymmBreak.MatrixGen

namespace Keller.Encoding

open Trestle

def AllVars.reorder (f : Fin n ≃ Fin n) : AllVars n s → AllVars n s :=
  let iMap : BitVec n → BitVec n := fun i => BitVec.ofFn ( i[f.symm ·] )
  fun
  | .x i j k => .x (iMap i) (f j) k
  | .y i i' j k =>
    -- the y vars are symmetric in the `i`s, and we only use the one where `i` < `i'`
    -- so we need to figure out which one is which after the mapping
    let (i1,i2) := if iMap i < iMap i' then (iMap i, iMap i') else (iMap i', iMap i)
    .y i1 i2 (f j) k
  | .z i i' j =>
    -- see above
    let (i1,i2) := if iMap i < iMap i' then (iMap i, iMap i') else (iMap i', iMap i)
    .z i1 i2 (f j)

def AllVars.renumber (f : Fin n → Fin s → Fin s) : AllVars n s → AllVars n s
| .x i j k => .x i j (f j k)
| .y i i' j k => .y i i' j (f j k)
| .z i i' j => .z i i' j

namespace SR


/-- Given a mapping, this returns all the substitutions for all "changed" variables -/
def substsOfMap (f : AllVars n s → AllVars n s) : Array (AllVars n s × Literal (AllVars n s)) := Id.run do
  let subst : AllVars n s → _ × _ := fun v => (v, Literal.pos (f v))

  let mut substs : Array (AllVars n s × Literal (AllVars n s)) := #[]
  -- x_i,j,k <-> x_map(i),j',k
  for i in allBitVecs n do
    for j in Array.finRange n do
      for k in Array.finRange s do
        substs := substs.push <| subst <| .x i j  k

  -- y_i,i',j,k <-> y_map(i),map(i'),j',k
  for i in allBitVecs n do
    for jdiff in Array.finRange n do
      let i' := i ^^^ BitVec.oneAt jdiff
      if i < i' then
        for j in Array.finRange n do
          if j ≠ jdiff then
            for k in Array.finRange s do
              substs := substs.push <| subst <| .y i i' j  k

  -- z_i,i',j <-> z_map(i),map(i'),j'
  for i in allBitVecs n do
    for i' in allBitVecs n do
      if i < i' then
        for j in Array.finRange n do
          substs := substs.push <| subst <| .z i i' j

  return substs.filter (fun (v,l) => v ≠ l.toVar)

def reorderSubsts {s} (j j' : Fin n) :=
  substsOfMap (s := s) <| AllVars.reorder <| Equiv.swap j j'

def renumberSubsts (j : Fin n) (perm : Equiv.Perm (Fin s)) := Id.run do
  substsOfMap <| AllVars.renumber (fun j' => if j' = j then perm else Equiv.refl _)

/-! ### SR Proof

We can add so many facts!
-/

abbrev SRGen (n s) := ReaderT (SR.Line (Literal (AllVars n s)) → IO Unit) IO
def SRGen.write (L : SR.Line (Literal (AllVars n s))) : SRGen n s Unit := do
  let printer ← read
  printer L

def bound (idx : BitVec n) (j : Fin n) (ltK : Nat) : SRGen n s Unit := do
  if h : ltK = 0 ∨ ltK > s then
    return
  else
  have : 0 < ltK ∧ ltK ≤ s := by omega
  let k_canonical : Fin s := ⟨ltK-1, by omega⟩

  for hk : k_to_block in [ltK:s] do
    have : ltK < s := Nat.lt_of_le_of_lt hk.lower hk.upper
    let k_to_block : Fin s := ⟨k_to_block,hk.upper⟩
    SRGen.write <|
      SR.mkLine
        (c := #[ Literal.neg <| .x idx j k_to_block ])
        (true_lits := Array.finRange s |>.map fun k =>
          Literal.mk (.x idx j k) (k = k_canonical))
        (substs := renumberSubsts j <| Equiv.swap k_canonical k_to_block)


/-- ##### Renumber c3

for all j in [2:n], assume `c3[j] < 2`
-/
def c3_bounds : SRGen n s Unit := do
  for hj : j in [2:n] do
    let j : Fin n := ⟨j,hj.upper⟩
    bound 3 j 2


/-- ##### Fix c3[2:5]
Now `c3[2] = c3[3] = 1` by unit prop.
We can also show `c3[4] = 1` with some quick casework.
We do not know about `c3[5]` and `c3[6]` yet, but can case on them down the road.
-/
def c3_fixed : SRGen n s Unit := do
  if h : n ≥ 5 ∧ s ≥ 2 then
    let one : Fin s := ⟨1,by omega⟩
    let two : Fin n := ⟨2,by omega⟩
    let three : Fin n := ⟨3,by omega⟩
    let four : Fin n := ⟨4,by omega⟩
    SRGen.write <| SR.mkLine #[ .pos <| .x 3 two one   ] (true_lits := #[]) (substs := #[])
    SRGen.write <| SR.mkLine #[ .pos <| .x 3 three one ] (true_lits := #[]) (substs := #[])
    SRGen.write <| SR.mkLine #[ .neg <| .x 7 three one, .pos <| .x 3 four one ] (true_lits := #[]) (substs := #[])
    SRGen.write <| SR.mkLine #[ .neg <| .x 11 two one,  .pos <| .x 3 four one ] (true_lits := #[]) (substs := #[])
    SRGen.write <| SR.mkLine #[ .pos <| .x 3 four one  ] (true_lits := #[]) (substs := #[])



/-! #### cX Constraints

Now we look at the special `cX` indices
(for `n=7`, these are `i=7, 11, 19, 35, 67`).
-/

def cX (row : Nat) (h : n ≥ 2 ∧ row + 2 < n := by omega) : BitVec n :=
  SymmBreak.C3Zeros.X (n := n-2) (row+2) (by omega)
  |>.cast (by omega)

/-- ##### Bound `cX`

In every column `j`, the `r`'th special index `cX[r]`
can be bounded below `3+r`
-/
def cX_bounds (j : Fin n) : SRGen n s Unit := do
  for hi : row in [0:min 3 (n-2)] do
    have : row < n-2 := by
      have : _ < min _ _ := hi.upper
      omega
    let idx : BitVec n := cX row

    bound idx j (row+3)


/-! ##### Increment Sorted Columns

Each column `2 ≤ j` can be constrained to be inc-sorted
on the `cX`s by renumbering.
We iterate over all non-inc-sorted colorings of the column,
blocking each one by mapping to its canonical version.
-/

def generateColorVecs (hdLt : Nat) (len : Nat) : List (Vector (Fin s) len) :=
  match len with
  | 0 => [#v[]]
  | len+1 =>
    let pres := generateColorVecs hdLt len
    let lasts : List (Fin s) :=
      List.range (min s (hdLt+len))
      |>.pmap (⟨·,·⟩) (by simp; omega)
    pres.flatMap fun pre =>
      lasts.map fun last =>
        pre.push last

/-- all the ways we can color the cX indices for columns 2/3/4 -/
def col234_colorings :=
  let colorings := generateColorVecs (hdLt := 3) (len := 3)
  colorings.map fun coloring =>
    let perm := renumberIncr' (s := 5) (L := 0 :: 1 :: (coloring.map (·.val) |>.toList))
      (by simp)
    let renumbered := coloring.map perm
    if coloring == renumbered then
      Sum.inl coloring
    else
      Sum.inr (coloring, perm, renumbered)

/-- all the ways we can color *c3 and cX* indices for columns 5+ -/
def col5_colorings (s) (h : s ≥ 2) :=
  let colorings := generateColorVecs (hdLt := 2) (len := 4)
  colorings.map fun coloring =>
    let perm := renumberIncr' (s := s) (L := 0 :: (coloring.map (·.val) |>.toList))
      (by simp; omega)
    let renumbered := coloring.map perm
    if coloring == renumbered then
      Sum.inl coloring
    else
      Sum.inr (coloring, perm, renumbered)

/-- all the ways to color columns 5+,
but with column permutations. -/
def col5n_colorings (s) (h : s ≥ 2) :=
  let colorings := col5_colorings s h |>.filterMap (·.getLeft?)
  let vec_colorings : List (Vector (Vector (Fin s) 4) 2) :=
    colorings.flatMap fun a => colorings.map fun b => #v[a,b]
  vec_colorings.filterMap fun coloring =>
    if coloring[0][0].val = 0 ∧ coloring[1][0].val = 1 then none
    else some <|
    if coloring[0] ≥ coloring[1] then
      Sum.inl coloring
    else
      Sum.inr (coloring, #v[coloring[1],coloring[0]])

def col234_incSorted (j : Nat) (hj : 2 ≤ j ∧ j < 5 ∧ j < n) : SRGen n s Unit := do
  if h : n < 5 ∨ s < 5 then return else

  let j : Fin n := ⟨j, by omega⟩
  have : j.val < 5 := by simp_all [j]

  for (coloring,perm,renumbered) in
      col234_colorings.filterMap (·.getRight?) do

    -- The diagonal element is always 1, so skip assns where that doesn't hold
    if coloring[j.val-2]'(by omega) ≠ 1 then continue

    -- The clause we want to block (negation of `coloring`)
    let clause : Clause (Literal <| AllVars n s) :=
      Array.ofFn (n := 3) fun row =>
        .neg <| .x (cX row) j (coloring[row].castLE (by omega))

    -- Assign all the literals associated with these 3 `(idx,j)` pairs
    let true_lits :=
      Array.flatten <|
      Array.ofFn (n := 3) fun row =>
        Array.ofFn (n := s) fun k =>
          Literal.mk (AllVars.x (cX row) j k) (k.val = renumbered[row].val)

    -- substitute everything else via perm
    let substs := renumberSubsts j (
      (show 5+(s-5) = s by omega) ▸ SymmBreak.Matrix.extendPerm perm.symm (n := s-5))

    SRGen.write <| SR.mkLine clause (hc := by simp [clause]) true_lits substs

def col5_incSorted (j : Nat) (hj : 5 ≤ j ∧ j < n) : SRGen n s Unit := do
  if h : n < 5 ∨ s < 5 then return else

  let j : Fin n := ⟨j, by omega⟩
  have : j.val ≥ 5 := by simp_all [j]

  for (coloring,perm,renumbered) in
      (col5_colorings s (by omega)).filterMap (·.getRight?) do

    -- The s-gap between c3 and cX[j-2] is always in column `j`,
    -- so skip any colorings where they are unequal
    -- if coloring[0].val ≠ coloring[1+j.val-2]'(by omega) then continue

    -- The clause we want to block (negation of `coloring`)
    let clause : Clause (Literal <| AllVars n s) :=
      Array.ofFn (n := 4) fun row =>
        let idx : BitVec n := if row.val = 0 then 3 else cX (row-1)
        .neg <| .x idx j (coloring[row].castLE (by omega))

    -- Assign all the literals associated with these 3 `(idx,j)` pairs
    let true_lits :=
      Array.flatten <|
      Array.ofFn (n := 4) fun row =>
        let idx : BitVec n := if row.val = 0 then 3 else cX (row-1)
        Array.ofFn (n := s) fun k =>
          Literal.mk (AllVars.x idx j k) (k.val = renumbered[row].val)

    -- substitute everything else via perm
    let substs := renumberSubsts j perm.symm

    SRGen.write <|
      SR.mkLine clause (hc := by simp [clause]) true_lits substs

def col5n_sorted (n s) : SRGen n s Unit := do
  IO.println s!"  (starting col5n_sorted)"

  if h : n = 7 ∧ _ then
    -- the substitution is always swapping 5/6
    let substs := reorderSubsts ⟨5,by omega⟩ ⟨6,by omega⟩

    let colColorings := col5_colorings s h.2 |>.filterMap (·.getLeft?)

    for hlen : len in [1:4] do
      have : len < 4 := hlen.upper
      let biggers := colColorings
        |>.map (·.take (len+1) |>.cast (m := len+1) (by omega))
        |>.dedup

      for bigger in biggers do
        let pref := bigger.take len |>.cast (m := len) (by omega)
        let lastR := bigger[len]

        for hlastL : lastL in [0:lastR] do
          let lastL : Fin s := ⟨lastL, have : lastL < lastR := hlastL.upper; by omega⟩
          -- We want to block the case where both columns 5 and 6 are `pref`,
          -- and the next element is `k` in 5 and `last` in 6
          let clause : Clause (Literal <| AllVars n s) :=
            Array.flatten (Array.ofFn (n := len+1) fun row =>
              let idx : BitVec n := if row.val = 0 then 3 else cX (row-1)
              let left := .neg <| .x idx ⟨5,by omega⟩ (if h : row.val < len then pref[row] else lastL)
              let right := .neg <| .x idx ⟨6,by omega⟩ (if h : row.val < len then pref[row] else lastR)
              #[ left, right ]
            )

          -- Assign all the literals in question to match `swapped`
          let true_lits :=
            Array.flatten <| Array.flatten <| Array.ofFn (n := len+1) fun row =>
              let idx : BitVec n := if row.val = 0 then 3 else cX (row-1)
              Array.ofFn (n := s) fun k =>
                #[ Literal.mk (AllVars.x idx ⟨5,by omega⟩ k) (k.val = if h : row.val < len then pref[row] else lastR)
                ,  Literal.mk (AllVars.x idx ⟨6,by omega⟩ k) (k.val = if h : row.val < len then pref[row] else lastL) ]


          SRGen.write <|
            SR.mkLine clause (hc := by simp [clause, ← Array.sum_eq_sum_toList])
                    true_lits substs



/-! ##### Canonical matrices

Interpreting the cX indices and columns `j ≥ 2` as a matrix,
we can do column reorderings and renumberings to eliminate many
potential color assignments within this matrix.
-/

def canonicalMats := SymmBreak.Matrix.matsUpTo 3

/-- convert a matrix automorphism (from noncanonical to canononical)
to a mapping (from canonical to noncanonical).

NB the change in direction.
-/
def autoToMap (a : SymmBreak.Matrix.Auto m) (h : 2+m ≤ n) : AllVars n s → AllVars n s :=
  match a with
  | .renumber f =>
      AllVars.renumber fun j k =>
        if h' : 2 ≤ j.val ∧ j.val < 2+m then
          let x := (f ⟨j-2,by omega⟩).symm k
          if h'' : x < s then
            ⟨x,h''⟩
          else
            have : Inhabited (Fin s) := ⟨k⟩
            panic! "renumber maps outside s"
        else
          k
  | .reorder p =>
      AllVars.reorder <|
        Equiv.Perm.extendDomain (p := fun j => 2 ≤ j.val ∧ j.val < 2+m)
          p.symm
          { toFun := (⟨⟨·.val+2,by omega⟩,by simp; omega⟩)
            invFun := (⟨·.val-2,by omega⟩)
            left_inv := by intro; simp, right_inv := by rintro ⟨a,b⟩; ext; simp; omega
          }
  | .trans a1 a2 =>
      fun x => x |> autoToMap a2 h |> autoToMap a1 h
  | .lift a1 =>
      autoToMap a1 (Nat.le_of_lt h)

def mat_canonical (matSize : Nat) (h : 2 ≤ matSize ∧ matSize ≤ 3) : SRGen n s Unit := do
  if h : ¬(2 + matSize ≤ n ∧ s ≥ 2 + matSize) then return else
  have := not_not.mp h

  have : NeZero s := ⟨by omega⟩

  for (x,v) in (canonicalMats.get matSize).map do
    match v with
    | .canon _ => pure ()
    | .noncanon canonical auto =>

      -- The clause we want to block (negation of `x`)
      let clause :=
        Array.finRange matSize |>.flatMap fun row => Array.ofFn (n := matSize) fun col =>
          Literal.neg <|
            AllVars.x (cX row.val) ⟨col+2, by omega⟩ (Fin.ofNat' s x.data[row][col])

      have : clause.size > 0 := by
        simp [clause, ← Array.sum_eq_sum_toList]; omega

      -- Assign all the literals associated with these rows/cols
      -- to their value under the canonical case
      let true_lits :=
        (Array.ofFn (n := matSize) fun row =>
          Array.ofFn (n := matSize) fun col =>
            Array.ofFn (n := s) fun k =>
              Literal.mk
                (AllVars.x (cX row.val) ⟨col+2, by omega⟩ k)
                (k.val = canonical.data[row][col])
        ).flatten.flatten

      -- Permute all the other variables based on the given `auto`
      let subst := substsOfMap <| autoToMap auto (by omega)

      SRGen.write <|
        SR.mkLine clause ‹_› true_lits subst

def extra_renumber_bounds (j : Fin n) : SRGen n s Unit := do
  if h : ¬(s > 6) then return else
  have := not_not.mp h

  let mut ltK : Fin s := ⟨6,this⟩
  for idx in allBitVecs n do
    if idx ∈ [0,1,3,7,11,19] then
      continue

    if idx[1]! = true then
      bound idx j ltK
      match ltK.succ? with
      | some next => ltK := next
      | none => break

def all (n s) : SRGen n s Unit := do
  c3_bounds
  c3_fixed

  for hj : j in [2:n] do
    have : 2 ≤ j ∧ j < n := ⟨hj.lower,hj.upper⟩
    cX_bounds ⟨j,hj.upper⟩

    if h : j < 5 then
      col234_incSorted j (by omega)
    else
      col5_incSorted j (by omega)

    if h : 3 ≤ j ∧ j < 5 then
      mat_canonical (j-1) (by omega)

  --for hj : j in [2:n] do
  --  have : 2 ≤ j ∧ j < n := ⟨hj.lower,hj.upper⟩
  --  extra_renumber_bounds ⟨j,hj.upper⟩

  col5n_sorted n s
