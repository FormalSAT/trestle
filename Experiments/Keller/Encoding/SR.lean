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
  | .y i i' j =>
    -- the y vars are symmetric in the `i`s, and we only use the one where `i` < `i'`
    -- so we need to figure out which one is which after the mapping
    let (i1,i2) := if iMap i < iMap i' then (iMap i, iMap i') else (iMap i', iMap i)
    .y i1 i2 (f j)
  | .z i i' j =>
    -- see above
    let (i1,i2) := if iMap i < iMap i' then (iMap i, iMap i') else (iMap i', iMap i)
    .z i1 i2 (f j)

def AllVars.renumber (f : Fin n → Fin s → Fin s) : AllVars n s → AllVars n s
| .x i j k => .x i j (f j k)
| .y i i' j => .y i i' j
| .z i i' j => .z i i' j

/-- convert a matrix automorphism (from noncanonical to canononical)
to a mapping (from canonical to noncanonical).

NB the change in direction.
-/
def AllVars.autoToMap (a : SymmBreak.Matrix.Auto) (h : 5 ≤ n) : AllVars n s → AllVars n s :=
  match a with
  | .renumber f =>
      AllVars.renumber fun j k =>
        if h' : 2 ≤ j.val ∧ j.val < 5 then
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
        Equiv.Perm.extendDomain (p := fun j => 2 ≤ j.val ∧ j.val < 5)
          p.symm
          { toFun := (⟨⟨·.val+2,by omega⟩,by simp; omega⟩)
            invFun := (⟨·.val-2,by omega⟩)
            left_inv := by intro; simp, right_inv := by rintro ⟨a,b⟩; ext; simp; omega
          }
  | .trans a1 a2 =>
      fun x => x |> autoToMap a2 h |> autoToMap a1 h


namespace SR

abbrev SRGen (n s) := ReaderT (SR.Line (Literal (AllVars n s)) → IO Unit) IO
def SRGen.write (L : SR.Line (Literal (AllVars n s))) : SRGen n s Unit := do
  let printer ← read
  printer L

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
            substs := substs.push <| subst <| .y i i' j

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

/-! ##### Matrix Symmetries

Interpreting index `7, 11, 19` and dimension `2,3,4` as a matrix,
we can reorder columns to get rid of symmetric cases.
-/

open AllVars in
/-- First we can get rid of any assignment in which `x7,3,0`,
by swapping dimension 2/3. -/
def c7_3_nonzero (hn : n ≥ 5) (hs : s > 0) : SRGen n s Unit := do
  let clause := #[.neg (x 7 ⟨3,by omega⟩ ⟨0,hs⟩)]
  let true_lits := #[.pos (x 11 ⟨2,by omega⟩ ⟨0,hs⟩), .neg (x 7 ⟨3,by omega⟩ ⟨0,hs⟩)]
  let substs := reorderSubsts ⟨2,by omega⟩ ⟨3,by omega⟩
  SRGen.write <|
    SR.mkLine clause (by simp +zetaDelta) true_lits substs

section
local notation "X" => false
local notation "O" => true

-- the 5 non-identity permutations of {0,1,2}
def reverse : Equiv.Perm (Fin 3) := Equiv.setAll [(2,0)] (.refl _)
def rotL    : Equiv.Perm (Fin 3) := Equiv.setAll [(0,1), (1,2), (2,0)] (.refl _)
def rotR    : Equiv.Perm (Fin 3) := Equiv.setAll [(0,2), (1,0), (2,1)] (.refl _)
def swapL   : Equiv.Perm (Fin 3) := Equiv.setAll [(0,1)] (.refl _)
def swapR   : Equiv.Perm (Fin 3) := Equiv.setAll [(1,2)] (.refl _)

open Vars in
def mat_to_cube (v : Vector Bool 5) (hn : n ≥ 5) (hs : s > 0) :
      Cube (Literal (Vars n s)) :=
  have : NeZero s := ⟨Nat.pos_iff_ne_zero.mp hs⟩
  let j2 : Fin n := ⟨2,by omega⟩
  let j3 : Fin n := ⟨3,by omega⟩
  let j4 : Fin n := ⟨4,by omega⟩
  #[  .mk (x 11 j2 0) v[0],
      .mk (x  7 j4 0) v[1],
      .mk (x 19 j2 0) v[2],
      .mk (x 11 j4 0) v[3],
      .mk (x 19 j3 0) v[4], ]

def mat_to_cube_allvars (v : Vector Bool 5) (hn : n ≥ 5) (hs : s > 0) :
      Cube (Literal (AllVars n s)) :=
  mat_to_cube v hn hs |>.map _ (fun | .x i j k => .x i j k)

/-- This is a complete list of all the remaining assignments to
the zero color variables in the matrix.
Each element of the list is a (starting assignment),
and an optional pair (equiv assignment, dimension reordering witness).

110  110  110  111  111  111  111
010  011  011  011  011  010  111
111  101  111  011  111  111  111
-/
def matList : List (Vector Bool 5 × Option (Vector Bool 5 × Equiv.Perm (Fin 3))) := [
  (#v[O, O,X, O,X], none),
  (#v[O, O,X, X,O], none),
  (#v[O, O,X, X,X], none),
  (#v[O, X,O, O,X], some (#v[O, O,X, O,X], reverse)),
  (#v[O, X,O, X,O], some (#v[O, O,X, O,X], rotL)),
  (#v[O, X,O, X,X], none),
  (#v[O, X,X, O,X], none),
  (#v[O, X,X, X,O], some (#v[O, O,X, X,X], rotL)),
  (#v[O, X,X, X,X], none),
  (#v[X, O,X, O,X], some (#v[O, X,O, X,X], rotR)),
  (#v[X, O,X, X,O], some (#v[O, O,X, X,X], rotR)),
  (#v[X, O,X, X,X], some (#v[O, X,X, X,X], rotR)),
  (#v[X, X,O, O,X], some (#v[O, O,X, X,X], reverse)),
  (#v[X, X,O, X,O], some (#v[O, X,X, O,X], rotL)),
  (#v[X, X,O, X,X], some (#v[O, X,X, X,X], swapR)),
  (#v[X, X,X, O,X], some (#v[O, X,X, X,X], reverse)),
  (#v[X, X,X, X,O], some (#v[O, X,X, X,X], rotL)),
  (#v[X, X,X, X,X], none),
]

end

def mat_zeros_canonical (hn : n ≥ 5) (hs : s > 0) : SRGen n s Unit := do
  have : NeZero s := ⟨by omega⟩

  for (m,v) in matList do
    match v with
    | none => pure ()
    | some (mCanon, auto) =>

      -- The clause we want to block (negation of `m`)
      let clause : Cube _ := (mat_to_cube_allvars m (by omega) (by omega)).negate

      have : clause.size > 0 := by
        simp [clause, mat_to_cube, mat_to_cube_allvars, Cube.map, Cube.negate]

      -- Assign all the literals associated with these rows/cols
      -- to their value under the canonical case
      let true_lits := mat_to_cube_allvars mCanon (by omega) (by omega)

      -- Permute all the other variables based on the given `auto`
      let subst := substsOfMap (s := s) <| AllVars.reorder (
        auto.extendDomain (Equiv.ofLeftInverse' (α := Fin 3) (β := Fin n)
          (f := fun ⟨i,h⟩ => ⟨i+2,by omega⟩)
          (f_inv := fun ⟨i,h⟩ => if h : i < 5 then ⟨i-2,by omega⟩ else 0)
          (by rintro ⟨i,h⟩; have : i+2 < 5 := (by omega); simp [*]))
      )

      SRGen.write <|
        SR.mkLine clause ‹_› true_lits subst

set_option maxHeartbeats 1000000 in
def mat_canonical (hn : n ≥ 5) (hs : s ≥ 4): SRGen n s Unit := do
  have : NeZero s := ⟨by omega⟩

  for (x,v) in SymmBreak.Matrix.canonicalMats.map do
    match v with
    | .canon _ => pure ()
    | .noncanon canonical auto =>

      -- The clause we want to block (negation of `x`)
      let clause :=
        Array.finRange 3 |>.flatMap fun row => Array.ofFn (n := 3) fun col =>
          Literal.neg <|
            AllVars.x #[(7 : BitVec n),11,19][row] ⟨col+2, by omega⟩ (Fin.ofNat s x.data[row][col])

      have : clause.size > 0 := by
        simp [clause, ← Array.sum_eq_sum_toList]

      -- Assign all the literals associated with these rows/cols
      -- to their value under the canonical case
      let true_lits :=
        (Array.ofFn (n := 3) fun row =>
          Array.ofFn (n := 3) fun col =>
            Array.ofFn (n := s) fun k =>
              Literal.mk
                (AllVars.x #[(7 : BitVec n),11,19][row] ⟨col+2, by omega⟩ k)
                (k.val = canonical.data[row][col])
        ).flatten.flatten

      -- Permute all the other variables based on the given `auto`
      let subst := substsOfMap <| AllVars.autoToMap auto (by omega)

      SRGen.write <|
        SR.mkLine clause this true_lits subst



/-- ##### Bound matrix rows

In every column `j`, the matrix elements can be bounded below `3,4,5`
-/
def mat_rows_bound (j : Fin n) : SRGen n s Unit := do
  bound  7 j 3
  bound 11 j 4
  bound 19 j 5


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
def col234_colorings (hs : s ≥ 2) :=
  let colorings := generateColorVecs (s := s) (hdLt := 3) (len := 3)
  colorings.map fun coloring =>
    let perm := renumberIncr' (s := s) (L := 0 :: 1 :: (coloring.map (·.val) |>.toList))
      (by simp; omega)
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

/-- all the ways to color columns 5,6,
but with column permutations. -/
def col56_colorings (s) (h : s ≥ 2) :=
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

def col234_incSorted (hs : s ≥ 2) (j : Nat) (hj : 2 ≤ j ∧ j < 5 ∧ j < n) : SRGen n s Unit := do
  let j : Fin n := ⟨j, by omega⟩
  have : j.val < 5 := by simp_all [j]

  for (coloring,perm,renumbered) in
      (col234_colorings hs).filterMap (·.getRight?) do

    -- The diagonal element is always 1, so skip assns where that doesn't hold
    if (coloring[j.val-2]'(by omega)).val ≠ 1 then continue

    -- The clause we want to block (negation of `coloring`)
    let clause : Clause (Literal <| AllVars n s) :=
      Array.ofFn (n := 3) fun row =>
        .neg <| .x #[7,11,19][row] j (coloring[row].castLE (by omega))

    -- Assign all the literals associated with these 3 `(idx,j)` pairs
    let true_lits :=
      Array.flatten <|
      Array.ofFn (n := 3) fun row =>
        Array.ofFn (n := s) fun k =>
          Literal.mk (AllVars.x #[7,11,19][row] j k) (k.val = renumbered[row].val)

    -- substitute everything else via perm
    let substs := renumberSubsts j perm.symm

    SRGen.write <| SR.mkLine clause (hc := by simp [clause]) true_lits substs

def col5_incSorted (hs : s ≥ 2) (j : Nat) (hj : 5 ≤ j ∧ j < n) : SRGen n s Unit := do
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
        let idx : BitVec n := #[3,7,11,19][row]
        .neg <| .x idx j (coloring[row].castLE (by omega))

    -- Assign all the literals associated with these 3 `(idx,j)` pairs
    let true_lits :=
      Array.flatten <|
      Array.ofFn (n := 4) fun row =>
        let idx : BitVec n := #[3,7,11,19][row]
        Array.ofFn (n := s) fun k =>
          Literal.mk (AllVars.x idx j k) (k.val = renumbered[row].val)

    -- substitute everything else via perm
    let substs := renumberSubsts j perm.symm

    SRGen.write <|
      SR.mkLine clause (hc := by simp [clause]) true_lits substs

def col56_zeros_sorted (n s) ( h : n = 7 ∧ s > 0) : SRGen n s Unit := do
  IO.println s!"  (starting col56_zeros_sorted)"

  have : NeZero s := ⟨Nat.ne_zero_iff_zero_lt.mpr h.2⟩
  let five := ⟨5,by omega⟩
  let six := ⟨6,by omega⟩

  -- the substitution is always swapping 5/6
  let substs := reorderSubsts (n := n) five six

  let idxs : Vector (BitVec n) 4 := #v[3,7,11,19]

  for hlen : len in [0:4] do
    have : len < 4 := hlen.upper

    for hi : i in [0:2^len] do
      let pref : Vector Bool len := Vector.ofFn (fun r => (i >>> r.val) % 2 = 0)

      -- We want to block the case where both columns 5 and 6 are `pref`
      let prefCube : Cube (Literal <| AllVars n s) :=
        Array.ofFn (n := len) (fun r =>
          #[.mk (.x idxs[r] five 0) pref[r], .mk (.x idxs[r] six 0) pref[r]])
        |>.flatten

      -- noncanonical goes 01 in last row, canon goes 10
      let noncanon : Cube (Literal <| AllVars n s) :=
        prefCube.and #[.pos (.x idxs[len] five 0), .neg (.x idxs[len] six 0)]
      let canon : Cube (Literal <| AllVars n s) :=
        prefCube.and #[.neg (.x idxs[len] five 0), .pos (.x idxs[len] six 0)]

      let clause := noncanon.negate
      let true_lits := canon

      SRGen.write <| SR.mkLine clause
        (hc := by simp [clause, noncanon, prefCube, Cube.and, Cube.negate, Cube.toArray, ← Array.sum_eq_sum_toList])
        true_lits substs

def col56_sorted (n s) (h : n = 7 ∧ s ≥ 2): SRGen n s Unit := do
  IO.println s!"  (starting col56_sorted)"

  -- the substitution is always swapping 5/6
  let substs := reorderSubsts ⟨5,by omega⟩ ⟨6,by omega⟩

  -- rather than iterate over all ~70 blocked assignments to 3,7,11,19,
  -- we optimize by blocking assignments to idxs 3,7 then 3,7,11 then 3,7,11,19

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
            let idx : BitVec n := #[3,7,11,19][row]
            let left := .neg <| .x idx ⟨5,by omega⟩ (if h : row.val < len then pref[row] else lastL)
            let right := .neg <| .x idx ⟨6,by omega⟩ (if h : row.val < len then pref[row] else lastR)
            #[ left, right ]
          )

        -- Assign all the literals in question to match `swapped`
        let true_lits :=
          Array.flatten <| Array.flatten <| Array.ofFn (n := len+1) fun row =>
            let idx : BitVec n := #[3,7,11,19][row]
            Array.ofFn (n := s) fun k =>
              #[ Literal.mk (AllVars.x idx ⟨5,by omega⟩ k) (k.val = if h : row.val < len then pref[row] else lastR)
              ,  Literal.mk (AllVars.x idx ⟨6,by omega⟩ k) (k.val = if h : row.val < len then pref[row] else lastL) ]


        SRGen.write <|
          SR.mkLine clause (hc := by simp [clause, ← Array.sum_eq_sum_toList])
                  true_lits substs



/-! ### Hardest cases symmetry breaking -/

open AllVars in
def hardest_mat_rotation {n s} (hn : n ≥ 5) (hs : s > 0) : SRGen n s Unit := do
  let z : Fin s := ⟨0,by omega⟩

  let j2 : Fin n := ⟨2, by omega⟩
  let j3 : Fin n := ⟨3, by omega⟩
  let j4 : Fin n := ⟨4, by omega⟩

  -- 1 1 0
  -- 0 1 1
  -- 1 0 1
  let cond : Array (Literal (AllVars n s)) :=
    Array.map Literal.neg #[ x 07 j4 z, x 11 j2 z, x 19 j3 z ]

  let substs := substsOfMap (s := s) <| AllVars.reorder <|
    ((Equiv.swap j2 j3).trans (Equiv.swap j3 j4))

  SRGen.write <| SR.mkLine (cond ++ #[.neg (x 2 j2 z), .pos (x 2 j3 z)]) (by simp +zetaDelta)
    ( #[.pos (x 2 j3 z), .neg (x 2 j4 z)] )
    substs

  SRGen.write <| SR.mkLine (cond ++ #[.neg (x 2 j3 z), .pos (x 2 j4 z)]) (by simp +zetaDelta)
    #[.pos (x 2 j4 z), .neg (x 2 j2 z),] substs

open AllVars in
def hardest_lastcol_swap {n s} (hn : n = 7) (hs : s > 0) : SRGen n s Unit := do
  let z : Fin s := ⟨0,by omega⟩

  let j5 : Fin n := ⟨5, by omega⟩
  let j6 : Fin n := ⟨6, by omega⟩

  let substs := substsOfMap (s := s) <| AllVars.reorder <| Equiv.swap j5 j6

  -- 3,7,11,19 all zero in col5/6
  let cond : Array (AllVars n s) := #[
      x 03 j5 z, x 07 j5 z, x 11 j5 z, x 19 j5 z,
      x 03 j6 z, x 07 j6 z, x 11 j6 z, x 19 j6 z, ]

  -- x2,5,0 -> x2,6,0
  SRGen.write <| SR.mkLine
    (c := cond.map .neg ++ #[.neg (x 2 j5 z), .pos (x 2 j6 z)])
    (hc := by simp +zetaDelta)
    (true_lits := cond.map .pos ++ #[.neg (x 2 j5 z), .pos (x 2 j6 z)])
    substs

  -- x2,5,1 -> x2,6,0 ∨ x2,6,1
  if h : s > 1 then
    let o : Fin s := ⟨1,h⟩
    SRGen.write <| SR.mkLine
      (c := cond.map .neg ++ #[.neg (x 2 j5 o), .pos (x 2 j6 z), .pos (x 2 j6 o)])
      (hc := by simp +zetaDelta)
      (true_lits := cond.map .pos ++ #[.pos (x 2 j6 o)])
      substs


def calculatedRenumbers (hn : n ≥ 5) : SRGen n s Unit := do
  -- col 0 is symmetric for k ≥ 1
  for (idx,k) in [23, 41, 50, 52].zipIdx 2 do
    bound idx ⟨0,by omega⟩ k

  -- col 1 is symmetric for k ≥ 2
  for (idx,k) in [15, 24, 31, 45].zipIdx 3 do
    bound idx ⟨1,by omega⟩ k

  -- col 2 is symmetric for k ≥ 4
  for (idx,k) in [6].zipIdx 5 do
    bound idx ⟨2,by omega⟩ k

  -- col 4 is symmetric for k ≥ 4
  for (idx,k) in [20, 31, 51].zipIdx 5 do
    bound idx ⟨4,by omega⟩ k

  for hj: j in [5:n] do
    for (idx,k) in [2, 23, 55].zipIdx 6 do
      bound idx ⟨j,hj.upper⟩ k


def all (n s) : SRGen n s Unit := do
  if hs : s ≥ 2 then
  -- c3 stuff
  c3_bounds
  c3_fixed

  -- matrix zeros
  if hn : 5 ≤ n then
    c7_3_nonzero hn (by omega)
    mat_zeros_canonical hn (by omega)
    hardest_mat_rotation hn (by omega)

  for hj : j in [2:min 5 n] do
    have : 2 ≤ j := hj.lower
    have : j < 5 ∧ j < n := by simpa using hj.upper

    mat_rows_bound ⟨j,by omega⟩
    col234_incSorted (by omega) j (by omega)

  -- add various other matrix symmetries beyond the zero symmetries
  -- (e.g. in the all non-zero case many of the matrices can be eliminated)
  if hn : 5 ≤ n ∧ s ≥ 4 then
    mat_canonical (by omega) (by omega)

  for hj : j in [5:n] do
    have : 5 ≤ j := hj.lower
    have : j < n := hj.upper
    mat_rows_bound ⟨j,this⟩
    col5_incSorted (by omega) j (by omega)

  -- dim 5/6 swap
  if h : n = 7 then
    if h : s ≥ 2 then
      col56_sorted n s (by omega)
    hardest_lastcol_swap h (by omega)

  if hn : 5 ≤ n then
    calculatedRenumbers hn
