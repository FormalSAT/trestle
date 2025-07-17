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
deriving Inhabited, DecidableEq, Repr, Hashable

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
instance : DecidableRel (α := Matrix m) (· ≤ ·) := inferInstance
instance : LT (Matrix m) := ltOfOrd
instance : DecidableRel (α := Matrix m) (· < ·) := inferInstance

nonrec def toString (x : Matrix m) : String :=
  x.data.map (·.map (toString) |>.toList |> String.intercalate " ")
  |>.toList |> String.intercalate "\n"

instance : ToString (Matrix m) := { toString }

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
  replace x_mem_v := Array.mem_def.mp x_mem_v.val
  induction len with
  | zero =>
    simp [Vector.mem_iff_getElem] at x_mem_v
  | succ len ih =>
    simp [lastRows, List.mem_ofFn] at v_mem_lastRows
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

/-- Given a matrix `x` and an extending last row `lastRow`,
generate all viable matrices by filling in the last column.

Notably, in order to maintain the `transpose_one` invariant,
we check whether the last row's corresponding element is *not* one,
in which case we are forced to place a one in the last column instead.
-/
def extend.withLastRow (x : Matrix m) (lastRow : Vector Nat m) : Array (Matrix (m+1)) :=
  let allButLastRow := fillLastCols x lastRow m (Nat.le_refl _)
  let datas := allButLastRow.map (·.push (lastRow.push 1))
  datas.map (fun data => {
    data
  })

def extend (x : Matrix m) : Array (Matrix (m+1)) :=
  let lastRows : Array (Vector Nat m) := extend.lastRows (2+m) m
  lastRows.flatMap (extend.withLastRow x)

def shrink (x : Matrix (m+1)) : Matrix m := {
  data := Vector.ofFn fun row => Vector.ofFn fun col => x.data[row][col]
}

/-- Matrix automorphisms. Used in the encoding to reconstruct SR witnesses. -/
inductive Auto : Nat → Type
| renumber (f : Fin m → Equiv.Perm Nat) : Auto m
| reorder (p : Equiv.Perm (Fin m)) : Auto m
| trans (a1 a2 : Auto m) : Auto m
| lift (a : Auto m) : Auto (m+1)

namespace Auto

instance : Inhabited (Auto m) := ⟨.renumber default⟩

partial def toFun (a : Auto m) (x : Matrix m) : Matrix m :=
  aux (Nat.le_refl _) a x
where aux {m1 m2} (h : m1 ≤ m2) (a : Auto m1) (x : Matrix m2) : Matrix m2 :=
  match a with
  | renumber f =>
    ⟨ Vector.ofFn fun row => Vector.ofFn fun col =>
        if h' : col.val < m1 then
          f ⟨col.val,h'⟩ x.data[row][col]
        else
          x.data[row][col]
      ⟩
  | reorder p =>
    ⟨ Vector.ofFn fun row => Vector.ofFn fun col =>
        let row' := if h' : row.val < m1 then (p.symm ⟨row,h'⟩).castLE h else row
        let col' := if h' : col.val < m1 then (p.symm ⟨col,h'⟩).castLE h else col
        x.data[row'][col']
      ⟩
  | trans a1 a2 =>
      x |> aux h a1 |> aux h a2
  | lift a =>
      aux (Nat.le_of_lt h) a x

def reprPrec (a : Auto m) (prec : Nat) : Std.Format :=
  match a with
  | .renumber f => .join [".renumber ", .line, "⋯"]
  | .reorder p =>
    let vec := Array.finRange _ |>.map p
    .join [".reorder ", Repr.reprPrec vec prec]
  | .trans a1 a2 =>
    .nestD <| .join [".trans ", .line, reprPrec a1 prec, .line, reprPrec a2 prec]
  | .lift a1 =>
    .join [".lift ", reprPrec a1 prec]

instance : Repr (Auto m) := { reprPrec }

end Auto


inductive CanonInfo (m : Nat)
/-- All equiv matrices are greater than us.
`eqPerms` is the column reorderings which are not identity but are idempotent. -/
| canon (eqPerms : Array <| Equiv.Perm (Fin m))
/-- There is a smaller equiv matrix `mat` which can be reached via automorphism `auto`. -/
| noncanon (mat : Matrix m) (auto : Auto m)
deriving Inhabited

/-- Canonicity info for all matrices of that size -/
structure CanonicalMats (m) where
  map : Std.HashMap (Matrix m) (CanonInfo m)
  canonical : Array (Matrix m) :=
    map.fold (init := #[]) fun acc k v =>
      match v with
      | .canon _ => acc.push k
      | .noncanon _ _ => acc

def renumber (x : Matrix m) :=
  let vec := Vector.ofFn (n := m) fun col =>
    renumberIncr (0 :: 1 :: List.ofFn (n := m) (x.data[·][col]))
  (vec[·] : Fin _ → _)

def extendPerm (e : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m+n)) := {
  toFun := fun i =>
    if h : i.val < m then
      (e ⟨i,h⟩).castAdd _
    else i
  invFun := fun i =>
    if h : i.val < m then
      (e.symm ⟨i,h⟩).castAdd _
    else i
  left_inv := by intro i; simp; split <;> simp_all
  right_inv := by intro i; simp; split <;> simp_all
}

def tryReorder (x : Matrix (m+1)) (c : CanonicalMats m): CanonInfo (m+1) := Id.run do
  -- if we find non-id idempotent permutations, they go here
  let mut eqPerms := #[]

  for perm in Equiv.allPerms (m+1) do
    let res := (Auto.reorder perm).toFun x
    let a := Auto.reorder perm

    let colorPerm := renumber res
    let res := (Auto.renumber colorPerm).toFun res
    let a := a.trans (Auto.renumber colorPerm)

    match compare res x with
    | .lt =>
      return .noncanon res a
    | .eq =>
      eqPerms := eqPerms.push perm
    | .gt => pure ()

  return .canon eqPerms



def findSmaller (x : Matrix (m+1)) (c : CanonicalMats m) : CanonInfo (m+1) :=
  let colorPerm := renumber x
  let res := (Auto.renumber colorPerm).toFun x
  match compare res x with
  | .lt =>
    .noncanon res (.renumber colorPerm)
  | .eq =>
    tryReorder res c
  | .gt =>
    panic! "findSmaller renumber is gt??"


def CanonicalMats.zero : CanonicalMats 0 where
  map := Std.HashMap.ofList [(
    ⟨#v[]⟩,
    .canon #[]
  )]

def CanonicalMats.step (c : CanonicalMats m) : CanonicalMats (m+1) where
  map :=
    have mats := c.canonical.flatMap (·.extend)
    have foundSmaller : Std.HashMap _ _ :=
      mats.foldl (init := .emptyWithCapacity) fun acc m =>
        acc.insert m (findSmaller m c)
    -- just doublecheck that x' is actually smaller...
    if foundSmaller.toArray.any (fun | (_,.canon _) => .false | (x,.noncanon x' _) => !(x' < x))
    then panic! "x' isn't actually smaller!!! D:" else
    foundSmaller.map fun _x i =>
      match i with
      | .canon eqPerms => .canon eqPerms
      | .noncanon x' a =>
        let (x',a) := chaseInfo foundSmaller x' a (foundSmaller.size)
        .noncanon x' a
where
  chaseInfo (map : Std.HashMap (Matrix (m+1)) (CanonInfo (m+1)))
    (x : Matrix (m+1)) (a : Auto (m+1)) (fuel : Nat) :=
  match fuel with
  | 0 => panic! "out of fuel"
  | fuel+1 =>
  match map[x]? with
  | some (.canon _) =>
      (x,a)
  | some (.noncanon x' a') =>
      chaseInfo map x' (a.trans a') fuel
  | none =>
      panic! "missing matrix in map"

structure CanonicalMatsUpTo (m : Nat) where
  data : Vector (Σ i, CanonicalMats i) (m+1)
  idx_eq : ∀ (i : Nat) (h : i ≤ m), data[i].fst = i

def CanonicalMatsUpTo.get (i) (hi : i ≤ m := by get_elem_tactic) (u : CanonicalMatsUpTo m) : CanonicalMats i :=
  (u.idx_eq i hi) ▸ u.data[i].snd

def matsUpTo (m : Nat) : CanonicalMatsUpTo m :=
  match m with
  | 0 =>
    { data := #v[⟨0,CanonicalMats.zero⟩]
      idx_eq := by simp }
  | m+1 =>
    let u := matsUpTo m
    let prev := u.get m (Nat.le_refl _)
    let next := prev.step
    let {data, idx_eq} := u
    { data := data.push ⟨m+1,next⟩
      idx_eq := by
        intro i h
        cases h.eq_or_lt
        · subst i; simp
        · rw [Vector.getElem_push_lt (by omega)]
          apply idx_eq
          omega }


end Matrix
