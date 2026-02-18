/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.SymmBreak.Autos
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
structure Matrix where
  data : Vector (Vector Nat 3) 3
deriving Inhabited, DecidableEq, Repr, Hashable

namespace Matrix

nonrec def compare (x y : Matrix) : Ordering :=
  match (x.data[0][1] == 1, y.data[0][1] == 1) with
  | (true, false) => .lt
  | (false, true) => .gt
  | (true, true) | (false, false) =>
  compare (x.data[1][0]) (y.data[1][0])
  |>.then (compare (x.data[0][2]) (y.data[0][2]))
  |>.then (compare (x.data[2][0]) (y.data[2][0]))
  |>.then (compare (x.data[1][2]) (y.data[1][2]))
  |>.then (compare (x.data[2][1]) (y.data[2][1]))

instance : Ord (Matrix) where compare := compare

instance : BEq (Matrix) := Ord.toBEq inferInstance

instance : LE (Matrix) := leOfOrd
instance : DecidableRel (α := Matrix) (· ≤ ·) := inferInstance
instance : LT (Matrix) := ltOfOrd
instance : DecidableRel (α := Matrix) (· < ·) := inferInstance

nonrec def toString (x : Matrix) : String :=
  x.data.map (·.map (toString) |>.toList |> String.intercalate " ")
  |>.toList |> String.intercalate "\n"

instance : ToString (Matrix) := { toString }


def allMats : Array Matrix := Id.run do
  let mut res := #[]
  for _10 in [0:3] do
    for _02 in [0:3] do
      for _20 in (if _02 == 1 then [0:(max 1 _10)+2] else [1:2]) do
        for _12 in [0:(max 1 _02)+2] do
          for _21 in (if _12 == 1 then [0:3] else [1:2]) do
            res := res.push ⟨#v[#v[1,1,_02],#v[_10,1,_12],#v[_20,_21,1]]⟩
  return res

--#eval allMats.size
--#eval show IO Unit from do
--  for i in [0:allMats.size] do
--    for j in [0:allMats.size] do
--      if compare allMats[i]! allMats[j]! ≠ Ord.compare i j then
--        IO.println s!"{i} {j}"
--  IO.println "boop!"


/-- Matrix automorphisms. Used in the encoding to reconstruct SR witnesses. -/
inductive Auto
| renumber (f : Fin 3 → Equiv.Perm Nat) : Auto
| reorder (p : Equiv.Perm (Fin 3)) : Auto
| trans (a1 a2 : Auto) : Auto

namespace Auto

instance : Inhabited Auto := ⟨.renumber default⟩

partial def toFun (a : Auto) (x : Matrix) : Matrix :=
  match a with
  | renumber f =>
    ⟨ Vector.ofFn fun row => Vector.ofFn fun col => f col x.data[row][col] ⟩
  | reorder p =>
    ⟨ Vector.ofFn fun row => Vector.ofFn fun col =>
        let row' := (p.symm row)
        let col' := (p.symm col)
        x.data[row'][col']
      ⟩
  | trans a1 a2 =>
      x |> toFun a1 |> toFun a2

def reprPrec (a : Auto) (prec : Nat) : Std.Format :=
  match a with
  | .renumber _f => .join [".renumber ", .line, "⋯"]
  | .reorder p =>
    let vec := Array.finRange _ |>.map p
    .join [".reorder ", Repr.reprPrec vec prec]
  | .trans a1 a2 =>
    .nestD <| .join [".trans ", .line, reprPrec a1 prec, .line, reprPrec a2 prec]

instance : Repr Auto := { reprPrec }

end Auto


inductive CanonInfo
/-- All equiv matrices are greater than us.
`eqPerms` is the column reorderings which are not identity but are idempotent. -/
| canon (eqPerms : Array <| Equiv.Perm (Fin 3))
/-- There is a smaller equiv matrix `mat` which can be reached via automorphism `auto`. -/
| noncanon (mat : Matrix) (auto : Auto)
deriving Inhabited

/-- Canonicity info for all matrices -/
structure CanonicalMats where
  map : Std.HashMap Matrix CanonInfo
  canonical : Array Matrix :=
    map.fold (init := #[]) fun acc k v =>
      match v with
      | .canon _ => acc.push k
      | .noncanon _ _ => acc

def renumber (x : Matrix) :=
  let vec := Vector.ofFn (n := 3) fun col =>
    renumberIncr (0 :: 1 :: List.ofFn (n := 3) (x.data[·][col]))
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

def tryReorder (x : Matrix) : CanonInfo := Id.run do
  -- if we find non-id idempotent permutations, they go here
  let mut eqPerms := #[]

  for perm in Equiv.allPerms 3 do
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



def findSmaller (x : Matrix) : CanonInfo :=
  let colorPerm := renumber x
  let res := (Auto.renumber colorPerm).toFun x
  match compare res x with
  | .lt =>
    .noncanon res (.renumber colorPerm)
  | .eq =>
    tryReorder res
  | .gt =>
    panic! "findSmaller renumber is gt??"

def canonicalMats : CanonicalMats where
  map :=
    have mats := allMats
    have foundSmaller : Std.HashMap _ _ :=
      mats.foldl (init := .emptyWithCapacity) fun acc m =>
        acc.insert m (findSmaller m)
    -- just doublecheck that x' is actually smaller...
    if foundSmaller.toArray.any (fun | (_,.canon _) => .false | (x,.noncanon x' _) => !(x' < x))
    then panic! "x' isn't actually smaller!!! D:" else
    foundSmaller.map fun _x i =>
      match i with
      | .canon eqPerms => .canon eqPerms
      | .noncanon x' a =>
        let (x',a) := chaseInfo foundSmaller _x x' a (foundSmaller.size)
        .noncanon x' a
where
  chaseInfo (map : Std.HashMap Matrix CanonInfo) (start : Matrix)
    (x : Matrix) (a : Auto) (fuel : Nat) :=
  match fuel with
  | 0 => panic! "out of fuel"
  | fuel+1 =>
  match map[x]? with
  | some (.canon _) =>
      (x,a)
  | some (.noncanon x' a') =>
      chaseInfo map start x' (a.trans a') fuel
  | none =>
      panic! s!"missing matrix in map:\ncurrent: {start}\nnew: {x}"

--#eval canonicalMats.map.filter (fun | _, .canon _ => false | _,_ => true)
--  |>.toList.map (·.1) |>.mergeSort |>.map (·.data.toArray.map (·.toArray))


/-
[[1, 1, 0], [0, 1, 0], [1, 1, 1]]
[[1, 1, 0], [0, 1, 1], [1, 0, 1]]
[[1, 1, 0], [0, 1, 1], [1, 1, 1]]
[[1, 1, 0], [0, 1, 1], [1, 2, 1]]
[[1, 1, 0], [0, 1, 2], [1, 1, 1]]
[[1, 1, 1], [0, 1, 1], [0, 1, 1]]
[[1, 1, 1], [0, 1, 1], [0, 2, 1]]
[[1, 1, 1], [0, 1, 0], [1, 1, 1]]
[[1, 1, 1], [0, 1, 0], [2, 1, 1]]
[[1, 1, 1], [0, 1, 1], [1, 1, 1]]
[[1, 1, 1], [0, 1, 1], [1, 2, 1]]
[[1, 1, 1], [0, 1, 2], [1, 1, 1]]
[[1, 1, 1], [0, 1, 1], [2, 1, 1]]
[[1, 1, 1], [0, 1, 1], [2, 2, 1]]
[[1, 1, 1], [0, 1, 2], [2, 1, 1]]
[[1, 1, 2], [0, 1, 1], [1, 1, 1]]
[[1, 1, 2], [0, 1, 1], [1, 2, 1]]
[[1, 1, 2], [0, 1, 2], [1, 1, 1]]
[[1, 1, 2], [0, 1, 3], [1, 1, 1]]
[[1, 1, 1], [1, 1, 1], [1, 1, 1]]
[[1, 1, 1], [1, 1, 1], [1, 2, 1]]
[[1, 1, 1], [1, 1, 1], [2, 2, 1]]
[[1, 1, 1], [1, 1, 2], [2, 1, 1]]
[[1, 1, 2], [1, 1, 2], [1, 1, 1]]
[[1, 1, 2], [1, 1, 3], [1, 1, 1]]
[[1, 1, 1], [2, 1, 1], [2, 2, 1]]
[[1, 1, 1], [2, 1, 1], [3, 2, 1]]
[[1, 1, 2], [2, 1, 1], [1, 2, 1]]

-/
end Matrix
