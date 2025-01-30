/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.Autos

import Mathlib.Data.Finset.Sort

namespace Keller

/-! ## Symmetry Breaking verified by SR -/

structure Matrix (s) where
  data : Vector (Fin s) 6
  has_one_0 : (data[0] : Nat) = 1 ∨ (data[2] : Nat) = 1 := by decide
  has_one_1 : (data[1] : Nat) = 1 ∨ (data[4] : Nat) = 1 := by decide
  has_one_2 : (data[3] : Nat) = 1 ∨ (data[5] : Nat) = 1 := by decide
deriving DecidableEq

def Matrix.get (r c : Fin 3) (h : s > 1 := by trivial) (m: Matrix s) : Fin s :=
  match r with
  | 0 => match c with | 0 => ⟨1,h⟩     | 1 => m.data[0] | 2 => m.data[1]
  | 1 => match c with | 0 => m.data[2] | 1 => ⟨1,h⟩     | 2 => m.data[3]
  | 2 => match c with | 0 => m.data[4] | 1 => m.data[5] | 2 => ⟨1,h⟩

@[simp] theorem Matrix.get_diag (r) {h} (m : Matrix s) : m.get r r h = ⟨1,h⟩ := by
  rcases r with (_|_|_|_) <;>
    first | contradiction | simp [get]

theorem Matrix.get_or_transpose_eq_one (r c : Fin 3) (h : s > 1 := by trivial) (m : Matrix s)
  : m.get r c = ⟨1,h⟩ ∨ m.get c r = ⟨1,h⟩ :=
  match r with
  | 0 =>
    match c with
    | 0 => Or.inl rfl
    | 1 => by simpa [get, ← Fin.val_eq_val] using m.has_one_0
    | 2 => by simpa [get, ← Fin.val_eq_val] using m.has_one_1
  | 1 =>
    match c with
    | 0 => by simpa [get, ← Fin.val_eq_val] using m.has_one_0.symm
    | 1 => Or.inl rfl
    | 2 => by simpa [get, ← Fin.val_eq_val] using m.has_one_2
  | 2 =>
    match c with
    | 0 => by simpa [get, ← Fin.val_eq_val] using m.has_one_1.symm
    | 1 => by simpa [get, ← Fin.val_eq_val] using m.has_one_2.symm
    | 2 => Or.inl rfl


def Matrix.ofFn (f : Fin 3 → Fin 3 → Fin s)
    (has_one_0 : (f 0 1 : Nat) = 1 ∨ (f 1 0 : Nat) = 1)
    (has_one_1 : (f 0 2 : Nat) = 1 ∨ (f 2 0 : Nat) = 1)
    (has_one_2 : (f 1 2 : Nat) = 1 ∨ (f 2 1 : Nat) = 1)
  : Matrix s := {
  data := Vector.ofFn (fun
    | 0 => f 0 1
    | 1 => f 0 2
    | 2 => f 1 0
    | 3 => f 1 2
    | 4 => f 2 0
    | 5 => f 2 1)
  has_one_0 := by simp [has_one_0]
  has_one_1 := by simp [has_one_1]
  has_one_2 := by simp [has_one_2]
  }

theorem Matrix.get_ofFn (r c) {f} {h1 h2 h3} : r ≠ c → Matrix.get r c h (Matrix.ofFn f h1 h2 h3) = f r c := by
  simp [get,ofFn]
  clear h1 h2 h3
  rcases r with (_|_|_|_)
  case succ.succ.succ => contradiction
  all_goals (
    simp
    rcases c with (_|_|_|_)
    case succ.succ.succ => contradiction
    all_goals simp
  )


def Matrix.lt (x y : Matrix s) : Bool :=
  x.data.toList < y.data.toList

instance : LT (Matrix s) where
  lt := (Matrix.lt · · = true)

instance {x y : Matrix s} : Decidable (x < y) := Bool.decEq ..
instance : IsTrans (Matrix s) (· < ·) where
  trans := by
    intro a b c; simp [instLTMatrix, Matrix.lt]
    intro h1 h2; trans; exact h1; exact h2

instance : Fintype (Matrix s) where
  elems :=
    Finset.univ (α := Vector (Fin s) 6)
    |>.filterMap (fun v =>
      if h : _ ∧ _ ∧ _ then
        have ⟨h1,h2,h3⟩ := h
        some ⟨v,h1,h2,h3⟩
      else
        none)
      (by
        intro v1 v2; simp
        intro m h; split; simp
        rintro rfl h'; split; simp
        exact Eq.symm)
  complete := by
    intro m; simp
    use m.data, ⟨m.has_one_0, m.has_one_1, m.has_one_2⟩
    split; simp


def Matrix.Perm := Equiv.Perm (Fin 3)

def Matrix.Perm.all : List Matrix.Perm := [
  Equiv.refl _,
  Equiv.Perm.setAll [(0,0),(1,2),(2,1)],
  Equiv.Perm.setAll [(0,1),(1,0),(2,2)],
  Equiv.Perm.setAll [(0,1),(1,2),(2,0)],
  Equiv.Perm.setAll [(0,2),(1,0),(2,1)],
  Equiv.Perm.setAll [(0,2),(1,1),(2,0)],
]

def Matrix.Perm.apply (m : Matrix s) (h : s > 1 := by trivial) (a: Matrix.Perm) : Matrix s := by
  have := m.get_or_transpose_eq_one
  simp [Fin.ext_iff] at this
  apply Matrix.ofFn (fun r c => m.get (a.toFun r) (a.toFun c))
  all_goals (apply this)

def Matrix.findSmallerPerm? (m : Matrix s) (h : s > 1 := by trivial) : Option (Matrix s) :=
  Matrix.Perm.all.map (fun p => p.apply m)
  |>.find? (· < m)



structure Matrix.Renumber (s) (h : s > 1 := by trivial) where
  renumber : Fin 3 → (Fin s ≃ Fin s)
  renumber_0 : ∀ i, (renumber i) ⟨0,by omega⟩ = ⟨0,by omega⟩
  renumber_1 : ∀ i, (renumber i) ⟨1,by omega⟩ = ⟨1,by omega⟩

def Matrix.Renumber.apply (m : Matrix s) (a: Matrix.Renumber s h) : Matrix s := by
  apply Matrix.ofFn (fun r c => (a.renumber c) (m.get r c))
  all_goals (
    generalize (OfNat.ofNat _ : Fin 3) = r
    generalize (OfNat.ofNat _ : Fin 3) = c
    have := m.get_or_transpose_eq_one r c
    cases this <;> simp_all [a.renumber_1]
  )

def renumber_fins (m : List (Fin s)) : Equiv.Perm (Fin s) :=
  match m.head? with
  | none => Equiv.refl _
  | some ⟨_,h⟩ =>
    Equiv.Perm.setAll (
      aux ⟨0,by omega⟩ m []
    )
where
  aux (nextSpot : Fin s) (L : List (Fin s))
      (acc : List (Fin s × Fin s)) : List (Fin s × Fin s) :=
  match L with
  | []    => acc
  | x::xs =>
    if acc.any (·.1 = x) then
      aux nextSpot xs acc
    else
      let acc := (x,nextSpot) :: acc
      if _ : nextSpot = s-1 then acc
      else aux ⟨nextSpot+1, by omega⟩ xs acc

def Matrix.findSmallerRenumber? (m : Matrix s) (h : s > 3 := by trivial) : Option (Matrix s) := do
  let p : Matrix.Renumber s (by omega) ← (do
    let x := renumber_fins [⟨0,by omega⟩,⟨1,by omega⟩, m.get 1 0 (by omega), m.get 2 0 (by omega)]
    let y := renumber_fins [⟨0,by omega⟩,⟨1,by omega⟩, m.get 0 1 (by omega), m.get 2 1 (by omega)]
    let z := renumber_fins [⟨0,by omega⟩,⟨1,by omega⟩, m.get 0 2 (by omega), m.get 1 2 (by omega)]
    if h : _ then some {
      renumber := fun | 0 => x | 1 => y | 2 => z
      renumber_0 := And.left h
      renumber_1 := And.right h
    } else none)
  let m' := p.apply m
  guard (m' < m)
  return m'


def oldCanonicalCases := #[
  #[0, 1, 1, 0, 0, 1] ,
  #[0, 1, 1, 0, 1, 1] ,
  #[0, 1, 1, 0, 2, 1] ,
  #[0, 0, 1, 0, 1, 1] ,
  #[0, 1, 1, 1, 0, 2] ,
  #[0, 1, 1, 1, 1, 0] ,
  #[0, 1, 1, 1, 1, 1] ,
  #[0, 1, 1, 1, 1, 2] ,
  #[0, 1, 1, 1, 2, 0] ,
  #[0, 1, 1, 1, 2, 1] ,
  #[0, 1, 1, 1, 2, 2] ,
  #[0, 1, 1, 2, 1, 1] ,
  #[0, 1, 1, 2, 2, 1] ,
  #[1, 1, 0, 0, 1, 1] ,
  #[1, 1, 0, 0, 2, 1] ,
  #[1, 1, 0, 2, 1, 1] ,
  #[1, 1, 0, 2, 2, 1] ,
  #[1, 1, 1, 1, 1, 1] ,
  #[1, 1, 1, 1, 1, 2] ,
  #[1, 1, 1, 1, 2, 2] ,
  #[1, 1, 1, 2, 2, 1] ,
  #[1, 1, 2, 0, 2, 1] ,
  #[1, 1, 2, 1, 2, 1] ,
  #[1, 1, 2, 1, 2, 2] ,
  #[2, 1, 1, 2, 2, 1] ,
  #[1, 1, 2, 0, 3, 1] ,
  #[1, 1, 2, 1, 3, 1] ,
  #[1, 1, 2, 1, 3, 2] ]

def canonicalCases := #[
  #[0, 0, 1, 0, 1, 1] ,
  #[0, 0, 1, 1, 1, 1] ,
  #[0, 0, 1, 1, 1, 2] ,
  #[0, 1, 1, 0, 0, 1] ,
  #[0, 1, 1, 0, 1, 1] ,
  #[0, 1, 1, 0, 2, 1] ,
  #[0, 1, 1, 1, 0, 2] ,
  #[0, 1, 1, 1, 1, 0] ,
  #[0, 1, 1, 1, 1, 1] ,
  #[0, 1, 1, 1, 1, 2] ,
  #[0, 1, 1, 1, 2, 0] ,
  #[0, 1, 1, 1, 2, 1] ,
  #[0, 1, 1, 1, 2, 2] ,
  #[0, 1, 1, 2, 1, 1] ,
  #[0, 1, 1, 2, 2, 1] ,
  #[0, 2, 1, 1, 1, 1] ,
  #[0, 2, 1, 1, 1, 2] ,
  #[0, 2, 1, 2, 1, 1] ,
  #[0, 2, 1, 3, 1, 1] ,
  #[1, 1, 1, 1, 1, 1] ,
  #[1, 1, 1, 1, 1, 2] ,
  #[1, 1, 1, 1, 2, 2] ,
  #[1, 1, 1, 2, 2, 1] ,
  #[1, 1, 2, 1, 2, 1] ,
  #[1, 1, 2, 1, 2, 2] ,
  #[1, 1, 2, 1, 3, 1] ,
  #[1, 1, 2, 1, 3, 2] ,
  #[1, 1, 2, 2, 3, 1] ,
  #[1, 2, 2, 1, 1, 2] ]

def asMatrices : Array (Matrix 4) :=
  canonicalCases.filterMap (fun data =>
    let data := data.filterMap (fun n => if h : _ then some ⟨n,h⟩ else none)
    if hsize : _ = 6 then
      let data := ⟨data, hsize⟩
      if h : _ ∧ _ ∧ _ then
        have ⟨has_one_0, has_one_1, has_one_2⟩ := h
        some {data, has_one_0, has_one_1, has_one_2}
      else none
    else none
  )

def sorted := asMatrices.insertionSort (·.lt ·)

def findSmaller (m : Matrix 4) : Option (Matrix 4) :=
  m.findSmallerPerm?.orElse (fun () => m.findSmallerRenumber?)

#eval! Finset.univ (α := Matrix 4)
  |>.filter (findSmaller · |>.isNone)
  --|>.card
  |>.map ⟨(·.data.toList), sorry⟩
  |>.sort (· ≤ ·)
