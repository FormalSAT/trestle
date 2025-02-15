/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.Autos

import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.LiftLets

namespace Keller.SymmBreak

/-! ## 3x3 Matrix Symmetries

For Keller graph with `n≥5`, we can do symmetry breaking
on dimension indices 2,3,4 from `c_7`, `c_11`, `c_19`
by permuting those indices and renumbering the colors at each index.
-/

@[ext]
structure Matrix (s) where
  data : Vector (Vector (Fin s) 3) 3
  transpose_one : ∀ i j : Fin 3, data[i][j].val = 1 ∨ data[j][i].val = 1
deriving DecidableEq, Repr

abbrev Matrix.get (r c : Fin 3) (m: Matrix s) : Fin s := m.data[r][c]

theorem Matrix.s_ge_2 (m : Matrix s) : s ≥ 2 := by
  have := m.data[0][0].isLt
  have := m.transpose_one 0 0
  simp at this
  omega

instance : Inhabited (Matrix (s+2)) where
  default := { data := Vector.ofFn fun r => Vector.ofFn fun c => 1, transpose_one := by simp }

def Matrix.toVec (m : Matrix s) : Vector (Fin s) 6 :=
  ⟨#[m.get 0 1, m.get 0 2, m.get 1 0, m.get 1 2, m.get 2 0, m.get 2 1],by simp⟩

def Matrix.ofVec? (v : Vector (Fin s) 6) : Option (Matrix s) :=
  if h : 1 < s then
    let data := data h
    if transpose_one : _ then
      some { data, transpose_one }
    else none
  else none
where data (h) := ⟨#[
  ⟨#[⟨1,h⟩,v[0] ,v[1] ],by simp⟩,
  ⟨#[v[2] ,⟨1,h⟩,v[3] ],by simp⟩,
  ⟨#[v[4] ,v[5] ,⟨1,h⟩],by simp⟩], by simp⟩

theorem Matrix.ofVec?.data_toVec (m : Matrix s) : Matrix.ofVec?.data m.toVec m.s_ge_2 = m.data := by
  rcases m with ⟨d,t⟩
  simp [toVec, data]
  have t00 := t 0 0; have t11 := t 1 1; have t22 := t 2 2
  simp at t00 t11 t22
  ext r hr c hc
  rcases r with (_|_|_) <;> (
    simp; simp [Nat.add_one_lt_add_one_iff] at hr
    rcases c with (_|_|_) <;> (
      simp [Nat.add_one_lt_add_one_iff] at hc
      simp [*]))

@[simp]
theorem Matrix.ofVec?_toVec (m : Matrix s) : Matrix.ofVec? m.toVec = some m := by
  have h : 1 < s := m.s_ge_2
  simp only [ofVec?, h, dite_true, ofVec?.data_toVec]
  simp only [Option.dite_none_right_eq_some, exists_prop, and_true]
  exact m.transpose_one

theorem Matrix.toVec_inj (m1 m2 : Matrix s) : m1.toVec = m2.toVec → m1 = m2 := by
  intro h
  simpa [Matrix.ofVec?_toVec] using congrArg Matrix.ofVec? h

def Matrix.lt (x y : Matrix s) : Bool :=
  Prod.Lex (· > ·) (· < ·) (aux x) (aux y)
where aux (m : Matrix s) :=
  ( decide (m.data[0][2].val = 1)
  , m.toVec.toList )

instance : LT (Matrix s) where
  lt := (Matrix.lt · · = true)

instance {x y : Matrix s} : Decidable (x < y) := Bool.decEq ..
instance : IsTrans (Matrix s) (· < ·) where
  trans := by
    intro a b c; simp [instLTMatrix, Matrix.lt]
    intro h1 h2; trans; exact h1; exact h2

def Matrix.le (x y : Matrix s) : Bool :=
  Prod.Lex (· > ·) (· ≤ ·) (Matrix.lt.aux x) (Matrix.lt.aux y)

instance : LE (Matrix s) where
  le := (Matrix.le · · = true)

instance {x y : Matrix s} : Decidable (x ≤ y) := Bool.decEq ..
instance : IsTrans (Matrix s) (· ≤ ·) where
  trans := by
    intro a b c; simp [instLEMatrix, Matrix.le]
    intro h1 h2; trans; exact h1; exact h2

instance : IsAntisymm (Matrix s) (· ≤ ·) where
  antisymm := by
    intro a b h1 h2
    simp [instLEMatrix, Matrix.le] at h1 h2
    have := Prod.instIsAntisymmLexOfIsStrictOrder.antisymm _ _ h1 h2
    simp [Matrix.lt.aux, Vector.map] at this
    apply Matrix.toVec_inj; apply Vector.ext'
    exact this.2

instance : IsTotal (Matrix s) (· ≤ ·) where
  total := by
    intro a b
    simp [instLEMatrix, Matrix.le]
    exact
      total_of (Prod.Lex (fun x1 x2 => x1 > x2) fun x1 x2 => x1 ≤ x2) (Matrix.lt.aux a)
        (Matrix.lt.aux b)



instance : Fintype (Matrix s) where
  elems :=
    Finset.univ (α := Vector (Vector (Fin s) 3) 3)
    |>.filterMap (fun v =>
      if h : _ then
        some ⟨v,h⟩
      else none)
      (by simp only [Option.mem_def, Option.dite_none_right_eq_some, Option.some.injEq, forall_exists_index, forall_apply_eq_imp_iff, Matrix.mk.injEq]
          intro _ _ _ _ h; exact h.symm)
  complete := by
    intro m
    simp only [Finset.mem_filterMap, Finset.mem_univ, Option.dite_none_right_eq_some, true_and]
    use m.data, m.transpose_one


def Matrix.Perm := Equiv.Perm (Fin 3)

def Matrix.Perm.all : List Matrix.Perm := [
  Equiv.refl _,
  Equiv.Perm.setAll [(0,0),(1,2),(2,1)],
  Equiv.Perm.setAll [(0,1),(1,0),(2,2)],
  Equiv.Perm.setAll [(0,1),(1,2),(2,0)],
  Equiv.Perm.setAll [(0,2),(1,0),(2,1)],
  Equiv.Perm.setAll [(0,2),(1,1),(2,0)],
]

@[simp] theorem Matrix.Perm.mem_all (p : Matrix.Perm) : p ∈ all := by
  simp [all, p.ext_iff, Fin.forall_fin_succ, Equiv.Perm.setAll, Equiv.setAll, Equiv.setValue, Equiv.swap, Equiv.swapCore]
  have p01 : (show Equiv.Perm _ from p) 0 ≠ (show Equiv.Perm _ from p) 1 := by simp
  have p02 : (show Equiv.Perm _ from p) 0 ≠ (show Equiv.Perm _ from p) 2 := by simp
  have p12 : (show Equiv.Perm _ from p) 1 ≠ (show Equiv.Perm _ from p) 2 := by simp
  generalize (show Equiv.Perm _ from p) 0 = p0 at *
  generalize (show Equiv.Perm _ from p) 1 = p1 at *
  generalize (show Equiv.Perm _ from p) 2 = p2 at *
  rcases p0 with ⟨(_|_|_),_⟩ <;>
    rcases p1 with ⟨(_|_|_),_⟩ <;>
      rcases p2 with ⟨(_|_|_),_⟩ <;> simp_all [Fin.ext_iff] <;> omega

def Matrix.Perm.apply (m : Matrix s) (a: Matrix.Perm) : Matrix s := {
  data := Vector.ofFn fun r => Vector.ofFn fun c => m.get (a.toFun r) (a.toFun c)
  transpose_one := by intros; simp; apply m.transpose_one
}

def Matrix.Perm.id : Matrix.Perm := Equiv.refl _

@[simp] theorem Matrix.Perm.apply_id (m : Matrix s) :
    Matrix.Perm.apply m id = m := by
  ext; simp [apply, id]



structure Matrix.Renumber (s) (h : s > 1 := by trivial) where
  renumber : Fin 3 → (Fin s ≃ Fin s)
  renumber_0 : ∀ i, (renumber i) ⟨0,by omega⟩ = ⟨0,by omega⟩
  renumber_1 : ∀ i, (renumber i) ⟨1,by omega⟩ = ⟨1,by omega⟩

def Matrix.Renumber.apply (m : Matrix s) (a : Matrix.Renumber s h) : Matrix s := {
  data := Vector.ofFn fun r => Vector.ofFn fun c => (a.renumber c) (m.get r c)
  transpose_one := by
    intro x y
    rcases m.transpose_one x y with (h1|h1) <;> (
      simp at h1
      replace h1 := Fin.eq_of_val_eq (j := ⟨1,h⟩) h1
      simp [h1, a.renumber_1])
}

def Matrix.Renumber.id (s) (h : s > 1 := by trivial) : Matrix.Renumber s h where
  renumber := fun _ => Equiv.refl _
  renumber_0 := by simp
  renumber_1 := by simp

@[simp] theorem Matrix.Renumber.apply_id (m : Matrix s) (h : s > 1 := by trivial) :
    Matrix.Renumber.apply m (id s h) = m := by
  ext; simp [apply, id]

private def renumber_fins (m : List (Fin s)) : Equiv.Perm (Fin s) :=
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
    let renumber := fun c =>
      renumber_fins <| ⟨0,by omega⟩ :: ⟨1,by omega⟩ :: List.ofFn fun r => m.get r c
    if h : _ then some {
      renumber := renumber
      renumber_0 := And.left h
      renumber_1 := And.right h
    } else none)
  let m' := p.apply m
  guard (m' < m)
  return m'

theorem Matrix.findSmallerRenumber?_eq_some (m m' : Matrix 4) :
    m.findSmallerRenumber? = some m' →
      ∃ (r : Renumber _), r.apply m = m' ∧ m' < m := by
  unfold findSmallerRenumber?
  suffices ∀ popt : Option _, bind popt _ = some m' → _ from this _
  rintro (_|r)
  · simp
  · simp [Option.bind_eq_some]; simp +contextual [eq_comm]

def Matrix.findSmaller? (m : Matrix 4) : Option (Matrix 4) :=
  let perms := Matrix.Perm.all.map (fun p => p.apply m)
  match perms.find? (· < m) with
  | some p => some p
  | none =>
    perms.findSome? fun p =>
      p.findSmallerRenumber?.filter (· < m)

theorem Matrix.findSmaller?_eq_some (m m' : Matrix 4) :
    m.findSmaller? = some m' →
      ∃ (p : Perm) (r : Renumber _), r.apply (p.apply m) = m' ∧ m' < m := by
  intro eq_some
  simp [Id.run, findSmaller?] at eq_some
  split at eq_some
  next m1 ms_related =>
    cases eq_some; simp at ms_related
    rcases ms_related with ⟨p,smaller,rfl⟩
    use p, Renumber.id 4
    simp [List.find?_eq_some_iff_append] at smaller
    simp [smaller]
  simp [List.findSome?_eq_some_iff, List.map_eq_append_iff, List.map_eq_cons_iff] at eq_some
  rcases eq_some with ⟨-,m_mid,⟨-,-,-,-,-,p,-,-,h_mid,-⟩,⟨h,hlt⟩,-⟩
  replace h := findSmallerRenumber?_eq_some _ _ h
  use p; subst m_mid; aesop

def Matrix.canonicalCases :=
  Array.filterMap aux #[
  #[0, 1, 1, 0, 0, 1] ,
  #[0, 1, 1, 0, 1, 1] ,
  #[0, 1, 1, 0, 2, 1] ,
  #[0, 1, 1, 1, 0, 0] ,
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
  #[1, 1, 2, 0, 3, 1] ,
  #[1, 1, 2, 1, 2, 1] ,
  #[1, 1, 2, 1, 2, 2] ,
  #[1, 1, 2, 1, 3, 1] ,
  #[1, 1, 2, 1, 3, 2] ,
  #[2, 1, 1, 2, 2, 1] ]
  |>.insertionSort
where aux (a : Array Nat) : Option (Matrix 4) :=
  if h : _ then
    Matrix.ofVec? ⟨a.map (Fin.ofNat' 4),h⟩
  else none

theorem Matrix.canonicalCases_are_canonical : ∀ m : Matrix 4, m ∈ canonicalCases ∨ (findSmaller? m).isSome := by
  native_decide
