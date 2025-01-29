/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.Autos

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
  match compare x.data[0] y.data[0] with
  | .lt => true | .gt => false | .eq =>
  match compare x.data[1] y.data[1] with
  | .lt => true | .gt => false | .eq =>
  match compare x.data[2] y.data[2] with
  | .lt => true | .gt => false | .eq =>
  match compare x.data[3] y.data[3] with
  | .lt => true | .gt => false | .eq =>
  match compare x.data[4] y.data[4] with
  | .lt => true | .gt => false | .eq =>
  match compare x.data[5] y.data[5] with
  | .lt => true | .gt | .eq => false

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

def Matrix.Perm.apply (m : Matrix s) (h : s > 1 := by trivial) (a: Matrix.Perm) : Matrix s := by
  have := m.get_or_transpose_eq_one
  simp [Fin.ext_iff] at this
  apply Matrix.ofFn (fun r c => m.get (a.toFun r) (a.toFun c))
  all_goals (apply this)

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

def Matrix.findRenumber (m : Matrix s) : 




def canonicalCases := #[
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
  #[1, 1, 2, 1, 2, 1] ,
  #[1, 1, 2, 1, 2, 2] ,
  #[2, 1, 1, 2, 2, 1] ,
  #[1, 1, 2, 0, 3, 1] ,
  #[1, 1, 2, 1, 3, 1] ,
  #[1, 1, 2, 1, 3, 2] ]

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
