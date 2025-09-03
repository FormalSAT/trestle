/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.KColoring

namespace Keller

structure ColoringData (n s : Nat) where
  vertices : Vector (Vector (Fin s) n) (2^n)
deriving Repr

instance : Fintype (ColoringData n s) :=
  Fintype.ofEquiv (Vector (Vector (Fin s) n) (2^n))
    { toFun := ColoringData.mk, invFun := ColoringData.vertices,
      left_inv := by intro; simp, right_inv := by intro; simp }

instance : ToString (ColoringData n s) where
  toString := fun kc => toString <| kc.vertices.toArray.map (·.toArray)

def ColoringData.get (i : BitVec n) (kc : ColoringData n s): Vector (Fin s) n :=
  kc.vertices[i.toFin]

def ColoringData.check (kc : ColoringData n s) : Bool :=
  decide (∀ i i' : BitVec n, i < i' →
    (∃ d : Fin n, i[d] ≠ i'[d] ∧ (kc.get i)[d] = (kc.get i')[d]) ∧
    (adjacent i i' → ∃ d : Fin n, (kc.get i)[d] ≠ (kc.get i')[d])
  )

def ColoringData.toKClique (kc : ColoringData n s) (h : kc.check = true) : KColoring n s where
  data := kc.get
  same := by
    intro i j ij_ne
    wlog iltj : i < j generalizing i j
    · specialize this j i ij_ne.symm (by
        simp [BitVec.toNat_eq, BitVec.le_def, BitVec.lt_def] at *
        omega
      )
      convert this using 3 <;> simp [eq_comm]

    simp [check] at h
    exact (h _ _ iltj).1
  diff := by
    intro i j ij_adj
    wlog iltj : i < j generalizing i j
    · rw [adjacent_symm] at ij_adj
      conv => enter [1,_]; rw [ne_eq,eq_comm,← ne_eq]
      specialize this j i ij_adj (by
        have := ne_of_adjacent ij_adj
        simp [BitVec.toNat_eq, BitVec.le_def, BitVec.lt_def] at *
        omega
      )
      exact this

    simp [check] at h
    exact (h _ _ iltj).2 ij_adj
