/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.Autos
import Experiments.Keller.SymmBreak.TwoCubes
import Experiments.Keller.SymmBreak.Matrix

namespace Keller.SymmBreak

def Matrix.rowIdx (n) : Vector (BitVec (n+5)) 3 :=
    #v[7,11,19]

def Matrix.colIdx (n) : Vector (Fin (n+5)) 3 :=
    #v[2,3,4]

def Matrix.ofClique (tc : ThreeCubes n s) : Matrix (s+2) where
  data := .ofFn fun r => .ofFn fun c =>
    (tc.kclique.get (rowIdx n)[r])[(colIdx n)[c]]
  transpose_one := by
    intro r c
    wlog r_le_c : r ≤ c
    · specialize this tc c r (by omega)
      rw [or_comm]; exact this
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]
    simp only [Fin.val_eq_iff_lt_and_eq, Fin.mk_one, Nat.lt_add_left_iff_pos,
      Nat.zero_lt_succ, exists_const]
    match r with
    | ⟨0,_⟩ =>
      match c with
      | ⟨0,_⟩ => simp [rowIdx, colIdx]; exact tc.c7_2
      | ⟨1,_⟩ => simp [rowIdx, colIdx]; exact tc.c7_or_c11_eq_one
      | ⟨2,_⟩ => simp [rowIdx, colIdx]; exact tc.c7_or_c19_eq_one
    | ⟨1,_⟩ =>
      match c with
      | ⟨1,_⟩ => simp [rowIdx, colIdx]; exact tc.c11_3
      | ⟨2,_⟩ => simp [rowIdx, colIdx]; exact tc.c11_or_c19_eq_one
    | ⟨2,_⟩ =>
      match c with
      | ⟨2,_⟩ => simp [rowIdx, colIdx]; exact tc.c19_4

theorem Matrix.canonicalizeClique (tc : ThreeCubes n s) :
    ∃ tc' : ThreeCubes n s, ofClique tc' ∈ canonicalCases := by
  sorry
