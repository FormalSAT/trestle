/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.KellerGraph

namespace Keller

structure KCliqueData (n s : Nat) where
  vertices : Vector (Vector (Fin s) n) (2^n)
deriving Repr

instance : Fintype (KCliqueData n s) :=
  Fintype.ofEquiv (Vector (Vector (Fin s) n) (2^n))
    { toFun := KCliqueData.mk, invFun := KCliqueData.vertices,
      left_inv := by intro; simp, right_inv := by intro; simp }

instance : ToString (KCliqueData n s) where
  toString := fun kc => toString <| kc.vertices.toArray.map (·.toArray)

def KCliqueData.get (i : BitVec n) (kc : KCliqueData n s): KVertex n s :=
  { bv := i, colors := kc.vertices[i.toFin] }

def KCliqueData.getEmbedding (kc : KCliqueData n s) : BitVec n ↪ KVertex n s :=
  ⟨kc.get, by intro a; simp [get]⟩

def KCliqueData.check (kc : KCliqueData n s) : Bool :=
  decide (∀ i i' : Fin (2^n), i < i' → KAdj (kc.get i) (kc.get i'))

def KCliqueData.toKClique (kc : KCliqueData n s) (h : kc.check = true) : KClique n s :=
  ⟨ Finset.univ.map kc.getEmbedding, by
    simp [check] at h
    constructor
    · intro x hx y hy hne; simp at hx hy
      rcases hx with ⟨⟨xi⟩,rfl⟩
      rcases hy with ⟨⟨yi⟩,rfl⟩
      simp at hne
      wlog hlt : xi < yi generalizing xi yi
      · apply SimpleGraph.adj_symm
        apply this; exact Ne.symm hne; omega
      specialize h xi yi hlt
      convert h using 1
        <;> simp [getEmbedding, BitVec.ofNat]
    · simp⟩

theorem KCliqueData.check_implies_not_conjecture (kc : KCliqueData n s)
  : kc.check = true → ¬ conjectureIn n := by
  intro h
  simp [conjectureIn]
  use s
  exact ⟨kc.toKClique h⟩

def KCliqueData.fromKClique (k : KClique n s) : KCliqueData n s :=
  ⟨Vector.ofFn fun i => k.get <| BitVec.ofFin i⟩

theorem KCliqueData.check_fromKClique (k : KClique n s) : (fromKClique k).check = true := by
  simp [check]
  intro a b h
  have := k.isClique (k.get_mem a) (k.get_mem b) ?diff
  case diff => simp [BitVec.ofNat, Fin.ne_of_lt h]
  simp [fromKClique, get, BitVec.ofNat]
  simp [BitVec.ofNat] at this
  exact this

/-- It is theoretically computable now to check all the potential cliques.
However, it is ill-advised to run this function for anything beyond n=2 s=2. -/
def KCliqueData.checkAll (n s : Nat) : Bool :=
  decide (∀ kc : KCliqueData n s, kc.check = false)

theorem KCliqueData.checkAll_iff_isempty_kclique (n s : Nat) :
    KCliqueData.checkAll n s = true ↔ IsEmpty (KClique n s) := by
  rw [← not_iff_not, isEmpty_iff]; simp [checkAll]
  constructor
  · rintro ⟨x,h⟩
    use x.toKClique h
  · rintro ⟨x,⟨⟩⟩
    use fromKClique x
    apply check_fromKClique
