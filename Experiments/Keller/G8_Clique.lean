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

instance : ToString (KCliqueData n s) where
  toString := fun kc => toString <| kc.vertices.toArray.map (·.toArray)

def KCliqueData.get (i : BitVec n) (kc : KCliqueData n s): KVertex n s :=
  { bv := i, colors := kc.vertices[i.toFin] }

def KCliqueData.getEmbedding (kc : KCliqueData n s) : BitVec n ↪ KVertex n s :=
  ⟨kc.get, by intro a; simp [get]⟩

def KCliqueData.checkAll (kc : KCliqueData n s) : Bool :=
  decide (∀ i i' : Fin (2^n), i < i' → KAdj (kc.get i) (kc.get i'))

theorem KCliqueData.checkAll_implies_not_conjecture (kc : KCliqueData n s)
  : kc.checkAll = true → ¬ conjectureIn n := by
  simp [checkAll, conjectureIn]
  intro h
  use s, (Finset.univ |>.map kc.getEmbedding)
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
  · simp

set_option maxRecDepth 800 in
def G8_clique: KCliqueData 8 2 :=
  KCliqueData.mk <| Vector.mk #[
  v 0 0 0 0 0 0 0 0, v 0 0 1 0 0 0 0 0, v 1 0 1 0 1 1 0 1, v 1 0 1 0 1 0 1 1,
  v 0 0 0 1 1 0 1 1, v 0 1 1 1 1 1 0 1, v 0 0 1 0 0 0 0 0, v 0 1 1 0 0 0 0 0,
  v 0 1 0 0 0 0 0 0, v 0 1 1 0 0 0 0 0, v 1 1 0 0 1 0 1 1, v 1 1 0 0 1 1 0 1,
  v 0 0 0 1 1 1 0 1, v 0 1 1 1 1 0 1 1, v 0 0 0 0 0 0 0 0, v 0 1 0 0 0 0 0 0,
  v 0 0 0 0 0 1 0 0, v 0 0 1 0 0 1 0 0, v 1 0 1 0 1 1 1 1, v 1 0 1 0 1 0 0 1,
  v 0 0 0 1 1 0 0 1, v 0 1 1 1 1 1 1 1, v 0 0 1 0 0 1 0 0, v 0 1 1 0 0 1 0 0,
  v 0 1 0 0 0 1 0 0, v 0 1 1 0 0 1 0 0, v 1 1 0 0 1 0 0 1, v 1 1 0 0 1 1 1 1,
  v 0 0 0 1 1 1 1 1, v 0 1 1 1 1 0 0 1, v 0 0 0 0 0 1 0 0, v 0 1 0 0 0 1 0 0,
  v 1 0 1 1 0 0 1 1, v 1 1 1 1 0 0 1 1, v 1 0 1 0 0 1 0 1, v 1 1 0 0 0 0 1 1,
  v 0 1 1 1 0 0 1 1, v 0 1 1 1 0 1 0 1, v 1 1 1 1 0 0 1 1, v 1 1 0 1 0 0 1 1,
  v 1 0 0 1 0 0 1 1, v 1 1 0 1 0 0 1 1, v 1 0 1 0 0 0 1 1, v 1 1 0 0 0 1 0 1,
  v 0 0 0 1 0 1 0 1, v 0 0 0 1 0 0 1 1, v 1 0 1 1 0 0 1 1, v 1 0 0 1 0 0 1 1,
  v 1 1 0 1 0 1 0 1, v 1 0 0 1 0 1 0 1, v 1 1 0 0 0 1 0 1, v 1 0 1 0 0 0 1 1,
  v 0 0 0 1 0 0 1 1, v 0 0 0 1 0 1 0 1, v 1 0 0 1 0 1 0 1, v 1 0 1 1 0 1 0 1,
  v 1 1 1 1 0 1 0 1, v 1 0 1 1 0 1 0 1, v 1 1 0 0 0 0 1 1, v 1 0 1 0 0 1 0 1,
  v 0 1 1 1 0 1 0 1, v 0 1 1 1 0 0 1 1, v 1 1 0 1 0 1 0 1, v 1 1 1 1 0 1 0 1,
  v 1 1 0 1 1 0 0 0, v 1 0 0 1 1 0 0 0, v 1 1 0 0 1 0 0 0, v 1 0 1 0 1 1 1 0,
  v 0 0 0 1 1 1 1 0, v 0 0 0 1 1 0 0 0, v 1 0 0 1 1 0 0 0, v 1 0 1 1 1 0 0 0,
  v 1 1 1 1 1 0 0 0, v 1 0 1 1 1 0 0 0, v 1 1 0 0 1 1 1 0, v 1 0 1 0 1 0 0 0,
  v 0 1 1 1 1 0 0 0, v 0 1 1 1 1 1 1 0, v 1 1 0 1 1 0 0 0, v 1 1 1 1 1 0 0 0,
  v 1 0 1 1 1 0 0 0, v 1 1 1 1 1 0 0 0, v 1 0 1 0 1 1 1 0, v 1 1 0 0 1 0 0 0,
  v 0 1 1 1 1 0 0 0, v 0 1 1 1 1 1 1 0, v 1 1 1 1 1 0 0 0, v 1 1 0 1 1 0 0 0,
  v 1 0 0 1 1 0 0 0, v 1 1 0 1 1 0 0 0, v 1 0 1 0 1 0 0 0, v 1 1 0 0 1 1 1 0,
  v 0 0 0 1 1 1 1 0, v 0 0 0 1 1 0 0 0, v 1 0 1 1 1 0 0 0, v 1 0 0 1 1 0 0 0,
  v 0 0 0 0 0 0 1 0, v 0 0 1 0 0 0 1 0, v 1 0 1 0 1 0 0 1, v 1 0 1 0 1 1 1 1,
  v 0 0 0 1 1 1 1 1, v 0 1 1 1 1 0 0 1, v 0 0 1 0 0 0 1 0, v 0 1 1 0 0 0 1 0,
  v 0 1 0 0 0 0 1 0, v 0 1 1 0 0 0 1 0, v 1 1 0 0 1 1 1 1, v 1 1 0 0 1 0 0 1,
  v 0 0 0 1 1 0 0 1, v 0 1 1 1 1 1 1 1, v 0 0 0 0 0 0 1 0, v 0 1 0 0 0 0 1 0,
  v 0 0 0 0 0 0 0 0, v 0 0 1 0 0 0 0 0, v 1 0 1 0 1 1 0 1, v 1 0 1 0 1 0 1 1,
  v 0 0 0 1 1 0 1 1, v 0 1 1 1 1 1 0 1, v 0 0 1 0 0 0 0 0, v 0 1 1 0 0 0 0 0,
  v 0 1 0 0 0 0 0 0, v 0 1 1 0 0 0 0 0, v 1 1 0 0 1 0 1 1, v 1 1 0 0 1 1 0 1,
  v 0 0 0 1 1 1 0 1, v 0 1 1 1 1 0 1 1, v 0 0 0 0 0 0 0 0, v 0 1 0 0 0 0 0 0,
  v 0 0 0 0 0 0 1 0, v 0 0 1 0 0 0 1 0, v 1 0 1 0 1 0 0 1, v 1 0 1 0 1 1 1 1,
  v 0 0 0 1 1 1 1 1, v 0 1 1 1 1 0 0 1, v 0 0 1 0 0 0 1 0, v 0 1 1 0 0 0 1 0,
  v 0 1 0 0 0 0 1 0, v 0 1 1 0 0 0 1 0, v 1 1 0 0 1 1 1 1, v 1 1 0 0 1 0 0 1,
  v 0 0 0 1 1 0 0 1, v 0 1 1 1 1 1 1 1, v 0 0 0 0 0 0 1 0, v 0 1 0 0 0 0 1 0,
  v 0 0 0 0 0 1 1 0, v 0 0 1 0 0 1 1 0, v 1 0 1 0 1 0 1 1, v 1 0 1 0 1 1 0 1,
  v 0 0 0 1 1 1 0 1, v 0 1 1 1 1 0 1 1, v 0 0 1 0 0 1 1 0, v 0 1 1 0 0 1 1 0,
  v 0 1 0 0 0 1 1 0, v 0 1 1 0 0 1 1 0, v 1 1 0 0 1 1 0 1, v 1 1 0 0 1 0 1 1,
  v 0 0 0 1 1 0 1 1, v 0 1 1 1 1 1 0 1, v 0 0 0 0 0 1 1 0, v 0 1 0 0 0 1 1 0,
  v 1 1 0 1 0 0 1 1, v 1 0 0 1 0 0 1 1, v 1 1 0 0 0 0 1 1, v 1 0 1 0 0 1 0 1,
  v 0 0 0 1 0 1 0 1, v 0 0 0 1 0 0 1 1, v 1 0 0 1 0 0 1 1, v 1 0 1 1 0 0 1 1,
  v 1 1 1 1 0 0 1 1, v 1 0 1 1 0 0 1 1, v 1 1 0 0 0 1 0 1, v 1 0 1 0 0 0 1 1,
  v 0 1 1 1 0 0 1 1, v 0 1 1 1 0 1 0 1, v 1 1 0 1 0 0 1 1, v 1 1 1 1 0 0 1 1,
  v 1 0 1 1 0 1 0 1, v 1 1 1 1 0 1 0 1, v 1 0 1 0 0 0 1 1, v 1 1 0 0 0 1 0 1,
  v 0 1 1 1 0 1 0 1, v 0 1 1 1 0 0 1 1, v 1 1 1 1 0 1 0 1, v 1 1 0 1 0 1 0 1,
  v 1 0 0 1 0 1 0 1, v 1 1 0 1 0 1 0 1, v 1 0 1 0 0 1 0 1, v 1 1 0 0 0 0 1 1,
  v 0 0 0 1 0 0 1 1, v 0 0 0 1 0 1 0 1, v 1 0 1 1 0 1 0 1, v 1 0 0 1 0 1 0 1,
  v 1 0 1 1 1 1 1 0, v 1 1 1 1 1 1 1 0, v 1 0 1 0 1 0 0 0, v 1 1 0 0 1 1 1 0,
  v 0 1 1 1 1 1 1 0, v 0 1 1 1 1 0 0 0, v 1 1 1 1 1 1 1 0, v 1 1 0 1 1 1 1 0,
  v 1 0 0 1 1 1 1 0, v 1 1 0 1 1 1 1 0, v 1 0 1 0 1 1 1 0, v 1 1 0 0 1 0 0 0,
  v 0 0 0 1 1 0 0 0, v 0 0 0 1 1 1 1 0, v 1 0 1 1 1 1 1 0, v 1 0 0 1 1 1 1 0,
  v 1 1 0 1 1 1 1 0, v 1 0 0 1 1 1 1 0, v 1 1 0 0 1 1 1 0, v 1 0 1 0 1 0 0 0,
  v 0 0 0 1 1 0 0 0, v 0 0 0 1 1 1 1 0, v 1 0 0 1 1 1 1 0, v 1 0 1 1 1 1 1 0,
  v 1 1 1 1 1 1 1 0, v 1 0 1 1 1 1 1 0, v 1 1 0 0 1 0 0 0, v 1 0 1 0 1 1 1 0,
  v 0 1 1 1 1 1 1 0, v 0 1 1 1 1 0 0 0, v 1 1 0 1 1 1 1 0, v 1 1 1 1 1 1 1 0,
  v 0 0 0 0 0 1 1 0, v 0 0 1 0 0 1 1 0, v 1 0 1 0 1 0 1 1, v 1 0 1 0 1 1 0 1,
  v 0 0 0 1 1 1 0 1, v 0 1 1 1 1 0 1 1, v 0 0 1 0 0 1 1 0, v 0 1 1 0 0 1 1 0,
  v 0 1 0 0 0 1 1 0, v 0 1 1 0 0 1 1 0, v 1 1 0 0 1 1 0 1, v 1 1 0 0 1 0 1 1,
  v 0 0 0 1 1 0 1 1, v 0 1 1 1 1 1 0 1, v 0 0 0 0 0 1 1 0, v 0 1 0 0 0 1 1 0,
  v 0 0 0 0 0 1 0 0, v 0 0 1 0 0 1 0 0, v 1 0 1 0 1 1 1 1, v 1 0 1 0 1 0 0 1,
  v 0 0 0 1 1 0 0 1, v 0 1 1 1 1 1 1 1, v 0 0 1 0 0 1 0 0, v 0 1 1 0 0 1 0 0,
  v 0 1 0 0 0 1 0 0, v 0 1 1 0 0 1 0 0, v 1 1 0 0 1 0 0 1, v 1 1 0 0 1 1 1 1,
  v 0 0 0 1 1 1 1 1, v 0 1 1 1 1 0 0 1, v 0 0 0 0 0 1 0 0, v 0 1 0 0 0 1 0 0
] (by simp)
where v (a b c d e f g h) : Vector (Fin 2) 8 :=
  Vector.mk #[a,b,c,d,e,f,g,h] (by simp)
