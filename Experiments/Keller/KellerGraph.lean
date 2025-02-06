/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.Upstream

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique

namespace Keller

@[ext]
structure KVertex (n s : Nat) where
  bv : BitVec n
  colors : Vector (Fin s) n
deriving Repr, DecidableEq

def KAdj (v₁ v₂ : KVertex n s) : Prop :=
  ∃ (j₁ : Fin n),
      v₁.bv[j₁] ≠ v₂.bv[j₁] ∧ v₁.colors[j₁] = v₂.colors[j₁] ∧
    ∃ j₂, j₁ ≠ j₂ ∧
      (v₁.bv[j₂] ≠ v₂.bv[j₂] ∨ v₁.colors[j₂] ≠ v₂.colors[j₂])

theorem KAdj.symm : Symmetric (KAdj (n := n) (s := s)) := by
  intro x y h
  unfold KAdj at h ⊢
  rcases h with ⟨j₁,hb1,hc1,j₂,hj,h2⟩
  refine ⟨j₁,hb1.symm,hc1.symm,j₂,hj,?_⟩
  aesop

theorem KAdj.irrefl : Irreflexive (KAdj (n := n) (s := s)) := by
  intro x; unfold KAdj; simp

def KGraph (n s) : SimpleGraph (KVertex n s) where
  Adj := KAdj
  symm := KAdj.symm
  loopless := KAdj.irrefl

@[simp] theorem KGraph.Adj : (KGraph n s).Adj = KAdj := rfl

def KClique (n s) :=
  {vs : Finset (KVertex n s) // (KGraph n s).IsNClique (2^n) vs }

/-- The Keller conjecture in `n` dimensions. -/
def conjectureIn (n : Nat) : Prop :=
  ∀ s, IsEmpty (KClique n s)




theorem sameBV_not_adj (v₁ v₂ : KVertex n s)
  : v₁.bv = v₂.bv → ¬ KAdj v₁ v₂ := by
  intro h
  unfold KAdj; simp [h]

theorem KVertex.bv_injOn_clique (isClique : (KGraph n s).IsClique vs) :
    vs.InjOn KVertex.bv := by
  intro v₁ hv₁ v₂ hv₂ h
  by_contra hne
  have := sameBV_not_adj v₁ v₂ h
  have := isClique hv₁ hv₂ hne
  contradiction

theorem KGraph.nclique_card_le (isNClique : (KGraph n s).IsNClique size vs) :
    vs.card ≤ 2^n := by
  rw [← BitVec.card (n := n)]
  apply Finset.card_le_card_of_injOn
  · simp
  · apply KVertex.bv_injOn_clique isNClique.isClique

theorem KGraph.cliqueNum_le : (KGraph n s).cliqueNum ≤ 2^n := by
  unfold SimpleGraph.cliqueNum
  generalize hsizes : setOf _ = sizes
  by_contra h
  simp at h
  have : ∃ size ∈ sizes, size > 2^n := by
    clear hsizes
    exact exists_lt_of_lt_csSup' h
  clear h
  simp [← hsizes] at this; clear hsizes
  rcases this with ⟨size,⟨clique,isNclique⟩,h⟩
  have := nclique_card_le isNclique
  have := isNclique.card_eq
  omega


namespace KClique

variable (k : KClique n s)

def isClique := k.prop.isClique
def card_eq := k.prop.card_eq

theorem exists_unique (i : BitVec n) : ∃! a, a ∈ k.val ∧ (fun v => v.bv = i) a := by
  apply existsUnique_of_exists_of_unique
  · have := Finset.surj_on_of_inj_on_of_card_le
      (s := k.val) (t := Finset.univ) (f := fun a _ => a.bv)
      (hf := by simp)
      (hinj := fun _ _ c d => KVertex.bv_injOn_clique k.isClique c d)
      (hst := by simp [k.card_eq])
      i (by simp)
    rcases this with ⟨v,hv,rfl⟩
    use v, hv
  · rintro x1 x2 ⟨h1,rfl⟩ ⟨h2,hbv⟩
    apply KVertex.bv_injOn_clique k.isClique h1 h2 hbv.symm

def get (i : BitVec n) : Vector (Fin s) n :=
  k.val.choose _ (k.exists_unique i) |>.2

theorem get_mem (i : BitVec n) : ⟨i, k.get i⟩ ∈ k.val := by
  unfold get
  generalize hv : Finset.choose (·.bv = i) k.val _ = v
  have ⟨mem,prop⟩ : v ∈ k.val ∧ v.bv = i := by
    rw [← hv]; apply Finset.choose_spec
  convert mem
  exact prop.symm

theorem get_eq_iff_mem (i : BitVec n) : k.get i = cs ↔ ⟨i,cs⟩ ∈ k.val := by
  unfold get
  generalize hv : Finset.choose (·.bv = i) k.val _ = v
  have ⟨mem,rfl⟩ : v ∈ k.val ∧ v.bv = i := by
    rw [hv.symm]; apply Finset.choose_spec
  clear hv
  constructor
  · rintro rfl; exact mem
  · intro mem2
    have := k.exists_unique v.bv |>.unique ⟨mem,rfl⟩ ⟨mem2,rfl⟩
    rw [this]

instance : GetElem (KClique n s) (BitVec n) (Vector (Fin s) n) ⊤ where
  getElem k i _ := k.get i

instance : GetElem (KClique n s) Nat (Vector (Fin s) n) (fun _ i => i < 2^n) where
  getElem k i h := k.get ⟨i, h⟩

theorem indices_connected {i₁ i₂ : BitVec n} (k : KClique n s) (j₁ : Fin n)
    : i₁ = i₂ ^^^ (1 <<< j₁.val) → ∃ j₂ : Fin n, j₂ ≠ j₁ ∧ k.get i₁ ≠ k.get i₂ := by
  intro h
  -- we know i₁ and i₂ are adjacent because they are not equal
  have := k.isClique (k.get_mem i₁) (k.get_mem i₂)
  subst h
  specialize this (by
    -- proof that i₁ ≠ i₂ basically
    simp [bv_toNat]
    suffices 1 <<< ↑j₁ % 2 ^ n > 0 by simp_all [← Nat.ne_zero_iff_zero_lt]
    rw [Nat.one_shiftLeft, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) j₁.isLt)]
    exact Nat.pow_pos (by decide)
  )

  rcases this with ⟨j1,bs_ne_at_j1,-,j2,js_ne,h2⟩
  dsimp at *

  -- we know this because i₁ and i₂ only differ at j₁
  have : j1 = j₁ := by
    clear! j2
    simp [bv_toNat, Nat.testBit_one_eq_true_iff_self_eq_zero] at bs_ne_at_j1
    omega
  clear bs_ne_at_j1; subst j₁
  -- we know the bitvecs aren't different at j2...
  cases h2
  case inl h =>
    exfalso; apply h; clear h
    simp [bv_toNat]
    rw [Bool.eq_false_iff, ne_eq, Nat.testBit_one_eq_true_iff_self_eq_zero]
    omega
  case inr h =>
  -- therefore the colors must be different!
  use j2, Ne.symm js_ne; intro contra; rw [contra] at h; contradiction

end KClique

/-! ##### Computational Utilities -/

instance : DecidableRel (KAdj (n := n) (s := s)) :=
  fun v₁ v₂ => by unfold KAdj; infer_instance

namespace KVertex

nonrec def toString (v : KVertex n s) : String :=
  s!"{v.bv};{v.colors.toList}"

instance : ToString (KVertex n s) where
  toString := KVertex.toString

instance : Fintype (KVertex n s) where
  elems := Finset.univ ×ˢ Finset.univ
            |>.map ⟨fun (a,b) => ⟨a,b⟩, by rintro ⟨_,_⟩ ⟨_,_⟩; simp⟩
  complete := by simp

end KVertex
