/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.Upstream

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Card

namespace Keller

@[ext]
structure KVertex (n s : Nat) where
  idx : BitVec n
  color : Vector (Fin s) n
deriving Repr, DecidableEq

def KAdj (v₁ v₂ : KVertex n s) : Prop :=
  ∃ (j₁ : Fin n),
      v₁.idx[j₁] ≠ v₂.idx[j₁] ∧ v₁.color[j₁] = v₂.color[j₁] ∧
    ∃ j₂, j₁ ≠ j₂ ∧
      (v₁.idx[j₂] ≠ v₂.idx[j₂] ∨ v₁.color[j₂] ≠ v₂.color[j₂])

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
  IsEmpty (KClique n (2^(n-1)))




theorem sam.idx_not_adj (v₁ v₂ : KVertex n s)
  : v₁.idx = v₂.idx → ¬ KAdj v₁ v₂ := by
  intro h
  unfold KAdj; simp [h]

theorem KVertex.idx_injOn_clique (isClique : (KGraph n s).IsClique vs) :
    vs.InjOn KVertex.idx := by
  intro v₁ hv₁ v₂ hv₂ h
  by_contra hne
  have := sam.idx_not_adj v₁ v₂ h
  have := isClique hv₁ hv₂ hne
  contradiction

theorem KGraph.nclique_card_le (isNClique : (KGraph n s).IsNClique size vs) :
    vs.card ≤ 2^n := by
  rw [← BitVec.card (n := n)]
  apply Finset.card_le_card_of_injOn
  · simp
  · apply KVertex.idx_injOn_clique isNClique.isClique

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

namespace KVertex

@[simp]
def liftS {s'} (h : s' ≥ s) (v : KVertex n s) : KVertex n s' :=
  { idx := v.idx, color := v.color.map (·.castLE h)}

end KVertex

namespace KClique

variable (k : KClique n s)

def isClique := k.prop.isClique
def card_eq := k.prop.card_eq

theorem exists_unique (i : BitVec n) : ∃! a, a ∈ k.val ∧ a.idx = i := by
  apply existsUnique_of_exists_of_unique
  · have := Finset.surj_on_of_inj_on_of_card_le
      (s := k.val) (t := Finset.univ) (f := fun a _ => a.idx)
      (hf := by simp)
      (hinj := fun _ _ c d => KVertex.idx_injOn_clique k.isClique c d)
      (hst := by simp [k.card_eq])
      i (by simp)
    rcases this with ⟨v,hv,rfl⟩
    use v, hv
  · rintro x1 x2 ⟨h1,rfl⟩ ⟨h2,hbv⟩
    apply KVertex.idx_injOn_clique k.isClique h1 h2 hbv.symm

def get (i : BitVec n) : Vector (Fin s) n :=
  k.val.choose _ (k.exists_unique i) |>.2

theorem get_mem (i : BitVec n) : ⟨i, k.get i⟩ ∈ k.val := by
  unfold get
  generalize hv : Finset.choose (·.idx = i) k.val _ = v
  have ⟨mem,prop⟩ : v ∈ k.val ∧ v.idx = i := by
    rw [← hv]; apply Finset.choose_spec
  convert mem
  exact prop.symm

theorem get_eq_iff_mem (i : BitVec n) : k.get i = cs ↔ ⟨i,cs⟩ ∈ k.val := by
  unfold get
  generalize hv : Finset.choose (·.idx = i) k.val _ = v
  have ⟨mem,rfl⟩ : v ∈ k.val ∧ v.idx = i := by
    rw [hv.symm]; apply Finset.choose_spec
  clear hv
  constructor
  · rintro rfl; exact mem
  · intro mem2
    have := k.exists_unique v.idx |>.unique ⟨mem,rfl⟩ ⟨mem2,rfl⟩
    rw [this]

instance : GetElem (KClique n s) (BitVec n) (Vector (Fin s) n) ⊤ where
  getElem k i _ := k.get i

instance : GetElem (KClique n s) Nat (Vector (Fin s) n) (fun _ i => i < 2^n) where
  getElem k i h := k.get ⟨i, h⟩

theorem get_adj {i₁ i₂ : BitVec n} (k : KClique n s) (h : i₁ ≠ i₂)
    : ∃ j₁ : Fin n, i₁[j₁] ≠ i₂[j₁] ∧ (k.get i₁)[j₁] = (k.get i₂)[j₁]
      ∧ ∃ j₂ ≠ j₁, i₁[j₂] ≠ i₂[j₂] ∨ (k.get i₁)[j₂] ≠ (k.get i₂)[j₂] := by
  -- i₁ and i₂ are adjacent because they are not equal
  have := k.isClique (k.get_mem i₁) (k.get_mem i₂) (by simp [h])

  rcases this with ⟨j1,bs_ne_at_j1,cs_eq_at_j1,j2,js_ne,h2⟩
  dsimp at *

  refine ⟨j1, ?in_xor, cs_eq_at_j1, j2, Ne.symm js_ne, ?colors_diff⟩
  case in_xor       => simpa [bv_toNat] using bs_ne_at_j1
  case colors_diff  => simpa [bv_toNat] using h2

theorem get_adj_one_diff {i₁ i₂ : BitVec n} (k : KClique n s) (j₁ : Fin n)
    : i₁[j₁] ≠ i₂[j₁] → (∀ j, i₁[j] ≠ i₂[j] → j = j₁) →
      (k.get i₁)[j₁] = (k.get i₂)[j₁] ∧ ∃ j₂ ≠ j₁, (k.get i₁)[j₂] ≠ (k.get i₂)[j₂] := by
  intro i1_i2_ne_at_j1 i1_i2

  have := get_adj (i₁ := i₁) (i₂ := i₂) k (by rintro rfl; contradiction)
  rcases this with ⟨j1,bs_ne_at_j1,cs_eq_at_j1,j2,js_ne,h2⟩

  -- there's only one coord where i₁ and i₂ are diff
  have : j1 = j₁ := by
    apply i1_i2
    simpa [bv_toNat] using bs_ne_at_j1
  subst j₁

  cases h2
  case inl h =>
    -- there's still only one coord where i₁ and i₂ differ
    exfalso; specialize i1_i2 j2 h; contradiction
  case inr h => use cs_eq_at_j1, j2, js_ne, h

theorem get_adj_of_eq_xor {i₁ i₂ : BitVec n} (k : KClique n s) (j₁ : Fin n)
    : i₂ = i₁ ^^^ BitVec.oneAt j₁ →
      (k.get i₁)[j₁] = (k.get i₂)[j₁] ∧ ∃ j₂ ≠ j₁, (k.get i₁)[j₂] ≠ (k.get i₂)[j₂] := by
  rintro rfl
  apply get_adj_one_diff
  · simp
  · intro j hj; by_contra contra; simp [← Fin.ext_iff, Ne.symm contra] at hj

theorem get_xor_oneAt (k : KClique n s) (j : Fin n) (j') (h : j.val = j' := by simp)
    : (k.get (i ^^^ BitVec.oneAt j))[j'] = (k.get i)[j'] := by
  subst j'
  have := get_adj_of_eq_xor (i₁ := i) k j rfl
  exact this.1.symm

theorem get_adj_of_xor_eq {i₁ i₂ : BitVec n} (k : KClique n s) (j₁ : Fin n)
    : i₁ ^^^ i₂ = BitVec.oneAt j₁ →
      (k.get i₁)[j₁] = (k.get i₂)[j₁] ∧ ∃ j₂ ≠ j₁, (k.get i₁)[j₂] ≠ (k.get i₂)[j₂] := by
  intro xor_eq
  apply get_adj_one_diff
  · simpa using congrArg (·[j₁]) xor_eq
  · intro j
    have := congrArg (·[j]) xor_eq
    simp [Bool.eq_iff_iff (b := decide _)] at this
    simp [this, Fin.ext_iff, eq_comm]

def liftS {s'} (h : s' ≥ s) (k : KClique n s) : KClique n s' :=
  ⟨ k.val.map ⟨KVertex.liftS h, by rintro ⟨xi,xc⟩ ⟨yi,yc⟩; simp [Vector.ext_iff]⟩
  , by
    constructor
    · intro x hx y hy ne
      simp at hx hy; rcases hx with ⟨x,hx,rfl⟩; rcases hy with ⟨y,hy,rfl⟩
      have ⟨j1,is_ne,cs_eq,j2,h2⟩ := k.property.isClique hx hy (by rintro rfl; simp at ne)
      clear ne
      use j1; simp_all
      use j2
    · simp [k.property.card_eq] ⟩

private theorem bv_oneBit_fixed_card (j : Fin (n+1)) :
    (Finset.univ |>.filter (α := BitVec (n+1)) (·[j])).card = 2^n := by
  let trues := Finset.filter (α := BitVec (n+1)) (fun x => x[j] = true) Finset.univ
  let falses := Finset.filter (α := BitVec (n+1)) (fun x => x[j] = false) Finset.univ
  refold_let trues

  have : trues.card = falses.card := by
    apply Finset.card_bijective (e := (· ^^^ .oneAt j))
    case he =>
      apply Function.Involutive.bijective
      intro x; simp [BitVec.xor_assoc]
    case hst =>
      simp +zetaDelta

  have : trues.card + falses.card = 2^(n+1) := by
    have disj : Disjoint trues falses := by
      rw [Finset.disjoint_iff_ne]; intro a a_mem b b_mem
      simp +zetaDelta at a_mem b_mem
      rintro rfl; simp_all
    have : trues.disjUnion falses disj = Finset.univ := by
      ext v; simp +zetaDelta
    rw [← Finset.card_disjUnion, this]; simp

  omega

def colorsInCol_lt (c : KClique (n+1) s) (j : Fin (n+1)) :
    (c.val.image (fun v => v.color[j])).card ≤ 2^n := by
  let S :=
    c.val.filter (α := KVertex _ _) (·.idx[j])
    |>.image (·.color[j])
  calc
    _ = S.card := by
      congr 1
      ext k
      simp [S]
      constructor
      · rintro ⟨⟨i,cs⟩,v_mem,rfl⟩
        rw [← c.get_eq_iff_mem] at v_mem; subst v_mem
        if h : i[j] then
          use ⟨i,c.get i⟩
          simp_all [c.get_mem i]
        else
          let i' := i ^^^ .oneAt j
          have : i'[j] := by unfold i'; simp_all
          have := c.get_adj_of_eq_xor (i₁ := i) (i₂ := i') j rfl |>.1
          use ⟨i', c.get i'⟩
          simp_all [c.get_mem i']
      · rintro ⟨a,⟨a_mem,_⟩,h⟩
        exact ⟨a,a_mem,h⟩
    _ ≤ (Finset.filter _ c.val).card :=
      Finset.card_image_le
    _ = (Finset.filter (fun x => x[j] = true) Finset.univ).card := by
      rw [eq_comm]
      apply Finset.card_nbij (i := fun i => ⟨i,c.get i⟩)
      case hi =>
        simp [c.get_mem]
      case i_inj =>
        simp +contextual [Set.InjOn]
      case i_surj =>
        rintro ⟨i,v⟩
        simp +contextual [c.get_eq_iff_mem]
    _ = 2^n := bv_oneBit_fixed_card j

end KClique

/-! ##### Computational Utilities -/

instance : DecidableRel (KAdj (n := n) (s := s)) :=
  fun v₁ v₂ => by unfold KAdj; infer_instance

namespace KVertex

nonrec def toString (v : KVertex n s) : String :=
  s!"{v.idx};{v.color.toList}"

instance : ToString (KVertex n s) where
  toString := KVertex.toString

instance : Fintype (KVertex n s) where
  elems := Finset.univ ×ˢ Finset.univ
            |>.map ⟨fun (a,b) => ⟨a,b⟩, by rintro ⟨_,_⟩ ⟨_,_⟩; simp⟩
  complete := by simp

end KVertex
