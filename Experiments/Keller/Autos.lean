/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.KellerGraph

namespace Keller

def KAuto (n s) := SimpleGraph.Iso (KGraph n s) (KGraph n s)

def KClique.map (a : KAuto n s) (k : KClique n s) : KClique n s :=
  ⟨(k.val.map a.toEmbedding.toEmbedding), by
  have ⟨vs,{card_eq, isClique}⟩ := k
  simp only [KClique, SimpleGraph.isNClique_iff,
    Finset.card_map, card_eq, and_true]
  clear card_eq
  generalize hvs' : vs.map _ = vs'
  simp [Finset.ext_iff] at hvs'
  intro v₁ hv₁ v₂ hv₂ hne
  simp [← hvs'] at hv₁ hv₂; clear hvs'
  rcases hv₁ with ⟨v₁,hv₁,rfl⟩; rcases hv₂ with ⟨v₂,hv₂,rfl⟩
  apply a.map_adj_iff.mpr
  simp [SimpleGraph.isClique_iff]
  replace hne : v₁ ≠ v₂ := fun h => hne (congrArg a.toFun h)
  apply isClique ?_ ?_ hne <;> simp [hv₁, hv₂]
  ⟩


namespace KVertex

def flip (mask : BitVec n) (v : KVertex n s) : KVertex n s :=
  { bv := v.bv ^^^ mask, colors := v.colors }

theorem bv_flip (mask) {v : KVertex n s} : (flip mask v).bv = v.bv ^^^ mask := rfl
@[simp] theorem bv_colors (mask) {v : KVertex n s} : (flip mask v).colors = v.colors := rfl

@[simp] theorem flip_flip (mask : BitVec n) {v : KVertex n s} : (v.flip mask).flip mask = v := by
  simp [flip, BitVec.xor_assoc]


def permute (f : Fin n → Fin s → Fin s) (v : KVertex n s) : KVertex n s :=
  { bv := v.bv, colors := Vector.ofFn (fun j => (f j) v.colors[j]) }

@[simp] theorem bv_permute (f) {v : KVertex n s} : (permute f v).bv = v.bv := rfl

theorem colors_permute (f) (v : KVertex n s) {j h} :
    (permute f v).colors[j]'h = (f ⟨j,h⟩) v.colors[j] := by
  simp [permute]


theorem permute_permute (f₁ f₂ : Fin n → Fin s → Fin s) {v} :
    permute f₁ (permute f₂ v) = permute (fun j => f₁ j ∘ f₂ j) v := by
  simp [permute]

@[simp] theorem permute_id {v : KVertex n s} : permute (fun _ => id) v = v := by
  simp [permute]
  congr
  ext i hi
  simp


def reorder (f : Fin n → Fin n) (v : KVertex n s) : KVertex n s :=
  ⟨ BitVec.ofFn (v.bv[f ·])
  , Vector.ofFn (v.colors[f ·])⟩

theorem bv_reorder (f : Fin n → Fin n) (v : KVertex n s) {j hj} :
    (v.reorder f).bv[j]'hj = v.bv[f ⟨j,hj⟩] := by
  simp [reorder]

theorem colors_reorder (f : Fin n → Fin n) (v : KVertex n s) {j hj} :
    (v.reorder f).colors[j]'hj = v.colors[f ⟨j,hj⟩] := by
  simp [reorder]

theorem reorder_comp (f₁ f₂ : Fin n → Fin n) (v : KVertex n s)
    : reorder f₁ (reorder f₂ v) = reorder (f₂ ∘ f₁) v := by
  simp [reorder]

@[simp] theorem reorder_id (v : KVertex n s) : reorder id v = v := by
  ext <;> simp [reorder]

end KVertex


namespace KAuto

def id : KAuto n s := RelIso.refl _

def flip (mask : BitVec n) : KAuto n s :=
  RelIso.mk ({
    toFun := KVertex.flip mask
    invFun := KVertex.flip mask
    left_inv  := by intro; simp
    right_inv := by intro; simp
  }) (by
    simp [KAdj, KVertex.bv_flip]
  )

@[simp] theorem toFun_flip {x : KVertex _ _ } :
  DFunLike.coe (F := KAdj ≃r KAdj) (α := KVertex n s) (β := fun _ => KVertex n s)
    (flip (n := n) (s := s) mask) x = KVertex.flip mask x := rfl

def permute (f : Fin n → Fin s ≃ Fin s) : KAuto n s :=
  RelIso.mk ({
    toFun := KVertex.permute (fun j => f j)
    invFun := KVertex.permute (fun j => (f j).symm)
    left_inv  := by intro; simp [KVertex.permute_permute]
    right_inv := by intro; simp [KVertex.permute_permute]
  }) (by
    intro v₁ v₂
    simp [KAdj, KVertex.colors_permute])

@[simp] theorem toFun_permute {x : KVertex _ _ } :
  DFunLike.coe (F := KAdj ≃r KAdj) (α := KVertex n s) (β := fun _ => KVertex n s)
    (permute (n := n) (s := s) f) x = KVertex.permute (fun j => f j) x := rfl

def reorder (f : Fin n ≃ Fin n) : KAuto n s :=
  RelIso.mk {
    toFun := KVertex.reorder f
    invFun := KVertex.reorder f.invFun
    left_inv := by intro; simp [KVertex.reorder_comp]
    right_inv := by intro; simp [KVertex.reorder_comp]
  } (by
    intro a b
    simp [KAdj, KVertex.reorder]
    constructor
    · rintro ⟨j₁,hbv₁,hc1,j₂,hne,h⟩
      use f j₁, hbv₁, hc1, f j₂
      rw [EmbeddingLike.apply_eq_iff_eq]
      simp [hne, h]
    · rintro ⟨j₁,hbv₁,hc1,j₂,hne,h⟩
      use f.symm j₁; simp
      use hbv₁, hc1, f.symm j₂
      rw [EmbeddingLike.apply_eq_iff_eq]
      simp [hne, h]
  )

@[simp] theorem toFun_reorder {x : KVertex _ _ } :
  DFunLike.coe (F := KAdj ≃r KAdj) (α := KVertex n s) (β := fun _ => KVertex n s)
    (reorder (n := n) (s := s) f) x = KVertex.reorder (fun j => f j) x := rfl

def swap [DecidableEq α] (L : List (α × α)) : α ≃ α :=
  match L with
  | [] => Equiv.refl _
  | (a,b) :: tail => (swap tail).insert a b

@[simp] theorem swap_nil [DecidableEq α] : swap (α := α) [] i = i := rfl

@[simp] theorem swap_cons_of_eq_left [DecidableEq α] :
    swap (α := α) ((i,o) :: tail) i = o := by
  simp [swap]

@[simp] theorem swap_cons_of_eq_right [DecidableEq α]
      (htail : swap tail i' = o) :
    swap (α := α) ((i,o) :: tail) i' = swap tail i := by
  simp [swap, htail]; rw [Equiv.insert_right]; exact htail

@[simp] theorem swap_cons_of_ne [DecidableEq α]
      (hhead : i' ≠ i) (htail : swap tail i' ≠ o) :
    swap (α := α) ((i,o) :: tail) i' = swap tail i' := by
  simp [swap, htail]; rw [Equiv.insert_unchanged] <;> assumption

theorem swap_eq_of_mem [DecidableEq α] (L : List (α × α))
    (is_distinct : L.Pairwise (·.1 ≠ ·.1)) (os_distinct : L.Pairwise (·.2 ≠ ·.2))
    (pair_mem : (i,o) ∈ L) :
    swap L i = o := by
  induction L generalizing i o with
  | nil => simp at pair_mem
  | cons hd tl ih =>
    simp at pair_mem
    rcases pair_mem with (rfl|pair_mem)
    case inl => simp
    case inr =>
    specialize ih is_distinct.tail os_distinct.tail pair_mem
    replace is_distinct := Ne.symm <| List.rel_of_pairwise_cons is_distinct pair_mem
    replace os_distinct := Ne.symm <| List.rel_of_pairwise_cons os_distinct pair_mem
    clear pair_mem
    rcases hd with ⟨x,y⟩; dsimp at is_distinct os_distinct ⊢
    simp [swap]; rw [← ih] at os_distinct ⊢
    apply Equiv.insert_unchanged <;> assumption
