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
@[simp] theorem colors_flip (mask) {v : KVertex n s} : (flip mask v).colors = v.colors := rfl

@[simp] theorem flip_flip (mask : BitVec n) {v : KVertex n s} : (v.flip mask).flip mask = v := by
  simp [flip, BitVec.xor_assoc]

/--
Actually *super* non-obvious that this is an automorphism!!!!
The justification is basically that if an s gap occurs at j, it still occurs there,
while the colors never change so other inequalities are preserved

I don't think this is an SR clausal symmetry?
This would require something stronger, like fully general substitutions.
-/
def flipAt (j : Fin n) (k : Fin s) (v : KVertex n s) : KVertex n s :=
  if v.colors[j] = k then
    { bv := v.bv ^^^ (1 <<< j.val)
    , colors := v.colors }
  else
    v

theorem bv_flipAt (j k) {v : KVertex n s} :
    (flipAt j k v).bv =
      if v.colors[j] = k
      then v.bv ^^^ (1 <<< j.val)
      else v.bv := by
  unfold flipAt; split <;> simp

@[simp] theorem colors_flipAt {j k} {v : KVertex n s} : (flipAt j k v).colors = v.colors := by
  unfold flipAt; split <;> rfl

@[simp] theorem flipAt_flipAt {j k} {v : KVertex n s} : (v.flipAt j k).flipAt j k = v := by
  unfold flipAt
  split
  · ext <;> simp
  · rfl

@[simp] theorem flipAt_inj {j k} : flipAt j k a = flipAt j k b ↔ a = b := by
  constructor
  · intro h; simpa using congrArg (flipAt j k) h
  · rintro rfl; rfl

@[simp] theorem bv_flipAt_inj_iff {j k} (h : a.colors[j] = b.colors[j]): (flipAt j k a).bv = (flipAt j k b).bv ↔ a.bv = b.bv := by
  simp [bv_flipAt, h]
  split
  · rw [BitVec.xor_comm, BitVec.xor_comm b.bv, BitVec.xor_right_inj]
  · rfl

@[simp] theorem getElem_bv_flipAt_inj_iff {j : Fin n} {j2 : Nat} {hj2 : j2 < n} {k}
      (h : a.colors[j2] = b.colors[j2])
    : (flipAt j k a).bv[j2] = (flipAt j k b).bv[j2] ↔ a.bv[j2] = b.bv[j2] := by
  if j = j2 then
    subst j2
    simp [bv_flipAt, h]
    split
    · simp
    · rfl
  else
    simp [bv_flipAt]
    split <;> split <;> simp <;> {
      apply iff_of_eq; congr
      rw [Bool.xor_eq_self_left]
      rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat
        , Nat.shiftLeft_eq, Nat.one_mul, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) j.isLt)
        , Nat.testBit_two_pow]
      simp_all [Fin.ext_iff]
    }


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
  ext <;> simp [reorder, BitVec.getLsbD_eq_getElem, *]

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

def flipAt (j : Fin n) (k : Fin s) : KAuto n s :=
  RelIso.mk ({
    toFun := KVertex.flipAt j k
    invFun := KVertex.flipAt j k
    left_inv  := by intro; simp
    right_inv := by intro; simp
  }) (by
    intro a b
    simp [KAdj]
    constructor
    · rintro ⟨j1,bv_ne_j1,cs_eq_j1,j2,js_ne,ne_j2⟩
      use j1
      rw [KVertex.getElem_bv_flipAt_inj_iff cs_eq_j1] at bv_ne_j1
      use bv_ne_j1, cs_eq_j1, j2, js_ne
      by_cases a.colors[j2.val] = b.colors[j2.val] <;> simp_all
    · rintro ⟨j1,bv_ne_j1,cs_eq_j1,j2,js_ne,ne_j2⟩
      use j1
      rw [KVertex.getElem_bv_flipAt_inj_iff cs_eq_j1]
      use bv_ne_j1, cs_eq_j1, j2, js_ne
      by_cases a.colors[j2.val] = b.colors[j2.val] <;> simp_all
  )

@[simp] theorem toFun_flipAt {x : KVertex _ _ } :
  DFunLike.coe (F := KAdj ≃r KAdj) (α := KVertex n s) (β := fun _ => KVertex n s)
    (flipAt (n := n) (s := s) j k) x = KVertex.flipAt j k x := rfl


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

end KAuto

namespace KClique

theorem get_map_flipAt {klique : KClique n s} {j k i}
  : ((klique.map (KAuto.flipAt j k)).get i) = klique.get (if (klique.get i)[j.val] = k then i ^^^ (1 <<< j.val) else i) := by
  simp [map, get_eq_iff_mem]
  refine ⟨⟨if (klique.get i)[j.val] = k then i ^^^ (1 <<< j.val) else i,_⟩, klique.get_mem _, ?_⟩
  split
  · have := klique.get_adj_one_diff (i₁ := i) (i₂ := i ^^^ (1 <<< j.val)) (j₁ := j)
      (by simp [bv_toNat])
      (by intro j h; simp [bv_toNat] at h; rw [eq_comm] at h; simp [Nat.testBit_one_eq_true_iff_self_eq_zero] at h; omega)
    replace this := this.1.symm; simp at this
    simp [KVertex.flipAt, BitVec.xor_assoc, *]
  · simp [KVertex.flipAt, *]

theorem get_map_permute {k : KClique n s} {f} {i}
  : (k.map (KAuto.permute f)).get i = Vector.ofFn fun j => (f j) (k.get i)[j] := by
  simp [get_eq_iff_mem, map]
  refine ⟨⟨i,_⟩, k.get_mem _, ?_⟩
  simp [KVertex.permute]

theorem get_map_reorder {k : KClique n s} {f} {i}
  : (k.map (KAuto.reorder f)).get i = Vector.ofFn fun j => (k.get (BitVec.ofFn fun j => i[f.symm j]))[f j] := by
  simp [get_eq_iff_mem, map]
  refine ⟨_, k.get_mem (BitVec.ofFn fun j => i[f.symm j]), ?_⟩
  simp [KVertex.reorder]
  ext; simp [BitVec.getLsbD_eq_getElem, *]

end KClique
