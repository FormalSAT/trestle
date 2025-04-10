/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.KellerGraph
import Mathlib.Tactic.Basic

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
  { idx := v.idx ^^^ mask, color := v.color }

theorem bv_flip (mask) {v : KVertex n s} : (flip mask v).idx = v.idx ^^^ mask := rfl
@[simp] theorem colors_flip (mask) {v : KVertex n s} : (flip mask v).color = v.color := rfl

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
  if v.color[j] = k then
    { idx := v.idx ^^^ BitVec.oneAt j
    , color := v.color }
  else
    v

theorem bv_flipAt (j k) {v : KVertex n s} :
    (flipAt j k v).idx =
      if v.color[j] = k
      then v.idx ^^^ BitVec.oneAt j
      else v.idx := by
  unfold flipAt; split <;> simp

@[simp] theorem colors_flipAt {j k} {v : KVertex n s} : (flipAt j k v).color = v.color := by
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

@[simp] theorem bv_flipAt_inj_iff {j k} (h : a.color[j] = b.color[j]): (flipAt j k a).idx = (flipAt j k b).idx ↔ a.idx = b.idx := by
  simp [bv_flipAt, h]
  split
  · rw [BitVec.xor_comm, BitVec.xor_comm b.idx, BitVec.xor_right_inj]
  · rfl

@[simp] theorem getElem_bv_flipAt_inj_iff {j : Fin n} {j2 : Nat} {hj2 : j2 < n} {k}
      (h : a.color[j2] = b.color[j2])
    : (flipAt j k a).idx[j2] = (flipAt j k b).idx[j2] ↔ a.idx[j2] = b.idx[j2] := by
  if j = j2 then
    subst j2
    simp [bv_flipAt, h]
    split
    · simp
    · rfl
  else
    simp [bv_flipAt]
    split <;> split <;> simp [*]


def permute (f : Fin n → Fin s → Fin s) (v : KVertex n s) : KVertex n s :=
  { idx := v.idx, color := Vector.ofFn (fun j => (f j) v.color[j]) }

@[simp] theorem bv_permute (f) {v : KVertex n s} : (permute f v).idx = v.idx := rfl

theorem colors_permute (f) (v : KVertex n s) {j h} :
    (permute f v).color[j]'h = (f ⟨j,h⟩) v.color[j] := by
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
  ⟨ BitVec.ofFn (v.idx[f ·])
  , Vector.ofFn (v.color[f ·])⟩

theorem bv_reorder (f : Fin n → Fin n) (v : KVertex n s) {j hj} :
    (v.reorder f).idx[j]'hj = v.idx[f ⟨j,hj⟩] := by
  simp [reorder]

theorem colors_reorder (f : Fin n → Fin n) (v : KVertex n s) {j hj} :
    (v.reorder f).color[j]'hj = v.color[f ⟨j,hj⟩] := by
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
      by_cases a.color[j2.val] = b.color[j2.val] <;> simp_all
    · rintro ⟨j1,bv_ne_j1,cs_eq_j1,j2,js_ne,ne_j2⟩
      use j1
      rw [KVertex.getElem_bv_flipAt_inj_iff cs_eq_j1]
      use bv_ne_j1, cs_eq_j1, j2, js_ne
      by_cases a.color[j2.val] = b.color[j2.val] <;> simp_all
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
  : ((klique.map (KAuto.flipAt j k)).get i) = klique.get (if (klique.get i)[j.val] = k then i ^^^ BitVec.oneAt j else i) := by
  simp [map, get_eq_iff_mem]
  refine ⟨⟨if (klique.get i)[j.val] = k then i ^^^ BitVec.oneAt j else i,_⟩, klique.get_mem _, ?_⟩
  split
  · have := klique.get_adj_one_diff (i₁ := i) (i₂ := i ^^^ BitVec.oneAt j) (j₁ := j)
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

noncomputable def lowerS {s'} (hs' : s' ≥ 2^n) (k : KClique (n+1) s') : KClique (n+1) (2^n) :=
  let colSets : Fin (n+1) → Finset (Fin s') := fun j =>
    k.val.image (fun v => v.color[j])
  let perms : Fin (n+1) → Fin s' ≃ Fin s' := fun j =>
    Equiv.Perm.setAll <| (colSets j |>.toList).zip (List.finRange s')
  let renumbered := k.map (KAuto.permute perms)
  have renumbered_lt : ∀ (i : BitVec (n+1)) (j : Fin (n+1)), (renumbered.get i)[j].val < 2^n := by
    intro i j
    have mem_colSets : (k.get i)[j] ∈ colSets j := by
      simp [colSets]; refine ⟨_, k.get_mem i, ?_⟩
      rfl
    rw [← Finset.mem_toList, List.mem_iff_getElem] at mem_colSets
    rcases mem_colSets with ⟨kIdx,kIdx_lt,kIdx_eq⟩

    replace kIdx_lt_pown : kIdx < 2^n := by
      simp [colSets] at kIdx_lt
      calc kIdx < _     := kIdx_lt
        _ ≤ 2^n         := by simpa using k.colorsInCol_lt j
    have kIdx_lt_s' : kIdx < s' := by
      calc kIdx < _     := kIdx_lt_pown
        _ ≤ s'          := hs'

    simp [renumbered, get_map_permute]; unfold perms
    rw [Equiv.Perm.setAll_eq_of_mem (o := ⟨kIdx,kIdx_lt_s'⟩)]
    exact kIdx_lt_pown

    case is_distinct =>
      rw [List.pairwise_iff_get]
      intro x y x_lt_y
      simp; rw [List.Nodup.getElem_inj_iff]; omega
      case h =>
      apply Finset.nodup_toList
    case os_distinct =>
      rw [List.pairwise_iff_get]
      intro x y x_lt_y
      simp; omega
    case pair_mem =>
      rw [List.mem_iff_getElem]
      simpa [*] using kIdx_lt

  ⟨renumbered.val.image (fun v => {idx := v.idx, color := v.color.map (Fin.ofNat' _ ·.val)})
  , by
  clear_value renumbered
  clear perms colSets k
  have renumbered_cast_eq : ∀ i (j) (hj : j < (n+1)),
        (renumbered.get i)[j].val % (2^n) =
          (renumbered.get i)[j].val := by
    intro i j hj; apply Nat.mod_eq_of_lt; simpa using renumbered_lt i ⟨j,hj⟩
  simp only at renumbered_cast_eq

  constructor
  · intro a a_mem b b_mem ne
    simp at a_mem b_mem
    rcases a_mem with ⟨⟨ai,ac⟩,a_mem,rfl⟩; rcases b_mem with ⟨⟨bi,bc⟩,b_mem,rfl⟩
    dsimp at ne ⊢
    simp [← KClique.get_eq_iff_mem] at a_mem b_mem
    subst ac bc
    replace ne : ai ≠ bi := by
      rintro rfl; simp at ne
    have := renumbered.isClique (KClique.get_mem _ ai) (KClique.get_mem _ bi) (by simp [ne])
    simpa [KAdj, Fin.ext_iff, renumbered_cast_eq] using this
  · rw [Finset.card_image_of_injOn ?H]; apply renumbered.card_eq
    case H =>
    rintro ⟨ai,ac⟩ a_mem ⟨bi,bc⟩ b_mem
    simp [← KClique.get_eq_iff_mem] at a_mem b_mem
    subst ac bc
    simp +contextual
    ⟩

end KClique

theorem conjectureIn_iff_forall_isEmpty (n : Nat) : conjectureIn n ↔ ∀ s, IsEmpty (KClique n s) := by
  unfold conjectureIn
  constructor
  · intro h s
    constructor; intro contra; apply h.false
    if s ≤ 2^(n-1) then
      exact contra.liftS ‹_›
    else
      match n with
      | 0 =>
        have := contra.card_eq
        sorry
      | n+1 =>
        simp_all; apply contra.lowerS; omega
  · intro h; apply h
