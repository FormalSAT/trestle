/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Mathlib.Tactic.Basic

import Experiments.Keller.KColoring
import Experiments.Keller.Upstream

namespace Keller

def KAuto (n s) := Equiv.Perm (KColoring n s)

namespace KColoring

def flip (mask : BitVec n) (K : KColoring n s) : KColoring n s where
  data := fun i => K.data (i ^^^ mask)
  same := by
    intro i j ne
    have := K.same (i ^^^ mask) (j ^^^ mask) (by simpa)
    simpa using this
  diff := by
    intro i j adj
    exact K.diff (i ^^^ mask) (j ^^^ mask) (by simpa [adjacent] using adj)

@[simp] theorem flip_flip (mask : BitVec n) {K : KColoring n s} :
    (K.flip mask).flip mask = K := by
  ext; simp [flip, BitVec.xor_assoc]


section variable [Decidable P]

def condFlipA (P : Prop) [Decidable P] (d : Fin n) (idx : BitVec n) :=
  if P then idx ^^^ BitVec.oneAt d else idx

@[simp] theorem condFlipA_T (d : Fin n) (idx) :
    P → condFlipA P d idx = idx ^^^ BitVec.oneAt d := by
  unfold condFlipA; simp +contextual

@[simp] theorem condFlipA_F (d : Fin n) (idx) :
    ¬P → condFlipA P d idx = idx := by
  unfold condFlipA; simp +contextual

@[simp] theorem condFlipA_condFlipA (d : Fin n) (idx) :
    condFlipA P d (condFlipA P d idx) = idx := by
  by_cases P <;> simp [*, BitVec.xor_assoc]

theorem condFlipA_getElem (d) (i : BitVec n) (d2 : Fin n) :
    (condFlipA P d i)[d2] = (i[d2] ^^ decide (P ∧ d2 = d)) := by
  by_cases P <;> simp [*, eq_comm, Fin.ext_iff]

end

def condFlipB (d : Fin n) (c : Fin s) (K : KColoring n s) (idx : BitVec n) :=
  condFlipA ((K.data idx)[d] = c) d idx

theorem condFlipB_color_eq (d c) (K : KColoring n s) (i) :
    (K.data (condFlipB d c K i))[d] = (K.data i)[d] := by
  unfold condFlipB condFlipA
  split
  · rw [K.oneAt_eq]
  · rfl

@[simp] theorem condFlipB.Involutive {K : KColoring n s} :
    (condFlipB d c K).Involutive := by
  intro
  rw [condFlipB, condFlipB_color_eq, condFlipB]
  apply condFlipA_condFlipA

@[simp] theorem condFlipB_condFlipB (d c) (K : KColoring n s) (i) :
    condFlipB d c K (condFlipB d c K i) = i := by
  apply condFlipB.Involutive

theorem condFlipB_getElem_inj (d c) (K : KColoring n s) (i₁ i₂) (d2 : Fin n)
    (h : d2 = d → (K.data i₁)[d] = (K.data i₂)[d]) :
    (condFlipB d c K i₁)[d2] = (condFlipB d c K i₂)[d2] ↔ i₁[d2] = i₂[d2] := by
  unfold condFlipB
  simp_rw [condFlipA_getElem]
  if d2 = d then
    subst d2; simp_all
  else
    simp_all


/--
Actually *super* non-obvious that this is an automorphism!!
The justification is basically that if an s gap occurs at d, it still occurs there,
while the colors never change so other inequalities are preserved

I don't think this is an SR clausal symmetry?
This would require something stronger, like fully general substitutions.
-/
def condFlip (d : Fin n) (c : Fin s) (K : KColoring n s) : KColoring n s where
  data i := K.data (condFlipB d c K i)
  same := by
    intro i₁ i₂ ne

    generalize hpi₁ : condFlipB d c K i₁ = pi₁ at *
    generalize hpi₂ : condFlipB d c K i₂ = pi₂ at *
    rw [condFlipB.Involutive.eq_iff] at hpi₁ hpi₂
    subst i₁ i₂

    obtain ⟨d',is_ne,cs_eq⟩ := K.same pi₁ pi₂ (by
      simp_all [condFlipB.Involutive.injective.eq_iff])
    clear ne

    refine ⟨d',?_,cs_eq⟩

    rw [ne_eq, condFlipB_getElem_inj]
    · exact is_ne
    · rintro rfl; cc

  diff := by
    intro i₁ i₂ adj

    generalize hpi₁ : condFlipB d c K i₁ = pi₁ at *
    generalize hpi₂ : condFlipB d c K i₂ = pi₂ at *
    rw [condFlipB.Involutive.eq_iff] at hpi₁ hpi₂
    subst i₁ i₂

    if adjacent pi₁ pi₂ then
      exact K.diff pi₁ pi₂ ‹_›
    else

    have : (K.data pi₁)[d] ≠ (K.data pi₂)[d] := by
      intro h
      by_cases (K.data pi₂)[d] = c <;>
        simp_all [condFlipB, ← adjacent_iff_xors_adjacent]

    use d

theorem condFlip.Involutive {d : Fin n} {c : Fin s} :
    (condFlip d c).Involutive := by
  intro K; ext1; ext1 i; simp [condFlip]
  rw (occs := .pos [2]) [condFlipB]
  rw [condFlipB_color_eq, ← condFlipB, condFlipB_condFlipB]

@[simp] theorem condFlip_condFlip {d c} {K : KColoring n s} :
    (K.condFlip d c).condFlip d c = K :=
  condFlip.Involutive ..

@[simp] theorem flipAt_inj_iff {j k} : condFlip j k a = condFlip j k b ↔ a = b :=
  condFlip.Involutive.injective.eq_iff



def permColors (f : Fin n → Fin s ≃ Fin s) (K : KColoring n s) : KColoring n s where
  data i := Vector.ofFn fun d => (f d) (K.data i)[d]
  same := by
    intro i j ne
    simpa using K.same i j ne
  diff := by
    intro i j adj
    simpa using K.diff i j adj

/-
@[simp] theorem idx_permColors (f) {v : KVertex n s} : (permColors f v).idx = v.idx := rfl

theorem colors_permColors (f) (v : KVertex n s) {j h} :
    (permColors f v).color[j]'h = (f ⟨j,h⟩) v.color[j] := by
  simp [permColors]


theorem permColors_permColors (f₁ f₂ : Fin n → Fin s → Fin s) {v} :
    permColors f₁ (permColors f₂ v) = permColors (fun j => f₁ j ∘ f₂ j) v := by
  simp [permColors]

@[simp] theorem permColors_id {v : KVertex n s} : permColors (fun _ => id) v = v := by
  simp [permColors]
  congr
  ext i hi
  simp
  -/


def permDims (f : Fin n ≃ Fin n) (K : KColoring n s) : KColoring n s where
  data i :=
    let i' := BitVec.ofFn (i[f.symm ·])
    Vector.ofFn fun d => (K.data i')[f d]
  same i j ne := by
    lift_lets; intro i' j'
    replace ne : i' ≠ j' := by
      intro h; apply ne
      ext d hd
      simpa +zetaDelta using congrArg (·[f ⟨d,hd⟩]) h

    obtain ⟨d,is_ne,cs_eq⟩ := K.same i' j' ne
    simp
    use f.symm d, (by simpa +zetaDelta using is_ne)
    simpa using cs_eq
  diff i j adj := by
    lift_lets; intro i' j'
    replace adj : adjacent i' j' := by
      obtain ⟨d,is,cs⟩ := adj
      use f d, (by simpa +zetaDelta using is)
      intro d'; specialize cs (f.symm d')
      simpa +zetaDelta [Equiv.symm_apply_eq] using cs

    obtain ⟨d,diff⟩ := K.diff i' j' adj
    use f.symm d
    simpa using diff

/-
theorem idx_permColumns (f : Fin n → Fin n) (v : KVertex n s) {j hj} :
    (v.permColumns f).idx[j]'hj = v.idx[f ⟨j,hj⟩] := by
  simp [permColumns]

theorem colors_permColumns (f : Fin n → Fin n) (v : KVertex n s) {j hj} :
    (v.permColumns f).color[j]'hj = v.color[f ⟨j,hj⟩] := by
  simp [permColumns]

theorem permColumns_comp (f₁ f₂ : Fin n → Fin n) (v : KVertex n s)
    : permColumns f₁ (permColumns f₂ v) = permColumns (f₂ ∘ f₁) v := by
  simp [permColumns]

@[simp] theorem permColumns_id (v : KVertex n s) : permColumns id v = v := by
  ext <;> simp [permColumns, BitVec.getLsbD_eq_getElem, *]
-/

end KColoring


namespace KAuto

instance : FunLike (KAuto n s) (KColoring n s) (KColoring n s) := by
  unfold KAuto; infer_instance

def id : KAuto n s := Equiv.refl _

def flip (mask : BitVec n) : KAuto n s := {
    toFun   := KColoring.flip mask
    invFun  := KColoring.flip mask
    left_inv  := by intro; simp
    right_inv := by intro; simp
  }

def condFlip (d : Fin n) (c : Fin s) : KAuto n s := {
    toFun   := KColoring.condFlip d c
    invFun  := KColoring.condFlip d c
    left_inv  := by intro; simp
    right_inv := by intro; simp
  }

def permColors (f : Fin n → Fin s ≃ Fin s) : KAuto n s := {
    toFun   := KColoring.permColors f
    invFun  := KColoring.permColors (fun j => (f j).symm)
    left_inv  := by intro; ext; simp [KColoring.permColors]
    right_inv := by intro; ext; simp [KColoring.permColors]
  }

def permDims (f : Fin n ≃ Fin n) : KAuto n s := {
    toFun   := KColoring.permDims f
    invFun  := KColoring.permDims f.symm
    left_inv  := by intro; ext; simp [KColoring.permDims]
    right_inv := by intro; ext; simp [KColoring.permDims]
  }

variable (K : KColoring n s)

@[simp] theorem apply_flip : (flip mask) K = K.flip mask := rfl

@[simp] theorem apply_condFlip : (condFlip d c) K = K.condFlip d c := rfl

@[simp] theorem apply_permColors : (permColors f) K = K.permColors f := rfl

@[simp] theorem apply_permDims : (permDims f) K = K.permDims f := rfl

end KAuto
