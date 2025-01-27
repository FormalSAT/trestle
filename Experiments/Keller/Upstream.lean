/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

def Fin.any (n : Nat) (P : Fin n → Bool) : Bool :=
  aux 0
where aux (i) :=
  if h : i < n then
    if P ⟨i,h⟩ then true
    else aux (i+1)
  else
    false

theorem Fin.any_iff_exists {n} {P} : Fin.any n P = true ↔ ∃ i, P i :=
  aux 0 (by simp)
where
  aux (i : Nat) (hprev : ∀ i' : Fin n, i' < i → ¬(P i')) : Fin.any.aux n P i = true ↔ ∃ i, P i :=
  by
    if hi : i < n then
      unfold Fin.any.aux; simp [hi]
      if h : P ⟨i,hi⟩ then
        simp [h]; refine ⟨⟨i,hi⟩,h⟩
      else
        simp [h]
        apply aux (i+1)
        intro i' hi'
        if i' = i then
          subst i; exact h
        else
          apply hprev; omega
    else
      unfold Fin.any.aux; simp [hi]
      intro x; specialize hprev x; simp at hprev; apply hprev
      omega

instance {P : Fin n → Prop} [DecidablePred P] : Decidable (∃ i : Fin n, P i) := by
  have : Decidable (Fin.any n (decide <| P ·)) := inferInstance
  rw [Fin.any_iff_exists] at this
  simpa using this

@[simp] theorem Vector.getElem_mk (A : Array α) (h : A.size = n) (i : Nat) (h2) :
    (Vector.mk A h)[i]'h2 = A[i] := rfl

@[ext]
def Vector.ext {v₁ : Vector α n} {v₂ : Vector α n}
    (h : ∀ (i : Nat) (h : i < n), v₁[i] = v₂[i]) : v₁ = v₂ := by
  rcases v₁ with ⟨v₁⟩; rcases v₂ with ⟨v₂⟩
  simp [Vector.cast] at h ⊢
  ext i
  · omega
  apply h i; omega

@[simp] theorem Vector.getElem_ofFn (f : Fin n → α) (i : Nat) (h)
  : (Vector.ofFn f)[i]'h = f ⟨i,h⟩ := by
  simp [ofFn]

@[simp] theorem Vector.getElem_cast (h : n = n') (v : Vector α n) (i : Nat) (hi)
  : (Vector.cast h v)[i]'hi = v[i] := by
  cases v; simp [Vector.cast]

@[simp] theorem Vector.getElem_take (v : Vector α n) (n') (i : Nat) (hi)
  : (v.take n')[i]'hi = v[i] := by
  cases v; simp [Vector.take]

def BitVec.equiv_fin (n) : BitVec n ≃ Fin (2^n) := {
    toFun := BitVec.toFin
    invFun := BitVec.ofFin
    left_inv := by intro; simp
    right_inv := by intro; simp
  }

instance : Fintype (BitVec n) :=
  Fintype.ofEquiv (Fin (2^n)) (BitVec.equiv_fin n).symm

@[simp] theorem BitVec.card (n) : Fintype.card (BitVec n) = 2^n := by
  rw [← Fintype.card_fin (n := 2^n)]
  apply Fintype.card_congr; apply BitVec.equiv_fin

@[simp] theorem BitVec.cast_inj (v₁ v₂ : BitVec n) (h₁ h₂ : n = n')
  : v₁.cast h₁ = v₂.cast h₂ ↔ v₁ = v₂ := by
  simp [BitVec.cast, BitVec.ofNatLt, BitVec.toNat_eq]

@[ext]
theorem BitVec.ext {v₁ v₂ : BitVec n}
    : (∀ i (hi : i < n), v₁[i] = v₂[i]) → v₁ = v₂ := by
  intro h
  apply BitVec.eq_of_getLsbD_eq_iff.mpr fun i => h (↑i) i.isLt


theorem BitVec.cons_inj (v₁ v₂ : BitVec n) (b₁ b₂) :
  v₁.cons b₁ = v₂.cons b₂ → v₁ = v₂ ∧ b₁ = b₂ := by
  intro h
  rw [BitVec.ext_iff] at h
  simp [BitVec.getElem_cons] at h
  constructor
  · ext i hi; specialize h i (by omega)
    simp [Nat.ne_of_lt hi] at h
    exact h
  · specialize h n (by omega); simpa using h

@[simp] theorem BitVec.cons_inj_iff (v₁ v₂ : BitVec n) (b₁ b₂) :
  v₁.cons b₁ = v₂.cons b₂ ↔ v₁ = v₂ ∧ b₁ = b₂ := by
  constructor
  · apply cons_inj
  · rintro ⟨rfl,rfl⟩; rfl

def BitVec.ofFn (f : Fin n → Bool) : BitVec n :=
  .cast (by simp) <| .ofBoolListLE (List.ofFn f)

@[simp] theorem BitVec.getElem_ofFn (f : Fin n → Bool) (i : Nat) (h)
  : (BitVec.ofFn f)[i]'h = f ⟨i,h⟩ := by
  unfold ofFn
  rw [getElem_cast, ← getLsbD_eq_getElem, getLsb_ofBoolListLE]
  simp [h]

section insert_mapping
variable [DecidableEq α] [DecidableEq β] (a : α) (b : β)
/-- Assuming `a ↦ f a` and `f⁻¹ b ↦ b` in `f`, this function maps
`a ↦ b` and `f⁻¹ b ↦ f a`. All other mappings are untouched.
This preserves bijectivity of `f`, if it had it. -/
def Function.insert_mapping (f : α → β) : α → β :=
  let old_ret := f a
  fun x => if x = a then b else
    let fx := f x
    if fx = b then old_ret else fx

@[simp] theorem Function.insert_mapping_left (f : α → β) : (insert_mapping a b f) a = b
  := by simp [insert_mapping]

theorem Function.insert_mapping_right (f : α → β) (h : f x = b):
    (Function.insert_mapping a b f) x = f a
  := by simp [insert_mapping, h]; rintro rfl; exact h.symm

theorem Function.insert_mapping_unchanged (f : α → β) (h₁ : x ≠ a) (h₂ : f x ≠ b):
    (Function.insert_mapping a b f) x = f x
  := by simp [insert_mapping]; aesop

/-- Assuming `a ↦ f a` and `f⁻¹ b ↦ b` in `f`, this function maps
`a ↦ b` and `f⁻¹ b ↦ f a`. All other mappings are untouched. -/
def Equiv.insert [DecidableEq α] [DecidableEq β] (a : α) (b : β) (f : α ≃ β) : α ≃ β := {
  toFun := Function.insert_mapping a b f.toFun
  invFun := Function.insert_mapping b a f.invFun
  left_inv := by
    intro x; simp [Function.insert_mapping]
    if ha : x = a then
      simp [ha]
    else
      simp [ha]
      if hb : f x = b then
        simp [← hb]
      else
        simp [hb, ha]
  right_inv := by
    intro x; simp [Function.insert_mapping]
    if ha : x = b then
      simp [ha]
    else
      simp [ha]
      if hb : f.symm x = a then
        simp [← hb]
      else
        simp [hb, ha]
}

@[simp] theorem Equiv.insert_left (f : α ≃ β) : (insert a b f) a = b
  := by simp [insert]

theorem Equiv.insert_right (f : α ≃ β) : (f x = b) → (insert a b f) x = f a
  := by intro; simp [insert]; rw [Function.insert_mapping_right a b f]; assumption

theorem Equiv.insert_unchanged (f : α ≃ β) : x ≠ a → (f x ≠ b) → (insert a b f) x = f x
  := by
    intros; simp [insert]
    rw [Function.insert_mapping_unchanged a b f] <;> assumption

end insert_mapping
