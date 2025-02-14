/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Pi

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

theorem Multiset.countP_singleton (p) [DecidablePred p] (x : α) :
      Multiset.countP p {x} = if p x then 1 else 0 := by
  rw [← cons_zero, countP_cons]
  simp

theorem Multiset.countP_eq_succ [DecidableEq α] (p) [DecidablePred p] (xs : Multiset α) :
      xs.countP p = n+1 ↔ ∃ x ∈ xs, p x ∧ (xs.erase x).countP p = n := by
  induction xs using Multiset.induction generalizing n
  · simp
  next hd tl ih =>
  if p_hd : p hd then
    match n with
    | 0 =>
      simp [p_hd]
      intro a ha pa
      rw [erase_cons_tail_of_mem ha]
      simp [p_hd]
    | n+1 =>
      simp [p_hd]
      intro a ha pa h
      rw [ih]
      use a, ha, pa
      rw [erase_cons_tail_of_mem ha] at h
      simpa [p_hd] using h
  else
    simp [p_hd]
    rw [ih]
    apply exists_congr; intro a
    apply and_congr_right; intro ha
    simp [countP_eq_zero, erase_cons_tail_of_mem ha, p_hd]


@[simp] theorem Array.mem_finRange (x : Fin n) : x ∈ Array.finRange n := by
  simp [Array.finRange, mem_def, List.mem_ofFn]

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

def Vector.ext' {v₁ : Vector α n} {v₂ : Vector α n} (h : v₁.toArray = v₂.toArray) : v₁ = v₂ := by
  cases v₁; cases v₂; simp_all

@[simp] theorem Vector.getElem_ofFn (f : Fin n → α) (i : Nat) (h)
  : (Vector.ofFn f)[i]'h = f ⟨i,h⟩ := by
  simp [ofFn]

@[simp] theorem Vector.getElem_cast (h : n = n') (v : Vector α n) (i : Nat) (hi)
  : (Vector.cast h v)[i]'hi = v[i] := by
  cases v; simp [Vector.cast]

@[simp] theorem Vector.getElem_take (v : Vector α n) (n') (i : Nat) (hi)
  : (v.take n')[i]'hi = v[i] := by
  cases v; simp [Vector.take]

instance [Fintype α] : Fintype (Vector α n) where
  elems :=
    (Finset.univ : Finset (Fin n)).pi (fun _ => (Finset.univ : Finset α))
    |>.map ⟨fun f => Vector.ofFn (f · <| Finset.mem_univ _), by
      intro f₁ f₂ h
      simp [Vector.ext_iff] at h
      ext; apply h⟩
  complete := by
    intro x
    simp; use (fun i hi => x[i])
    ext; simp


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

theorem BitVec.eq_of_getElem_eq {v₁ v₂ : BitVec n}
    : (∀ i (hi : i < n), v₁[i] = v₂[i]) → v₁ = v₂ :=
  fun h => BitVec.eq_of_getLsbD_eq (h ↑·)

theorem BitVec.eq_of_getElem_eq_iff {v₁ v₂ : BitVec n}
    : v₁ = v₂ ↔ (∀ i (hi : i < n), v₁[i] = v₂[i]) :=
  ⟨ by rintro rfl; simp
  , BitVec.eq_of_getElem_eq⟩


theorem BitVec.cons_inj (v₁ v₂ : BitVec n) (b₁ b₂) :
  v₁.cons b₁ = v₂.cons b₂ → v₁ = v₂ ∧ b₁ = b₂ := by
  intro h
  rw [BitVec.eq_of_getLsbD_eq_iff] at h
  simp [BitVec.getLsbD_cons] at h
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

@[simp] theorem BitVec.getLsbD_ofFn (f : Fin n → Bool) (i : Nat) (h)
  : (BitVec.ofFn f).getLsbD i = f ⟨i,h⟩ := by
  unfold ofFn
  rw [getLsbD_cast, getLsb_ofBoolListLE]
  simp [h]

@[simp] theorem BitVec.getElem_ofBoolListLE (L : List Bool) (i : Nat) (h : i < L.length)
    : (BitVec.ofBoolListLE L)[i] = L[i] := by
  rw [← getLsbD_eq_getElem, getLsb_ofBoolListLE]
  rw [List.getD_eq_getElem?_getD, List.getElem_eq_getElem?_get]
  rw [Option.get_eq_getD]

attribute [bv_toNat] BitVec.getElem_eq_testBit_toNat

theorem BitVec.getElem_ofNat (n i : Nat) (hj : j < n)
    : (BitVec.ofNat n i)[j] = i.testBit j := by
  simp [bv_toNat, hj]

theorem BitVec.ofNat_eq_of_width_ge (minWidth : Nat) (hwidth : n ≥ minWidth) (hi : i < 2^minWidth)
  : BitVec.ofNat n i = ⟨i, Nat.lt_of_lt_of_le hi (Nat.pow_le_pow_right (by decide) hwidth)⟩ := by
  simp only [bv_toNat]
  rw [Nat.mod_eq_of_lt]
  exact Nat.lt_of_lt_of_le hi (Nat.pow_le_pow_right (by decide) hwidth)

theorem Nat.xor_mod_pow_2 (x y n : Nat) : x % 2^n ^^^ y % 2^n = (x ^^^ y) % 2^n := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases i < n <;> simp [*]

theorem Nat.shiftLeft_mod_pow_2 (x y n : Nat) : x <<< y % 2^n = ((x % 2^(n-y)) <<< y) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Bool.eq_iff_iff]; simp
  rw [← and_assoc, ← and_assoc]
  apply and_congr_left'
  rw [and_comm, and_congr_right_iff]
  simp (config := {contextual := true}) [Nat.sub_lt_sub_iff_right]

@[simp] theorem BitVec.xor_right_inj (x y z : BitVec n) : x ^^^ y = x ^^^ z ↔ y = z := by
  refine ⟨fun h => ?_, by rintro rfl; rfl⟩
  simp [bv_toNat] at h ⊢
  apply Nat.eq_of_testBit_eq; intro i
  replace h := congrArg (·.testBit i) h
  simpa using h

@[simp] theorem BitVec.xor_eq_self_left (x y : BitVec n) : x ^^^ y = x ↔ y = 0#n := by
  rw (occs := .pos [2]) [← BitVec.xor_zero (x := x)]; simp only [BitVec.xor_right_inj]

@[simp] theorem Bool.xor_eq_self_left (x y : Bool) : ((x ^^ y) = x) ↔ (y = false) := by
  rw (occs := .pos [2]) [← Bool.xor_false (x := x)]; simp only [Bool.xor_right_inj]

@[simp] theorem Nat.shiftLeft_pos (x y : Nat) : 0 < x <<< y ↔ 0 < x := by
  simp [Nat.shiftLeft_eq, Nat.mul_pos_iff_of_pos_right, Nat.pow_pos]

@[simp] theorem Nat.shiftLeft_eq_zero (x y : Nat) : x <<< y = 0 ↔ x = 0 := by
  simp [Nat.shiftLeft_eq, Nat.mul_eq_zero, Nat.pow_pos]

theorem Fin.val_eq_iff_lt_and_eq (x : Fin n) (y : Nat) : x.val = y ↔ ∃ (h : y < n), x = ⟨y,h⟩ := by
  rcases x; simp; intro; simp_all

theorem Fin.val_ofNat {n} [NeZero n] (x : Nat) : Fin.val (n := n) (no_index (OfNat.ofNat x)) = x % n := rfl

@[simp] theorem Fin.val_ofNat_of_lt {n} [NeZero n] (x : Nat) (h : x < n) : Fin.val (n := n) (no_index (OfNat.ofNat x)) = x :=
  by rw [Fin.val_ofNat, Nat.mod_eq_of_lt h]

attribute [-simp] lt_add_iff_pos_left

namespace Equiv

def setAll [DecidableEq α] (L : List (α × β)) (f: α ≃ β) : α ≃ β :=
  match L with
  | [] => f
  | (a,b) :: tail => (setAll tail f).setValue a b

theorem setAll_eq_of_mem [DecidableEq α] {L : List (α × β)} {f}
    (is_distinct : L.Pairwise (·.1 ≠ ·.1)) (os_distinct : L.Pairwise (·.2 ≠ ·.2))
    (pair_mem : (i,o) ∈ L) :
    setAll L f i = o := by
  induction L generalizing i o with
  | nil => simp at pair_mem
  | cons hd tl ih =>
    simp at pair_mem
    rcases pair_mem with (rfl|pair_mem)
    case inl => simp [setAll]
    case inr =>
    specialize ih is_distinct.tail os_distinct.tail pair_mem
    replace is_distinct := Ne.symm <| List.rel_of_pairwise_cons is_distinct pair_mem
    replace os_distinct := Ne.symm <| List.rel_of_pairwise_cons os_distinct pair_mem
    clear pair_mem
    rcases hd with ⟨x,y⟩; dsimp at is_distinct os_distinct ⊢
    simp [setAll]; rw [← ih] at os_distinct ⊢
    simp [setValue, swap, swapCore, is_distinct]
    rintro rfl; simp at os_distinct

theorem setValue_neq [DecidableEq α] (f : α ≃ β) (a : α) (b : β) (x : α) :
    x ≠ a → f x ≠ b → setValue f a b x = f x := by
  intros; simp [setValue, swap_apply_def, eq_symm_apply, *]

theorem setAll_eq_of_not_mem [DecidableEq α] {L : List (α × β)} {f}
    (not_mem_is : i ∉ L.map (·.1)) (not_mem_os : f i ∉ L.map (·.2)) :
    setAll L f i = f i := by
  induction L with
  | nil => simp [setAll]
  | cons hd tl ih =>
    simp at not_mem_is not_mem_os
    simp only [setAll]
    specialize ih (by simp [*]) (by simp [*])
    rw [← ih]
    apply setValue_neq
    · exact not_mem_is.1
    · rw [ih]; exact not_mem_os.1

nonrec def Perm.setAll [DecidableEq α] (L : List (α × α)) : α ≃ α :=
  setAll L (Equiv.refl _)

theorem Perm.setAll_eq_of_mem [DecidableEq α] {L : List (α × α)}
    (is_distinct : L.Pairwise (·.1 ≠ ·.1)) (os_distinct : L.Pairwise (·.2 ≠ ·.2))
    (pair_mem : (i,o) ∈ L) :
    setAll L i = o :=
  Equiv.setAll_eq_of_mem is_distinct os_distinct pair_mem

theorem Perm.setAll_eq_of_not_mem [DecidableEq α] {L : List (α × α)}
    (not_mem_is : i ∉ L.map (·.1)) (not_mem_os : i ∉ L.map (·.2)) :
    setAll L i = i :=
  Equiv.setAll_eq_of_not_mem not_mem_is not_mem_os

end Equiv
