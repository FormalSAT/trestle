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
