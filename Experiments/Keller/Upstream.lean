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
  apply h i <;> omega

@[simp] theorem Vector.getElem_ofFn (f : Fin n → α) (i : Nat) (h)
  : (Vector.ofFn f)[i]'h = f ⟨i,h⟩ := by
  simp [ofFn]
