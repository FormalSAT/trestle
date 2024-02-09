import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.Linarith

/-- Intended to clash with Mathlib's FinEnum -/
class FinEnum (α : Type u) where
  card : Nat
  toEqv : α ≃ Fin card

namespace FinEnum

def prodNEZero (n m) (hm : m > 0) (f : α ≃ Fin n) (g : β ≃ Fin m) : (α × β) ≃ Fin (n * m) where
  toFun := fun (a,b) =>
    let ⟨a,ha⟩ := f a
    let ⟨b,hb⟩ := g b
    ⟨ a * m + b, by
      simp [Nat.lt_iff_add_one_le] at *
      calc
        _ ≤ a * m + m := Nat.add_le_add_left hb _
        _ = (a + 1) * m := by simp [Nat.add_mul]
        _ ≤ n * m := Nat.mul_le_mul_right _ ha
      ⟩
  invFun := fun ⟨x,hx⟩ =>
    let a := ⟨x / m, by
      calc
        _ < (n * m) / m := Nat.div_lt_div_of_lt_of_dvd (Nat.dvd_mul_left m n) hx
        _ = _ := Nat.mul_div_cancel _ hm
      ⟩
    let b := ⟨x % m, Nat.mod_lt x hm⟩
    (f.symm a, g.symm b)
  left_inv := by
    rintro ⟨a,b⟩
    simp [Equiv.symm_apply_eq, Fin.eq_iff_veq]
    generalize f a = fa; generalize g b = gb
    rcases fa with ⟨fa,ha⟩; rcases gb with ⟨gb,hb⟩
    simp [hm, hb, Nat.add_div, Nat.add_mod
          , Nat.mod_eq_of_lt hb, (Nat.div_eq_zero_iff hm).mpr]
  right_inv := by
    rintro ⟨x,hx⟩
    simp; exact Nat.div_add_mod' x m


instance prod [FinEnum α] [FinEnum β] : FinEnum (α × β) where
  card := card α * card β
  toEqv :=
    if h : card β > 0 then
      prodNEZero (card α) (card β) h toEqv toEqv
    else
      have : card β = 0 := Nat.eq_zero_of_not_pos h
      have : IsEmpty β := by
        apply Equiv.isEmpty (this ▸ toEqv)
      have : IsEmpty (Fin (card α * card β)) := by
        simp [*]
        apply Fin.isEmpty
      Equiv.equivOfIsEmpty _ _

instance sum [FinEnum α] [FinEnum β] : FinEnum (α ⊕ β) where
  card := card α + card β
  toEqv := {
    toFun := fun
      | .inl a => Fin.castAdd _ (toEqv a)
      | .inr b => Fin.natAdd _ (toEqv b)
    invFun := fun ⟨x,h⟩ =>
      if h' : x < card α then
        .inl <| toEqv.symm ⟨x,h'⟩
      else
        have : x - card α < card β := by
          simp at h'
          exact Nat.sub_lt_left_of_lt_add h' h
        .inr <| toEqv.symm ⟨x - card α, this⟩
    left_inv := by rintro (a|b) <;> simp
    right_inv := by rintro ⟨x,h⟩; aesop
  }