/-
Copyright (c) 2025 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Trestle.Model.PropFun
import Trestle.Data.Cnf.Basic
import Trestle.Upstream.ToStd
import Trestle.Data.ICnf.Defs
import Trestle.Data.LitVar.Basic

import Mathlib.Data.PNat.Basic

namespace Trestle

open Model LitVar

namespace IVar

def toPropFun (v : IVar) : PropFun IVar := .var v
instance : Coe IVar (PropFun IVar) := ⟨toPropFun⟩

theorem eq_PNat : IVar = PNat := rfl

@[simp] theorem ne_zero (v : IVar) : v.val ≠ 0 := PNat.ne_zero _
@[simp] theorem pos (v : IVar) : 0 < v.val := PNat.pos _

def natPred : IVar → Nat := PNat.natPred
@[simp] theorem natPred_inj {m n : IVar} : m.natPred = n.natPred ↔ m = n :=
  PNat.natPred_inj

-- CC: Easy target for golfing.
-- CC: Alternatively, `index` is injective/surjective?
@[simp]
theorem index_eq_iff {v₁ v₂ : IVar} : v₁.index = v₂.index ↔ v₁ = v₂ := by
  have ⟨v₁, h₁⟩ := v₁
  have ⟨v₂, h₂⟩ := v₂
  simp [index]
  constructor
  · intro h
    have : (v₁ - 1) + 1 = (v₂ - 1) + 1 := by rw [h]
    rw [Nat.sub_add_cancel (Nat.succ_le_of_lt h₁)] at this
    rw [Nat.sub_add_cancel (Nat.succ_le_of_lt h₂)] at this
    subst_vars
    rfl
  · intro h
    injection h
    subst_vars
    rfl

@[simp]
theorem index_ne_iff {v₁ v₂ : IVar} : v₁.index ≠ v₂.index ↔ v₁ ≠ v₂ := by
  simp only [ne_eq, index_eq_iff]

@[simp]
theorem toPosILit_negate (v : IVar) : -(v.toPosILit) = v.toNegILit :=
  rfl

@[simp]
theorem toNegILit_negate (v : IVar) : -(v.toNegILit) = v.toPosILit := by
  have ⟨n, hn⟩ := v
  simp [toNegILit, toPosILit]
  simp only [Neg.neg, Int.neg, negate, Int.negOfNat]
  split
  · contradiction
  · simp

end IVar

--------------------------------------------------------------------------------

namespace ILit

@[simp]
theorem toIVar_negate (l : ILit) : (-l).toIVar = l.toIVar := by
  simp [toIVar]; rfl

@[simp]
theorem toIVar_mkPos (v : IVar) : ILit.toIVar (mkPos v) = v := by
  simp [toIVar]

@[simp]
theorem toIVar_mkNeg (v : IVar) : ILit.toIVar (mkNeg v) = v := by
  simp [toIVar]

@[simp] abbrev toPropFun (l : ILit) := LitVar.toPropFun l
instance instCoeILit : Coe ILit (PropFun IVar) := ⟨LitVar.toPropFun⟩

theorem exists_succ_toVar (l : ILit) : ∃ n, (toVar l).val = n + 1 := by
  exact Nat.exists_eq_add_of_le' (toVar l).property

@[simp]
theorem toVar_index (l : ILit) : (toVar l).index = l.index := by
  rfl

@[simp]
theorem index_mkPos (v : IVar) : ILit.index (mkPos v) = v.index := by
  simp [index, mkPos, IVar.index]

@[simp]
theorem index_mkNeg (v : IVar) : ILit.index (mkNeg v) = v.index := by
  simp [index, mkNeg, IVar.index]

@[simp]
theorem index_negate (l : ILit) : ILit.index (-l) = l.index := by
  conv => lhs; rw [← toVar_index]
  simp only [LawfulLitVar.toVar_negate, toVar_index]

theorem index_eq_iff_toVar_eq {l₁ l₂ : ILit} : l₁.index = l₂.index ↔ (toVar l₁) = (toVar l₂) := by
  rcases exists_mkPos_or_mkNeg l₁ with ⟨v₁, (rfl | rfl)⟩
  <;> rcases exists_mkPos_or_mkNeg l₂ with ⟨v₂, (rfl | rfl)⟩
  <;> simp

theorem index_ne_of_var_ne {l₁ l₂ : ILit} : (toVar l₁) ≠ (toVar l₂) → l₁.index ≠ l₂.index := by
  intro h_ne h_con
  exact absurd (index_eq_iff_toVar_eq.mp h_con) h_ne

theorem index_eq_iff_eq_or_negate_eq {l₁ l₂ : ILit} : l₁.index = l₂.index ↔ l₁ = l₂ ∨ -l₁ = l₂ := by
  rw [index_eq_iff_toVar_eq]
  exact toVar_eq_iff'

end ILit

end Trestle
