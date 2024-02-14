/-
Copyright (c) 2024 The LeanSAT Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: Wojciech Nawrocki
-/

import LeanSAT.Data.Cnf
import LeanSAT.Upstream.ToStd

namespace LeanSAT

/-! Defines (non-zero) integer literals
over (non-zero) natural number variables
and proves that they are lawful. -/

/-! ### Variables -/

abbrev IVar := PNat

namespace IVar

instance : ToString IVar where
  toString x := toString x.val

instance : Hashable IVar where
  hash v := hash v.val

instance : Ord IVar where
  compare a b := compare a.val b.val

end IVar

/-! ### Literals -/

def ILit := { i : Int // i ≠ 0 }
  deriving DecidableEq, Repr

instance : LitVar ILit IVar where
  negate l := ⟨-l.val, Int.neg_ne_zero.mpr l.property⟩
  mkPos x := ⟨Int.ofNat x.val, by simp⟩
  mkNeg x := ⟨-Int.ofNat x.val, by simp⟩
  toVar l := ⟨Int.natAbs l.val, Int.natAbs_pos.mpr l.property⟩
  polarity l := (0 : Int) < l.val

open LitVar in
theorem polarity_eq {l₁ l₂ : ILit} :
    polarity l₁ = polarity l₂ ↔ ((0 : Int) < l₁.val ↔ (0 : Int) < l₂.val) := by
  simp [polarity]

open LitVar in
instance : LawfulLitVar ILit IVar where
  toVar_negate l := by
    apply Subtype.ext
    apply Int.natAbs_neg
  toVar_mkPos x :=
    Subtype.ext (Int.natAbs_ofNat x.val)
  toVar_mkNeg x := by
    apply Subtype.ext
    simp [toVar, mkNeg]
    rfl
  polarity_negate l := by
    rw [Bool.eq_bnot, polarity_eq]
    intro hEq
    exact l.property (Int.eq_zero_of_lt_neg_iff_lt _ hEq)
  polarity_mkPos l := by
    simp [polarity, mkPos]
  polarity_mkNeg l := by
    simp [polarity, mkNeg]
  ext l₁ l₂ := by
    /- Strip type alias. -/
    suffices ∀ {l₁ l₂ : Int}, l₁.natAbs = l₂.natAbs → (0 < l₁ ↔ 0 < l₂) → l₁ = l₂ by
      intro h₁ h₂
      apply Subtype.ext
      apply this
      . exact Subtype.mk_eq_mk.mp h₁
      . exact polarity_eq.mp h₂
    intro l₁ l₂ h₁ h₂
    cases Int.natAbs_eq_natAbs_iff.mp h₁
    . assumption
    next h =>
      rw [h] at h₂
      have : l₂ = 0 := Int.eq_zero_of_lt_neg_iff_lt l₂ h₂
      simp [this, h]

abbrev IClause := Clause ILit
abbrev ICnf := Cnf ILit

/-- Find the max variable in the CNF. WARNING: very expensive; result not cached. -/
def ICnf.maxVar (fml : ICnf) : Nat :=
  fml.maxBy (·.maxBy (LitVar.toVar · |>.val) |>.getD 0) |>.getD 0
