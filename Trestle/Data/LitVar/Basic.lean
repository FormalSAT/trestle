/-
Copyright (c) 2025 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Trestle.Upstream.ToStd
import Trestle.Upstream.ToMathlib
import Trestle.Data.LitVar.Defs
import Trestle.Model.Subst

/-!

  Basic theorems about literals and variables.

-/

namespace Trestle

open Model

namespace LitVar

variable {L : Type u} {ν : Type v} [LitVar L ν]

def toPropForm (l : L) : PropForm ν :=
  if polarity l then .var (toVar l) else .neg (.var $ toVar l)

instance : CoeHead L (PropForm ν) := ⟨toPropForm⟩

def toPropFun (l : L) : PropFun ν :=
  if polarity l then .var (toVar l) else (.var $ toVar l)ᶜ

instance : CoeHead L (PropFun ν) := ⟨toPropFun⟩

open PropFun in
theorem satisfies_iff {τ : PropAssignment ν} {l : L} :
    τ ⊨ toPropFun l ↔ τ (toVar l) = polarity l := by
  dsimp [toPropFun, polarity]
  aesop

-- Some theorems can be proven on `LitVar`s, without the `Lawful` laws.

@[simp]
theorem mk_toPropForm (l : L) : ⟦toPropForm l⟧ = toPropFun l := by
  dsimp [toPropForm, toPropFun]
  cases polarity l <;> simp

@[simp]
theorem vars_toPropForm [DecidableEq ν] (l : L) : (toPropForm l).vars = {toVar l} := by
  dsimp [toPropForm]
  cases polarity l <;> simp [PropForm.vars]

@[simp]
theorem semVars_toPropFun [DecidableEq ν] (l : L) : (toPropFun l).semVars = {toVar l} := by
  dsimp [toPropFun]
  cases polarity l <;> simp

-- The rest of the theorems need the laws

variable [LawfulLitVar L ν]

open LawfulLitVar

@[simp] theorem var_mkLit (x : ν) (p : Bool) : toVar (mkLit L x p) = x := by
  dsimp [mkLit]; split <;> simp
@[simp] theorem polarity_mkLit (x : ν) (p : Bool) : polarity (mkLit L x p) = p := by
  dsimp [mkLit]; split <;> simp_all

@[simp] theorem eta (l : L) : mkLit L (toVar l) (polarity l) = l := by
  ext <;> simp
@[simp] theorem eta_neg (l : L) : mkLit L (toVar l) (!polarity l) = -l := by
  ext <;> simp

theorem mkPos_or_mkNeg (l : L) : l = mkPos (toVar l) ∨ l = mkNeg (toVar l) := by
  rw [← eta l]
  cases polarity l
  . apply Or.inr
    simp [mkLit]
  . apply Or.inl
    simp [mkLit]

-- CC: For better `rcases (... rfl)` patterns
theorem exists_mkPos_or_mkNeg (l : L) : ∃ v, l = mkPos v ∨ l = mkNeg v := by
  use toVar l
  rcases mkPos_or_mkNeg l with (h | h)
  · exact Or.inl h
  · exact Or.inr h

@[simp]
theorem mkPos_ne_mkNeg {v₁ v₂ : ν} : mkPos (L := L) v₁ ≠ mkNeg (L := L) v₂ := by
  intro h_con
  have := LawfulLitVar.ext_iff.mp h_con
  simp at this

@[simp]
theorem mkNeg_ne_mkPos {v₁ v₂ : ν} : mkNeg (L := L) v₁ ≠ mkPos (L := L) v₂ :=
  Ne.symm (@mkPos_ne_mkNeg _ _ _ _ v₂ v₁)

-- CC: Could also use `Function.Injective`
@[simp]
theorem mkPos_inj {x y : ν} : mkPos (L := L) x = mkPos (L := L) y ↔ x = y := by
  constructor
  · intro h
    rcases LawfulLitVar.ext_iff.mp h with ⟨h, _⟩
    simp at h
    exact h
  · rintro rfl
    rfl

@[simp]
theorem mkNeg_inj {x y : ν} : mkNeg (L := L) x = mkNeg (L := L) y ↔ x = y := by
  constructor
  · intro h
    rcases LawfulLitVar.ext_iff.mp h with ⟨h, _⟩
    simp at h
    exact h
  · rintro rfl
    rfl

@[simp] theorem toPropForm_mkPos (x : ν) : toPropForm (mkPos (L := L) x) = .var x := by
  simp [toPropForm]
@[simp] theorem toPropForm_mkNeg (x : ν) : toPropForm (mkNeg (L := L) x) = .neg (.var x) := by
  simp [toPropForm]

@[simp] theorem toPropFun_mkPos (x : ν) : toPropFun (mkPos (L := L) x) = .var x := by
  simp [toPropFun]
@[simp] theorem toPropFun_mkNeg (x : ν) : toPropFun (mkNeg (L := L) x) = (.var x)ᶜ := by
  simp [toPropFun]
@[simp] theorem toPropFun_mkLit_true : toPropFun (mkLit L v true) = .var v := by
  simp [toPropFun]
@[simp] theorem toPropFun_mkLit_false : toPropFun (mkLit L v false) = (.var v)ᶜ := by
  simp [toPropFun]
@[simp] theorem toPropFun_neg (l : L) : toPropFun (-l) = (toPropFun l)ᶜ := by
  dsimp [toPropFun]
  aesop

-- CC: This theorem already exists in the `LawfulLitVar` namespace
--     due to `attribute [ext]`
theorem ext_iff (l1 l2 : L) : l1 = l2 ↔ toVar l1 = toVar l2 ∧ polarity l1 = polarity l2 := by
  constructor
  · rintro rfl; simp
  · aesop

@[simp] theorem neg_eq_neg (l1 l2 : L) : -l1 = -l2 ↔ l1 = l2 := by
  constructor
  · rw [ext_iff, ext_iff (L := L)]; simp
  · rintro rfl; rfl

@[simp] theorem neg_neg (l : L) : - (- l) = l := by
  rw [ext_iff]; simp

@[simp] theorem neg_mkPos (x : ν) : - (mkPos (L := L) x) = mkNeg x := by
  rw [ext_iff]; simp

@[simp] theorem neg_mkNeg (x : ν) : - (mkNeg (L := L) x) = mkPos x := by
  rw [ext_iff]; simp

theorem neg_eq_iff_eq_neg {x y : L} : -x = y ↔ x = -y := by
  constructor
  all_goals
  ( intro h
    have := congrArg (-·) h
    simp only [neg_neg] at this
    exact this )

-- CC: Have a simp attribute here?
theorem toVar_eq_iff {l₁ l₂ : L} : toVar l₁ = toVar l₂ ↔ (l₁ = l₂ ∨ l₁ = -l₂) := by
  rcases exists_mkPos_or_mkNeg l₁ with ⟨v₁, (rfl | rfl)⟩
  <;> rcases exists_mkPos_or_mkNeg l₂ with ⟨v₂, (rfl | rfl)⟩
  <;> simp

theorem toVar_eq_iff' {l₁ l₂ : L} : toVar l₁ = toVar l₂ ↔ (l₁ = l₂ ∨ -l₁ = l₂) := by
  rcases exists_mkPos_or_mkNeg l₁ with ⟨v₁, (rfl | rfl)⟩
  <;> rcases exists_mkPos_or_mkNeg l₂ with ⟨v₂, (rfl | rfl)⟩
  <;> simp

open PropFun

theorem satisfies_neg {τ : PropAssignment ν} {l : L} :
    τ ⊨ toPropFun (-l) ↔ τ ⊭ toPropFun l := by
  simp [satisfies_iff]

omit [LawfulLitVar L ν] in
theorem satisfies_set [DecidableEq ν] (τ : PropAssignment ν) (l : L) :
    τ.set (toVar l) (polarity l) ⊨ toPropFun l := by
  simp [satisfies_iff, τ.set_get]

theorem eq_of_flip [DecidableEq ν] {τ : PropAssignment ν} {l : L} {x : ν} {p : Bool} :
    τ ⊭ toPropFun l → τ.set x p ⊨ toPropFun l → l = mkLit L x p := by
  simp only [satisfies_iff]
  intro h hSet
  by_cases hEq : x = toVar l
  . rw [hEq, τ.set_get] at hSet
    simp [hSet, hEq]
  . exfalso; exact h (τ.set_get_of_ne p hEq ▸ hSet)

theorem eq_of_flip' [DecidableEq ν] {τ : PropAssignment ν} {l : L} {x : ν} {p : Bool} :
    τ ⊨ toPropFun l → τ.set x p ⊭ toPropFun l → l = mkLit L x !p := by
  simp only [satisfies_iff]
  intro h hSet
  by_cases hEq : x = toVar l
  . rw [hEq, τ.set_get] at hSet
    have : (!p) = polarity l := by
      simp [Bool.eq_bnot, hSet]
    simp [hEq, this]
  . exfalso; exact hSet (τ.set_get_of_ne p hEq ▸ h)

theorem toPropFun.inj [DecidableEq ν] : (toPropFun (L := L)).Injective := by
  intro l₁ l₂ h; simp [toPropFun] at h
  split_ifs at h
  · rename_i h₁ h₂
    rw [var_eq_var] at h
    apply LawfulLitVar.ext _ _ h
    rw [h₁, h₂]
  · simp only [var_ne_var_compl] at h
  · simp only [var_compl_ne_var] at h
  · rename_i h₁ h₂
    simp only [Bool.not_eq_true] at h₁ h₂
    simp only [compl_inj_iff, var_eq_var] at h
    apply LawfulLitVar.ext _ _ h
    rw [h₁, h₂]

/-! #### map -/

@[simp]
theorem satisfies_map [LitVar L V] [LitVar L' V']
    [LawfulLitVar L' V'] (f : V → V') (l : L) (τ : PropAssignment V')
  : τ ⊨ LitVar.toPropFun (LitVar.map f l : L') ↔ τ.map f ⊨ LitVar.toPropFun l
  := by
  simp [map, toPropFun]
  split <;> simp

@[simp]
theorem toPropFun_map [LitVar L V] [LitVar L' V'] [LawfulLitVar L' V'] (f : V → V') (l : L)
    : LitVar.toPropFun (LitVar.map f l : L') = (LitVar.toPropFun l).map f := by
  ext τ; simp


/-! #### Sums as valid literals -/

section
variable [LitVar L1 V1] [LitVar L2 V2]

instance [LawfulLitVar L1 V1] [LawfulLitVar L2 V2]
    : LawfulLitVar (L1 ⊕ L2) (V1 ⊕ V2) where
  toVar_mkPos     := by rintro (_ | _) <;> simp [toVar, mkPos]
  toVar_mkNeg     := by rintro (_ | _) <;> simp [toVar, mkNeg]
  toVar_negate    := by rintro (_ | _) <;> simp_rw [Neg.neg, negate] <;> simp [toVar]
  polarity_mkPos  := by rintro (_ | _) <;> simp [polarity, mkPos]
  polarity_mkNeg  := by rintro (_ | _) <;> simp [polarity, mkNeg]
  polarity_negate := by rintro (_ | _) <;> simp_rw [Neg.neg, negate] <;> simp [polarity]
  ext := by
    rintro (l₁ | l₁) (l₂ | l₂)
    <;> rcases mkPos_or_mkNeg l₁ with (h₁ | h₁)
    <;> rcases mkPos_or_mkNeg l₂ with (h₂ | h₂)
    all_goals (
      rw [h₁, h₂]
      simp [toVar, polarity]
      try intro h
      try rw [h]
    )

@[simp] theorem polarity_inl (l : L1)
  : polarity (L := L1 ⊕ L2) (ν := V1 ⊕ V2) (Sum.inl l) = polarity l := rfl

@[simp] theorem polarity_inr (l : L2)
  : polarity (L := L1 ⊕ L2) (ν := V1 ⊕ V2) (Sum.inr l) = polarity l := rfl

@[simp] theorem toVar_inl (l : L1)
  : toVar (L := L1 ⊕ L2) (ν := V1 ⊕ V2) (Sum.inl l) = .inl (toVar l) := rfl

@[simp] theorem toVar_inr (l : L2)
  : toVar (L := L1 ⊕ L2) (ν := V1 ⊕ V2) (Sum.inr l) = .inr (toVar l) := rfl
end

end LitVar

end Trestle
