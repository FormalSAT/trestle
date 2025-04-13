/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Trestle.Data.LitVar.Defs

-- Included by `Trestle.Data.Cnf`

namespace Trestle

structure Literal (ν : Type u) : Type u where
  toVar : ν
  polarity : Bool
deriving Repr, DecidableEq, Inhabited

namespace Literal

instance : LitVar (Literal ν) ν where
  mkPos := fun v => ⟨v,true⟩
  mkNeg := fun v => ⟨v,false⟩
  negate := fun ⟨v,p⟩ => ⟨v,!p⟩
  toVar := toVar
  polarity := polarity

instance : LawfulLitVar (Literal ν) ν where
  toVar_negate := by intro _; simp only [Neg.neg, LitVar.negate, LitVar.toVar]
  toVar_mkPos := by simp [LitVar.mkPos, LitVar.toVar]
  toVar_mkNeg := by simp [LitVar.mkNeg, LitVar.toVar]
  polarity_negate := by intro _; simp only [Neg.neg, LitVar.negate, LitVar.polarity]
  polarity_mkPos := by simp [LitVar.mkPos, LitVar.polarity]
  polarity_mkNeg := by simp [LitVar.mkNeg, LitVar.polarity]
  ext := by
    intro l1 l2; cases l1; cases l2;
    simp [LitVar.toVar, LitVar.polarity]
    rintro rfl rfl
    exact ⟨rfl, rfl⟩

@[simp] abbrev pos : ν → Literal ν := LitVar.mkPos
@[simp] abbrev neg : ν → Literal ν := LitVar.mkNeg
