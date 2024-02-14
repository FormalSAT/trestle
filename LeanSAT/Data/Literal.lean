/-
Copyright (c) 2024 The LeanSAT Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import LeanSAT.Data.Cnf

namespace LeanSAT

structure Literal (ν : Type u) : Type u where
  toVar : ν
  polarity : Bool

namespace Literal

instance : LitVar (Literal ν) ν where
  mkPos := fun v => ⟨v,true⟩
  mkNeg := fun v => ⟨v,false⟩
  negate := fun ⟨v,p⟩ => ⟨v,!p⟩
  toVar := toVar
  polarity := polarity

instance : LawfulLitVar (Literal ν) ν where
  toVar_negate := by aesop
  toVar_mkPos := by aesop
  toVar_mkNeg := by aesop
  polarity_negate := by aesop
  polarity_mkPos := by aesop
  polarity_mkNeg := by aesop
  ext := by intro l1 l2; cases l1; cases l2; aesop

abbrev pos : ν → Literal ν := (.mk · true)
abbrev neg : ν → Literal ν := (.mk · false)
