/-
Copyright (c) 2024 The LeanSAT Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice

import LeanSAT.Model.PropFun
import LeanSAT.Model.PropForm

namespace LeanSAT.Model

/-! # Propositional Predicates

This file defines the type of arbitrary predicates over `PropAssignment ν`.
This allows us to use arbitrary Lean `Prop` constructs like `∀` and `∃`.
-/

abbrev PropPred (ν) := PropAssignment ν → Prop

namespace PropPred

instance : Coe (PropFun ν) (PropPred ν) := ⟨fun F τ => open PropFun in τ ⊨ F⟩

instance : BooleanAlgebra (PropPred ν) :=
  inferInstanceAs (BooleanAlgebra (PropAssignment ν → Prop))

scoped instance : SemanticEntails (PropAssignment ν) (PropPred ν) := ⟨(· |> ·)⟩

@[simp]
theorem satisfies_def (τ : PropAssignment ν) (f) : (τ ⊨ f) ↔ f τ := by rfl
