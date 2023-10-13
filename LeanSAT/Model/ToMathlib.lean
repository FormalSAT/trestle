/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

/-! Stuff that seems like it should be in std or mathlib. -/

/-! Std.Logic or Std.Bool? -/

@[simp] theorem Bool.bnot_eq_bnot (a b : Bool) :
  ((!a) = !b) = (a = b) := by cases a <;> cases b <;> decide
@[simp] theorem Bool.eq_true_iff_eq_true_to_eq (a b : Bool) :
  (a = true ↔ b = true) = (a = b) := by cases a <;> cases b <;> decide
@[simp] theorem Bool.eq_false_iff_eq_false_to_eq (a b : Bool) :
  (a = false ↔ b = false) = (a = b) := by cases a <;> cases b <;> decide

/-- Notation typeclass for semantic entailment `⊨`. -/
class SemanticEntails (α : Type u) (β : outParam $ Type v) where
  entails : α → β → Prop

infix:51 " ⊨ " => SemanticEntails.entails
infix:51 " ⊭ " => fun M φ => ¬(M ⊨ φ)