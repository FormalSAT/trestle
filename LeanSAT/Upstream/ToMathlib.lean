/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Mathlib.Tactic.Linarith

/-! Stuff that seems like it should be in std or mathlib. -/

/-! Std.Logic or Std.Bool? -/

@[simp] theorem Bool.bnot_eq_bnot (a b : Bool) :
  ((!a) = !b) ↔ (a = b) := by cases a <;> cases b <;> decide
@[simp] theorem Bool.eq_true_iff_eq_true (a b : Bool) :
  (a = true ↔ b = true) ↔ (a = b) := by cases a <;> cases b <;> decide
@[simp] theorem Bool.eq_false_iff_eq_false (a b : Bool) :
  (a = false ↔ b = false) ↔ (a = b) := by cases a <;> cases b <;> decide

theorem Bool.bnot_eq (a b : Bool) :
  ((!a) = b) ↔ ¬(a = b) := by cases a <;> cases b <;> decide
theorem Bool.eq_bnot (a b : Bool) :
  (a = (!b)) ↔ ¬(a = b) := by cases a <;> cases b <;> decide

/-- Notation typeclass for semantic entailment `⊨`. -/
class SemanticEntails (α : Type u) (β : outParam $ Type v) where
  entails : α → β → Prop

infix:51 " ⊨ " => SemanticEntails.entails
notation:51 M:51 " ⊭ " φ:52 => ¬(M ⊨ φ)

/-! Int -/

theorem Int.eq_zero_of_lt_neg_iff_lt (i : Int) : (0 < -i ↔ 0 < i) → i = 0 := by
  intro h
  by_cases hLt : 0 < i
  . have := h.mpr hLt; linarith
  . have : ¬ 0 < -i := fun h₂ => hLt (h.mp h₂); linarith

instance : HAdd PNat Nat PNat where
  hAdd | ⟨a,h⟩, b => ⟨a+b, Nat.add_pos_left h _⟩
