/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-! Stuff that seems like it should be in std or mathlib. -/

/-! Std.Logic or Std.Bool? -/

@[simp] theorem Bool.bnot_eq_bnot (a b : Bool) :
  ((!a) = !b) ↔ (a = b) := by cases a <;> cases b <;> decide
@[simp] theorem Bool.eq_true_iff_eq_true (a b : Bool) :
  (a = true ↔ b = true) ↔ (a = b) := by cases a <;> cases b <;> decide
@[simp] theorem Bool.eq_false_iff_eq_false (a b : Bool) :
  (a = false ↔ b = false) ↔ (a = b) := by cases a <;> cases b <;> decide

-- Cayden TODO: Mathlib priority binding makes this theorem not equivalent to not_eq_iff
theorem Bool.bnot_eq (a b : Bool) : ((!a) = b) ↔ ¬(a = b) := by
  rw [← ne_eq]; cases a <;> cases b <;> simp

-- Cayden TODO: Replace with the appropriate Mathlib theorem, eq_not_iff
theorem Bool.eq_bnot (a b : Bool) :
  (a = (!b)) ↔ ¬(a = b) := by exact eq_not_iff

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

-- TODO: Simpler proof? Perhaps by matching on i?
theorem Int.toNat_negate_of_lt_zero {i : Int} : i < 0 → (-i).toNat = -i := by
  intro hi
  unfold toNat
  cases' hij : -i with j j
  · simp only [ofNat_eq_coe]
  · have : negSucc j < 0 := negSucc_lt_zero j
    rw [← hij] at this
    have := Int.not_lt.mpr (le_of_lt this)
    exact absurd (Int.neg_pos_of_neg hi) this

@[simp] theorem Int.negate_negSucc {n : Nat} : -(negSucc n) = n + 1 := rfl

instance : HAdd PNat Nat PNat where
  hAdd | ⟨a,h⟩, b => ⟨a+b, Nat.add_pos_left h _⟩

/- Credit Kyle Miller, Timo Carlin-Burns, Eric Weiser for these lemmas: -/
section Quotients
def Quotient.toTrunc {α : Sort*} [s : Setoid α] (q : Quotient s) : Trunc { a // ⟦a⟧ = q } :=
  Quotient.recOn q (fun a ↦ Trunc.mk ⟨a, rfl⟩) (fun _ _ _ ↦ Trunc.eq ..)

def Quotient.elim {α β : Sort*} [s : Setoid α] (q : Quotient s)
    (f : (a : α) → ⟦a⟧ = q → β) (h : ∀ a b ha hb, f a ha = f b hb)
    : β :=
  q.toTrunc.lift (fun x ↦ f x.val x.prop) (fun _ _ ↦ h ..)

theorem Quotient.elim_mk {α β : Sort*} [s : Setoid α] (a : α)
    (f : (b : α) → (⟦b⟧ : Quotient s) = ⟦a⟧ → β) (h : ∀ a b ha hb, f a ha = f b hb)
  : ⟦a⟧.elim f h = f a rfl := by
  simp [elim]
  apply Trunc.lift_mk

def Multiset.elim {α β : Type*} (s : Multiset α) (f : (L : List α) → L = s → β)
    (h : ∀ a b ha hb, f a ha = f b hb) : β :=
  Quotient.elim s f h

theorem Multiset.elim_mk {α β : Type*} (L : List α)
    (f : (L' : List α) → (⟦L'⟧ : Multiset α) = ⟦L⟧ → β) (h : ∀ a b ha hb, f a ha = f b hb)
  : elim ⟦L⟧ f h = f L rfl := by
  simp [elim]
  apply Trunc.lift_mk

theorem Multiset.elim_eq_forall {α β : Type*} {s : Multiset α} {f : (L : List α) → L = s → β} {h}
    (motive : Prop) (hmotive : ∀ {L hL}, Multiset.elim s f h = f L hL → motive) : motive := by
  induction s using Quotient.inductionOn with | _ L =>
  exact hmotive rfl

abbrev Finset.elim {α β : Type*} (s : Finset α) (f : (L : List α) → L = s.val → β)
    (h : ∀ a b ha hb, f a ha = f b hb) : β :=
  Multiset.elim s.val f h

theorem Finset.elim_eq_forall {α β : Type*} {s : Finset α} {f : (L : List α) → L = s.val → β} {h}
    (motive : Prop) (hmotive : ∀ {L hL}, Finset.elim s f h = f L hL → motive) : motive := by
  rcases s with ⟨s,h⟩
  induction s using Quotient.inductionOn with | _ L =>
  exact hmotive rfl

/-- Given a function over the (complete set of distinct) elements of a fintype,
  and a proof the function is constant, produce the value of that function. -/
def Fintype.elim_elems [Fintype V]
      (f : (L : List V) → (∀ v, v ∈ L) → List.Nodup L → β)
      (h : ∀ L1 h1 h11 L2 h2 h22, f L1 h1 h11 = f L2 h2 h22)
      : β :=
  Fintype.elems.elim
    (fun L hL =>
      f L
        (by intro; rw [←Multiset.mem_coe, hL]; simp [Fintype.complete])
        (by rw [←Multiset.coe_nodup, hL]; apply Finset.nodup))
    (by intros; apply h)

theorem Fintype.elim_elems_eq_forall [Fintype V] (f : (L : List V) → _ → _ → β) {h} {C : Prop}
    (h' : ∀ L h1 h2, Fintype.elim_elems f h = f L h1 h2 → C)
    : C
  := by
  apply Multiset.elim_eq_forall (motive := C)
  intro L hL hM
  apply h'
  apply hM

end Quotients

theorem Finset.biUnion_union [DecidableEq α] [DecidableEq β] (s1 s2 : Finset α) (f : α → Finset β)
  : Finset.biUnion (s1 ∪ s2) f = ((Finset.biUnion s1 f) ∪ Finset.biUnion s2 f)
  := by
  ext b
  simp only [mem_biUnion, mem_union]
  constructor
  · rintro ⟨a,b|b⟩
    · refine Or.inl ⟨a,?_⟩
      simp only [and_self, *]
    · refine Or.inr ⟨a,?_⟩
      simp only [and_self, *]
  · rintro (⟨a,b,c⟩|⟨a,b,c⟩)
      <;> refine ⟨a, ?_⟩
    · simp only [and_self, true_or, *]
    · simp only [and_self, or_true, *]

def Finset.getUnique (xs : Finset α) (h : ∃ x, xs = {x}) : α :=
  xs.elim (fun L hL =>
    match L with
    | [] => by
      exfalso; cases h; simp_all
      apply Multiset.not_mem_zero
      rw [hL]
      apply Multiset.mem_singleton.mpr
      rfl
    | x::_ => x
    ) (by
    intro a b ha hb
    rcases h with ⟨x,rfl⟩
    simp at ha hb
    cases ha; cases hb
    simp)

@[simp] theorem Finset.getUnique_eq (xs : Finset α) (h) (v)
  : Finset.getUnique xs h = v ↔ xs = {v}
  := by
  rcases h with ⟨x,rfl⟩
  simp [getUnique]
  apply elim_eq_forall
  intro L hL heq
  rw [heq]; clear heq
  simp at hL; cases hL
  simp

-- Cayden note/TODO: Added {a b : List α} and swapped out (h : a ~ b) with (h : Perm a b)
--   Occurred due to Lean upgrade from 4.4.0 to 4.5.0 (?)
theorem List.Perm.find?_unique {f : α → Bool} {a b : List α}
    (hunique : ∀ a1 a2, f a1 → f a2 → a1 = a2) (h : Perm a b)
  : a.find? f = b.find? f := by
  induction h with
  | nil => simp
  | cons => simp [find?]; split <;> simp [*]
  | swap =>
    simp [find?]; split <;> split <;> simp
    apply hunique; repeat assumption
  | trans =>
    simp_all

def Multiset.find? (f : α → Bool) (xs : Multiset α)
      (h : ∀ a1 a2, f a1 = true → f a2 = true → a1 = a2) : Option α :=
  xs.lift (·.find? f) (by
    intro a b perm
    simp
    apply List.Perm.find?_unique h perm
  )

theorem Multiset.mem_of_find?_eq_some (xs : Multiset α)
  : xs.find? f h = some x → x ∈ xs := by
  have ⟨L,hL⟩ := xs.exists_rep; cases hL
  simp [-quot_mk_to_coe, find?]
  simp; apply List.mem_of_find?_eq_some

theorem Multiset.find?_some (xs : Multiset α)
  : xs.find? f h = some x → f x := by
  have ⟨L,hL⟩ := xs.exists_rep; cases hL
  simp [-quot_mk_to_coe, find?]
  apply List.find?_some

@[simp] theorem Multiset.find?_eq_none (xs : Multiset α)
  : xs.find? f h = none ↔ ∀ x ∈ xs, f x = false := by
  have ⟨L,hL⟩ := xs.exists_rep; cases hL
  simp only [find?, Quotient.lift_mk, List.find?_eq_none, Bool.not_eq_true]
  simp only [quot_mk_to_coe, mem_coe]
