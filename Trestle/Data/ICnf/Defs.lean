/-
Copyright (c) 2025 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Trestle.Data.LitVar.Defs
import Trestle.Data.Cnf.Defs
import Trestle.Upstream.ToStd

/-

Implementations of DIMACS literals, variables, and formulas.

-/

namespace Trestle

-- TODO: We could add an implementation type that uses `UInt64` or `USize` instead,
--       since almost all CNF instances will use "small" variable names.

/--
  The implementation type of DIMACS variables (hence the "I" in `IVar`).

  In DIMACS, variables are represented by strictly positive integers.
  We attach the positivity-hypothesis as a subtype here.

  This type is the exact same as the one for `PNat` in Mathlib
  (see [Data.PNat.Defs.lean](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/PNat/Defs.lean)).
  We redefine it here to avoid the dependency on Mathlib,
  and also in case we want to change the backing type to `UInt64` in the future.
-/
def IVar := { n : Nat // 0 < n }
  deriving DecidableEq, Repr

/--
  The implementation type of DIMACS literals (hence the "I" in `ILit`).

  In DIMACS, literals are non-zero integers, with negative numbers variables with an optional negation.
  We represent them as integers, with the invariant that they are non-zero.
-/
def ILit := { i : Int // i ≠ 0 }
  deriving DecidableEq, Repr

namespace IVar

/-! # index -/

/--
  Converts an `IVar` into a 0-indexed `Nat`.

  DIMACS variables are 1-indexed, but arrays are 0-indexed,
  so `index` subtracts one and does the coercion.
-/
@[inline, always_inline]
def index (v : IVar) : Nat := v.val - 1

/-- Converts a 0-indexed `Nat` into an `IVar`.  -/
@[inline, always_inline]
def ofIndex (n : Nat) : IVar := ⟨n + 1, by omega⟩

@[simp]
theorem ofIndex_inj (n m : Nat) : ofIndex n = ofIndex m ↔ n = m := by
  simp [ofIndex]
  constructor
  · rintro ⟨⟩; rfl
  · rintro rfl; rfl

instance instInhabited : Inhabited IVar := ⟨⟨1, by decide⟩⟩

def toString : IVar → String
  | ⟨n, _⟩ => s!"{n}"

instance instToString : ToString IVar where
  toString := toString

instance instHashable : Hashable IVar where
  hash v := hash v.val

instance instOrd : Ord IVar where
  compare a b := compare a.val b.val

instance instLT : LT IVar where
  lt a b := a.val < b.val

theorem lt_def (a b : IVar) : (a < b) = (a.val < b.val) := rfl

@[simp] theorem lt_ofIndex (a b : Nat) : ofIndex a < ofIndex b ↔ a < b := by simp [ofIndex, lt_def]

instance instLE : LE IVar where
  le a b := a.val ≤ b.val

theorem le_def (a b : IVar) : (a ≤ b) = (a.val ≤ b.val) := rfl

@[simp] theorem le_refl (a : IVar) : a ≤ a := Nat.le_refl _
@[simp] theorem le_ofIndex (a b : Nat) : ofIndex a ≤ ofIndex b ↔ a ≤ b := by simp [ofIndex, le_def]

instance : HAdd IVar Nat IVar where
  hAdd v off := ⟨v.val + off, by have := v.property; omega⟩

@[simp] theorem val_addNat (v : IVar) (x : Nat) : (v + x).val = v.val + x := rfl
@[simp] theorem index_addNat (v : IVar) (x : Nat) : (v + x).index = v.index + x := by
  have := v.property
  simp [index]
  omega

theorem add_lt_of_pos (pos : 0 < x) (v : IVar) : v < v + x := by
  rw [IVar.lt_def]; simp; omega

@[simp] theorem add_lt_add_left (v : IVar) (x y : Nat) : v + x < v + y ↔ x < y := by
  rw [IVar.lt_def]; simp

protected def max : IVar → IVar → IVar
  | ⟨v₁, _⟩, ⟨v₂, _⟩ => ⟨max v₁ v₂, by
      have := Nat.le_max_left v₁ v₂
      have := Nat.le_max_right v₁ v₂
      omega
    ⟩

def toPosILit : IVar → ILit
  | ⟨n, hn⟩ => ⟨Int.ofNat n, by exact Int.natAbs_pos.mp hn⟩

def toNegILit : IVar → ILit
  | ⟨n, hn⟩ => ⟨-Int.ofNat n, by
    intro h_con
    rw [Int.neg_eq_zero] at h_con
    revert h_con
    exact Int.natAbs_pos.mp hn⟩

instance instCoeIVar : Coe IVar ILit where
  coe v := toPosILit v

instance instOfNat : OfNat IVar (n+1) := ⟨n+1, by omega⟩

end IVar

--------------------------------------------------------------------------------

namespace ILit

instance instInhabited : Inhabited ILit := ⟨1, by decide⟩

instance instHashable : Hashable ILit where
  hash v := hash v.val

instance instOrd : Ord ILit where
  compare a b := compare a.val b.val

instance instCoeInt : Coe ILit Int where
  coe v := v.val

def toString : ILit → String
  | ⟨l, _⟩ => s!"{l}"

instance instToString : ToString ILit where
  toString := toString

def toIVar : ILit → IVar
  | ⟨l, hl⟩ => ⟨l.natAbs, Int.natAbs_pos.mpr hl⟩

instance instCoeToIVar : Coe ILit IVar where
  coe v := toIVar v

def ofIVar : IVar → ILit
  | ⟨n, hn⟩ => ⟨Int.ofNat n, by exact Int.natAbs_pos.mp hn⟩

instance instCoeOfIVar : Coe IVar ILit where
  coe v := ofIVar v

instance instOfNat : OfNat ILit (n+1) := ⟨n+1, by omega⟩

def toNat : ILit → Nat
  | ⟨l, _⟩ => l.natAbs

/-- Returns `true` iff the literal is positive. -/
protected def polarity : ILit → Bool
  | ⟨l, _⟩ => l > 0

def negate : ILit → ILit
  | ⟨l, _⟩ => ⟨-l, by
    intro h
    have := Int.neg_eq_zero.mp h
    contradiction⟩

instance instLitVar : LitVar ILit IVar where
  negate l := ⟨-l.val, Int.neg_ne_zero.mpr l.property⟩
  mkPos x := ⟨Int.ofNat x.val, by cases x; simp; omega⟩
  mkNeg x := ⟨-Int.ofNat x.val, by cases x; simp; omega⟩
  toVar l := ⟨Int.natAbs l.val, Int.natAbs_pos.mpr l.property⟩
  polarity l := (0 : Int) < l.val

instance instNeg : Neg ILit where
  neg := LitVar.negate

open LitVar in
theorem polarity_eq {l₁ l₂ : ILit} :
    polarity l₁ = polarity l₂ ↔ ((0 : Int) < l₁.val ↔ (0 : Int) < l₂.val) := by
  simp [polarity]

open LitVar in
instance instLawfulLitVar : LawfulLitVar ILit IVar where
  toVar_negate l := by
    apply Subtype.ext
    apply Int.natAbs_neg
  toVar_mkPos x :=
    Subtype.ext (Int.natAbs_ofNat x.val)
  toVar_mkNeg x := by
    apply Subtype.ext
    simp [toVar, mkNeg]
  polarity_negate l := by
    rw [Bool.eq_bnot, polarity_eq]
    intro hEq
    exact l.property (Int.eq_zero_of_lt_neg_iff_lt _ hEq)
  polarity_mkPos l := by
    cases l
    simp [polarity, mkPos]
    assumption
  polarity_mkNeg l := by
    cases l
    simp [polarity, mkNeg]
    omega
  ext l₁ l₂ := by
    /- Strip type alias. -/
    suffices ∀ {l₁ l₂ : Int}, l₁.natAbs = l₂.natAbs → (0 < l₁ ↔ 0 < l₂) → l₁ = l₂ by
      intro h₁ h₂
      apply Subtype.ext
      apply this
      . cases l₁; cases l₂
        simp [toVar] at h₁
        injection h₁
      . exact polarity_eq.mp h₂
    intro l₁ l₂ h₁ h₂
    cases Int.natAbs_eq_natAbs_iff.mp h₁
    . assumption
    next h =>
      rw [h] at h₂
      have : l₂ = 0 := Int.eq_zero_of_lt_neg_iff_lt l₂ h₂
      simp [this, h]

/-! # index -/

/--
  Converts an `ILit` into a 0-indexed `Nat`.

  DIMACS literals are 1-indexed (ignoring sign), but arrays are 0-indexed,
  so `index` subtracts one and does the coercion.
-/
@[inline, always_inline]
def index (l : ILit) : Nat := l.val.natAbs - 1

/-- Converts a 0-indexed `Nat` into an `ILit`. -/
@[inline, always_inline]
def ofIndex (n : Nat) : ILit := ⟨n + 1, by omega⟩

end ILit

--------------------------------------------------------------------------------

abbrev IClause := Clause ILit
abbrev ICnf := Cnf ILit
abbrev ICube := Cube ILit

namespace IClause

/--
  Finds the maximum DIMACS variable in a clause.
  If the clause is empty, then 0 is returned.
-/
def maxVar (C : IClause) : Nat :=
  Array.map ILit.toNat C |> Array.foldl max 0

end IClause

namespace ICnf
/--
  Finds the maximum DIMACS variable in the CNF.
  If there are no variables in the formula, then 0 is returned.
-/
def maxVar (F : ICnf) : Nat :=
  Array.map IClause.maxVar F |> Array.foldl max 0

end ICnf

end Trestle
