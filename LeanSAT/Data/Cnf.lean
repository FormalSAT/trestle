/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki, Jeremy Avigad
-/

import LeanSAT.Upstream.ToMathlib
import LeanSAT.Model.PropFun
import LeanSAT.Model.PropVars

namespace LeanSAT

open Model

/-! ### Literals -/

/-- The type `L` is a representation of literals over variables of type `ν`. -/
@[specialize]
class LitVar (L : Type u) (ν : outParam $ Type v) where
  negate : L → L
  mkPos : ν → L
  mkNeg : ν → L := fun x => negate (mkPos x)
  toVar : L → ν
  polarity : L → Bool
  -- TODO: ν moreover needs to biject with PNat (perhaps in a separate typeclass)
  -- so that we can use variable names as array indices

namespace LitVar

def mkLit (L : Type u) {ν : Type v} [LitVar L ν] (x : ν) (p : Bool) : L :=
  if p then mkPos x else mkNeg x

variable {L : Type u} {ν : Type v} [LitVar L ν]

-- controversial maybe?
instance : Coe ν L :=
  ⟨mkPos⟩

instance : Neg L :=
  ⟨negate⟩

@[simp] theorem negate_eq (l : L) : negate l = -l := rfl

instance [ToString ν] : ToString L where
  toString l := if polarity l then s!"{toVar l}" else s!"-{toVar l}"

def toPropForm (l : L) : PropForm ν :=
  if polarity l then .var (toVar l) else .neg (.var $ toVar l)

def toPropFun (l : L) : PropFun ν :=
  if polarity l then .var (toVar l) else (.var $ toVar l)ᶜ

open PropFun

theorem satisfies_iff {τ : PropAssignment ν} {l : L} :
    τ ⊨ toPropFun l ↔ τ (toVar l) = polarity l := by
  dsimp [toPropFun, polarity]
  aesop

end LitVar

/-! ### Lawful literals -/

-- TODO: see if a shorter list of axioms implies this one
open LitVar in
class LawfulLitVar (L : Type u) (ν : Type v) [LitVar L ν] where
  toVar_negate (l : L) : toVar (-l) = toVar l
  toVar_mkPos (x : ν) : toVar (mkPos (L := L) x) = x
  toVar_mkNeg (x : ν) : toVar (mkNeg (L := L) x) = x
  polarity_negate (l : L) : polarity (-l) = !polarity l
  polarity_mkPos (x : ν) : polarity (mkPos (L := L) x) = true
  polarity_mkNeg (x : ν) : polarity (mkNeg (L := L) x) = false
  protected ext (l₁ l₂ : L) : toVar l₁ = toVar l₂ → polarity l₁ = polarity l₂ → l₁ = l₂

namespace LitVar
variable {L : Type u} {ν : Type v} [LitVar L ν] [LawfulLitVar L ν]
open LawfulLitVar

attribute [simp] toVar_negate toVar_mkPos toVar_mkNeg polarity_negate polarity_mkPos polarity_mkNeg
attribute [ext] LawfulLitVar.ext

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

@[simp] theorem toPropForm_mkPos (x : ν) : toPropForm (mkPos (L := L) x) = .var x := by
  simp [toPropForm]
@[simp] theorem toPropForm_mkNeg (x : ν) : toPropForm (mkNeg (L := L) x) = .neg (.var x) := by
  simp [toPropForm]

@[simp] theorem mk_toPropForm (l : L) : ⟦toPropForm l⟧ = toPropFun l := by
  dsimp [toPropForm, toPropFun]
  cases polarity l <;> simp

@[simp] theorem toPropFun_mkPos (x : ν) : toPropFun (mkPos (L := L) x) = .var x := by
  simp [toPropFun]
@[simp] theorem toPropFun_mkNeg (x : ν) : toPropFun (mkNeg (L := L) x) = (.var x)ᶜ := by
  simp [toPropFun]
@[simp] theorem toPropFun_neg (l : L) : toPropFun (-l) = (toPropFun l)ᶜ := by
  dsimp [toPropFun]
  aesop

variable [DecidableEq ν]

@[simp] theorem vars_toPropForm (l : L) : (toPropForm l).vars = {toVar l} := by
  dsimp [toPropForm]
  cases polarity l <;> simp [PropForm.vars]

@[simp] theorem semVars_toPropFun (l : L) : (toPropFun l).semVars = {toVar l} := by
  dsimp [toPropFun]
  cases polarity l <;> simp

open PropFun

theorem satisfies_neg {τ : PropAssignment ν} {l : L} :
    τ ⊨ toPropFun (-l) ↔ τ ⊭ toPropFun l := by
  simp [satisfies_iff]

theorem satisfies_set (τ : PropAssignment ν) (l : L) :
    τ.set (toVar l) (polarity l) ⊨ toPropFun l := by
  simp [satisfies_iff, τ.set_get]

theorem eq_of_flip {τ : PropAssignment ν} {l : L} {x : ν} {p : Bool} :
    τ ⊭ toPropFun l → τ.set x p ⊨ toPropFun l → l = mkLit L x p := by
  simp only [satisfies_iff]
  intro h hSet
  by_cases hEq : x = toVar l
  . rw [hEq, τ.set_get] at hSet
    simp [hSet, hEq]
  . exfalso; exact h (τ.set_get_of_ne p hEq ▸ hSet)

theorem eq_of_flip' {τ : PropAssignment ν} {l : L} {x : ν} {p : Bool} :
    τ ⊨ toPropFun l → τ.set x p ⊭ toPropFun l → l = mkLit L x !p := by
  simp only [satisfies_iff]
  intro h hSet
  by_cases hEq : x = toVar l
  . rw [hEq, τ.set_get] at hSet
    have : (!p) = polarity l := by
      simp [Bool.bnot_eq, hSet]
    simp [hEq, this]
  . exfalso; exact hSet (τ.set_get_of_ne p hEq ▸ h)

end LitVar

/-! ### Clauses -/

abbrev Clause (L : Type u) := Array L

namespace Clause

instance [ToString L] : ToString (Clause L) where
  toString C := s!"({String.intercalate " ∨ " (C.map toString).toList})"

@[simp]
theorem of_append (l₁ l₂ : List L) : { data := l₁ ++ l₂ : Clause L } = { data := l₁ : Clause L } ++ { data := l₂ : Clause L } := by
  show { data := l₁ ++ l₂ : Clause L } = { data := ({data := l₁ : Clause L } ++ { data := l₂ : Clause L }).data }
  simp only [Array.append_data]

@[simp]
theorem of_singleton (l : L) : { data := [l] : Clause L } = #[l] := by
  rfl

@[simp]
theorem of_empty : { data := [] : Clause L } = #[] := by
  rfl

variable {L : Type u} {ν : Type v} [LitVar L ν]

def toPropForm (C : Clause L) : PropForm ν :=
  C.data.foldr (init := .fls) (fun l φ => (LitVar.toPropForm l).disj φ)

def toPropFun (C : Clause L) : PropFun ν :=
  C.data.foldr (init := ⊥) (fun l φ => (LitVar.toPropFun l) ⊔ φ)

@[simp] theorem mk_toPropForm (C : Clause L) : ⟦C.toPropForm⟧ = C.toPropFun := by
  dsimp [toPropForm, toPropFun]
  induction C.data <;> simp_all

open PropFun

theorem satisfies_iff {τ : PropAssignment ν} {C : Clause L} :
    τ ⊨ C.toPropFun ↔ ∃ l ∈ C.data, τ ⊨ LitVar.toPropFun l := by
  rw [toPropFun]
  induction C.data <;> simp_all

theorem tautology_iff' [DecidableEq ν] [LawfulLitVar L ν] (C : Clause L) :
    C.toPropFun = ⊤ ↔ ∃ l₁ ∈ C.data, ∃ l₂ ∈ C.data, l₁ = -l₂ := by
  refine ⟨?mp, ?mpr⟩
  case mp =>
    refine not_imp_not.mp ?_
    simp only [not_exists, not_and]
    unfold toPropFun -- :( have to do it because no induction principle for arrays
    induction C.data with
    | nil => simp
    | cons l₀ ls ih =>
      -- crazy list-array induction boilerplate
      have : ls.foldr (init := ⊥) (fun l φ => LitVar.toPropFun l ⊔ φ) = toPropFun ls.toArray := by
        simp [toPropFun]
      simp only [List.foldr_cons, this] at *
      -- end boilerplate
      intro hCompl hEq
      specialize ih fun l₁ h₁ l₂ h₂ => hCompl l₁ (by simp [h₁]) l₂ (by simp [h₂])
      simp only [PropFun.eq_top_iff, satisfies_disj, not_forall] at hEq ih
      have ⟨τ₀, h₀⟩ := ih
      have := hEq τ₀
      have : τ₀ ⊨ LitVar.toPropFun l₀ := by tauto
      let τ₁ := τ₀.set (LitVar.toVar l₀) !(LitVar.polarity l₀)
      have : τ₁ ⊭ LitVar.toPropFun l₀ := by simp [LitVar.satisfies_iff]
      have : τ₁ ⊭ toPropFun ls.toArray := fun h => by
        have ⟨lₛ, hₛ, hτ⟩ := satisfies_iff.mp h
        simp only [satisfies_iff, not_exists, not_and] at h₀
        have : τ₀ ⊭ LitVar.toPropFun lₛ := h₀ lₛ hₛ
        have : lₛ = LitVar.mkLit L (LitVar.toVar l₀) !(LitVar.polarity l₀) :=
          LitVar.eq_of_flip this hτ
        have : lₛ = -l₀ := by simp [this]
        simp at hₛ
        apply hCompl lₛ (List.mem_cons_of_mem _ hₛ) l₀ (List.mem_cons_self _ _) this
      have := hEq τ₁
      tauto
  case mpr =>
    intro ⟨l₁, h₁, l₂, h₂, hEq⟩
    ext τ
    rw [satisfies_iff]
    by_cases hτ : τ ⊨ LitVar.toPropFun l₂
    . aesop
    . have : τ ⊨ LitVar.toPropFun l₁ := by
        rw [hEq, LitVar.satisfies_neg]
        assumption
      tauto

theorem tautology_iff [DecidableEq ν] [LawfulLitVar L ν] (C : Clause L) :
    C.toPropFun = ⊤ ↔ ∃ l ∈ C.data, -l ∈ C.data := by
  rw [tautology_iff' C]
  aesop

@[simp]
theorem toPropFun_append (C₁ C₂ : Clause L) : (C₁ ++ C₂).toPropFun = C₁.toPropFun ⊔ C₂.toPropFun := by
  ext; aesop (add norm satisfies_disj, norm satisfies_iff)

@[simp]
theorem toPropFun_singleton (l : L) : Clause.toPropFun #[l] = LitVar.toPropFun l := by
  ext; simp [satisfies_iff]

theorem toPropFun_getElem_lt (C : Clause L) (i : Nat) (h : i < C.size) : LitVar.toPropFun (C[i]'h) ≤ C.toPropFun := by
  apply PropFun.entails_ext.mpr
  intro σ hσ
  exact satisfies_iff.mpr ⟨C[i]'h, C.getElem_mem_data h, hσ⟩

theorem toPropFun_take_lt (C : Clause L) (i : Nat) : toPropFun ⟨C.data.take i⟩ ≤ C.toPropFun := by
  apply PropFun.entails_ext.mpr
  intro σ hσ
  have ⟨l, hl, hl'⟩ := satisfies_iff.mp hσ
  refine satisfies_iff.mpr ⟨l, List.mem_of_mem_take hl, hl'⟩

end Clause

/-! ### CNF -/

abbrev Cnf (L : Type u) := Array (Clause L)

namespace Cnf

instance [ToString L] : ToString (Cnf L) where
  toString C := s!"{String.intercalate " ∧ " (C.map toString).toList}"

variable {L : Type u} {ν : Type v} [LitVar L ν]

def toPropForm (φ : Cnf L) : PropForm ν :=
  φ.data.foldr (init := .tr) (fun l φ => l.toPropForm.conj φ)

def toPropFun (φ : Cnf L) : PropFun ν :=
  φ.data.foldr (init := ⊤) (fun l φ => l.toPropFun ⊓ φ)

@[simp] theorem mk_toPropForm (φ : Cnf L) : ⟦φ.toPropForm⟧ = φ.toPropFun := by
  simp only [toPropForm, toPropFun]
  induction φ.data <;> simp_all

open PropFun

theorem satisfies_iff {τ : PropAssignment ν} {φ : Cnf L} :
    τ ⊨ φ.toPropFun ↔ ∀ C ∈ φ.data, τ ⊨ C.toPropFun := by
  rw [toPropFun]
  induction φ.data <;> simp_all

end Cnf
