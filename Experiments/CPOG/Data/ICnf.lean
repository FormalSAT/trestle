/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Mathlib.Tactic.Linarith

import ProofChecker.Data.HashMap.Lemmas
import ProofChecker.Data.HashSet
import ProofChecker.Model.ToMathlib
import ProofChecker.Model.PropTerm
import ProofChecker.Model.PropVars

abbrev Var := PNat

namespace Var

instance : ToString Var where
  toString x := toString x.val

instance : Hashable Var where
  hash v := hash v.val
  
instance : Ord Var where
  compare a b := compare a.val b.val

end Var

/-! Literals -/

def ILit := { i : Int // i ≠ 0 }
  deriving DecidableEq, Repr

namespace ILit

def mkPos (x : Var) : ILit :=
  ⟨Int.ofNat x.val, by simp⟩

def mkNeg (x : Var) : ILit :=
  ⟨-Int.ofNat x.val, by simp⟩

def mk (x : Var) (p : Bool) : ILit :=
  if p then mkPos x else mkNeg x
  
instance : Coe Var ILit :=
  ⟨mkPos⟩

def var (l : ILit) : Var :=
  ⟨Int.natAbs l.val, Int.natAbs_pos.mpr l.property⟩

def polarity (l : ILit) : Bool :=
  (0 : Int) < l.val

def negate (l : ILit) : ILit :=
  ⟨-l.val, Int.neg_ne_zero.mpr l.property⟩

instance : Neg ILit := ⟨negate⟩

instance : ToString ILit where
  toString l := if l.polarity then s!"{l.var}" else s!"-{l.var}"

/-! Theorems about `ILit` -/

@[simp]
theorem var_mkPos (x :  Var) : var (mkPos x) = x :=
  Subtype.ext (Int.natAbs_ofNat x.val)

@[simp]
theorem var_mkNeg (x : Var) : var (mkNeg x) = x := by
  apply Subtype.ext
  simp [var, mkNeg]
  rfl

@[simp]
theorem var_mk (x : Var) (p : Bool) : var (mk x p) = x := by
  dsimp [mk]; split <;> simp

@[simp]
theorem polarity_mkPos (x : Var) : polarity (mkPos x) = true := by
  simp [polarity, mkPos]

@[simp]
theorem polarity_mkNeg (x : Var) : polarity (mkNeg x) = false := by
  simp [polarity, mkNeg]

@[simp]
theorem polarity_mk (x : Var) (p : Bool) : polarity (mk x p) = p := by
  dsimp [mk]; split <;> simp_all

@[simp]
theorem var_negate (l : ILit) : (-l).var = l.var := by
  simp only [var, Neg.neg, negate]
  apply Subtype.ext
  apply Int.natAbs_neg

theorem polarity_eq {l₁ l₂ : ILit} :
    l₁.polarity = l₂.polarity ↔ ((0 : Int) < l₁.val ↔ (0 : Int) < l₂.val) := by
  simp [polarity]

@[simp]
theorem polarity_negate (l : ILit) : (-l).polarity = !l.polarity := by
  rw [Bool.eq_bnot_to_not_eq, polarity_eq]
  intro hEq
  exact l.property (Int.eq_zero_of_lt_neg_iff_lt _ hEq)

@[ext]
theorem ext {l₁ l₂ : ILit} : l₁.var = l₂.var → l₁.polarity = l₂.polarity → l₁ = l₂ := by
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

@[simp]
theorem eta (l : ILit) : mk l.var l.polarity = l := by
  apply ext <;> simp

@[simp]
theorem eta_neg (l : ILit) : mk l.var (!l.polarity) = -l := by
  apply ext <;> simp

theorem mkPos_or_mkNeg (l : ILit) : l = .mkPos l.var ∨ l = .mkNeg l.var := by
  rw [← eta l]
  cases l.polarity
  . apply Or.inr
    simp [mk]
  . apply Or.inl
    simp [mk]

def toPropForm (l : ILit) : PropForm Var :=
  if l.polarity then .var l.var else .neg (.var l.var)

@[simp]
theorem toPropForm_mkPos (x : Var) : (mkPos x).toPropForm = .var x := by
  simp [toPropForm]

@[simp]
theorem toPropForm_mkNeg (x : Var) : (mkNeg x).toPropForm = .neg (.var x) := by
  simp [toPropForm]

def toPropTerm (l : ILit) : PropTerm Var :=
  if l.polarity then .var l.var else (.var l.var)ᶜ

@[simp]
theorem mk_toPropForm (l : ILit) : ⟦l.toPropForm⟧ = l.toPropTerm := by
  dsimp [toPropForm, toPropTerm]
  cases l.polarity <;> simp
  
@[simp]
theorem vars_toPropForm (l : ILit) : l.toPropForm.vars = {l.var} := by
  dsimp [toPropForm]
  cases l.polarity <;> simp [PropForm.vars]

@[simp]
theorem toPropTerm_mkPos (x : Var) : (mkPos x).toPropTerm = .var x := by
  simp [toPropTerm]

@[simp]
theorem toPropTerm_mkNeg (x : Var) : (mkNeg x).toPropTerm = (.var x)ᶜ := by
  simp [toPropTerm]

@[simp]
theorem toPropTerm_neg (l : ILit) : (-l).toPropTerm = l.toPropTermᶜ := by
  dsimp [toPropTerm]
  aesop
  
@[simp]
theorem semVars_toPropTerm (l : ILit) : l.toPropTerm.semVars = {l.var} := by
  dsimp [toPropTerm]
  cases l.polarity <;> simp

open PropTerm

theorem satisfies_iff {τ : PropAssignment Var} {l : ILit} :
    τ ⊨ l.toPropTerm ↔ τ l.var = l.polarity := by
  dsimp [toPropTerm, var, polarity]
  aesop

theorem satisfies_neg {τ : PropAssignment Var} {l : ILit} :
    τ ⊨ (-l).toPropTerm ↔ τ ⊭ l.toPropTerm := by
  simp [satisfies_iff]

theorem satisfies_set [DecidableEq ν] (τ : PropAssignment Var) (l : ILit) :
    τ.set l.var l.polarity ⊨ l.toPropTerm := by
  simp [satisfies_iff, τ.set_get]

theorem eq_of_flip {τ : PropAssignment Var} {l : ILit} {x : Var} {p : Bool} :
    τ ⊭ l.toPropTerm → τ.set x p ⊨ l.toPropTerm → l = mk x p := by
  simp only [satisfies_iff]
  intro h hSet
  by_cases hEq : x = var l
  . rw [hEq, τ.set_get] at hSet
    simp [hSet, hEq]
  . exfalso; exact h (τ.set_get_of_ne p hEq ▸ hSet)

theorem eq_of_flip' {τ : PropAssignment Var} {l : ILit} {x : Var} {p : Bool} :
    τ ⊨ l.toPropTerm → τ.set x p ⊭ l.toPropTerm → l = mk x !p := by
  simp only [satisfies_iff]
  intro h hSet
  by_cases hEq : x = var l
  . rw [hEq, τ.set_get] at hSet
    have : (!p) = l.polarity := by
      simp [hSet]
    simp [hEq, this]
  . exfalso; exact hSet (τ.set_get_of_ne p hEq ▸ h)

end ILit

/-! Clauses -/

abbrev IClause := Array ILit

namespace IClause

def vars (C : IClause) : HashSet Var :=
  C.foldr (init := .empty Var) fun l acc => acc.insert l.var

instance : BEq IClause :=
  inferInstanceAs (BEq IClause)

instance : ToString IClause where
  toString C := s!"({String.intercalate " ∨ " (C.map toString).toList})"

/-! Theorems about `IClause` -/

theorem mem_vars (C : IClause) (x : Var) : x ∈ C.vars.toFinset ↔ ∃ l ∈ C.data, x = l.var := by
  rw [vars, Array.foldr_eq_foldr_data]
  induction C.data <;> aesop
  
def toPropForm (C : IClause) : PropForm Var :=
  C.data.foldr (init := .fls) (fun l φ => l.toPropForm.disj φ)

def toPropTerm (C : IClause) : PropTerm Var :=
  C.data.foldr (init := ⊥) (fun l φ => l.toPropTerm ⊔ φ)
  
@[simp]
theorem mk_toPropForm (C : IClause) : ⟦C.toPropForm⟧ = C.toPropTerm := by
  dsimp [toPropForm, toPropTerm]
  induction C.data <;> simp_all
  
@[simp]
theorem vars_toPropForm (C : IClause) : C.toPropForm.vars = C.vars.toFinset := by
  ext x
  simp [mem_vars, toPropForm]
  induction C.data <;> simp_all [PropForm.vars]
  
open PropTerm

theorem satisfies_iff {τ : PropAssignment Var} {C : IClause} :
    τ ⊨ C.toPropTerm ↔ ∃ l ∈ C.data, τ ⊨ l.toPropTerm := by
  rw [toPropTerm]
  induction C.data <;> simp_all

theorem semVars_sub (C : IClause) : C.toPropTerm.semVars ⊆ C.vars.toFinset := by
  rw [← vars_toPropForm, ← mk_toPropForm]
  apply PropForm.semVars_subset_vars

theorem tautology_iff (C : IClause) :
    C.toPropTerm = ⊤ ↔ ∃ l₁ ∈ C.data, ∃ l₂ ∈ C.data, l₁ = -l₂ := by
  refine ⟨?mp, ?mpr⟩
  case mp =>
    refine not_imp_not.mp ?_
    simp only [not_exists, not_and]
    unfold toPropTerm -- :( have to do it because no induction principle for arrays
    induction C.data with
    | nil => simp
    | cons l₀ ls ih =>
      -- crazy list-array induction boilerplate
      have : ls.foldr (init := ⊥) (fun l φ => l.toPropTerm ⊔ φ) = toPropTerm ls.toArray := by
        simp [toPropTerm]
      simp only [List.foldr_cons, this] at *
      -- end boilerplate
      intro hCompl hEq
      specialize ih fun l₁ h₁ l₂ h₂ => hCompl l₁ (by simp [h₁]) l₂ (by simp [h₂])
      simp only [PropTerm.eq_top_iff, satisfies_disj, not_forall] at hEq ih
      have ⟨τ₀, h₀⟩ := ih
      have := hEq τ₀
      have : τ₀ ⊨ l₀.toPropTerm := by tauto
      let τ₁ := τ₀.set l₀.var !l₀.polarity
      have : τ₁ ⊭ l₀.toPropTerm := by simp [ILit.satisfies_iff]
      have : τ₁ ⊭ toPropTerm ls.toArray := fun h => by
        have ⟨lₛ, hₛ, hτ⟩ := satisfies_iff.mp h
        simp only [satisfies_iff, not_exists, not_and] at h₀
        have : τ₀ ⊭ lₛ.toPropTerm := h₀ lₛ hₛ
        have : lₛ = ILit.mk l₀.var !l₀.polarity := ILit.eq_of_flip this hτ
        have : lₛ = -l₀ := by simp [this]
        simp at hₛ
        apply hCompl lₛ (List.mem_cons_of_mem _ hₛ) l₀ (List.mem_cons_self _ _) this
      have := hEq τ₁
      tauto
  case mpr =>
    intro ⟨l₁, h₁, l₂, h₂, hEq⟩
    ext τ
    rw [satisfies_iff]
    by_cases hτ : τ ⊨ l₂.toPropTerm
    . aesop
    . have : τ ⊨ l₁.toPropTerm := by
        rw [hEq, ILit.satisfies_neg]
        assumption
      tauto

/-! Tautology decision procedure -/

/-- `encodes enc C` says that the hashmap `enc` encodes the (non-tautological) clause `C`.
More generally, `encodes enc C i` says that `enc` encodes the disjunction of all but the
first `i` literals of `C`. -/
def encodes (enc : HashMap Var Bool) (C : IClause) (start : Nat := 0) : Prop :=
  (∀ j : Fin C.size, start ≤ j → enc.find? C[j].var = .some C[j].polarity) ∧
    ∀ x : Var, enc.contains x ↔ ∃ j : Fin C.size, start ≤ j ∧ C[j].var = x

theorem encodes_empty (C : IClause) : encodes HashMap.empty C (Array.size C) := by
  simp [encodes]; intro j; exact not_le_of_lt j.isLt

theorem not_tautology_of_encodes (C : IClause) (enc : HashMap Var Bool) (h : encodes enc C) :
    ¬ (toPropTerm C = ⊤) := by
  rw [tautology_iff]; simp only [not_exists, not_and]
  intros l₁ hl₁ l₂ hl₂ heq
  have ⟨i, hi⟩ := C.get_of_mem_data hl₁
  have ⟨j, hj⟩ := C.get_of_mem_data hl₂
  simp only [encodes, zero_le, forall_true_left, true_and] at h
  have hi' := h.1 i
  rw [hi, heq, ILit.var_negate, ILit.polarity_negate] at hi'
  have hj' := h.1 j
  rw [hj, hi'] at hj'
  simp at hj'

theorem encodes_insert_of_find?_eq_none {C : IClause} {i : Nat} {enc : HashMap Var Bool}
      (ilt: i < C.size)
      (henc : encodes enc C (i + 1))
      (h: HashMap.find? enc C[i].var = none) :
    encodes (HashMap.insert enc C[i].var C[i].polarity) C i := by
  constructor
  . intro j hile
    cases lt_or_eq_of_le hile
    case inl h' =>
      have := henc.1 _ (Nat.succ_le_of_lt h')
      rw [HashMap.find?_insert_of_ne, this]
      rw [bne_iff_ne, ne_eq]
      intro hc
      rw [←hc, h] at this; contradiction
    case inr h' =>
      cases h'
      simp [HashMap.find?_insert]
  . intro x
    rw [HashMap.contains_insert, henc.2 x, beq_iff_eq]; simp only [getElem_fin]
    constructor
    . rintro (⟨j, hile, rfl⟩ | rfl)
      . use j, (Nat.le_succ i).trans hile
      . use ⟨i, ilt⟩; simp
    . rintro ⟨j, hile, rfl⟩
      cases lt_or_eq_of_le hile
      case inl h' =>
        left; use j, Nat.succ_le_of_lt h'
      case inr h' =>
        right; simp [h']

theorem tautology_of_encodes_of_find?_eq_some
      {C : IClause} {i : Nat} {enc : HashMap Var Bool} {p : Bool}
      (ilt: i < C.size)
      (henc : encodes enc C (i + 1))
      (h : HashMap.find? enc C[i].var = some p)
      (hpne : p ≠ C[i].polarity) :
    toPropTerm C = ⊤ := by
  rw [tautology_iff]
  use C[i], C.get_mem_data ⟨i, ilt⟩
  have : enc.contains C[i].var := by
    rw [HashMap.contains_iff]; use p; exact h
  rw [henc.2] at this
  rcases this with ⟨j, hj, h'⟩
  use C[j], C.get_mem_data j
  ext; rw [ILit.var_negate, h']
  have := henc.1 j hj
  rw [h', h, Option.some.injEq] at this
  rw [ILit.polarity_negate, Bool.eq_bnot_to_not_eq, ←this]
  exact hpne.symm

theorem encode_of_encodes_of_find?_eq_some
      {C : IClause} {i : Nat} {enc : HashMap Var Bool} {p : Bool}
      (ilt: i < C.size)
      (henc : encodes enc C (i + 1))
      (h : HashMap.find? enc C[i].var = some p)
      (hpeq : p = C[i].polarity) :
    encodes enc C i := by
  constructor
  . intro j hile
    cases lt_or_eq_of_le hile
    case inl h' =>
      exact henc.1 _ (Nat.succ_le_of_lt h')
    case inr h' => cases h'; simp [h, hpeq]
  . intro x
    rw [henc.2]
    constructor
    . rintro ⟨j, hile, rfl⟩
      use j, (Nat.le_succ i).trans hile
    . rintro ⟨j, hile, rfl⟩
      cases lt_or_eq_of_le hile
      case inl h' => use j, Nat.succ_le_of_lt h'
      case inr h' =>
        have : enc.contains C[i].var := by
          rw [HashMap.contains_iff]; use p; exact h
        rw [henc.2] at this
        rcases this with ⟨j', hj', h''⟩
        use j', hj'
        rw [h'']; cases h'; simp

def checkTautoAux (C : IClause) : { b : Bool // b ↔ toPropTerm C = ⊤ } :=
  go C.size (le_refl _) .empty C.encodes_empty
where
  go : (i : Nat) → i ≤ C.size → (acc : HashMap Var Bool) → encodes acc C i →
      { b : Bool // b ↔ toPropTerm C = ⊤ }
    | 0,   _,  acc, hinv => ⟨false, by simp [C.not_tautology_of_encodes acc hinv]⟩
    | i+1, hi, acc, hinv =>
        have ilt := Nat.lt_of_succ_le hi
        match h: acc.find? C[i].var with
          | .none   => go i (le_of_lt ilt) _ (encodes_insert_of_find?_eq_none ilt hinv h)
          | .some p =>
              if hp: p = C[i].polarity then
                go i (le_of_lt ilt) _ (encode_of_encodes_of_find?_eq_some ilt hinv h hp)
              else
                ⟨true, by simp [tautology_of_encodes_of_find?_eq_some ilt hinv h hp]⟩

instance : DecidablePred (IClause.toPropTerm · = ⊤) :=
  fun C => match checkTautoAux C with
    | ⟨true, h⟩  => .isTrue (h.mp rfl)
    | ⟨false, h⟩ => .isFalse fun hC => nomatch h.mpr hC

/-- Check whether a clause is a tautology. The type is a hack for early-return. The clause is
tautological iff `none` is returned. -/
@[deprecated checkTautoAux]
def checkTautoAux' (C : IClause) : Option (HashMap Var Bool) :=
  C.foldlM (init := .empty) fun acc l => do
    match acc.find? l.var with
    | .none => acc.insert l.var l.polarity
    | .some p => if p ≠ l.polarity then none else acc

end IClause

/-! CNF -/

abbrev ICnf := Array IClause

namespace ICnf

def vars (φ : ICnf) : HashSet Var :=
  φ.foldr (init := .empty Var) fun C acc => acc.union C.vars

instance : ToString ICnf where
  toString C := s!"{String.intercalate " ∧ " (C.map toString).toList}"

/-! Theorems about `ICnf` -/

theorem mem_vars (φ : ICnf) (x : Var) : x ∈ φ.vars.toFinset ↔ ∃ C ∈ φ.data, x ∈ C.vars.toFinset :=
by
  simp only [vars, Array.foldr_eq_foldr_data]
  induction φ.data <;> aesop
  
def toPropForm (φ : ICnf) : PropForm Var :=
  φ.data.foldr (init := .tr) (fun l φ => l.toPropForm.conj φ)

def toPropTerm (φ : ICnf) : PropTerm Var :=
  φ.data.foldr (init := ⊤) (fun l φ => l.toPropTerm ⊓ φ)
  
@[simp]
theorem mk_toPropForm (φ : ICnf) : ⟦φ.toPropForm⟧ = φ.toPropTerm := by
  simp only [toPropForm, toPropTerm]
  induction φ.data <;> simp_all
  
@[simp]
theorem vars_toPropForm (φ : ICnf) : φ.toPropForm.vars = φ.vars.toFinset := by
  ext x
  simp only [mem_vars, toPropForm]
  induction φ.data <;> simp_all [PropForm.vars]

open PropTerm

theorem satisfies_iff {τ : PropAssignment Var} {φ : ICnf} :
    τ ⊨ φ.toPropTerm ↔ ∀ C ∈ φ.data, τ ⊨ C.toPropTerm := by
  rw [toPropTerm]
  induction φ.data <;> simp_all

theorem semVars_sub (φ : ICnf) : φ.toPropTerm.semVars ⊆ φ.vars.toFinset := by
  rw [← vars_toPropForm, ← mk_toPropForm]
  apply PropForm.semVars_subset_vars

end ICnf

/-! Partial assignments -/

/-- A partial assignment to propositional variables. -/
-- TODO: Using `HashMap` for this is cache-inefficient but I don't have time to verify better
-- structures rn
abbrev PartPropAssignment := HashMap Var Bool

namespace PartPropAssignment

/-- Interpret the assignment (x ↦ ⊤, y ↦ ⊥) as x ∧ ¬y, for example. -/
-- NOTE: Partial assignments really are more like formulas than they are like assignments because
-- there is no nice to way to extend one to a `PropAssignment` (i.e. a total assignment).
def toPropTerm (τ : PartPropAssignment) : PropTerm Var :=
  τ.fold (init := ⊤) fun acc x v => acc ⊓ if v then .var x else (.var x)ᶜ

instance : ToString PartPropAssignment where
  toString τ := String.intercalate " ∧ "
    (τ.fold (init := []) (f := fun acc x p => s!"{ILit.mk x p}" :: acc))

open PropTerm

theorem satisfies_iff (τ : PartPropAssignment) (σ : PropAssignment Var) :
    σ ⊨ τ.toPropTerm ↔ ∀ x p, τ.find? x = some p → σ x = p :=
  ⟨mp, mpr⟩
where
  mp := fun h => by
    intro x p? hFind
    have ⟨φ, hφ⟩ := τ.fold_of_mapsTo_of_comm
      (init := ⊤) (f := fun acc x v => acc ⊓ if v then PropTerm.var x else (PropTerm.var x)ᶜ)
      hFind ?comm
    case comm =>
      intros
      dsimp
      ac_rfl
    rw [toPropTerm, hφ] at h
    aesop

  mpr := fun h => by
    apply HashMap.foldRecOn (hInit := satisfies_tr)
    intro φ x p hφ hFind
    rw [satisfies_conj]
    refine ⟨hφ, ?_⟩
    have := h _ _ hFind
    split <;> simp [*]

end PartPropAssignment

namespace IClause

/-- Reduces a clause by a partial assignment. Returns `none` if it became satisfied,
otherwise `some C'` where `C'` is the reduced clause. -/
def reduce (C : IClause) (τ : PartPropAssignment) : Option IClause :=
  C.foldlM (init := #[]) fun acc l =>
    match τ.find? l.var with
    | some v => if v = l.polarity then none else acc
    | none => some <| acc.push l

theorem reduce_characterization (C : IClause) (σ : PartPropAssignment) :
    SatisfiesM (fun C' =>
      ∀ l ∈ C.data, (!σ.contains l.var → l ∈ C'.data) ∧
        σ.find? l.var ≠ some l.polarity) (reduce C σ) := by
  have := C.SatisfiesM_foldlM (init := #[]) (f := fun acc l =>
      match σ.find? l.var with
      | some v => if v = l.polarity then none else acc
      | none => some <| acc.push l)
    (motive := fun sz acc =>
      ∀ (i : Fin C.size), i < sz → (!σ.contains C[i].var → C[i] ∈ acc.data) ∧
        σ.find? C[i].var ≠ some C[i].polarity)
    (h0 := by simp)
    (hf := by
      simp only [SatisfiesM_Option_eq, getElem_fin]
      intro sz acc ih acc'
      split; split
      . simp
      next p hFind hP =>
        intro h i hLt; injection h with h; rw [← h]
        refine Or.elim (Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hLt)) (ih i) fun hEq => ?_
        simp only [hEq]
        refine ⟨?l, fun h => ?r⟩
        case r =>
          rw [hFind] at h
          injection h with h
          exact hP h
        case l =>
          have := HashMap.contains_iff _ _ |>.mpr ⟨_, hFind⟩
          simp_all
      next p hFind =>
        intro h i hLt; injection h with h; rw [← h]
        simp only [Array.push_data, List.mem_append, List.mem_singleton]
        refine Or.elim (Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hLt)) (fun hLt => ?_) fun hEq => ?_
          <;> aesop
      )
  dsimp [reduce]
  apply SatisfiesM.imp this
  intro C' hRed
  exact fun l hL =>
    have ⟨i, h⟩ := Array.get_of_mem_data hL
    h ▸ hRed i i.isLt

open PropTerm in
theorem reduce_eq_some (C C' : IClause) (σ : PartPropAssignment) :
    reduce C σ = some C' → C.toPropTerm ⊓ σ.toPropTerm ≤ C'.toPropTerm := by
  intro hSome
  have hRed := SatisfiesM_Option_eq.mp (reduce_characterization C σ) _ hSome
  refine entails_ext.mpr fun τ hτ => ?_
  rw [satisfies_conj] at hτ
  have ⟨l, hL, hτL⟩ := IClause.satisfies_iff.mp hτ.left
  by_cases hCont : σ.contains l.var
  next =>
    exfalso
    have ⟨p, hFind⟩ := HashMap.contains_iff _ _ |>.mp hCont
    have := PartPropAssignment.satisfies_iff _ _ |>.mp hτ.right _ _ hFind
    have : p = l.polarity := by
      rw [ILit.satisfies_iff, this] at hτL
      assumption
    exact hRed l hL |>.right (this ▸ hFind)
  next =>
    simp only [Bool.not_eq_true, Bool.bnot_eq_to_not_eq] at *
    exact IClause.satisfies_iff.mpr ⟨l, (hRed l hL).left hCont, hτL⟩

/-- When `C` is not a tautology, return the smallest assignment falsifying it. When it is not,
return an undetermined assignment. -/
def toFalsifyingAssignment (C : IClause) : PartPropAssignment :=
  C.foldl (init := .empty) fun acc l => acc.insert l.var !l.polarity

theorem toFalsifyingAssignment_characterization (C : IClause) : C.toPropTerm ≠ ⊤ →
    (∀ i : Fin C.size, C.toFalsifyingAssignment.find? C[i].var = some !C[i].polarity) ∧
    (∀ x p, C.toFalsifyingAssignment.find? x = some p → (ILit.mk x !p) ∈ C.data) := by
  intro hTauto
  have := C.foldl_induction
    (motive := fun (sz : Nat) (τ : PartPropAssignment) =>
      (∀ i : Fin C.size, i < sz → τ.find? C[i].var = some !C[i].polarity) ∧
      (∀ x p, τ.find? x = some p → (ILit.mk x !p) ∈ C.data))
    (init := .empty)
    (f := fun acc l => acc.insert l.var !l.polarity)
    (h0 := by simp)
    (hf := by
      intro sz τ ⟨ih₁, ih₂⟩
      refine ⟨?step₁, ?step₂⟩
      case step₁ =>
        intro i hLt
        cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hLt) with
        | inl h =>
          by_cases hEq : C[sz].var = C[i].var
          . have : C[sz].polarity = C[i].polarity := by
              by_contra hPol
              have : C[sz] = -C[i] := by
                apply ILit.ext <;> simp_all
              apply hTauto
              rw [tautology_iff]
              exact ⟨C[sz], Array.get_mem_data _ _, C[i], Array.get_mem_data _ _, this⟩
            have : C[sz] = C[i] := ILit.ext hEq this
            simp_all [HashMap.find?_insert]
          . simp only [HashMap.find?_insert_of_ne _ _ (bne_iff_ne _ _ |>.mpr hEq), ih₁ i h]
        | inr h =>
          simp [h]
          rw [HashMap.find?_insert _ _ LawfulBEq.rfl]
      case step₂ =>
        intro x p hFind
        by_cases hEq : C[sz].var = x
        . rw [← hEq, HashMap.find?_insert _ _ (LawfulBEq.rfl)] at hFind
          injection hFind with hFind
          rw [← hEq, ← hFind]
          simp [Array.getElem_mem_data]
        . rw [HashMap.find?_insert_of_ne _ _ (bne_iff_ne _ _|>.mpr hEq)] at hFind
          apply ih₂ _ _ hFind)
  dsimp [toFalsifyingAssignment]
  exact ⟨fun i => this.left i i.isLt, this.right⟩

theorem toFalsifyingAssignment_ext (C : IClause) : C.toPropTerm ≠ ⊤ →
    (∀ l, l ∈ C.data ↔ (toFalsifyingAssignment C).find? l.var = some !l.polarity) := by
  intro hTauto l
  have ⟨h₁, h₂⟩ := toFalsifyingAssignment_characterization C hTauto
  apply Iff.intro
  . intro hL
    have ⟨i, hI⟩ := Array.get_of_mem_data hL
    rw [← hI]
    exact h₁ i
  . intro hFind
    have := h₂ _ _ hFind
    rw [Bool.not_not, ILit.eta] at this
    exact this

theorem toPropTerm_toFalsifyingAssignment (C : IClause) : C.toPropTerm ≠ ⊤ →
    C.toFalsifyingAssignment.toPropTerm = C.toPropTermᶜ := by
  intro hTauto
  have := toFalsifyingAssignment_ext C hTauto
  ext τ
  simp only [PartPropAssignment.satisfies_iff, PropTerm.satisfies_neg, IClause.satisfies_iff,
    not_exists, not_and, ILit.satisfies_iff]
  apply Iff.intro
  . intro h l hL hτ
    have := h _ _ (this l |>.mp hL)
    simp [hτ] at this
  . intro h x p hFind
    have := this (ILit.mk x !p)
    simp only [ILit.var_mk, ILit.polarity_mk, Bool.not_not] at this
    have := h _ (this.mpr hFind)
    simp at this
    exact this

end IClause