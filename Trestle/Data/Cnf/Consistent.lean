/-
Copyright (c) 2026 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: Cayden Codel
-/

import Trestle.Data.Cnf.Basic
import Trestle.Model.PropPred

/-!
# Consistency and arc-consistency of CNF encodings

A CNF formula `F` *encodes* a constraint `P` when the models of `F`, projected onto
the constraint's (visible) variables `X`, are exactly the models of `P`.
Correctness alone says nothing about how well a SAT solver can reason about `F`.
The standard quality measures for encodings are stated in terms of unit propagation
(see e.g. Abío, Nieuwenhuis, Oliveras, Rodríguez-Carbonell,
*A Parametric Approach for Smaller and Better Encodings of Cardinality Constraints*, CP 2013,
and Bailleux, Boufkhad, Roussel, *New Encodings of Pseudo-Boolean Constraints into CNF*, SAT 2009).
For every partial assignment `ρ` on the variables `X`,

* `F` is **consistent** for `P` if, whenever `ρ` cannot be extended to a model of `P`,
  unit propagation on `F` under `ρ` derives a conflict; and
* `F` is **arc-consistent** for `P` if it is consistent, and moreover, whenever `ρ` *can*
  be extended to a model of `P`, unit propagation on `F` under `ρ` derives every literal
  over `X` that is entailed by `P ∧ ρ`.
  (This is *generalized arc consistency* (GAC) of the constraint, maintained by unit propagation.)

In particular, if `F` is arc-consistent for `P`, then as soon as the assignment to `X`
violates `P` (or makes it unsatisfiable), unit propagation on `F` derives `⊥`
(`ArcConsistent.unitConflict`, `ArcConsistent.unitConflict_of_not_sat`).

## Unit propagation

To keep this file independent of any particular implementation of unit propagation,
we specify unit propagation *relationally*. `F.UnitDerives ρ l` holds when the literal `l`
is in the unit-propagation closure of `F` under the assumptions `ρ`, and `F.UnitConflict ρ`
holds when that closure falsifies a clause of `F`. An executable unit propagator
(see `Trestle.Data.Cnf.UnitProp`) is correct when it reports a conflict iff `UnitConflict`
holds, and otherwise assigns exactly the literals satisfying `UnitDerives`.

The closure is sound (`UnitDerives.sound`, `UnitConflict.not_sat`), monotone in both the
formula and the assumptions (`UnitDerives.mono`), and invariant under injective renaming
of variables (`UnitDerives.mapVars`). These properties lift to consistency and
arc-consistency, so they survive adding clauses (`ArcConsistent.of_subset`) and
renaming variables into an encoder's variable space (`ArcConsistent.mapVars`).
-/

namespace Trestle

open Model PropFun

/-! ### Partial assignments -/

namespace Model

/-- A partial assignment of truth values to propositional variables.
    A variable `v` is unassigned when `ρ v = none`. -/
def PartialAssignment (V : Type v) := V → Option Bool

namespace PartialAssignment

variable {V : Type v} {W : Type w}

/-- The partial assignment that assigns no variables. -/
def empty : PartialAssignment V := fun _ => none

@[simp] theorem empty_apply (v : V) : (empty : PartialAssignment V) v = none := rfl

/-- `ρ ≤ ρ'` when `ρ'` agrees with every assignment made by `ρ`. -/
instance : LE (PartialAssignment V) := ⟨fun ρ ρ' => ∀ v b, ρ v = some b → ρ' v = some b⟩

theorem le_def {ρ ρ' : PartialAssignment V} :
    ρ ≤ ρ' ↔ ∀ v b, ρ v = some b → ρ' v = some b := Iff.rfl

theorem le_refl (ρ : PartialAssignment V) : ρ ≤ ρ := fun _ _ h => h

theorem le_trans {ρ₁ ρ₂ ρ₃ : PartialAssignment V} : ρ₁ ≤ ρ₂ → ρ₂ ≤ ρ₃ → ρ₁ ≤ ρ₃ :=
  fun h₁ h₂ v b h => h₂ v b (h₁ v b h)

theorem empty_le (ρ : PartialAssignment V) : empty ≤ ρ := by
  intro v b h; simp at h

/-- `ρ` only assigns variables in `X`. -/
def IsOver (ρ : PartialAssignment V) (X : Set V) : Prop :=
  ∀ v b, ρ v = some b → v ∈ X

theorem isOver_univ (ρ : PartialAssignment V) : ρ.IsOver Set.univ :=
  fun _ _ _ => Set.mem_univ _

theorem IsOver.mono {ρ : PartialAssignment V} {X Y : Set V} (hXY : X ⊆ Y) :
    ρ.IsOver X → ρ.IsOver Y :=
  fun h v b hv => hXY (h v b hv)

/-- The literal `l` is true under `ρ`. -/
def SatLit [LitVar L V] (ρ : PartialAssignment V) (l : L) : Prop :=
  ρ (LitVar.toVar l) = some (LitVar.polarity l)

/-- Pulls a partial assignment on `W` back along `f : V → W`. -/
def comap (f : V → W) (ρ : PartialAssignment W) : PartialAssignment V :=
  fun v => ρ (f v)

@[simp] theorem comap_apply (f : V → W) (ρ : PartialAssignment W) (v : V) :
    ρ.comap f v = ρ (f v) := rfl

theorem IsOver.comap {f : V → W} (hf : f.Injective) {ρ : PartialAssignment W} {X : Set V} :
    ρ.IsOver (f '' X) → (ρ.comap f).IsOver X := by
  intro h v b hv
  obtain ⟨x, hx, hxv⟩ := h (f v) b hv
  rwa [← hf hxv]

end PartialAssignment

namespace PropAssignment

variable {V : Type v} {W : Type w}

/-- The total assignment `τ` agrees with every assignment made by the partial assignment `ρ`. -/
def Extends (τ : PropAssignment V) (ρ : PartialAssignment V) : Prop :=
  ∀ v b, ρ v = some b → τ v = b

theorem extends_empty (τ : PropAssignment V) : τ.Extends .empty := by
  intro v b h; simp at h

theorem Extends.mono {τ : PropAssignment V} {ρ ρ' : PartialAssignment V} :
    ρ ≤ ρ' → τ.Extends ρ' → τ.Extends ρ :=
  fun hle h v b hv => h v b (hle v b hv)

theorem Extends.satisfies [LitVar L V] {τ : PropAssignment V} {ρ : PartialAssignment V}
    (h : τ.Extends ρ) {l : L} (hl : ρ.SatLit l) : τ ⊨ LitVar.toPropFun l := by
  rw [LitVar.satisfies_iff]; exact h _ _ hl

theorem Extends.set [DecidableEq V] {τ : PropAssignment V} {ρ : PartialAssignment V}
    (h : τ.Extends ρ) {x : V} (hx : ρ x = none) (b : Bool) : (τ.set x b).Extends ρ := by
  intro v c hv
  have : v ≠ x := by rintro rfl; simp [hx] at hv
  rw [PropAssignment.get_set_of_ne (Ne.symm this)]
  exact h v c hv

theorem Extends.of_agreeOn {τ σ : PropAssignment V} {ρ : PartialAssignment V} {X : Set V}
    (h : τ.Extends ρ) (hρ : ρ.IsOver X) (hτσ : τ.agreeOn X σ) : σ.Extends ρ := by
  intro v b hv
  rw [← hτσ v (hρ v b hv)]
  exact h v b hv

theorem Extends.map {f : V → W} {τ : PropAssignment W} {ρ : PartialAssignment W}
    (h : τ.Extends ρ) : (τ.map f).Extends (ρ.comap f) :=
  fun v b hv => h (f v) b hv

/-- A total assignment that extends `ρ.comap f` lifts along an injective `f`
    to a total assignment that extends `ρ`. -/
theorem exists_lift {f : V → W} (hf : f.Injective) {ρ : PartialAssignment W}
    {τ : PropAssignment V} (h : τ.Extends (ρ.comap f)) :
    ∃ τ' : PropAssignment W, τ'.map f = τ ∧ τ'.Extends ρ := by
  classical
  refine ⟨fun w => if hw : ∃ v, f v = w then τ hw.choose else (ρ w).getD false, ?_, ?_⟩
  · funext v
    have hv : ∃ v', f v' = f v := ⟨v, rfl⟩
    simp only [PropAssignment.map, Function.comp, dif_pos hv]
    rw [hf hv.choose_spec]
  · intro w b hw
    dsimp only
    split
    · next hv =>
      apply h
      simp [hv.choose_spec, hw]
    · simp [hw]

/-- The restriction of the total assignment `τ` to the variables in `X`. -/
def restrict (τ : PropAssignment V) (X : Set V) [DecidablePred (· ∈ X)] : PartialAssignment V :=
  fun v => if v ∈ X then some (τ v) else none

theorem restrict_isOver (τ : PropAssignment V) (X : Set V) [DecidablePred (· ∈ X)] :
    (τ.restrict X).IsOver X := by
  intro v b h
  by_contra hv
  simp [restrict, hv] at h

theorem extends_restrict (τ : PropAssignment V) (X : Set V) [DecidablePred (· ∈ X)] :
    τ.Extends (τ.restrict X) := by
  intro v b h
  unfold restrict at h
  split at h <;> simp_all

theorem agreeOn_of_extends_restrict {τ σ : PropAssignment V} {X : Set V} [DecidablePred (· ∈ X)]
    (h : σ.Extends (τ.restrict X)) : τ.agreeOn X σ := by
  intro v hv
  exact (h v (τ v) (by simp [restrict, hv])).symm

end PropAssignment

namespace PartialAssignment

variable {V : Type v} {W : Type w} {L : Type u} [LitVar L V]

/-- `ρ` can be extended to a model of the constraint `P`. -/
def ConsistentWith (ρ : PartialAssignment V) (P : PropPred V) : Prop :=
  ∃ τ : PropAssignment V, τ.Extends ρ ∧ P τ

/-- The constraint `P` together with `ρ` entails the literal `l`,
    i.e., every model of `P` that extends `ρ` satisfies `l`. -/
def Entails (ρ : PartialAssignment V) (P : PropPred V) (l : L) : Prop :=
  ∀ τ : PropAssignment V, τ.Extends ρ → P τ → τ ⊨ LitVar.toPropFun l

theorem ConsistentWith.mono {ρ ρ' : PartialAssignment V} {P : PropPred V} :
    ρ ≤ ρ' → ρ'.ConsistentWith P → ρ.ConsistentWith P :=
  fun hle ⟨τ, hτ, hP⟩ => ⟨τ, hτ.mono hle, hP⟩

theorem entails_of_satLit {ρ : PartialAssignment V} {P : PropPred V} {l : L}
    (h : ρ.SatLit l) : ρ.Entails P l :=
  fun _ hτ _ => hτ.satisfies h

/-- If `ρ` is consistent with `P` and assigns the variable of an entailed literal `l`,
    then `ρ` already makes `l` true. -/
theorem Entails.satLit_of_assigned {ρ : PartialAssignment V} {P : PropPred V} {l : L}
    (hl : ρ.Entails P l) (hρ : ρ.ConsistentWith P) {b : Bool} (hb : ρ (LitVar.toVar l) = some b) :
    ρ.SatLit l := by
  obtain ⟨τ, hτ, hP⟩ := hρ
  have := hl τ hτ hP
  rw [LitVar.satisfies_iff, hτ _ _ hb] at this
  rw [SatLit, hb, this]

/-- If `P` does not constrain the (unassigned) variable of `l` -- that is, flipping the
    variable to falsify `l` preserves `P` -- then `P ∧ ρ` does not entail `l`. -/
theorem not_entails_of_flip [DecidableEq V] {ρ : PartialAssignment V} {P : PropPred V} {l : L}
    (hρ : ρ.ConsistentWith P) (hx : ρ (LitVar.toVar l) = none)
    (hP : ∀ τ : PropAssignment V, P τ → P (τ.set (LitVar.toVar l) (!LitVar.polarity l))) :
    ¬ ρ.Entails P l := by
  intro hl
  obtain ⟨τ, hτ, hPτ⟩ := hρ
  have := hl _ (hτ.set hx _) (hP τ hPτ)
  simp [LitVar.satisfies_iff] at this

theorem consistentWith_comap_iff {f : V → W} (hf : f.Injective) {ρ : PartialAssignment W}
    {P : PropPred V} :
    (ρ.comap f).ConsistentWith P ↔ ρ.ConsistentWith (fun σ => P (σ.map f)) := by
  constructor
  · rintro ⟨τ, hτ, hP⟩
    obtain ⟨τ', rfl, hτ'⟩ := PropAssignment.exists_lift hf hτ
    exact ⟨τ', hτ', hP⟩
  · rintro ⟨τ', hτ', hP⟩
    exact ⟨τ'.map f, hτ'.map, hP⟩

theorem entails_comap_iff {L' : Type u'} [LitVar L' W] [LawfulLitVar L' W]
    {f : V → W} (hf : f.Injective) {ρ : PartialAssignment W} {P : PropPred V} {l : L} :
    (ρ.comap f).Entails P l ↔ ρ.Entails (fun σ => P (σ.map f)) (LitVar.map f l : L') := by
  constructor
  · intro h τ' hτ' hP
    rw [LitVar.satisfies_map]
    exact h _ hτ'.map hP
  · intro h τ hτ hP
    obtain ⟨τ', rfl, hτ'⟩ := PropAssignment.exists_lift hf hτ
    rw [← LitVar.satisfies_map (L' := L')]
    exact h τ' hτ' hP

end PartialAssignment

end Model

/-! ### Literal lemmas -/

namespace LitVar

variable {L : Type u} {V : Type v} [LitVar L V] [LawfulLitVar L V]
  {L' : Type u'} {W : Type w} [LitVar L' W] [LawfulLitVar L' W]

omit [LawfulLitVar L V] in
@[simp] theorem toVar_map (f : V → W) (l : L) : toVar (map f l : L') = f (toVar l) := by
  simp [map]

omit [LawfulLitVar L V] in
@[simp] theorem polarity_map (f : V → W) (l : L) : polarity (map f l : L') = polarity l := by
  simp [map]

theorem map_neg (f : V → W) (l : L) : (map f (-l) : L') = -(map f l : L') := by
  ext <;> simp

theorem map_injective {f : V → W} (hf : f.Injective) : (map f : L → L').Injective := by
  intro l₁ l₂ h
  ext
  · exact hf (by simpa using congrArg toVar h)
  · simpa using congrArg polarity h

theorem neg_ne_self (l : L) : -l ≠ l := by
  intro h
  have := congrArg polarity h
  simp at this

theorem satLit_neg_iff {ρ : PartialAssignment V} {l : L} {b : Bool} (hb : ρ (toVar l) = some b) :
    ρ.SatLit (-l) ↔ ¬ ρ.SatLit l := by
  unfold PartialAssignment.SatLit
  rw [LawfulLitVar.toVar_negate, LawfulLitVar.polarity_negate, hb]
  cases b <;> cases polarity l <;> simp

end LitVar

/-! ### Unit propagation (specification) -/

namespace Cnf

variable {L : Type u} {V : Type v} [LitVar L V]

/-- Renames the variables of every clause in `F` by `f`. -/
def mapVars {L' : Type u'} {W : Type w} [LitVar L' W] (f : V → W) (F : Cnf L) : Cnf L' :=
  Array.map (Clause.map f) F

/--
  `F.UnitDerives ρ l` holds when the literal `l` is in the unit-propagation closure
  of the formula `F` under the assumptions `ρ`. Either

  * `l` is an assumption (`ρ` makes `l` true), or
  * some clause `C ∈ F` contains `l` and every other literal of `C` has been falsified.

  This is a specification. Once unit propagation derives a conflict, a real propagator
  stops, while this relation only describes the literals derivable before the conflict.
  See `UnitConflict`.
-/
inductive UnitDerives (F : Cnf L) (ρ : PartialAssignment V) : L → Prop
  | assn {l : L} : ρ.SatLit l → UnitDerives F ρ l
  | unit {C : Clause L} {l : L} : C ∈ F → l ∈ C →
      (∀ l' ∈ C, l' ≠ l → UnitDerives F ρ (-l')) → UnitDerives F ρ l

/-- Unit propagation on `F` under `ρ` derives a conflict: some clause of `F` has
    every one of its literals falsified. -/
def UnitConflict (F : Cnf L) (ρ : PartialAssignment V) : Prop :=
  ∃ C ∈ F, ∀ l ∈ C, F.UnitDerives ρ (-l)

namespace UnitDerives

variable {F F' : Cnf L} {ρ ρ' : PartialAssignment V}

/-- Unit propagation is monotone in the clauses and the assumptions. -/
theorem mono (hF : ∀ C ∈ F, C ∈ F') (hρ : ρ ≤ ρ') {l : L} :
    F.UnitDerives ρ l → F'.UnitDerives ρ' l := by
  intro h
  induction h with
  | assn h => exact .assn (hρ _ _ h)
  | unit hC hl _ ih => exact .unit (hF _ hC) hl ih

theorem of_subset (hF : ∀ C ∈ F, C ∈ F') {l : L} : F.UnitDerives ρ l → F'.UnitDerives ρ l :=
  mono hF (PartialAssignment.le_refl ρ)

/-- A literal derived by a clause whose negation is also derived gives a conflict on that clause. -/
theorem unitConflict_of_unit {C : Clause L} {l : L} (hC : C ∈ F)
    (h : ∀ l' ∈ C, l' ≠ l → F.UnitDerives ρ (-l')) (hneg : F.UnitDerives ρ (-l)) :
    F.UnitConflict ρ :=
  ⟨C, hC, fun l' hl' => by
    by_cases heq : l' = l
    · exact heq ▸ hneg
    · exact h l' hl' heq⟩

variable [LawfulLitVar L V]

/-- Unit propagation is sound: every model of `F` extending `ρ` satisfies every derived literal. -/
theorem sound {τ : PropAssignment V} (hτ : τ.Extends ρ) (hF : τ ⊨ F.toPropFun) {l : L} :
    F.UnitDerives ρ l → τ ⊨ LitVar.toPropFun l := by
  intro h
  induction h with
  | assn h => exact hτ.satisfies h
  | @unit C l hC _ _ ih =>
    obtain ⟨l', hl', hsat⟩ := Clause.satisfies_iff.mp (Cnf.satisfies_iff.mp hF C hC)
    by_cases heq : l' = l
    · exact heq ▸ hsat
    · exact absurd hsat (LitVar.satisfies_neg.mp (ih l' hl' heq))

/-- Deriving both a literal and its negation gives a conflict. -/
theorem unitConflict_of_neg {l : L} (h₁ : F.UnitDerives ρ l) (h₂ : F.UnitDerives ρ (-l)) :
    F.UnitConflict ρ := by
  cases h₁ with
  | unit hC _ h => exact unitConflict_of_unit hC h h₂
  | assn h₁ =>
    cases h₂ with
    | unit hC _ h => exact unitConflict_of_unit hC h (by rw [LitVar.neg_neg]; exact .assn h₁)
    | assn h₂ =>
      exfalso
      exact (LitVar.satLit_neg_iff h₁).mp h₂ h₁

/-- Unit propagation commutes with injective renaming of variables. -/
theorem mapVars {L' : Type u'} {W : Type w} [LitVar L' W] [LawfulLitVar L' W]
    {f : V → W} {ρ : PartialAssignment W} {l : L} :
    F.UnitDerives (ρ.comap f) l → (F.mapVars f : Cnf L').UnitDerives ρ (LitVar.map f l) := by
  intro h
  induction h with
  | assn h =>
    apply UnitDerives.assn
    simpa [PartialAssignment.SatLit] using h
  | @unit C l hC hl _ ih =>
    refine .unit (C := Clause.map f C) (Array.mem_map_of_mem hC) (Array.mem_map_of_mem hl) ?_
    intro l' hl' hne
    obtain ⟨l'', hl'', rfl⟩ := Array.mem_map.mp hl'
    rw [← LitVar.map_neg]
    exact ih l'' hl'' (fun h => hne (h ▸ rfl))

end UnitDerives

namespace UnitConflict

variable {F F' : Cnf L} {ρ ρ' : PartialAssignment V}

theorem mono (hF : ∀ C ∈ F, C ∈ F') (hρ : ρ ≤ ρ') : F.UnitConflict ρ → F'.UnitConflict ρ' :=
  fun ⟨C, hC, h⟩ => ⟨C, hF C hC, fun l hl => (h l hl).mono hF hρ⟩

theorem of_subset (hF : ∀ C ∈ F, C ∈ F') : F.UnitConflict ρ → F'.UnitConflict ρ :=
  mono hF (PartialAssignment.le_refl ρ)

/-- If unit propagation derives a conflict under `ρ`, then no model of `F` extends `ρ`. -/
theorem not_sat [LawfulLitVar L V] {τ : PropAssignment V} (hτ : τ.Extends ρ) :
    F.UnitConflict ρ → τ ⊭ F.toPropFun := by
  rintro ⟨C, hC, h⟩ hF
  obtain ⟨l, hl, hsat⟩ := Clause.satisfies_iff.mp (Cnf.satisfies_iff.mp hF C hC)
  exact LitVar.satisfies_neg.mp ((h l hl).sound hτ hF) hsat

theorem mapVars [LawfulLitVar L V] {L' : Type u'} {W : Type w} [LitVar L' W] [LawfulLitVar L' W]
    {f : V → W} {ρ : PartialAssignment W} :
    F.UnitConflict (ρ.comap f) → (F.mapVars f : Cnf L').UnitConflict ρ := by
  rintro ⟨C, hC, h⟩
  refine ⟨Clause.map f C, Array.mem_map_of_mem hC, ?_⟩
  intro l' hl'
  obtain ⟨l, hl, rfl⟩ := Array.mem_map.mp hl'
  rw [← LitVar.map_neg]
  exact (h l hl).mapVars

end UnitConflict

theorem mem_mapVars {L' : Type u'} {W : Type w} [LitVar L' W] {f : V → W} {F : Cnf L}
    {C : Clause L'} : C ∈ (F.mapVars f : Cnf L') ↔ ∃ C' ∈ F, Clause.map f C' = C := by
  simp [mapVars]

/-! ### Consistency and arc-consistency -/

/--
  `F` is *consistent* for the constraint `P` over the visible variables `X`
  when unit propagation detects every partial assignment over `X`
  that cannot be extended to a model of `P`.

  The formula `F` may mention variables outside of `X` (e.g., auxiliary variables).
-/
def Consistent (F : Cnf L) (P : PropPred V) (X : Set V) : Prop :=
  ∀ ρ : PartialAssignment V, ρ.IsOver X → ¬ ρ.ConsistentWith P → F.UnitConflict ρ

/--
  `F` *propagates* the constraint `P` over the visible variables `X` when,
  for every partial assignment `ρ` over `X` that can be extended to a model of `P`,
  unit propagation derives every literal over `X` that `P ∧ ρ` entails.
-/
def Propagates (F : Cnf L) (P : PropPred V) (X : Set V) : Prop :=
  ∀ ρ : PartialAssignment V, ρ.IsOver X → ρ.ConsistentWith P →
    ∀ l : L, LitVar.toVar l ∈ X → ρ.Entails P l → F.UnitDerives ρ l

/--
  `F` is *arc-consistent* (maintains generalized arc consistency by unit propagation)
  for the constraint `P` over the visible variables `X` when it is consistent,
  and it propagates every literal over `X` entailed by the constraint.
-/
def ArcConsistent (F : Cnf L) (P : PropPred V) (X : Set V) : Prop :=
  F.Consistent P X ∧ F.Propagates P X

variable {F F' : Cnf L} {P : PropPred V} {X Y : Set V} {ρ : PartialAssignment V}

theorem ArcConsistent.consistent (h : F.ArcConsistent P X) : F.Consistent P X := h.1
theorem ArcConsistent.propagates (h : F.ArcConsistent P X) : F.Propagates P X := h.2

/-- If `F` is consistent for `P` and `ρ` cannot be extended to a model of `P`,
    then unit propagation on `F` under `ρ` derives a conflict. -/
theorem Consistent.unitConflict (h : F.Consistent P X) (hρ : ρ.IsOver X)
    (hP : ¬ ρ.ConsistentWith P) : F.UnitConflict ρ :=
  h ρ hρ hP

/-- If `F` is arc-consistent for `P` and `ρ` cannot be extended to a model of `P`,
    then unit propagation on `F` under `ρ` derives a conflict. -/
theorem ArcConsistent.unitConflict (h : F.ArcConsistent P X) (hρ : ρ.IsOver X)
    (hP : ¬ ρ.ConsistentWith P) : F.UnitConflict ρ :=
  h.consistent.unitConflict hρ hP

/-- If `F` propagates `P` and `ρ` can be extended to a model of `P`,
    then unit propagation derives every literal over `X` entailed by `P ∧ ρ`. -/
theorem Propagates.unitDerives (h : F.Propagates P X) (hρ : ρ.IsOver X)
    (hP : ρ.ConsistentWith P) {l : L} (hl : LitVar.toVar l ∈ X) (hent : ρ.Entails P l) :
    F.UnitDerives ρ l :=
  h ρ hρ hP l hl hent

theorem ArcConsistent.unitDerives (h : F.ArcConsistent P X) (hρ : ρ.IsOver X)
    (hP : ρ.ConsistentWith P) {l : L} (hl : LitVar.toVar l ∈ X) (hent : ρ.Entails P l) :
    F.UnitDerives ρ l :=
  h.propagates.unitDerives hρ hP hl hent

/-- If `F` is consistent for `P` (which depends only on `X`), and a total assignment `τ`
    violates `P`, then unit propagation on `F` under `τ` restricted to `X` derives a conflict. -/
theorem Consistent.unitConflict_of_not_sat (h : F.Consistent P X) [DecidablePred (· ∈ X)]
    (hX : ∀ τ σ : PropAssignment V, τ.agreeOn X σ → P σ → P τ)
    {τ : PropAssignment V} (hτ : ¬ P τ) : F.UnitConflict (τ.restrict X) := by
  apply h _ (τ.restrict_isOver X)
  rintro ⟨σ, hσ, hP⟩
  exact hτ (hX τ σ (PropAssignment.agreeOn_of_extends_restrict hσ) hP)

/-- If `F` is arc-consistent for `P` (which depends only on `X`), and a total assignment `τ`
    violates `P`, then unit propagation on `F` under `τ` restricted to `X` derives a conflict. -/
theorem ArcConsistent.unitConflict_of_not_sat (h : F.ArcConsistent P X) [DecidablePred (· ∈ X)]
    (hX : ∀ τ σ : PropAssignment V, τ.agreeOn X σ → P σ → P τ)
    {τ : PropAssignment V} (hτ : ¬ P τ) : F.UnitConflict (τ.restrict X) :=
  h.consistent.unitConflict_of_not_sat hX hτ

/-! #### Soundness relative to a correct encoding

  If every model of `P` extends to a model of `F` (agreeing on `X`),
  then unit propagation on `F` is also *sound* for `P`.
  Consistency and propagation then characterize unit propagation exactly.
-/

section Complete

variable [LawfulLitVar L V]
  (hcomp : ∀ τ : PropAssignment V, P τ → ∃ σ : PropAssignment V, τ.agreeOn X σ ∧ σ ⊨ F.toPropFun)
include hcomp

theorem not_consistentWith_of_unitConflict (hρ : ρ.IsOver X) (h : F.UnitConflict ρ) :
    ¬ ρ.ConsistentWith P := by
  rintro ⟨τ, hτ, hP⟩
  obtain ⟨σ, hτσ, hσ⟩ := hcomp τ hP
  exact h.not_sat (hτ.of_agreeOn hρ hτσ) hσ

theorem entails_of_unitDerives (hρ : ρ.IsOver X) {l : L} (hl : LitVar.toVar l ∈ X)
    (h : F.UnitDerives ρ l) : ρ.Entails P l := by
  intro τ hτ hP
  obtain ⟨σ, hτσ, hσ⟩ := hcomp τ hP
  have := h.sound (hτ.of_agreeOn hρ hτσ) hσ
  rw [LitVar.satisfies_iff] at this ⊢
  rw [hτσ _ hl, this]

theorem Consistent.unitConflict_iff (h : F.Consistent P X) (hρ : ρ.IsOver X) :
    F.UnitConflict ρ ↔ ¬ ρ.ConsistentWith P :=
  ⟨not_consistentWith_of_unitConflict hcomp hρ, h.unitConflict hρ⟩

theorem Propagates.unitDerives_iff (h : F.Propagates P X) (hρ : ρ.IsOver X)
    (hP : ρ.ConsistentWith P) {l : L} (hl : LitVar.toVar l ∈ X) :
    F.UnitDerives ρ l ↔ ρ.Entails P l :=
  ⟨entails_of_unitDerives hcomp hρ hl, h.unitDerives hρ hP hl⟩

end Complete

/-! #### Structural lemmas -/

/-- Adding clauses preserves consistency. -/
theorem Consistent.of_subset (hF : ∀ C ∈ F, C ∈ F') (h : F.Consistent P X) : F'.Consistent P X :=
  fun ρ hρ hP => (h ρ hρ hP).of_subset hF

theorem Propagates.of_subset (hF : ∀ C ∈ F, C ∈ F') (h : F.Propagates P X) : F'.Propagates P X :=
  fun ρ hρ hP l hl hent => (h ρ hρ hP l hl hent).of_subset hF

/-- Adding clauses preserves arc-consistency. -/
theorem ArcConsistent.of_subset (hF : ∀ C ∈ F, C ∈ F') (h : F.ArcConsistent P X) :
    F'.ArcConsistent P X :=
  ⟨h.1.of_subset hF, h.2.of_subset hF⟩

theorem ArcConsistent.append_left (G : Cnf L) (h : F.ArcConsistent P X) :
    (G ++ F).ArcConsistent P X :=
  h.of_subset fun _ hC => Array.mem_append_right _ hC

theorem ArcConsistent.append_right (G : Cnf L) (h : F.ArcConsistent P X) :
    (F ++ G).ArcConsistent P X :=
  h.of_subset fun _ hC => Array.mem_append_left _ hC

/-- Consistency over `Y` implies consistency over any `X ⊆ Y`. -/
theorem Consistent.of_vars_subset (hXY : X ⊆ Y) (h : F.Consistent P Y) : F.Consistent P X :=
  fun ρ hρ hP => h ρ (hρ.mono hXY) hP

theorem Propagates.of_vars_subset (hXY : X ⊆ Y) (h : F.Propagates P Y) : F.Propagates P X :=
  fun ρ hρ hP l hl hent => h ρ (hρ.mono hXY) hP l (hXY hl) hent

theorem ArcConsistent.of_vars_subset (hXY : X ⊆ Y) (h : F.ArcConsistent P Y) :
    F.ArcConsistent P X :=
  ⟨h.1.of_vars_subset hXY, h.2.of_vars_subset hXY⟩

theorem Consistent.congr {P' : PropPred V} (hPP' : ∀ τ, P τ ↔ P' τ) (h : F.Consistent P X) :
    F.Consistent P' X := by
  obtain rfl : P = P' := funext fun τ => propext (hPP' τ)
  exact h

theorem ArcConsistent.congr {P' : PropPred V} (hPP' : ∀ τ, P τ ↔ P' τ)
    (h : F.ArcConsistent P X) : F.ArcConsistent P' X := by
  obtain rfl : P = P' := funext fun τ => propext (hPP' τ)
  exact h

/-! #### Renaming variables

  Consistency and arc-consistency are preserved by injective renamings of variables,
  e.g., when an encoder maps the variables of a constraint into its own variable space.
-/

section MapVars

variable [LawfulLitVar L V] {L' : Type u'} {W : Type w} [LitVar L' W] [LawfulLitVar L' W]
  {f : V → W}

theorem Consistent.mapVars (hf : f.Injective) (h : F.Consistent P X) :
    (F.mapVars f : Cnf L').Consistent (fun σ => P (σ.map f)) (f '' X) := by
  intro ρ hρ hP
  apply UnitConflict.mapVars
  apply h _ (hρ.comap hf)
  rwa [PartialAssignment.consistentWith_comap_iff hf]

theorem Propagates.mapVars (hf : f.Injective) (h : F.Propagates P X) :
    (F.mapVars f : Cnf L').Propagates (fun σ => P (σ.map f)) (f '' X) := by
  intro ρ hρ hP l' hl' hent
  obtain ⟨v, hv, hvl⟩ := hl'
  -- `l'` is the image of the literal `l` over `v`
  have hl : (LitVar.map f (LitVar.mkLit L v (LitVar.polarity l')) : L') = l' := by
    ext <;> simp [hvl]
  rw [← hl] at hent ⊢
  apply UnitDerives.mapVars
  apply h _ (hρ.comap hf) ((PartialAssignment.consistentWith_comap_iff hf).mpr hP)
  · simpa using hv
  · exact (PartialAssignment.entails_comap_iff hf).mpr hent

theorem ArcConsistent.mapVars (hf : f.Injective) (h : F.ArcConsistent P X) :
    (F.mapVars f : Cnf L').ArcConsistent (fun σ => P (σ.map f)) (f '' X) :=
  ⟨h.1.mapVars hf, h.2.mapVars hf⟩

end MapVars

end Cnf

end Trestle
