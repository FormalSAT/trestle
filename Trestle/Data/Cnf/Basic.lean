/-
Copyright (c) 2025 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Trestle.Data.Cnf.Defs
import Trestle.Data.LitVar.Basic
import Trestle.Model.PropVars

namespace Trestle

open Model

namespace Clause

variable {L : Type u} {ν : Type v} [LitVar L ν]

def toPropFun (C : Clause L) : PropFun ν :=
  .any (Multiset.ofList C.toList |>.map LitVar.toPropFun)

instance instCoeToPropFun : CoeHead (Clause L) (PropFun ν) := ⟨toPropFun⟩

theorem mem_semVars_toPropFun [DecidableEq ν] (x : ν) (C : Clause L)
  : x ∈ C.toPropFun.semVars → ∃ l, l ∈ C ∧ LitVar.toVar l = x := by
  intro h
  rcases C with ⟨data⟩
  have ⟨τ,hpos,hneg⟩ := (PropFun.mem_semVars _ _).mp h; clear h
  simp_all [toPropFun, Array.mem_def]
  rcases hpos with ⟨l,hl,h⟩
  have := (PropFun.mem_semVars _ _).mpr ⟨τ,h,hneg l hl⟩; clear hneg h
  aesop

open PropFun

theorem satisfies_iff {τ : PropAssignment ν} {C : Clause L} :
    τ ⊨ C.toPropFun ↔ ∃ l ∈ C, τ ⊨ LitVar.toPropFun l := by
  simp_rw [toPropFun, Array.mem_def]
  simp

theorem tautology_iff [DecidableEq ν] [LawfulLitVar L ν] (C : Clause L) :
    C.toPropFun = ⊤ ↔ ∃ l₁ ∈ C, ∃ l₂ ∈ C, l₁ = -l₂ := by
  constructor
  · intro h
    rcases C with ⟨lits⟩
    simp_all [toPropFun, Array.mem_def]
    induction lits with
    | nil => rw [PropFun.ext_iff] at h; simp [Array.mem_def] at h
    | cons hd tl ih =>
    classical
    refine if hr : any _ = ⊤ then have := ih hr; ?_ else ?_
    · aesop
    · clear ih
      rw [PropFun.ext_iff] at hr h
      simp at hr h
      rcases hr with ⟨τ,hr⟩
      replace h := h (τ.set (LitVar.toVar hd) (!LitVar.polarity hd))
      simp [LitVar.satisfies_iff, Bool.not_ne_self] at h
      rcases h with ⟨hd',hd'_mem,h⟩
      · replace hr := hr hd' hd'_mem
        simp [LitVar.satisfies_iff, PropAssignment.set] at hr h
        use hd, (List.mem_cons_self _ _), hd', (List.mem_cons_of_mem _ hd'_mem)
        split at h
        · ext
          · rw [LawfulLitVar.toVar_negate]; symm; assumption
          · rw [LawfulLitVar.polarity_negate]; exact Bool.not_eq_eq_eq_not.mp h
        · exact absurd h hr
  · rintro ⟨_,hl1,l,hl2,rfl⟩
    ext τ; simp [satisfies_iff]
    by_cases τ ⊨ LitVar.toPropFun l <;> aesop

@[simp] theorem toPropFun_or (c1 c2 : Clause L)
  : (c1.or c2).toPropFun = c1.toPropFun ⊔ c2.toPropFun := by
  ext τ
  simp [or, satisfies_iff]
  apply Iff.intro
  · rintro ⟨l,h1,h2⟩
    cases h1
    · refine Or.inl ⟨l,?_⟩
      simp [*]
    · refine Or.inr ⟨l,?_⟩
      simp [*]
  · rintro (⟨l,h1,h2⟩|⟨l,h1,h2⟩)
    · refine ⟨l,?_⟩
      simp [*]
    · refine ⟨l,?_⟩
      simp [*]

@[simp] theorem toPropFun_map [LitVar L' ν'] [LawfulLitVar L' ν'] (f : ν → ν') (c : Clause L)
  : (c.map L' f).toPropFun = c.toPropFun.map f
  := by
  ext τ
  simp [map, satisfies_iff]

@[simp] theorem toPropFun_empty : Clause.toPropFun (#[] : Clause L) = ⊥ := rfl
@[simp] theorem toPropFun_nil : Clause.toPropFun ({ toList := [] } : Clause L) = ⊥ := rfl

@[simp]
theorem toPropFun_cons (l : L) (C : List L)
  : Clause.toPropFun { toList := l :: C } = LitVar.toPropFun l ⊔ Clause.toPropFun { toList := C } := rfl

end Clause

/-! ### CNF -/

namespace Cnf

variable {L : Type u} {ν : Type v} [LitVar L ν]

def toPropFun (φ : Cnf L) : PropFun ν :=
  .all (φ.toList.map Clause.toPropFun)

theorem semVars_toPropFun [DecidableEq ν] (F : Cnf L)
  : v ∈ (toPropFun F).semVars → ∃ C, C ∈ F ∧ ∃ l, l ∈ C ∧ LitVar.toVar l = v := by
  rcases F with ⟨F⟩; simp_rw [Array.mem_def]; simp [toPropFun, PropFun.all]
  induction F <;> simp
  next hd tl ih =>
  intro hv
  have := PropFun.semVars_conj _ _ hv
  simp at this
  rcases this with (h|h)
  · have := Clause.mem_semVars_toPropFun _ _ h
    simp_rw [Array.mem_def] at this
    aesop
  · have := ih h
    simp_rw [Array.mem_def] at *
    simp_all

instance : CoeHead (Cnf L) (PropFun ν) := ⟨toPropFun⟩

theorem mem_semVars_toPropFun [DecidableEq ν] (x : ν) (F : Cnf L)
  : x ∈ F.toPropFun.semVars → ∃ C, C ∈ F ∧ x ∈ C.toPropFun.semVars := by
  intro h
  rcases F with ⟨data⟩
  simp [Array.mem_def]
  induction data <;> simp_all [toPropFun, PropFun.all]
  replace h := PropFun.semVars_conj _ _ h
  aesop

open PropFun

theorem satisfies_iff {τ : PropAssignment ν} {φ : Cnf L} :
    τ ⊨ φ.toPropFun ↔ ∀ C ∈ φ, τ ⊨ C.toPropFun := by
  rw [toPropFun]
  rcases φ with ⟨φ⟩
  induction φ <;> simp_all [Array.mem_def]

@[simp]
theorem toPropFun_addClause (C : Clause L) (f : Cnf L)
    : (f.addClause C).toPropFun = f.toPropFun ⊓ C.toPropFun := by
  have ⟨C⟩ := C
  have ⟨f⟩ := f
  ext τ
  simp [satisfies_iff, addClause]
  constructor
  · intro h
    constructor
    · intro C' hC'
      exact h C' (Or.inl hC')
    · exact h _ (Or.inr rfl)
  · rintro ⟨hF, hC⟩ C' (hC' | rfl)
    · exact hF _ hC'
    · exact hC

@[simp]
theorem toPropFun_and (f1 f2 : Cnf L)
    : (f1.and f2).toPropFun = f1.toPropFun ⊓ f2.toPropFun := by
  have ⟨f1⟩ := f1
  have ⟨f2⟩ := f2
  ext τ
  simp [satisfies_iff, and]
  constructor
  · intro h
    constructor
    <;> intro C hC
    · exact h C (Or.inl hC)
    · exact h C (Or.inr hC)
  · rintro ⟨h₁, h₂⟩ C (hC | hC)
    · exact h₁ _ hC
    · exact h₂ _ hC

@[simp]
theorem toPropFun_not (c : Clause L) [LawfulLitVar L ν]
    : (not c).toPropFun = (c.toPropFun)ᶜ := by
  have ⟨c⟩ := c
  ext τ
  simp [not, satisfies_iff, Clause.satisfies_iff, LitVar.satisfies_iff]
  constructor
  · intro h l h_mem hl
    simp [h _ h_mem] at hl
  · intro h l h_mem
    exact Bool.eq_not.mpr (h l h_mem)

@[simp]
theorem toPropFun_any (ls : Array L)
    : (any ls).toPropFun = .any (ls.toList.map LitVar.toPropFun) := by
  have ⟨ls⟩ := ls
  ext τ
  simp [any, toPropFun, Clause.toPropFun]

@[simp]
theorem toPropFun_all (ls : Array L)
    : (all ls).toPropFun = .all (ls.toList.map LitVar.toPropFun) := by
  have ⟨ls⟩ := ls
  ext τ
  simp [satisfies_iff, Clause.satisfies_iff, LitVar.satisfies_iff, all]

/-! #### Satisfiability -/

abbrev Sat (f : Cnf L) : Prop := f.toPropFun.Sat

end Cnf

namespace Cube

variable [LitVar L ν]

def toPropFun (C : Cube L) : PropFun ν :=
  .all (Multiset.ofList C.toList |>.map LitVar.toPropFun)

instance : CoeHead (Cube L) (PropFun ν) := ⟨toPropFun⟩

theorem mem_semVars_toPropFun [DecidableEq ν] (x : ν) (C : Cube L)
  : x ∈ C.toPropFun.semVars → ∃ l, l ∈ C.toArray ∧ LitVar.toVar l = x := by
  intro h
  rcases C with ⟨data⟩
  have ⟨τ,hpos,hneg⟩ := (PropFun.mem_semVars _ _).mp h; clear h
  simp_all [toPropFun, Array.mem_def]
  rcases hneg with ⟨l,hl,h⟩
  have := (PropFun.mem_semVars _ _).mpr ⟨τ,hpos l hl,h⟩; clear hpos h
  aesop

open PropFun

theorem satisfies_iff {τ : PropAssignment ν} {C : Cube L} :
    τ ⊨ C.toPropFun ↔ ∀ l ∈ C.toArray, τ ⊨ LitVar.toPropFun l := by
  simp_rw [toPropFun, Array.mem_def]
  simp

theorem empty_iff [DecidableEq ν] [LawfulLitVar L ν] (C : Cube L) :
    C.toPropFun = ⊥ ↔ ∃ l₁ ∈ C.toArray, ∃ l₂ ∈ C.toArray, l₁ = -l₂ := by
  constructor
  · intro h
    rcases C with ⟨lits⟩
    simp_all [toPropFun, Array.mem_def]
    induction lits with
    | nil => rw [PropFun.ext_iff] at h; simp [Array.mem_def] at h
    | cons hd tl ih =>
    classical
    refine if hr : all _ = ⊥ then have := ih hr; ?_ else ?_
    · aesop
    · clear ih
      rw [PropFun.ext_iff] at hr h
      simp at hr h
      rcases hr with ⟨τ,hr⟩
      replace h := h (τ.set (LitVar.toVar hd) (LitVar.polarity hd)) (by
        simp [LitVar.satisfies_iff])
      simp at h
      rcases h with ⟨hd',hd'_mem,h⟩
      replace hr := hr hd' hd'_mem
      simp [LitVar.satisfies_iff, PropAssignment.set] at hr h
      split at h
      · use hd, (List.mem_cons_self _ _), hd', (List.mem_cons_of_mem _ hd'_mem)
        ext
        · rw [LawfulLitVar.toVar_negate]; symm; assumption
        · rw [LawfulLitVar.polarity_negate, Bool.eq_not]; assumption
      · exact absurd hr h
  · rintro ⟨_,hl1,l,hl2,rfl⟩
    ext τ; simp [satisfies_iff]
    by_cases τ ⊨ LitVar.toPropFun l <;> aesop

@[simp] theorem toPropFun_and (c1 c2 : Cube L)
  : (c1.and c2).toPropFun = c1.toPropFun ⊓ c2.toPropFun := by
  ext τ
  simp [and, satisfies_iff]
  apply Iff.intro
  · rintro h
    constructor
    · aesop
    · aesop
  · rintro h l (l_mem|l_mem) <;>
      aesop

@[simp] theorem toPropFun_map [LitVar L' ν'] [LawfulLitVar L' ν'] (f : ν → ν') (c : Cube L)
  : (c.map L' f).toPropFun = c.toPropFun.map f
  := by
  ext τ
  simp [map, satisfies_iff]

end Cube

end Trestle
