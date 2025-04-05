/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Galllicchio
-/

import Trestle.Model.PropFun
import Trestle.Data.Cnf

namespace Trestle

/-! ### Cubes

Cubes are identical in implementation to clauses, but have the opposite semantics.
Where a clause is interpreted as a disjunction, a cube is interpreted as a conjunction.
-/

abbrev Cube (L : Type u) := Array L

namespace Cube

open Model

instance [ToString L] : ToString (Cube L) where
  toString C := s!"({String.intercalate " ∧ " (C.map toString).toList})"

variable {L : Type u} {ν : Type v} [LitVar L ν]

def toPropFun (C : Cube L) : PropFun ν :=
  .all (Multiset.ofList C.toList |>.map LitVar.toPropFun)

instance : CoeHead (Cube L) (PropFun ν) := ⟨toPropFun⟩

theorem mem_semVars_toPropFun [DecidableEq ν] (x : ν) (C : Cube L)
  : x ∈ C.toPropFun.semVars → ∃ l, l ∈ C ∧ LitVar.toVar l = x := by
  intro h
  rcases C with ⟨data⟩
  have ⟨τ,hpos,hneg⟩ := (PropFun.mem_semVars _ _).mp h; clear h
  simp_all [toPropFun, Array.mem_def]
  rcases hneg with ⟨l,hl,h⟩
  have := (PropFun.mem_semVars _ _).mpr ⟨τ,hpos l hl,h⟩; clear hpos h
  aesop

open PropFun

theorem satisfies_iff {τ : PropAssignment ν} {C : Cube L} :
    τ ⊨ C.toPropFun ↔ ∀ l ∈ C, τ ⊨ LitVar.toPropFun l := by
  simp_rw [toPropFun, Array.mem_def]
  simp

theorem empty_iff [DecidableEq ν] [LawfulLitVar L ν] (C : Cube L) :
    C.toPropFun = ⊥ ↔ ∃ l₁ ∈ C, ∃ l₂ ∈ C, l₁ = -l₂ := by
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

def and (c1 c2 : Cube L) : Cube L :=
  c1 ++ c2

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

nonrec def map (L') [LitVar L' ν'] (f : ν → ν') (c : Cube L) : Cube L' :=
  c.map (LitVar.map f)

@[simp] theorem toPropFun_map [LitVar L' ν'] [LawfulLitVar L' ν'] (f : ν → ν') (c : Cube L)
  : (c.map L' f).toPropFun = c.toPropFun.map f
  := by
  ext τ
  simp [map, satisfies_iff]


end Cube

abbrev Cubing (L) := List (Cube L)

namespace Cubing

def unit : Cubing L := [#[]]

def prod (c1 c2 : Cubing L) : Cubing L :=
  c1.product c2
  |>.map fun (a,b) => a.and b

end Cubing
