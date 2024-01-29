/- Copyright (c) the LeanSAT contributors

Authors: James Gallicchio
-/

import LeanSAT.Model.PropVars
import LeanSAT.Model.OfFun
import Mathlib.Data.Finset.Preimage

namespace LeanSAT.Model


/-! ## Substitution

This file defines operations on [PropForm] and [PropFun] for
substituting the variables in a formula with other variables,
or in general with other formulas.

The main definitions are:
- [PropForm.subst], [PropFun.subst]
- [PropForm.substOne], [PropFun.substOne]
- [PropForm.map], [PropFun.map]
- [PropForm.pmap], [PropFun.pmap]
-/

/-! ### `subst` -/

def PropForm.subst (p : PropForm ν₁) (f : ν₁ → PropForm ν₂) : PropForm ν₂ :=
  match p with
  | .var l => f l
  | .tr => .tr
  | .fls => .fls
  | .neg φ => .neg (φ.subst f)
  | .conj φ₁ φ₂ => .conj (φ₁.subst f) (φ₂.subst f)
  | .disj φ₁ φ₂ => .disj (φ₁.subst f) (φ₂.subst f)
  | .impl φ₁ φ₂ => .impl (φ₁.subst f) (φ₂.subst f)
  | .biImpl φ₁ φ₂ => .biImpl (φ₁.subst f) (φ₂.subst f)

theorem PropForm.subst_assoc (p : PropForm ν₁) (f₁ : ν₁ → PropForm ν₂) (f₂ : ν₂ → PropForm ν₃)
  : (p.subst f₁ |>.subst f₂) = p.subst (fun v => f₁ v |>.subst f₂)
  := by
  induction p <;> simp [subst, *]

theorem PropForm.vars_subst [DecidableEq ν₁] [DecidableEq ν₂]
    (p : PropForm ν₁) (f : ν₁ → PropForm ν₂)
  : vars (p.subst f) = (vars p).biUnion (fun v1 => vars (f v1)) := by
  induction p <;> simp [subst, Finset.biUnion_union, *]

open PropFun in
def PropAssignment.subst (f : ν → PropFun ν') (τ : PropAssignment ν') : PropAssignment ν :=
  fun v => τ ⊨ f v

@[simp]
theorem PropForm.satisfies_subst [DecidableEq ν] (φ : PropForm ν) (f : ν → PropForm ν') {τ : PropAssignment ν'}
  : τ ⊨ φ.subst f ↔ τ.subst (⟦f ·⟧) ⊨ φ
  := by induction φ <;> simp [subst, PropAssignment.subst, *]; rw [PropFun.satisfies_mk]

noncomputable
def PropFun.subst [DecidableEq ν₁] (φ : PropFun ν₁) (f : ν₁ → PropFun ν₂) : PropFun ν₂ :=
  φ.prod (Quotient.choice f)
  |>.lift (fun (p,f) => ⟦ p.subst f ⟧) (by
    rintro ⟨p1,f1⟩ ⟨p2,f2⟩ hab
    simp at *
    rcases hab with ⟨hp,hf⟩
    ext τ; rw [PropFun.satisfies_mk, PropFun.satisfies_mk]
    simp
    have : ∀ x, ⟦f1 x⟧ = ⟦f2 x⟧ := fun x => Quotient.eq.mpr (hf x)
    simp [this]
    apply PropForm.equivalent_ext.mp hp
  )

@[simp]
theorem PropFun.satisfies_subst [DecidableEq ν₁]
    (φ : PropFun ν₁) (f : ν₁ → PropFun ν₂) (τ : PropAssignment ν₂)
  : τ ⊨ φ.subst f ↔ τ.subst f ⊨ φ := by
  unfold subst
  generalize hq : φ.prod (Quotient.choice f) = q
  have ⟨(p,f'),h⟩ := q.exists_rep; cases h
  simp [Quotient.lift_mk (s := .prod _ _)]
  rw [satisfies_mk, PropForm.satisfies_subst, ← satisfies_mk]
  rw [Quotient.prod_eq_mk] at hq
  rcases hq with ⟨rfl,hq⟩
  apply iff_of_eq; congr; apply congrFun; apply congrArg
  funext x; simp [Quotient.choice] at hq
  have := Quotient.sound (hq x)
  simp at this
  exact this.symm

theorem PropFun.semVars_subst [DecidableEq ν₁] [DecidableEq ν₂]
    {φ} {f : ν₁ → PropFun ν₂}
  : semVars (PropFun.subst φ f) ⊆ (semVars φ).biUnion (fun v1 => semVars (f v1)) := by
  intro v2 hv2
  -- dig through the quotients & definitions
  unfold subst at hv2
  rw [Finset.mem_biUnion]
  have ⟨p,hp⟩ := φ.exists_rep; cases hp
  generalize hf' : Quotient.choice f = f' at hv2
  have ⟨f'', hf''⟩ := f'.exists_rep; cases hf''
  simp [Quotient.lift_mk (s := .prod _ _)] at hv2
  -- get assignments for which v2 is meaningful
  rw [mem_semVars] at hv2; rcases hv2 with ⟨τ,hsat,hunsat⟩
  -- now we can use `PropForm.satisfies_subst`
  rw [satisfies_mk] at hsat hunsat
  simp at hsat hunsat
  -- eliminate references to f'' by rewriting back to f
  have : ∀ x, ⟦f'' x⟧ = f x := by
    simp [Quotient.choice, piSetoid, instHasEquiv, Setoid.r] at hf'
    intro x; have := sound (hf' x); simp at this; simp [this]
  simp [this] at hsat hunsat; clear this hf' f''
  -- any two disagreeing assignments give you a semantic variable
  rw [← satisfies_mk] at hsat hunsat
  have ⟨x,h1,h2⟩ := exists_semVar hsat hunsat; clear hsat hunsat
  use x; simp [h2]; clear h2
  -- push info around
  rw [mem_semVars]
  simp [PropAssignment.subst] at h1
  by_cases h : τ ⊨ f x
  · use τ; simp [h] at h1; simp [*]
  · simp [h] at h1
    refine ⟨_, h1, ?_⟩
    simp [h]


/-! ### `substOne` -/

def PropForm.substOne [DecidableEq ν] (φ : PropForm ν) (v : ν) (φ' : PropForm ν) : PropForm ν :=
  φ.subst (fun v' => if v' = v then φ' else .var v')

theorem PropForm.substOne_congr [DecidableEq ν]
      (φ₁ φ₂ : PropForm ν) (v : ν) (ψ₁ ψ₂ : PropForm ν)
      (hφ : @Eq (PropFun _) ⟦φ₁⟧ ⟦φ₂⟧) (hψ : @Eq (PropFun _) ⟦ψ₁⟧ ⟦ψ₂⟧)
  : (⟦ φ₁.substOne v ψ₁ ⟧ : PropFun _) = ⟦ φ₂.substOne v ψ₂ ⟧
  := by
  apply PropFun.ext
  intro τ
  rw [PropFun.satisfies_mk, PropFun.satisfies_mk]
  simp [substOne]
  rw [←PropFun.satisfies_mk, ←PropFun.satisfies_mk]
  rw [hφ]
  simp
  apply iff_of_eq; congr; ext v
  simp [PropAssignment.subst]
  split
  · rw [hψ]
  · simp

theorem PropForm.satisfies_substOne [DecidableEq ν] (φ : PropForm ν) (v : ν) (ψ : PropForm ν)
        (τ : PropAssignment ν)
  : τ ⊨ φ.substOne v ψ ↔ τ.set v (τ ⊨ ψ) ⊨ φ := by
  simp [substOne]
  apply iff_of_eq; congr
  ext v
  simp [PropAssignment.subst, PropAssignment.set]
  split <;> simp
  exact PropFun.satisfies_mk

theorem PropForm.vars_substOne [DecidableEq ν] (v : ν) : (PropForm.substOne φ v φ').vars ⊆ (φ.vars \ {v}) ∪ φ'.vars := by
  induction φ with
  | var =>
      intro v hv; simp [subst, substOne] at hv ⊢
      split at hv
      · simp [hv]
      · simp at hv; subst_vars; simp [*]
  | tr  => simp
  | fls => simp
  | neg φ₁ ih => simp; exact ih
  | disj φ₁ φ₂ ih₁ ih₂
  | conj φ₁ φ₂ ih₁ ih₂
  | impl φ₁ φ₂ ih₁ ih₂
  | biImpl φ₁ φ₂ ih₁ ih₂ =>
    intro v hv; simp at *
    cases hv
    · have := ih₁ ‹_›
      simp at this; rcases this with ⟨a,b⟩|c <;> simp [*]
    · have := ih₂ ‹_›
      simp at this; rcases this with ⟨a,b⟩|c <;> simp [*]

def PropFun.substOne [DecidableEq ν] (ψ : PropFun ν) (v : ν) (φ : PropFun ν) : PropFun ν :=
  ψ.lift (fun ψ => φ.lift (fun φ => ⟦ψ.substOne v φ⟧) (by
      intro a b h
      ext τ
      simp
      rw [PropForm.substOne_congr]
      · simp
      · apply PropFun.sound h
      )
    ) (by
    intro a b h
    ext τ
    simp
    apply iff_of_eq; congr
    ext φ
    apply PropForm.substOne_congr
    · apply PropFun.sound h
    · simp
    )

@[simp]
theorem PropFun.satisfies_substOne [DecidableEq ν] (ψ : PropFun ν)
      (v : ν) (φ : PropFun ν) (τ : PropAssignment ν)
  : τ ⊨ ψ.substOne v φ ↔ τ.set v (τ ⊨ φ) ⊨ ψ := by
  have ⟨ψ,hψ⟩ := ψ.exists_rep; cases hψ
  have ⟨φ,hφ⟩ := φ.exists_rep; cases hφ
  simp [substOne]; rw [satisfies_mk, satisfies_mk]
  rw [PropForm.satisfies_substOne]
  rfl


/-! ### `map` -/

def PropForm.map (f : ν₁ → ν₂) : PropForm ν₁ → PropForm ν₂
| .var l => .var (f l)
| .tr => .tr
| .fls => .fls
| .neg φ => .neg (map f φ)
| .conj φ₁ φ₂ => .conj (map f φ₁) (map f φ₂)
| .disj φ₁ φ₂ => .disj (map f φ₁) (map f φ₂)
| .impl φ₁ φ₂ => .impl (map f φ₁) (map f φ₂)
| .biImpl φ₁ φ₂ => .biImpl (map f φ₁) (map f φ₂)

@[simp]
theorem PropForm.vars_map [DecidableEq ν₁] [DecidableEq ν₂]
      (f : ν₁ → ν₂) (φ : PropForm ν₁)
  : vars (φ.map f) = φ.vars.image f := by
  induction φ <;> simp [*, Finset.image_union]

theorem PropForm.satisfies_map (f : ν₂ → ν₁) (τ : PropAssignment ν₁) (φ : PropForm ν₂)
  : τ ⊨ φ.map f ↔ (τ.map f) ⊨ φ
  := by
  induction φ <;> (simp [map, PropAssignment.map] at *) <;> (simp [*])

@[simp]
theorem PropForm.semVars_map [DecidableEq ν₁] [DecidableEq ν₂] [Fintype ν₁]
      (f : ν₁ → ν₂) (hf : f.Injective) (φ : PropForm ν₁)
  : PropFun.semVars ⟦φ.map f⟧ = (PropFun.semVars ⟦φ⟧).map ⟨f,hf⟩ := by
  ext v2; simp
  constructor
  · intro h
    have isVar : v2 ∈ vars (map f φ) := semVars_subset_vars _ h
    simp at isVar
    rcases isVar with ⟨v1, _, rfl⟩
    simp [hf.eq_iff]
    have := by rw [PropFun.mem_semVars] at h; exact h
    rcases this with ⟨τ,hpos,hneg⟩
    rw [PropFun.satisfies_mk] at hpos hneg
    simp [satisfies_map] at hpos hneg
    rw [PropAssignment.map_set (finj := hf)] at hneg
    rw [PropFun.mem_semVars]
    use PropAssignment.map f τ
    simp
    rw [PropFun.satisfies_mk, PropFun.satisfies_mk]; simp [*]
  . rintro ⟨v1,hv1,rfl⟩
    rw [PropFun.mem_semVars] at hv1 ⊢
    rcases hv1 with ⟨τ,hpos,hneg⟩
    rw [PropFun.satisfies_mk] at hpos hneg
    use τ.preimage ⟨f,hf⟩
    dsimp
    rw [PropFun.satisfies_mk, PropFun.satisfies_mk]
    simp [satisfies_map, hpos]
    rw [PropAssignment.map_set]
    · simp; exact hneg
    · assumption

def PropFun.map (f : ν → ν') (φ : PropFun ν) : PropFun ν' :=
  φ.lift (⟦ PropForm.map f · ⟧) (by
    intro a b h
    simp
    ext τ
    rw [PropFun.satisfies_mk, PropFun.satisfies_mk]
    simp [PropForm.satisfies_map]
    rw [← PropFun.satisfies_mk, ← PropFun.satisfies_mk]
    rw [Quotient.eq.mpr h])

@[simp]
theorem PropFun.satisfies_map (f : ν → ν') (τ : PropAssignment ν') (φ : PropFun ν)
  : τ ⊨ φ.map f ↔ (τ.map f) ⊨ φ
  := by
  let ⟨ϕ,hϕ⟩ := φ.toTrunc.out
  cases hϕ
  simp [map]
  rw [satisfies_mk, satisfies_mk]
  apply PropForm.satisfies_map

theorem PropFun.semVars_map [DecidableEq ν] [DecidableEq ν'] [Fintype ν]
    (f : ν → ν') (φ : PropFun ν) (hf : f.Injective)
  : (φ.map f).semVars = φ.semVars.map ⟨f,hf⟩ := by
  let ⟨ϕ,hϕ⟩ := φ.toTrunc.out; cases hϕ
  simp [map, *, PropForm.semVars_map]

noncomputable def PropFun.attach [DecidableEq ν] (φ : PropFun ν) : PropFun φ.semVars :=
  .ofFun fun τ => τ.preimage ⟨Subtype.val, Subtype.val_injective⟩ ⊨ φ

theorem PropFun.preimage_satisfies [Fintype ν] [DecidableEq ν']
      (τ : PropAssignment ν) (f : ν ↪ ν') (h : φ.semVars ⊆ Finset.univ.map f)
  : τ.preimage f ⊨ φ ↔ ∃ σ, τ = PropAssignment.map f σ ∧ σ ⊨ φ := by
  constructor
  · intro h; refine ⟨_, ?_, h⟩
    simp
  · rintro ⟨σ,rfl,hσ⟩
    apply (agreeOn_semVars _).mpr hσ
    intro v' hv'
    simp at hv'; have := h hv'; simp at this
    simp [PropAssignment.preimage, PropAssignment.pmap, this]

@[simp]
theorem PropFun.satisfies_attach [DecidableEq ν] (φ : PropFun ν) (τ : PropAssignment _)
  : τ ⊨ φ.attach ↔ ∃ σ, τ = PropAssignment.map Subtype.val σ ∧ σ ⊨ φ := by
  simp [attach]
  rw [preimage_satisfies]
  · rfl
  · intro; simp
