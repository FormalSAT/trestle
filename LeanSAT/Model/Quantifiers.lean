/- Copyright (c) the LeanSAT contributors

Authors: James Gallicchio
-/

import LeanSAT.Model.Subst

namespace LeanSAT.Model

/-! ## Existential Quantifiers

The main result of this file is a characterization of
existential quantification over [PropFun].

Quantifying over a single variable is straightforward
(see [PropFun.satisfies_existQuant]).
Quantifying over a *set* of variables is less straightforward.
-/

/-! ### Single Variable -/

namespace PropForm

def existQuant [DecidableEq ν] (φ : PropForm ν) (v : ν) : PropForm ν :=
  disj (φ.substOne v .fls)
       (φ.substOne v .tr)

theorem satisfies_existQuant [DecidableEq ν] (φ : PropForm ν) (v : ν) {τ : PropAssignment ν}
  : τ ⊨ φ.existQuant v ↔ τ ⊨ φ.substOne v .fls ∨ τ ⊨ φ.substOne v .tr
  := by simp [existQuant]

end PropForm

namespace PropFun

variable [DecidableEq ν] (φ : PropFun ν) (v : ν)

def existQuant : PropFun ν :=
    (φ.substOne v ⊥)
  ⊔ (φ.substOne v ⊤)

theorem satisfies_existQuant (τ : PropAssignment ν)
  : τ ⊨ φ.existQuant v ↔ ∃ b, τ.set v b ⊨ φ := by
  simp [existQuant, satisfies_substOne]

theorem existQuant_comm (v₁ v₂ : ν)
  : (φ.existQuant v₁ |>.existQuant v₂) = (φ.existQuant v₂ |>.existQuant v₁)
  := by
  if h' : v₁ = v₂ then
    cases h'; rfl
  else
  ext τ
  simp [existQuant, satisfies_disj, satisfies_substOne]
  generalize eval τ ⊤ = _τ1
  generalize eval τ ⊥ = _τ2
  -- TODO: rewrite this to be a terminal aesop call
  aesop <;> (
    rw [PropAssignment.set_comm] at h
    simp [h]
    first | exact h' | exact ne_comm.mp h')

theorem semVars_existQuant : semVars (φ.existQuant v) ⊆ semVars φ \ {v} := by
  intro v'
  simp [mem_semVars, existQuant, satisfies_substOne]
  push_neg
  rintro τ h1 ⟨h2,h3⟩
  if h:v = v' then
    cases h
    simp_all
  else
    simp [Ne.symm h]
    rw [PropAssignment.set_comm] at h2 h3
    · rcases h1 with h1|h1
        <;> (
        refine ⟨_,h1,?_⟩
        rw [PropAssignment.set_get_of_ne]
        repeat assumption)
    repeat assumption

theorem existQuant_eq_of_not_mem_semVars
  : ¬v ∈ φ.semVars → existQuant φ v = φ := by
  intro h
  ext τ
  simp [satisfies_existQuant]
  convert @or_self_iff (τ ⊨ φ) using 2 <;> (
    apply PropFun.agreeOn_semVars
    apply PropAssignment.agreeOn_set_of_not_mem
    apply h
  )

@[simp] theorem existQuant_top : existQuant ⊤ v = ⊤ := by
  ext τ
  simp [satisfies_existQuant]


/-! ### Sets of Variables -/

def existQuantSet (φ : PropFun ν) [DecidableEq ν] (vs : Finset ν) : PropFun ν :=
  vs.elim (fun L _ => L.foldl existQuant φ) pf
where
  pf := by
    intro a b ha hb
    have h1 := ha
    rw [←hb] at h1
    have : a ~ b := Quotient.eq_rel.mp h1
    simp; clear ha hb h1
    induction this generalizing φ with
    | nil         => simp at *
    | cons _ _ ih => simp at *; apply ih
    | swap        => simp; rw [existQuant_comm]
    | trans _ _ ih1 ih2 =>
      rw [ih1, ih2]

theorem satisfies_existQuantSet (φ : PropFun ν) [DecidableEq ν] (vs : Finset ν) (τ : PropAssignment ν)
  : τ ⊨ φ.existQuantSet vs ↔ ∃ τ', τ.setMany vs τ' ⊨ φ := by
  simp [existQuantSet]
  apply Finset.elim_eq_forall (s := vs)
    (f := fun L _ => List.foldl existQuant φ L)
    (h := existQuantSet.pf _ _)
  intro L hL hs
  rcases vs with ⟨vs,h⟩
  cases hL
  rw [hs]; clear hs
  unfold PropAssignment.setMany; simp; clear h
  induction L generalizing φ with
  | nil =>
    simp [PropAssignment.setMany]
  | cons x xs ih =>
    simp
    rw [ih]; clear ih
    simp only [satisfies_existQuant]
    constructor
    · rintro ⟨τ', b, h⟩; refine ⟨τ'.set x b, ?_⟩
      convert h using 1; ext v
      simp [PropAssignment.set]
      aesop
    · rintro ⟨τ', h⟩; refine ⟨τ', τ' x, ?_⟩
      convert h using 1; ext v
      simp [PropAssignment.set]
      aesop

def semVars_existQuantSet (φ : PropFun ν) [DecidableEq ν] (vs : Finset ν)
  : semVars (φ.existQuantSet vs) ⊆ φ.semVars \ vs := by
  rcases vs with ⟨vs,h⟩
  have ⟨L,h⟩ := Quotient.exists_rep vs; cases h
  simp [existQuantSet, Finset.elim]
  rw [Multiset.elim_mk]
  induction L generalizing φ with
  | nil => simp
  | cons hd tl ih =>
    simp at h; simp_all
    intro v hv
    have := ih _ hv
    simp at this
    rcases this with ⟨hhd,htl⟩
    have := semVars_existQuant φ hd hhd
    simp at this
    simp [*]

theorem existQuantSet_eq_of_semVars_disjoint
  : Disjoint (φ.semVars) vs → existQuantSet φ vs = φ
  := by
  intro hdis
  ext τ
  simp [satisfies_existQuantSet]
  have : ∀ τ', (τ.setMany vs τ').agreeOn φ.semVars τ := by
    intro τ'
    apply PropAssignment.agreeOn_setMany_of_disjoint
    simp [hdis]
  simp [PropFun.agreeOn_semVars (this _)]

theorem existQuantSet_existQuantSet (φ : PropFun ν) (vs vs' : Finset ν)
  : (φ.existQuantSet vs).existQuantSet vs' = φ.existQuantSet (vs' ∪ vs)
  := by
  ext τ
  simp [satisfies_existQuantSet, PropAssignment.setMany_setMany]
  constructor
  · rintro ⟨τ1,τ2,h⟩
    exact ⟨_,h⟩
  · rintro ⟨τ1,h⟩
    refine ⟨τ1,τ1,?_⟩
    simp [h]

theorem existQuantSet_union_of_disjoint_semVars_right (φ : PropFun ν) (vs vs' : Finset ν)
  : Disjoint φ.semVars vs' → φ.existQuantSet (vs ∪ vs') = φ.existQuantSet vs := by
  intro h; rw [← existQuantSet_existQuantSet, existQuantSet_eq_of_semVars_disjoint _ h]

theorem existQuantSet_eq_of_inter_semVars_eq (φ : PropFun ν) (vs vs' : Finset ν)
  : vs ∩ φ.semVars = vs' ∩ φ.semVars → φ.existQuantSet vs = φ.existQuantSet vs' := by
  intro h
  ext τ; simp [satisfies_existQuantSet]
  conv => lhs; arg 1; ext; rw [PropFun.setMany_satisfies_iff_inter_semVars, h]
  conv => rhs; arg 1; ext; rw [PropFun.setMany_satisfies_iff_inter_semVars]

@[simp] theorem existQuantSet_top [DecidableEq ν] (vs : Finset ν)
  : existQuantSet ⊤ vs = ⊤ := by
  ext τ
  simp [satisfies_existQuantSet]

theorem existQuantSet_conj [DecidableEq ν] (a b : PropFun ν) (vs)
  : Disjoint b.semVars vs → existQuantSet (a ⊓ b) vs = existQuantSet a vs ⊓ b
  := by
  intro h
  ext τ
  have := fun τ' =>
    PropAssignment.agreeOn_setMany_of_disjoint
      τ (semVars b) vs τ' (by simp; exact h)
  simp [satisfies_existQuantSet, PropFun.agreeOn_semVars (this _)]
