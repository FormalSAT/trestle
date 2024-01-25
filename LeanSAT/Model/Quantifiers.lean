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

/-
theorem existQuantSet_pmap [DecidableEq ν'] [Fintype ν] (f : φ.semVars → ν') (vs : Finset ν')
  : existQuantSet (pmap φ f) vs =
      pmap (existQuantSet φ (Finset.univ.filter (fun v =>
          if h : _ then f ⟨v,h⟩ ∈ vs else false))) (fun ⟨v,h⟩ =>
              f ⟨v, by have := semVars_existQuantSet _ _ h; simp at this; simp [*]⟩) := by
  ext τ
  stop
  simp [satisfies_existQuantSet, satisfies_invImage]
  constructor
  · rintro ⟨τ', hsat⟩
    use (fun v =>
      if h : v ∈ vs.map f then
        τ' ((Finset.mapEquiv vs f).symm ⟨v,h⟩)
      else
        false)
    refine (agreeOn_semVars ?_).mp hsat
    · intro v hv
      simp [invImage.assn, PropAssignment.setMany]
      aesop
  · rintro ⟨τ', hsat⟩
    use (fun v' =>
      if v' ∈ vs then
        τ' (f v')
      else
        false)
    refine (agreeOn_semVars ?_).mp hsat
    · intro v hv
      simp [invImage.assn, PropAssignment.setMany]
      have : ∀ w, w ∈ vs' → w ∈ vs := h
      aesop
-/

noncomputable def existQuantInv [DecidableEq ν'] (f : ν ↪ ν') [Fintype ν] (φ : PropFun ν') : PropFun ν :=
  φ |>.existQuantSet (φ.semVars \ Finset.univ.map f)
    |>.preimage f

theorem existQuantInv_conj [DecidableEq ν'] (f : ν ↪ ν') [Fintype ν]
  : existQuantInv f (φ₁ ⊓ φ₂.map f) = existQuantInv f φ₁ ⊓ φ₂ := by
  simp [existQuantInv]
  rw [existQuantSet_conj _ _ _ ?disj]
  case disj =>
    apply Finset.disjoint_of_subset_left (u := Finset.univ.map f)
    · intro v' hv'
      rw [semVars_map] at hv'
      simp at hv' ⊢; rcases hv' with ⟨v,hv,h⟩; use v; apply h
    · apply Finset.disjoint_sdiff
  rw [existQuantSet_eq_of_inter_semVars_eq (vs' := semVars φ₁ \ Finset.univ.map f)]
  · rw [preimage_conj _ _ _ ?hp ?hq]
    case hp =>
      trans; apply semVars_existQuantSet
      simp; apply Finset.inter_subset_right
    case hq =>
      rw [semVars_map]
      repeat sorry
    simp
  · sorry
  stop
  unfold existQuantInv
  suffices ∀ φ h, φ = existQuantSet _ _ → invImage f Finset.univ φ h = _
    from this _ _ rfl
  intro φ h hφ
  ext τ; simp [satisfies_invImage]
  generalize hA : φ₁.semVars = A
  generalize hB : Finset.univ.map f = B at hφ
  generalize hC : (φ₂.map f).semVars = C
  generalize hD : (φ₁ ⊓ φ₂.map f).semVars = D at hφ
  have cb : C ⊆ B := by rw [←hC, ←hB]; apply _root_.trans; apply semVars_map; intro x; aesop
  have dac : D ⊆ A ∪ C := by rw [←hA,←hC,←hD]; apply semVars_conj _ _
  have dba : D \ B ⊆ A \ B := by
    clear hφ; intro x
    replace cb := @cb x
    replace dac := @dac x
    intro h
    simp at *
    aesop
  have : Disjoint D ((A \ B) \ (D \ B)) := by
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy
    aesop
  conv at this => arg 1; rw [← hD]
  rw [← existQuantSet_union_of_disjoint_semVars_right _ _ _ this] at hφ
  clear this
  rw [PropFun.existQuantSet_conj] at hφ
  · cases hφ; simp; intro
    apply iff_of_eq; congr
    exact Finset.union_eq_right.mpr dba
  · rw [hC]; simp
    constructor <;> (apply Finset.disjoint_of_subset_left cb; apply Finset.disjoint_sdiff)

set_option pp.proofs.withType false
theorem existQuantInv_existQuantInv
    [DecidableEq ν] [DecidableEq ν'] [DecidableEq ν'']
    [Fintype ν] [Fintype ν'] [Fintype ν'']
    (f : ν'' ↪ ν') (g : ν' ↪ ν)
  : existQuantInv f (existQuantInv g φ) = existQuantInv (f.trans g) φ := by
  ext τ
  unfold Function.Embedding.trans
  simp [existQuantInv]
  conv => lhs; rw [satisfies_preimage]
  conv => rhs; rw [satisfies_preimage]
  rw [existQuantSet_invImage, satisfies_invImage]
  · rw [existQuantSet_existQuantSet]
    apply iff_of_eq; congr 1
    · sorry
    · congr 1
      ext v; simp
      constructor
      · rintro (⟨v',⟨h1,h2⟩,rfl⟩|⟨h1,h2⟩)
        · have := semVars_invImage_subset_preimage _ _ _ _ h1
          simp at this
          have := semVars_existQuantSet _ _ this
          simp at this; simp [this]
          intro v''; apply h2
        · simp [h1, h2]
      · rintro ⟨h1,h2⟩
        simp [h1]
        rw [Classical.or_iff_not_imp_right]
        simp; intro x hx; use x; simp [*]
        constructor
        · apply semVars_invImage_subset_preimage; sorry
        · intro v''; have := h2 v''; cases hx; simp at this; use this
  · intro; simp
