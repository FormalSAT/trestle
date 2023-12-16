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

def PropForm.existQuant [DecidableEq ν] (φ : PropForm ν) (v : ν) : PropForm ν :=
  disj (φ.substOne v .fls)
       (φ.substOne v .tr)

theorem PropForm.satisfies_existQuant [DecidableEq ν] (φ : PropForm ν) (v : ν) {τ : PropAssignment ν}
  : τ ⊨ φ.existQuant v ↔ τ ⊨ φ.substOne v .fls ∨ τ ⊨ φ.substOne v .tr
  := by simp [existQuant]

def PropFun.existQuant [DecidableEq ν] (φ : PropFun ν) (v : ν) : PropFun ν :=
    (φ.substOne v ⊥)
  ⊔ (φ.substOne v ⊤)

theorem PropFun.satisfies_existQuant [DecidableEq ν] (φ : PropFun ν) (v : ν) (τ : PropAssignment ν)
  : τ ⊨ φ.existQuant v ↔ ∃ b, τ.set v b ⊨ φ := by
  simp [existQuant, satisfies_substOne]

theorem PropFun.existQuant_comm [DecidableEq ν] (φ : PropFun ν) (v₁ v₂ : ν)
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

theorem PropFun.semVars_existQuant [DecidableEq ν] (φ : PropFun ν) (v : ν)
  : semVars (φ.existQuant v) ⊆ semVars φ \ {v} := by
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


/-! ### Sets of Variables -/

def PropFun.existQuantSet (φ : PropFun ν) [DecidableEq ν] (vs : Finset ν) : PropFun ν :=
  vs.elim (fun L _ => L.foldl PropFun.existQuant φ) pf
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

theorem PropFun.satisfies_existQuantSet (φ : PropFun ν) [DecidableEq ν] [Fintype ν] (vs : Finset ν) (τ : PropAssignment ν)
  : τ ⊨ φ.existQuantSet vs ↔ ∃ τ', τ.setMany vs τ' ⊨ φ := by
  simp [existQuantSet]
  apply Finset.elim_eq_forall (s := vs)
    (f := fun L _ => List.foldl PropFun.existQuant φ L)
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

def PropFun.semVars_existQuantSet (φ : PropFun ν) [DecidableEq ν] (vs : Finset ν)
  : semVars (φ.existQuantSet vs) ⊆ φ.semVars \ vs := by
  simp [existQuantSet]
  apply Finset.elim_eq_forall (s := vs)
    (f := fun L _ => List.foldl PropFun.existQuant φ L)
    (h := existQuantSet.pf _ _)
  intro L hL hs
  rcases vs with ⟨vs,h⟩
  cases hL
  rw [hs]; clear hs
  induction L generalizing φ with
  | nil => simp
  | cons hd tl ih =>
    simp
    intro v hv
    have := ih _ h.tail hv
    simp at this
    rcases this with ⟨hhd,htl⟩
    have := semVars_existQuant φ hd hhd
    simp at this
    simp [*]

/-- For every variable `v`, if `x ∈ xs` with `f x = v` then map `v` to `x`,
and otherwise existentially quantify it.

Useful for existentially quantifying temporaries out of a proposition. -/
noncomputable def PropFun.invImage [DecidableEq ν'] (f : ν ↪ ν')
      (xs : Finset ν) (φ : PropFun ν') : PropFun ν :=
  let varsToQuant := φ.semVars \ xs.map f
  let φ' := φ.existQuantSet varsToQuant
  φ'.pmap fun v' h =>
    xs.filter (f · = v') |>.getUnique (by
      have := semVars_existQuantSet _ _ h
      simp at this
      rcases this with ⟨h1, v, h3, rfl⟩
      refine ⟨v, ?_⟩
      ext v''; simp (config := {contextual := true}) [h3]
    )

theorem PropFun.semVars_invImage [DecidableEq ν] [DecidableEq ν'] (f : ν ↪ ν')
      (xs : Finset ν) (φ : PropFun ν')
  : semVars (φ.invImage f xs) ⊆ xs := by
  simp [invImage]
  apply Finset.Subset.trans (semVars_pmap ..)
  intro v
  simp
  intro v' _ h
  suffices v ∈ Finset.filter (f · = v') xs from
    Finset.filter_subset _ _ this
  rw [h]; simp

def PropFun.invImage.invOption [D : DecidableEq ν'] (f : ν ↪ ν') (xs : Finset ν)
  : ν' → Option ν :=
  fun v' =>
    xs.val.find? (f := fun v => f.toFun v = v') (by
      intros; apply f.injective; simp_all)

@[simp] theorem PropFun.invImage.invOption_eq_none [DecidableEq ν'] (f : ν ↪ ν') (xs)
  : PropFun.invImage.invOption f xs v' = none ↔ ∀ v ∈ xs, f v ≠ v'
  := by
  simp [invOption]

theorem PropFun.invImage.invOption_eq_some [DecidableEq ν'] (f : ν ↪ ν') (xs)
  : PropFun.invImage.invOption f xs v' = some v → v ∈ xs ∧ v' = f v
  := by simp (config := {contextual := true}) [invOption]

/-- Kind of a strange theorem but I use it later... -/
lemma PropFun.invImage_setManyMap_map_idem (f : ν → ν') (h : f.Injective) [DecidableEq ν'] [Fintype ν]
  : PropAssignment.map f
      (PropAssignment.setManyMap τ' τ
        (PropFun.invImage.invOption ⟨f,h⟩ Finset.univ))
    = τ
  := by
  ext v
  simp [PropAssignment.setManyMap]
  split
  case _ hx =>
    simp at hx
    exfalso; exact hx v rfl
  case _ v' hx =>
    have := PropFun.invImage.invOption_eq_some _ _ hx
    simp at this
    rw [h this]

theorem PropFun.invImage.setManyMap_of_map (f : ν → ν') (h : f.Injective) [DecidableEq ν'] [Fintype ν]
  : PropAssignment.setManyMap τ' (PropAssignment.map f τ)
      (PropFun.invImage.invOption ⟨f,h⟩ Finset.univ)
    |>.agreeOn (Set.range f) τ
  := by
  intro v' hv'
  rw [Set.mem_range] at hv'
  rcases hv' with ⟨v,hv⟩
  simp [PropAssignment.setManyMap]
  split
  case _ hx =>
    simp at hx
    exfalso; exact hx v hv
  case _ v2 hx =>
    have := PropFun.invImage.invOption_eq_some _ _ hx
    simp at this
    rw [this]

theorem PropFun.satisfies_invImage [DecidableEq ν] [DecidableEq ν'] (f : ν ↪ ν')
      (xs : Finset ν) (φ : PropFun ν') (τ : PropAssignment ν)
  : τ ⊨ φ.invImage f xs ↔ ∃ τ' : PropAssignment ν',
      τ'.setManyMap τ (invImage.invOption f xs) ⊨ φ := by
  simp [invImage]
  sorry
