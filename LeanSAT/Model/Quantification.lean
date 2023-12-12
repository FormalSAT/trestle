/- Copyright (c) the LeanSAT contributors

Authors: James Gallicchio
-/

import LeanSAT.Model.PropVars

namespace LeanSAT.Model

/-! ## Quantification

This file defines operations on `PropForm` and `PropFun` for
- substitution (replacing variables with formulas)
- existential quantification over (sets of) variables
-/

/-! ### Substitution -/

def PropForm.bind (p : PropForm ν₁) (f : ν₁ → PropForm ν₂) : PropForm ν₂ :=
  match p with
  | .var l => f l
  | .tr => .tr
  | .fls => .fls
  | .neg φ => .neg (φ.bind f)
  | .conj φ₁ φ₂ => .conj (φ₁.bind f) (φ₂.bind f)
  | .disj φ₁ φ₂ => .disj (φ₁.bind f) (φ₂.bind f)
  | .impl φ₁ φ₂ => .impl (φ₁.bind f) (φ₂.bind f)
  | .biImpl φ₁ φ₂ => .biImpl (φ₁.bind f) (φ₂.bind f)

theorem PropForm.bind_assoc (p : PropForm ν₁) (f₁ : ν₁ → PropForm ν₂) (f₂ : ν₂ → PropForm ν₃)
  : (p.bind f₁ |>.bind f₂) = p.bind (fun v => f₁ v |>.bind f₂)
  := by
  induction p <;> simp [bind, *]

theorem PropForm.vars_bind [DecidableEq ν₁] [DecidableEq ν₂]
    (p : PropForm ν₁) (f : ν₁ → PropForm ν₂)
  : vars (p.bind f) = (vars p).biUnion (fun v1 => vars (f v1)) := by
  induction p <;> simp [bind, Finset.biUnion_union, *]

open PropFun in
def PropAssignment.preimage (f : ν → PropFun ν') (τ : PropAssignment ν') : PropAssignment ν :=
  fun v => τ ⊨ f v

@[simp] theorem PropForm.satisfies_bind [DecidableEq ν] (φ : PropForm ν) (f : ν → PropForm ν') {τ : PropAssignment ν'}
  : τ ⊨ φ.bind f ↔ τ.preimage (⟦f ·⟧) ⊨ φ
  := by induction φ <;> simp [bind, PropAssignment.preimage, *]; rw [PropFun.satisfies_mk]

def PropForm.subst [DecidableEq ν] (φ : PropForm ν) (v : ν) (φ' : PropForm ν) : PropForm ν :=
  φ.bind (fun v' => if v' = v then φ' else .var v')

theorem PropForm.subst_congr [DecidableEq ν]
      (φ₁ φ₂ : PropForm ν) (v : ν) (ψ₁ ψ₂ : PropForm ν)
      (hφ : @Eq (PropFun _) ⟦φ₁⟧ ⟦φ₂⟧) (hψ : @Eq (PropFun _) ⟦ψ₁⟧ ⟦ψ₂⟧)
  : (⟦ φ₁.subst v ψ₁ ⟧ : PropFun _) = ⟦ φ₂.subst v ψ₂ ⟧
  := by
  apply PropFun.ext
  intro τ
  rw [PropFun.satisfies_mk, PropFun.satisfies_mk]
  simp [subst]
  rw [←PropFun.satisfies_mk, ←PropFun.satisfies_mk]
  rw [hφ]
  simp
  apply iff_of_eq; congr; ext v
  simp [PropAssignment.preimage]
  split
  · rw [hψ]
  · simp

theorem PropForm.satisfies_subst [DecidableEq ν] (φ : PropForm ν) (v : ν) (ψ : PropForm ν)
        (τ : PropAssignment ν)
  : τ ⊨ φ.subst v ψ ↔ τ.set v (τ ⊨ ψ) ⊨ φ := by
  simp [subst]
  apply iff_of_eq; congr
  ext v
  simp [PropAssignment.preimage, PropAssignment.set]
  split <;> simp
  exact PropFun.satisfies_mk

theorem PropForm.vars_subst [DecidableEq ν] (v : ν) : (PropForm.subst φ v φ').vars ⊆ (φ.vars \ {v}) ∪ φ'.vars := by
  induction φ with
  | var =>
      intro v hv; simp [bind, subst] at hv ⊢
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


/-! ### Map -/

def PropForm.map (f : ν₁ → ν₂) : PropForm ν₁ → PropForm ν₂
| .var l => .var (f l)
| .tr => .tr
| .fls => .fls
| .neg φ => .neg (map f φ)
| .conj φ₁ φ₂ => .conj (map f φ₁) (map f φ₂)
| .disj φ₁ φ₂ => .disj (map f φ₁) (map f φ₂)
| .impl φ₁ φ₂ => .impl (map f φ₁) (map f φ₂)
| .biImpl φ₁ φ₂ => .biImpl (map f φ₁) (map f φ₂)

@[simp] theorem PropForm.vars_map [DecidableEq ν₁] [DecidableEq ν₂]
      (f : ν₁ → ν₂) (φ : PropForm ν₁)
  : vars (φ.map f) = φ.vars.image f := by
  induction φ <;> simp [*, Finset.image_union]

theorem PropForm.satisfies_map (f : ν₂ → ν₁) (τ : PropAssignment ν₁) (φ : PropForm ν₂)
  : τ ⊨ φ.map f ↔ (τ.map f) ⊨ φ
  := by
  induction φ <;> (simp [map, PropAssignment.map] at *) <;> (simp [*])

def PropFun.map (f : ν → ν') (φ : PropFun ν) : PropFun ν' :=
  φ.lift (⟦ PropForm.map f · ⟧) (by
    intro a b h
    simp
    ext τ
    rw [PropFun.satisfies_mk, PropFun.satisfies_mk]
    simp [PropForm.satisfies_map]
    rw [← PropFun.satisfies_mk, ← PropFun.satisfies_mk]
    rw [Quotient.eq.mpr h])

theorem PropFun.satisfies_map (f : ν → ν') (τ : PropAssignment ν') (φ : PropFun ν)
  : τ ⊨ φ.map f ↔ (τ.map f) ⊨ φ
  := by
  let ⟨ϕ,hϕ⟩ := φ.toTrunc.out
  cases hϕ
  simp [map]
  rw [satisfies_mk, satisfies_mk]
  apply PropForm.satisfies_map

/-! ### Partial map -/

namespace PropForm

variable [DecidableEq ν]

def attach : (φ : PropForm ν) → PropForm {v : ν // v ∈ φ.vars }
| .var l => .var ⟨l, by simp [PropForm.vars]⟩
| .tr => .tr
| .fls => .fls
| .neg φ => .neg (attach φ)
| .conj φ₁ φ₂ =>
    .conj (attach φ₁ |>.map (·.map id fun _ h => by simp [vars,h]))
          (attach φ₂ |>.map (·.map id fun _ h => by simp [vars,h]))
| .disj φ₁ φ₂ =>
    .disj (attach φ₁ |>.map (·.map id fun _ h => by simp [vars,h]))
          (attach φ₂ |>.map (·.map id fun _ h => by simp [vars,h]))
| .impl φ₁ φ₂ =>
    .impl (attach φ₁ |>.map (·.map id fun _ h => by simp [vars,h]))
          (attach φ₂ |>.map (·.map id fun _ h => by simp [vars,h]))
| .biImpl φ₁ φ₂ =>
    .biImpl (attach φ₁ |>.map (·.map id fun _ h => by simp [vars,h]))
            (attach φ₂ |>.map (·.map id fun _ h => by simp [vars,h]))

@[simp] theorem vars_attach (φ : PropForm ν)
  : φ.attach.vars = φ.vars.attach := by
  ext ⟨v,h⟩
  simp
  induction φ
    <;> simp [vars] at h
    -- TODO: this aesop is very, very slow...
    <;> aesop

theorem satisfies_attach (φ : PropForm ν) (τ : PropAssignment ν)
    (τ' : PropAssignment φ.vars) (h : ∀ v : φ.vars, τ' v = τ v)
  : τ' ⊨ φ.attach ↔ τ ⊨ φ
  := by
  induction φ generalizing τ with
  | var =>
    simp [attach]
    apply h
  | tr
  | fls =>
    simp [attach]
  | neg _ ih =>
    have := ih τ τ' h
    simp [attach, this]
  | conj φ1 φ2 ih1 ih2
  | disj φ1 φ2 ih1 ih2
  | impl φ1 φ2 ih1 ih2
  | biImpl φ1 φ2 ih1 ih2 =>
    simp [attach, satisfies_map]
    rw [(show τ'.map _ ⊨ attach φ1 ↔ τ ⊨ φ1 from ih1 ..)]
    rw [(show τ'.map _ ⊨ attach φ2 ↔ τ ⊨ φ2 from ih2 ..)]
    repeat {
      rintro ⟨v,_⟩
      simp [Subtype.map]
      apply h
    }


def pmap (φ : PropForm ν) (f : (v : ν) → v ∈ φ.vars → ν') : PropForm ν' :=
  φ.attach.map (fun ⟨v,h⟩ => f v h)

theorem vars_pmap [DecidableEq ν'] (φ : PropForm ν) (f : (v : ν) → v ∈ φ.vars → ν')
  : (φ.pmap f).vars ⊆ φ.vars.attach.image (fun ⟨v,h⟩ => f v h)
  := by
  simp [pmap]

theorem satisfies_pmap {φ} {f : (v : ν) → v ∈ φ.vars → ν'} {τ : PropAssignment ν'}
    (τ' : PropAssignment ν) (h : ∀ v : φ.vars, τ (f v v.2) = τ' v)
  : τ ⊨ φ.pmap f ↔ τ' ⊨ φ
  := by
  simp [pmap, satisfies_map]
  apply satisfies_attach
  exact h

/-- Replace all non-semantic variables in `φ` with `.fls` -/
noncomputable def restrict (φ : PropForm ν) : PropForm ν :=
  φ.bind (fun v => if v ∈ PropFun.semVars ⟦φ⟧ then .var v else .fls)

theorem vars_restrict (φ : PropForm ν)
  : vars φ.restrict = PropFun.semVars ⟦φ⟧
  := by
  simp [restrict, vars_bind]
  ext v
  simp
  constructor
  · rintro ⟨a,h1,h2⟩
    split at h2
      <;> simp at h2; cases h2; assumption
  · intro h
    refine ⟨v,?_,?_⟩
    · apply semVars_subset_vars; exact h
    · split <;> simp

@[simp] theorem satisfies_restrict (φ : PropForm ν) (τ : PropAssignment ν)
  : τ ⊨ φ.restrict ↔ τ ⊨ φ
  := by
  simp [restrict]
  rw [← PropFun.satisfies_mk, ← PropFun.satisfies_mk]
  apply PropFun.agreeOn_semVars
  intro v h
  simp at h
  simp [PropAssignment.preimage, h]

end PropForm

namespace PropFun

variable [DecidableEq ν]

noncomputable def pmap (φ : PropFun ν)
      (f : (v : ν) → v ∈ φ.semVars → ν') : PropFun ν' :=
  φ.elim (fun ψ hψ =>
      ⟦ ψ.restrict.pmap (fun v h =>
          f v (by simp [PropForm.vars_restrict, hψ] at h; exact h)
      ) ⟧
    ) (by
    intro a b ha hb
    ext τ
    simp
    let τ' : PropAssignment ν := fun v => if h : v ∈ φ.semVars then τ (f v h) else false
    iterate 2 (
      rw [satisfies_mk, PropForm.satisfies_pmap τ', PropForm.satisfies_restrict]
    )
    rw [← satisfies_mk, ← satisfies_mk, ha, hb]
    iterate 2 (
      rintro ⟨v,h⟩
      simp [PropForm.vars_restrict, ha, hb] at h
      simp [h]
    ))

theorem semVars_pmap [DecidableEq ν'] (φ) (f : (v : ν) → v ∈ φ.semVars → ν')
  : semVars (pmap φ f) ⊆ φ.semVars.attach.image fun ⟨v,h⟩ => f v h
  := by
  have ⟨φ,hφ⟩ := φ.exists_rep; cases hφ
  intro v
  simp [pmap, Quotient.elim_mk]
  intro hv
  have := PropForm.semVars_subset_vars _ hv; clear hv
  have := PropForm.vars_pmap _ _ this
  simp at this
  rcases this with ⟨a,h,eq⟩
  rw [PropForm.vars_restrict] at h
  exact ⟨a,h,eq⟩

theorem satisfies_pmap [DecidableEq ν]
    (φ) (f : (v : ν) → v ∈ φ.semVars → ν') (τ : PropAssignment ν')
    (τ' : PropAssignment ν) (h : ∀ v : φ.semVars, τ (f v v.2) = τ' v)
  : τ ⊨ φ.pmap f ↔ τ' ⊨ φ
  := by
  have ⟨φ,hφ⟩ := φ.exists_rep; cases hφ
  simp [pmap, satisfies_map, Quotient.elim_mk]
  rw [satisfies_mk, satisfies_mk]
  rw [PropForm.satisfies_pmap (ν := ν) _ ?_]
  · apply PropForm.satisfies_restrict
  · rintro ⟨v,hv⟩
    simp [PropForm.vars_restrict] at hv
    have := h ⟨v,hv⟩
    simp at this
    exact this

end PropFun


/-! ## `ofFun` -/

def PropForm.ofBool (b : Bool) : PropForm V :=
  if b then .tr else .fls

@[simp] theorem PropForm.eval_ofBool (b : Bool) : (PropForm.ofBool b).eval τ = b := by
  cases b <;> simp

/-- Any function from assignments to `Prop` over a list of variables
can be written as a `PropForm`, by truth table construction. -/
def PropForm.ofFun [DecidableEq V] (p : PropAssignment V → Bool) (L : List V) (h : ∀ v, v ∈ L) :=
  aux L (fun v h => by simp [*] at h)
where aux (rem : List V) (passn : (v : V) → ¬ v ∈ rem → Bool) : PropForm V :=
  match rem with
  | [] =>
    ofBool <| p fun v => passn v (by simp)
  | v::vs =>
    disj
      (conj (var v) (aux vs fun v' h' =>
        if h : v' = v then true  else passn v' (by simp [*, h'])))
      (conj (neg <| var v) (aux vs fun v' h' =>
        if h : v' = v then false else passn v' (by simp [*, h'])))

@[simp] theorem PropForm.eval_ofFun [DecidableEq V] {L : List V} {hc}
  : (PropForm.ofFun p L hc).eval τ = p τ
  := by
  unfold ofFun
  suffices ∀ {rem passn},
    (∀ v h, passn v h = τ v ) →
    eval τ (ofFun.aux p rem passn) = p τ
    from this (fun v h => by have := h (hc v); contradiction)
  intro rem passn ht
  induction rem with
  | nil => simp [ofFun.aux]; congr; funext v; simp [*]
  | cons head tail ih =>
    simp
    cases hhead : τ head <;> (simp; apply ih; intro v h; split <;> simp [*])

@[simp] theorem PropForm.entails_ofFun [DecidableEq V] {L : List V} {hc} (p τ)
  : τ ⊨ (PropForm.ofFun p L hc) ↔ p τ
  := by simp [SemanticEntails.entails, satisfies]

namespace PropFun

def ofFun {V : Type u} [DecidableEq V] [Fintype V]
      (p : PropAssignment V → Bool) : PropFun V :=
  Fintype.elim_elems (fun L h1 _ => ⟦ PropForm.ofFun p L h1 ⟧) (by
    intro L1 L2 h1 _ h2 _
    simp; ext; rw [satisfies_mk, satisfies_mk]
    simp [SemanticEntails.entails, PropForm.satisfies]
  )

@[simp] theorem entails_ofFun [DecidableEq V] [Fintype V] (p : PropAssignment V → Bool) (τ)
  : τ ⊨ ofFun p ↔ p τ
  := by
    simp [SemanticEntails.entails, satisfies, ofFun]
    apply Fintype.elim_elems_eq_forall (V := V)
    intro L h1 h2 h'
    rw [h']
    simp

end PropFun


/-! ### Existential Quantification -/

def PropForm.existQuant [DecidableEq ν] (φ : PropForm ν) (v : ν) : PropForm ν :=
  disj (φ.subst v .fls)
       (φ.subst v .tr)

theorem PropForm.satisfies_existQuant [DecidableEq ν] (φ : PropForm ν) (v : ν) {τ : PropAssignment ν}
  : τ ⊨ φ.existQuant v ↔ τ ⊨ φ.subst v .fls ∨ τ ⊨ φ.subst v .tr
  := by simp [existQuant]

def PropFun.subst [DecidableEq ν] (ψ : PropFun ν) (v : ν) (φ : PropFun ν) : PropFun ν :=
  ψ.lift (fun ψ => φ.lift (fun φ => ⟦ψ.subst v φ⟧) (by
      intro a b h
      ext τ
      simp
      rw [PropForm.subst_congr]
      · simp
      · apply PropFun.sound h
      )
    ) (by
    intro a b h
    ext τ
    simp
    apply iff_of_eq; congr
    ext φ
    apply PropForm.subst_congr
    · apply PropFun.sound h
    · simp
    )

theorem PropFun.satisfies_subst [DecidableEq ν] (ψ : PropFun ν)
      (v : ν) (φ : PropFun ν) (τ : PropAssignment ν)
  : τ ⊨ ψ.subst v φ ↔ τ.set v (τ ⊨ φ) ⊨ ψ := by
  have ⟨ψ,hψ⟩ := ψ.exists_rep; cases hψ
  have ⟨φ,hφ⟩ := φ.exists_rep; cases hφ
  simp [subst]; rw [satisfies_mk, satisfies_mk]
  rw [PropForm.satisfies_subst]
  rfl

open PropForm in
def PropFun.existQuant [DecidableEq ν] (φ : PropFun ν) (v : ν) : PropFun ν :=
    (φ.subst v ⊥)
  ⊔ (φ.subst v ⊤)

theorem PropFun.satisfies_existQuant [DecidableEq ν] (φ : PropFun ν) (v : ν) (τ : PropAssignment ν)
  : τ ⊨ φ.existQuant v ↔ ∃ b, τ.set v b ⊨ φ := by
  simp [existQuant, satisfies_subst]

theorem PropFun.existQuant_comm [DecidableEq ν] (φ : PropFun ν) (v₁ v₂ : ν)
  : (φ.existQuant v₁ |>.existQuant v₂) = (φ.existQuant v₂ |>.existQuant v₁)
  := by
  if h' : v₁ = v₂ then
    cases h'; rfl
  else
  ext τ
  simp [existQuant, satisfies_disj, satisfies_subst]
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
  simp [mem_semVars, existQuant, satisfies_subst]
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
  := by
  simp [invOption]
  intro h
  constructor
  · exact Multiset.mem_of_find?_eq_some _ h
  · have := Multiset.find?_some _ h
    simp at this
    rw [this]

/-- Kind of a strange theorem but I use it later... -/
theorem PropFun.invImage_setManyMap_map_idem (f : ν → ν') (h : f.Injective) [DecidableEq ν'] [Fintype ν]
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

theorem PropFun.invImage_setManyMap_of_map (f : ν → ν') (h : f.Injective) [DecidableEq ν'] [Fintype ν]
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
