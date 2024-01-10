/- Copyright (c) the LeanSAT contributors

Authors: James Gallicchio
-/

import LeanSAT.Model.PropVars

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
def PropAssignment.preimage (f : ν → PropFun ν') (τ : PropAssignment ν') : PropAssignment ν :=
  fun v => τ ⊨ f v

@[simp] theorem PropForm.satisfies_subst [DecidableEq ν] (φ : PropForm ν) (f : ν → PropForm ν') {τ : PropAssignment ν'}
  : τ ⊨ φ.subst f ↔ τ.preimage (⟦f ·⟧) ⊨ φ
  := by induction φ <;> simp [subst, PropAssignment.preimage, *]; rw [PropFun.satisfies_mk]

noncomputable def PropFun.subst [DecidableEq ν₁] (φ : PropFun ν₁) (f : ν₁ → PropFun ν₂) : PropFun ν₂ :=
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

@[simp] theorem PropFun.satisfies_subst [DecidableEq ν₁]
    (φ : PropFun ν₁) (f : ν₁ → PropFun ν₂) (τ : PropAssignment ν₂)
  : τ ⊨ φ.subst f ↔ τ.preimage f ⊨ φ := by
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
  simp [PropAssignment.preimage] at h1
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
  simp [PropAssignment.preimage]
  split
  · rw [hψ]
  · simp

theorem PropForm.satisfies_substOne [DecidableEq ν] (φ : PropForm ν) (v : ν) (ψ : PropForm ν)
        (τ : PropAssignment ν)
  : τ ⊨ φ.substOne v ψ ↔ τ.set v (τ ⊨ ψ) ⊨ φ := by
  simp [substOne]
  apply iff_of_eq; congr
  ext v
  simp [PropAssignment.preimage, PropAssignment.set]
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

@[simp] theorem PropFun.satisfies_map (f : ν → ν') (τ : PropAssignment ν') (φ : PropFun ν)
  : τ ⊨ φ.map f ↔ (τ.map f) ⊨ φ
  := by
  let ⟨ϕ,hϕ⟩ := φ.toTrunc.out
  cases hϕ
  simp [map]
  rw [satisfies_mk, satisfies_mk]
  apply PropForm.satisfies_map

theorem PropFun.semVars_map [DecidableEq ν] [DecidableEq ν']
    (f : ν → ν') (φ : PropFun ν)
  : (φ.map f).semVars ⊆ φ.semVars.image f := by
  let ⟨ϕ,hϕ⟩ := φ.toTrunc.out; cases hϕ
  intro v' hv'
  simp [mem_semVars] at hv'
  rcases hv' with ⟨τ, htrue, hfalse⟩
  have ⟨v, h, hv⟩ := PropFun.exists_semVar htrue hfalse
  simp [PropAssignment.set] at h
  split at h <;> simp_all
  use v


/-! ### `attach` and `pmap` -/

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
  φ.subst (fun v => if v ∈ PropFun.semVars ⟦φ⟧ then .var v else .fls)

theorem vars_restrict (φ : PropForm ν)
  : vars φ.restrict = PropFun.semVars ⟦φ⟧
  := by
  simp [restrict, vars_subst]
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


/-! ### `ofFun` -/

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

/-- Replace every semantic variable `v'` in `φ` with its preimage under `f`.

Useful for restricting the variable type after quantifying out a variable. -/
noncomputable def invImage [DecidableEq ν'] (f : ν ↪ ν')
      (vs : Finset ν) (φ : PropFun ν')
      (h : φ.semVars ⊆ vs.map f) : PropFun ν :=
  φ.pmap (fun v' hv' => (vs.mapEquiv f).symm ⟨v',h hv'⟩)

theorem semVars_invImage [DecidableEq ν] [DecidableEq ν'] (f : ν ↪ ν')
      (xs : Finset ν) (φ : PropFun ν') (h)
  : semVars (φ.invImage f xs h) ⊆ xs := by
  simp [invImage]
  apply Finset.Subset.trans (semVars_pmap ..)
  intro v
  simp
  rintro v' _ rfl
  simp

@[simp] def invImage.assn [DecidableEq ν] [DecidableEq ν'] (f : ν ↪ ν')
      (xs : Finset ν)
      (τ : PropAssignment ν) : PropAssignment ν' :=
  fun v' =>
    if h : v' ∈ xs.map f then
      τ ((xs.mapEquiv f).symm ⟨v',h⟩)
    else
      false

@[simp] theorem invImage.assn.map [DecidableEq ν] [DecidableEq ν'] [Fintype ν]
      (f : ν ↪ ν') (τ)
  : (invImage.assn f Finset.univ τ).map f = τ := by
  ext v
  simp; congr
  rw [← @Subtype.mk.injEq _ _ (Subtype.val _), eq_comm, Equiv.eq_symm_apply]
  rfl
  · simp

theorem satisfies_invImage [DecidableEq ν] [DecidableEq ν'] (f : ν ↪ ν')
      (xs) (φ : PropFun ν') (h)
      (τ : PropAssignment ν)
  : τ ⊨ φ.invImage f xs h ↔ invImage.assn f xs τ ⊨ φ := by
  simp [invImage]
  apply satisfies_pmap
  rintro ⟨v',hv'⟩
  replace h := h hv'
  simp at h
  simp [invImage.assn, h]

end PropFun
