/- Copyright (c) the LeanSAT contributors.

Authors: James Gallicchio
-/

import LeanSAT.Encode.EncCNF

/-! # Verified Encodings

This file defines `VEncCNF`,
the main type for building *verified* encodings to CNF.
This augments the regular `EncCNF` with the ability to specify
and verify what a particular `EncCNF` value actually encodes.
-/

namespace LeanSAT.Encode

open Model PropFun EncCNF

def EncCNF.satisfiesProp [LitVar L ν] (e : EncCNF L α) (P : PropFun ν) : Prop :=
  ∀ s,
    let (a,s') := (e.1 s)
    s'.vMap = s.vMap ∧
    s'.assumeVars = s.assumeVars ∧
    s'.interp = (s.interp ⊓ ((s.assumeVars.toPropFun)ᶜ ⇨ P))

def VEncCNF (L : Type u) [LitVar L ν] (α : Type u) (P : PropFun ν) :=
  { e : EncCNF L α // e.satisfiesProp P }

namespace VEncCNF

variable {L} [LitVar L ν]

instance : CoeHead (VEncCNF L α P) (EncCNF L α) := ⟨(·.1)⟩

def mapProp {P P' : PropFun ν} (h : P = P') : VEncCNF L α P → VEncCNF L α P' :=
  fun ⟨e,he⟩ => ⟨e, h ▸ he⟩

def newCtx (name : String) (inner : VEncCNF L α P) : VEncCNF L α P :=
  ⟨EncCNF.newCtx name inner, inner.2⟩

def addClause [DecidableEq ν] (C : Clause L) : VEncCNF L Unit (C.toPropFun) :=
  ⟨EncCNF.addClause C, by
    intro s
    generalize he : (EncCNF.addClause C).1 s = e
    rcases e with ⟨_,s'⟩
    simp
    simp [EncCNF.addClause] at he; cases he; simp
    ext τ
    simp [EncCNF.LawfulState.interp]
    simp [PropFun.satisfies_invImage]
    have : ∀ {_ _ _}, _ := @PropFun.invImage_setManyMap_map_idem (f := s.1.vMap) (h := s.vMapInj) (τ := τ)
    constructor
    · rintro ⟨τ',h1,h2⟩
      refine ⟨⟨τ',h1⟩,?_⟩
      rw [this] at h2
      rcases h2 with (h2|h2)
        <;> simp [h2]
    · rintro ⟨⟨τ',h1⟩,h2⟩
      refine ⟨τ',?_⟩
      simp [*]
      by_cases τ ⊨ s.assumeVars.toPropFun
      · simp [*]
      · simp [*]
    ⟩

/-- runs `e`, adding `ls` to each generated clause -/
def unlessOneOf [LawfulLitVar L ν] (ls : Array L) (ve : VEncCNF L α P)
    : VEncCNF L α ((Cnf.not ls).toPropFun ⇨ P) :=
  ⟨EncCNF.unlessOneOf ls ve, by
    -- TODO: terrible, slow proof
    intro s
    rcases ve with ⟨ve,hve⟩
    simp [StateT.run] at hve ⊢
    generalize he : (EncCNF.unlessOneOf ls ve).1 s = e
    rcases e with ⟨a,s'⟩; dsimp
    simp [EncCNF.unlessOneOf] at he
    generalize hsprev : EncCNF.LawfulState.mk .. = sprev at he
    generalize he' : ve.1 sprev = e
    rcases e with ⟨a',s''⟩
    have := hve sprev; clear hve
    simp [he'] at he this
    clear he'
    cases he; cases hsprev
    rcases s'' with ⟨⟨s''a,s''b,s''c⟩,s''d,s''e,s''f⟩
    rcases s with ⟨⟨sa,sb,sc⟩,sd,se,sf⟩
    simp_all
    cases this
    subst_vars
    simp [EncCNF.LawfulState.interp] at *
    simp_all
    clear! s''f s''e s''d sf se sd
    ext τ
    simp
    apply Function.const
    clear! sa sb sc s''a s''b
    push_neg
    exact and_imp⟩

def assuming [LawfulLitVar L ν] (ls : Array L) (e : VEncCNF L α P)
    : VEncCNF L α ((Cnf.all ls).toPropFun ⇨ P) :=
  unlessOneOf (ls.map (- ·)) e |>.mapProp (by
    ext τ
    simp [Clause.satisfies_iff, Array.mem_def]
  )

noncomputable def withTemps.prop [DecidableEq ν] [Fintype ν] (P : PropFun (ν ⊕ Fin n)) :=
  P.invImage ⟨Sum.inl,Sum.inl_injective⟩ Finset.univ

--theorem withTemps.prop_of_

set_option pp.proofs.withType false in
def withTemps [DecidableEq ν] [Fintype ν] (n) {P : PropFun (ν ⊕ Fin n)}
    (e : VEncCNF (WithTemps L n) α P) :
    VEncCNF L α (withTemps.prop P) :=
  ⟨EncCNF.withTemps _ e.1, by
    intro s
    rcases e with ⟨e,he⟩
    generalize hs' : (EncCNF.withTemps n e).1 s = res
    rcases res with ⟨a,s'⟩
    simp [EncCNF.withTemps] at hs'
    simp
    split at hs'; next a s'' hs'' =>
    cases hs'
    have := he (LawfulState.withTemps s); clear he; have he := this; clear this
    rw [hs''] at he
    simp at he ⊢
    rcases s'' with ⟨⟨nv,cnf,vm,av⟩,cvlt,vmlt,vmi⟩
    simp [LawfulState.withTemps, State.withTemps, LawfulState.interp] at he
    rcases he with ⟨rfl,rfl,he⟩
    simp [LawfulState.withoutTemps, State.withoutTemps, LawfulState.interp]
    ext τ
    have : ∀ τ' : PropAssignment _, τ' ⊨ _ ↔ τ' ⊨ _ ⊓ _ :=
        fun _ => iff_of_eq <| congrArg _ he
    clear he
    simp [PropFun.satisfies_invImage] at this ⊢
    constructor
    · rintro ⟨τ',h⟩
      have := this τ'
    · rintro ⟨τ',h⟩
      sorry⟩

theorem bind_satisfiesProp (e1 : EncCNF L α) (e2 : α → EncCNF L β)
  : e1.satisfiesProp P → (∀ s, (e2 (e1.1 s).1).satisfiesProp Q) →
    (do let a ← e1.1; (e2 a).1).satisfiesProp (P ⊓ Q)
  := by
  intro s
  rcases ve1 with ⟨⟨s1,_⟩,he1⟩
  have := he1 s
  simp [Bind.bind, StateT.bind] at this ⊢
  clear he1; have he1 := this; clear this
  generalize hs' : s1 s = res' at he1 ⊢
  rcases res' with ⟨a,s'⟩
  simp at he1 ⊢
  generalize ve2 a = ve2
  rcases ve2 with ⟨⟨s2,_⟩,he2⟩
  have := he2 s'
  simp at this ⊢
  clear he2; have he2 := this; clear this
  generalize hs'' : s2 s' = res' at he2 ⊢
  rcases res' with ⟨b,s''⟩
  simp at he2 ⊢
  simp [*]
  rw [inf_assoc]; congr
  exact (himp_inf_distrib ..).symm

def seq (e1 : VEncCNF L α P) (e2 : VEncCNF L β Q) : VEncCNF L (α × β) (P ⊓ Q) :=
  ⟨ do let a ← e1; let b ← e2; return (a,b)
  , by
    apply bind_satisfiesProp
    sorry
    ⟩
