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
  aux e.1
where aux (e' : StateM _ α) :=
  ∀ s,
    let s' := (e' s).2
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

set_option pp.proofs.withType false

def addClause [DecidableEq ν] (C : Clause L) : VEncCNF L Unit (C.toPropFun) :=
  ⟨EncCNF.addClause C, by
    intro s
    generalize he : (EncCNF.addClause C).1 s = e
    rcases e with ⟨_,s'⟩
    simp [EncCNF.addClause] at he; cases he
    simp; simp [LawfulState.addClause, State.addClause]
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
    simp⟩

def assuming [LawfulLitVar L ν] (ls : Array L) (e : VEncCNF L α P)
    : VEncCNF L α ((Cnf.all ls).toPropFun ⇨ P) :=
  unlessOneOf (ls.map (- ·)) e |>.mapProp (by
    ext τ
    simp [Clause.satisfies_iff, Array.mem_def]
  )

noncomputable def withTemps.prop [DecidableEq ν] [Fintype ν] (P : PropFun (ν ⊕ Fin n)) :=
  P.existQuantSet (Finset.univ.map ⟨Sum.inr,Sum.inr_injective⟩)
    |>.invImage ⟨Sum.inl,Sum.inl_injective⟩ Finset.univ (by
      apply _root_.trans; apply semVars_existQuantSet
      intro v; cases v <;> simp)

set_option pp.proofs.withType false in
def withTemps [DecidableEq ν] [Fintype ν] (n) {P : PropFun (ν ⊕ Fin n)}
    (e : VEncCNF (WithTemps L n) α P) :
    VEncCNF L α (withTemps.prop P) :=
  ⟨EncCNF.withTemps _ e.1, by
    intro s
    -- give various expressions names and specialize hypotheses
    rcases e with ⟨e,he⟩
    generalize h : (EncCNF.withTemps n e) = te
    replace h := h.symm
    simp [EncCNF.withTemps] at h
    rcases te with ⟨te,hte⟩
    rw [Subtype.mk_eq_mk] at h
    simp
    replace h := congrFun h s
    replace hte := hte s
    generalize hs''' : te s = s''' at h hte
    replace hs''' := hs'''.symm
    rcases s''' with ⟨a,s'''⟩
    simp at h hte ⊢
    clear hs''' te
    split at h; next a s'' hs'' =>
    replace he := he (LawfulState.withTemps s)
    rw [hs''] at he
    simp at he
    generalize hs''' : LawfulState.withoutTemps .. = lswt at h
    replace hs''' := hs'''.symm
    cases h
    -- we want to generalize `LawfulState.withTemps s` but need to
    -- get rid of some dependent types first
    rw [LawfulState.ext_iff] at hs'''
    simp [LawfulState.withoutTemps, State.withoutTemps] at hs'''
    clear hs''
    generalize hs' : LawfulState.withTemps s = s' at he hs'''
    replace hs' := hs'.symm
    rw [LawfulState.ext_iff] at hs'
    simp [LawfulState.withTemps, State.withTemps] at hs'
    -- now we have all the info we should need.
    simp_all
    -- we want to clear out a bunch of un-helpful values
    rcases s''' with ⟨⟨nextVar''', cnf''', vMap''', assumeVars'''⟩, cnfVars''', cnfVarsLt''', vMapInj'''⟩
    rcases hs''' with ⟨rfl,rfl,rfl,rfl⟩
    rcases s' with ⟨⟨nextVar', cnf', vMap', assumeVars'⟩, cnfVars', cnfVarsLt', vMapInj'⟩
    rcases hs' with ⟨rfl,rfl,rfl,rfl⟩
    simp [LawfulState.interp] at *
    ext τ
    have := he.2.2; rw [PropFun.ext_iff] at this
    simp [PropFun.satisfies_invImage] at this ⊢
    sorry
  ⟩

theorem bind_satisfiesProp (e1 : EncCNF L α) (f : α → EncCNF L β)
  : e1.satisfiesProp P → (∀ s, (f (e1.1 s).1).satisfiesProp Q) →
    (e1 >>= f).satisfiesProp (P ⊓ Q)
  := by
  intro hP hQ s
  simp [satisfiesProp, satisfiesProp.aux] at hP hQ
  -- specialize hypotheses to the first state `s`
  rcases e1 with ⟨e1,he1⟩
  replace hP := hP s
  replace hQ := hQ s
  simp [Bind.bind, StateT.bind] at hP hQ ⊢
  replace he1 := he1 s
  -- give name to the next state `s'`
  generalize hs' : e1 s = s' at *
  rcases s' with ⟨a,s'⟩
  simp at *
  -- give name to the next state machine
  generalize he2 : (f a) = e2 at *
  rcases e2 with ⟨e2,he2⟩
  -- specialize hypotheses to this state `s'`
  replace hQ := hQ s'
  simp at *
  -- give name to the next state `s''`
  generalize hs'' : e2 s' = s'' at *
  rcases s'' with ⟨b,s''⟩
  simp at hQ ⊢
  -- once again we ♥ aesop
  aesop

def seq (e1 : VEncCNF L α P) (e2 : VEncCNF L β Q) : VEncCNF L (α × β) (P ⊓ Q) :=
  VEncCNF.mapProp (show P ⊓ (Q ⊓ ⊤) = P ⊓ Q by simp)
    ⟨ do let a ← e1; return (a, ← e2)
    , by
      apply bind_satisfiesProp _ _ e1.2
      intro s
      apply bind_satisfiesProp _ _ e2.2
      simp [satisfiesProp, satisfiesProp.aux, pure, StateT.pure]
    ⟩
