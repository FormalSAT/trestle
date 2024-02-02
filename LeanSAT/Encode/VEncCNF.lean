/- Copyright (c) the LeanSAT contributors.

Authors: James Gallicchio
-/

import LeanSAT.Encode.EncCNF
import Mathlib.Tactic.LiftLets

/-! ## Verified Encodings

This file defines `VEncCNF`,
the main type for building *verified* encodings to CNF.
This augments the regular `EncCNF` with the ability to specify
and verify what a particular `EncCNF` value actually encodes.
-/

namespace LeanSAT.Encode

open Model PropFun EncCNF

namespace EncCNF

variable [LitVar L ν] [Fintype ν]

def satisfiesProp (e : EncCNF L α) (P : PropFun ν) : Prop :=
  aux e.1
where aux (e' : StateM _ α) :=
  ∀ s,
    let s' := (e' s).2
    s'.vMap = s.vMap ∧
    s'.assumeVars = s.assumeVars ∧
    s'.interp = (s.interp ⊓ ((s.assumeVars)ᶜ ⇨ P))

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

@[simp] theorem satisfiesProp_pure (a : α) : satisfiesProp (pure a : EncCNF L α) ⊤ := by
  intro s; simp [Pure.pure, StateT.pure]

end EncCNF

def VEncCNF (L) [LitVar L ν] [Fintype ν] (α : Type u) (P : PropFun ν) :=
  { e : EncCNF L α // e.satisfiesProp P }

namespace VEncCNF

variable {L} [LitVar L ν] [Fintype ν]

instance : CoeHead (VEncCNF L α P) (EncCNF L α) := ⟨(·.1)⟩

def mapProp {P P' : PropFun ν} (h : P = P') : VEncCNF L α P → VEncCNF L α P' :=
  fun ⟨e,he⟩ => ⟨e, h ▸ he⟩

def newCtx (name : String) (inner : VEncCNF L α P) : VEncCNF L α P :=
  ⟨EncCNF.newCtx name inner, inner.2⟩

def pure (a : α) : VEncCNF L α ⊤ := ⟨Pure.pure a, by
    intro s; simp [Pure.pure, StateT.pure]⟩

def addClause [DecidableEq ν] (C : Clause L) : VEncCNF L Unit C :=
  ⟨EncCNF.addClause C, by
    intro s
    generalize he : (EncCNF.addClause C).1 s = e
    rcases e with ⟨_,s'⟩
    simp [EncCNF.addClause] at he; cases he
    simp; simp [LawfulState.addClause, State.addClause]
    ⟩

/-- runs `e`, adding `ls` to each generated clause -/
def unlessOneOf [LawfulLitVar L ν] (ls : Array L) (ve : VEncCNF L α P)
    : VEncCNF L α ((Cnf.not ls) ⇨ P) :=
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
    : VEncCNF L α ((Cnf.all ls) ⇨ P) :=
  unlessOneOf (ls.map (- ·)) e |>.mapProp (by
    ext τ
    simp [Clause.satisfies_iff, Array.mem_def]
  )

set_option pp.proofs.withType false in
def withTemps [DecidableEq ν] [Fintype ν] (n) {P : PropFun (ν ⊕ Fin n)}
    (ve : VEncCNF (WithTemps L n) α P) :
    VEncCNF L α (P.existsInv Sum.inl) :=
  ⟨EncCNF.withTemps _ ve.1, by
    intro ls_pre ls_post'
    -- give various expressions names and specialize hypotheses
    have def_ls_post : ls_post' = Prod.snd _ := rfl
    generalize ls_post' = ls_post at *; clear ls_post'
    generalize def_ls_post_pair : (EncCNF.withTemps n ve.1).1 ls_pre = ls_post_pair
      at def_ls_post
    unfold EncCNF.withTemps at def_ls_post_pair
    simp (config := {zeta := false}) at def_ls_post_pair
    lift_lets at def_ls_post_pair
    extract_lets vMap vMapInj assumeVars at def_ls_post_pair
    split at def_ls_post_pair; next a ls_post_temps def_pair =>
    generalize_proofs h
    subst def_ls_post_pair
    simp at def_ls_post; clear vMap assumeVars
    generalize def_ls_pre_temps : LawfulState.withTemps ls_pre = ls_pre_temps
    rw [def_ls_pre_temps] at def_pair
    -- extract relationship between ls_pre_temps and ls_post_temps
    have ls_temps_nextVar := ve.1.2 ls_pre_temps
    simp [def_pair] at ls_temps_nextVar
    have ls_temps_satisfies := ve.2 ls_pre_temps
    simp [def_pair] at ls_temps_satisfies
    clear def_pair
    rcases ls_temps_satisfies with ⟨hvmap, hassume, h⟩
    sorry
  ⟩

def bind (e1 : VEncCNF L α P) (e2 : α → VEncCNF L β Q) : VEncCNF L β (P ⊓ Q) :=
  VEncCNF.mapProp (show P ⊓ (Q ⊓ ⊤) = P ⊓ Q by simp)
    ⟨ do let a ← e1; return ← e2 a
    , by
      apply bind_satisfiesProp _ _ e1.2
      intro s
      apply bind_satisfiesProp _ _ (e2 _).2
      simp [satisfiesProp, satisfiesProp.aux, Pure.pure, StateT.pure]
    ⟩

def seq (e1 : VEncCNF L Unit P) (e2 : VEncCNF L β Q) : VEncCNF L β (P ⊓ Q) :=
  bind e1 (fun () => e2)


def for_all (arr : Array α) {P : α → PropFun ν} (f : (a : α) → VEncCNF L Unit (P a))
  : VEncCNF L Unit (.all (arr.toList.map P)) :=
  ⟨ arr.foldlM (fun () x => f x) ()
  , by
    rcases arr with ⟨L⟩
    rw [Array.foldlM_eq_foldlM_data]
    unfold all
    simp
    induction L with
    | nil   => aesop
    | cons hd tl ih =>
      simp
      apply bind_satisfiesProp
      · apply (f hd).2
      · aesop⟩

-- Cayden TODO: Unit could possibly made to be β instead? Generalize later.
-- One would think that P could be of type {P : PropFun ν}. But Lean timed out synthesizing that
def guard (p : Prop) [Decidable p] {P : p → PropFun ν} (f : (h : p) → VEncCNF L Unit (P h))
  : VEncCNF L Unit (if h : p then P h else ⊤) :=
  ⟨ do if h : p then f h
  , by
    by_cases h : p <;> simp [h]
    exact (f h).2⟩

def ite (p : Prop) [Decidable p] {P : p → PropFun ν} {Q : ¬p → PropFun ν}
    (f : (h : p) → VEncCNF L Unit (P h))
    (g : (h : ¬p) → VEncCNF L Unit (Q h))
  : VEncCNF L Unit (if h : p then P h else Q h) :=
  ⟨ if h : p then f h
             else g h
  , by
    by_cases h : p <;> simp [h]
    · exact (f h).2
    · exact (g h).2⟩

def andImplyOr [LawfulLitVar L ν] [DecidableEq ν] (hyps : Array L) (conc : Array L)
  : VEncCNF L Unit (.all (hyps.toList.map LitVar.toPropFun)
                    ⇨ .any (conc.toList.map LitVar.toPropFun)) :=
  addClause (hyps.map LitVar.negate ++ conc)
  |> mapProp (by
    ext τ
    simp [Clause.satisfies_iff]
    constructor
    · aesop
    · intro h
      by_cases h' : ∀ a ∈ hyps.data, τ ⊨ LitVar.toPropFun a
      · aesop
      · aesop)

def andImply [LawfulLitVar L ν] [DecidableEq ν] (hyps : Array L) (conc : L)
  : VEncCNF L Unit (.all (hyps.toList.map LitVar.toPropFun) ⇨ conc) :=
  andImplyOr hyps #[conc]
  |> mapProp (by simp [any])

def implyOr [LawfulLitVar L ν] [DecidableEq ν] (hyp : L) (conc : Array L)
  : VEncCNF L Unit (hyp ⇨ .any (conc.toList.map LitVar.toPropFun)) :=
  andImplyOr #[hyp] conc
  |> mapProp (by simp [all])

def orImplyOr [LawfulLitVar L ν] [DecidableEq ν] (hyps : Array L) (conc : Array L)
  : VEncCNF L Unit (.any (hyps.toList.map LitVar.toPropFun)
                    ⇨ .any (conc.toList.map LitVar.toPropFun)) :=
  for_all hyps (fun hyp => andImplyOr #[hyp] conc)
  |> mapProp (by
    ext τ
    simp [Clause.satisfies_iff]
  )

def orImply [LawfulLitVar L ν] [DecidableEq ν] (hyps : Array L) (conc : L)
  : VEncCNF L Unit (.any (hyps.toList.map LitVar.toPropFun) ⇨ conc) :=
  orImplyOr hyps #[conc]
  |> mapProp (by simp [any])

def andImplyAnd [LawfulLitVar L ν] [DecidableEq ν] (hyps : Array L) (concs : Array L)
  : VEncCNF L Unit (.all (hyps.toList.map LitVar.toPropFun)
                    ⇨ .all (concs.toList.map LitVar.toPropFun)) :=
  for_all concs (fun conc => andImplyOr hyps #[conc])
  |> mapProp (by
    ext τ
    simp [Clause.satisfies_iff]
    aesop
  )

def implyAnd [LawfulLitVar L ν] [DecidableEq ν] (hyp : L) (conc : Array L)
  : VEncCNF L Unit (hyp ⇨ .all (conc.toList.map LitVar.toPropFun)) :=
  andImplyAnd #[hyp] conc
  |> mapProp (by simp [all])

def orImplyAnd [LawfulLitVar L ν] [DecidableEq ν] (hyps : Array L) (concs : Array L)
  : VEncCNF L Unit (.any (hyps.toList.map LitVar.toPropFun)
                    ⇨ .all (concs.toList.map LitVar.toPropFun)) :=
  for_all hyps (fun hyp =>
    for_all concs (fun conc =>
      andImplyOr #[hyp] #[conc]
    )
  )
  |> mapProp (by
    ext τ
    simp [Clause.satisfies_iff]
    aesop
  )


def defConj [LawfulLitVar L ν] [DecidableEq ν] (v : L) (vs : Array L)
  : VEncCNF L Unit (.biImpl v (.all <| vs.toList.map LitVar.toPropFun)) :=
  seq (implyAnd v vs) (andImply vs v)
  |> mapProp (by simp [Model.PropFun.biImpl_eq_impls])

def defDisj [LawfulLitVar L ν] [DecidableEq ν] (v : L) (vs : Array L)
  : VEncCNF L Unit (.biImpl v (.any <| vs.toList.map LitVar.toPropFun)) :=
  seq (implyOr v vs) (orImply vs v)
  |> mapProp (by simp [Model.PropFun.biImpl_eq_impls])
