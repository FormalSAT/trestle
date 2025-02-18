/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Trestle.Encode.EncCNF
import Trestle.Model.PropPred
import Mathlib.Tactic.LiftLets

/-! ## Verified Encodings

This file defines `VEncCNF`,
the main type for building *verified* encodings to CNF.
This augments the regular `EncCNF` with the ability to specify
and verify what a particular `EncCNF` value actually encodes.
-/

namespace Trestle.Encode

open Model EncCNF

namespace EncCNF

/-- `e` encodes proposition `P` -/
def encodesProp (e : EncCNF ν α) (P : PropPred ν) : Prop :=
  aux e.1
where aux (e' : StateM _ α) :=
  ∀ s,
    let s' := (e' s).2
    s'.vMap = s.vMap ∧
    -- TODO(JG): should we weaken this to equisatisfiability?
    ∀ (τ : PropAssignment ν), s'.interp τ ↔ s.interp τ ∧ (open PropPred in τ ⊨ P)

/-- If `e` encodes `P`, then `P` is satisfiable iff `e.toICnf` is satisfiable -/
theorem encodesProp_equisatisfiable [IndexType ν] [LawfulIndexType ν]
          (e : EncCNF ν α) (P : PropPred ν) (h : encodesProp e P)
  : (∃ τ : PropAssignment ν   , open PropPred in τ ⊨ P) ↔
    (∃ τ : PropAssignment IVar, open PropFun  in τ ⊨ e.toRichCnf.toICnf.toPropFun) := by
  simp [EncCNF.toRichCnf, run, StateT.run]
  generalize hls : LawfulState.new' _ _ = ls
  have := h ls
  generalize hls' : e.1 ls = ls' at this
  rcases ls' with ⟨a,ls'⟩
  simp only at this ⊢
  rcases this with ⟨-,h3⟩
  rw [←hls] at h3
  simp [LawfulState.new', State.new, Clause.toPropFun] at h3
  clear hls' hls
  simp_rw [← h3]
  simp [LawfulState.interp]
  aesop

attribute [aesop unsafe apply] le_trans

theorem bind_encodesProp (e1 : EncCNF ν α) (f : α → EncCNF ν β)
  : e1.encodesProp P → (∀ s, (f (e1.1 s).1).encodesProp Q) →
    (e1 >>= f).encodesProp (P ⊓ Q)
  := by
  intro hP hQ s
  simp [encodesProp, encodesProp.aux] at hP hQ
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
  open PropPred in --necessary because simp doesn't simp thru scoped instances not in scope
  simp at hP hQ ⊢
  -- once again we ♥ aesop
  aesop

@[simp] theorem encodesProp_pure (a : α) : encodesProp (pure a : EncCNF ν α) ⊤ := by
  intro s; simp [Pure.pure, StateT.pure]

theorem encodesProp_map (e1 : EncCNF ν α) (f : α → β)
  : (f <$> e1).encodesProp P ↔ e1.encodesProp P
  := by
  constructor
  · intro h s
    specialize h s
    intro s'
    extract_lets s'' at h
    suffices s' = s'' by rw [this]; exact h
    rfl
  · intro h
    rw [map_eq_pure_bind]
    rw [show P = P ⊓ ⊤ by simp]
    apply bind_encodesProp
    · exact h
    simp

end EncCNF

/-- The verified encoding monad. -/
def VEncCNF (ν) (α : Type u) (P : PropPred ν) :=
  { e : EncCNF ν α // e.encodesProp P }

namespace VEncCNF

instance : CoeHead (VEncCNF ν α P) (EncCNF ν α) := ⟨(·.1)⟩

theorem toICnf_equisatisfiable [IndexType ν] [LawfulIndexType ν] (v : VEncCNF ν α P) :
    (∃ τ : PropAssignment _, open PropFun in τ ⊨ v.val.toRichCnf.toICnf.toPropFun) ↔
    (∃ τ : PropAssignment ν, open PropPred in τ ⊨ P)
  := by
  rw [v.val.encodesProp_equisatisfiable _ v.property]

def mapProp {P P' : PropPred ν} (h : P = P') : VEncCNF ν α P → VEncCNF ν α P' :=
  fun ⟨e,he⟩ => ⟨e, h ▸ he⟩

def newCtx (name : String) (inner : VEncCNF ν α P) : VEncCNF ν α P :=
  ⟨ EncCNF.newCtx name inner
  , by
    simp [EncCNF.newCtx]
    rw (occs := .pos [2]) [show P = ⊤ ⊓ (P ⊓ ⊤) by simp]
    apply bind_encodesProp
    · intro s; simp [addComment]
    rintro -
    apply bind_encodesProp
    · apply inner.prop
    intro s; rw [encodesProp_map]; clear s
    intro s; simp [addComment]
  ⟩

open PropPred in
protected def pure (a : α) : VEncCNF ν α ⊤ :=
  ⟨ Pure.pure a
  , by intro s; simp [Pure.pure, StateT.pure]⟩

def addClause (C : Clause (Literal ν)) : VEncCNF ν Unit C :=
  ⟨EncCNF.addClause C, by
    intro s
    generalize he : (EncCNF.addClause C).1 s = e
    rcases e with ⟨_,s'⟩
    simp [EncCNF.addClause, dbgTraceIfShared] at he; cases he
    simp; simp [SemanticEntails.entails, himp, compl, LawfulState.addClause, dbgTraceIfShared, State.addClause]
    ⟩

open PropFun in
set_option pp.proofs.withType false in
@[inline]
def withTemps (ι) [IndexType ι] [LawfulIndexType ι] {P : PropAssignment (ν ⊕ ι) → Prop}
    (ve : VEncCNF (ν ⊕ ι) α P) :
    VEncCNF ν α (fun τ => ∃ σ, τ = σ.map Sum.inl ∧ P σ) :=
  ⟨EncCNF.withTemps _ ve.1, by
    -- this proof is about relating the states pre/post running ve
    intro ls_pre ls_post'
    unfold ls_post'; clear ls_post'
    generalize retVal_def : (EncCNF.withTemps ι ve.val).val ls_pre = retVal
    -- let's get through a nasty match in withTemps
    dsimp [EncCNF.withTemps] at retVal_def
    split at retVal_def; next a ls_post_withTemps pre_to_post =>
    generalize ls_post_def : ls_post_withTemps.withoutTemps _ _ _ = ls_post at retVal_def
    subst retVal; dsimp
    -- now we can prove the first goal
    constructor
    · simp [← ls_post_def]
    case right =>
    -- ve's correctness property gives us some facts from pre_to_post
    have ⟨vMap_pre_post, interp_pre_post⟩ := ve.prop ls_pre.withTemps
    rw [pre_to_post] at vMap_pre_post interp_pre_post
    -- the second goal relies on the interpretation of withoutTemps
    rw [← ls_post_def]; clear! ls_post
    rw [LawfulState.interp_withoutTemps]
    -- hypothesis for `LawfulState.interp_withoutTemps`
    case h =>
      ext v
      simp only [LawfulState.vMap_withTemps] at vMap_pre_post
      simp only [vMap_pre_post, Function.comp_apply, State.withTemps.vMap]
    -- In this branch we don't need vMap_pre_post and can rewrite interp_pre_post
    simp only [interp_pre_post]; clear interp_pre_post vMap_pre_post
    -- Now we can use some simp lemmas about `interp (withTemps _)`
    simp only [LawfulState.interp_withTemps, PropPred.satisfies_def]
    -- the rest is just reasoning about assignments
    intro τ
    aesop
  ⟩

protected def bind (e1 : VEncCNF ν α P) (e2 : α → VEncCNF ν β Q) : VEncCNF ν β (P ⊓ Q) :=
  VEncCNF.mapProp (show P ⊓ (Q ⊓ ⊤) = (P ⊓ Q) by simp)
    ⟨ do let a ← e1; return ← e2 a
    , by
      simp
      apply bind_encodesProp _ _ e1.2
      intro s
      exact (e2 (e1.1.1 s).1).2
    ⟩

/-- Sequences two encodings together, i.e. a conjunction of the encodings.

For sequencing many encodings together, see `seq[ ... ]` syntax
-/
def seq (e1 : VEncCNF ν Unit P) (e2 : VEncCNF ν β Q) : VEncCNF ν β (fun τ => P τ ∧ Q τ) :=
  VEncCNF.bind e1 (fun () => e2)

scoped syntax "seq[ " term,+ " ]" : term

-- TODO(JG): this inserts unnecessary ⊤ propfuns
macro_rules
| `(seq[$as:term,*]) => do
  as.getElems.foldrM (β := Lean.TSyntax `term)
    (fun a acc => `(seq $a $acc))
    (← `(VEncCNF.pure ()))

@[inline]
def for_all (arr : Array α) {P : α → PropPred ν} (f : (a : α) → VEncCNF ν Unit (P a))
  : VEncCNF ν Unit (fun τ => ∀ a ∈ arr, P a τ) :=
  ⟨ arr.foldlM (fun () x => f x) (),
    by
    rcases arr with ⟨L⟩
    simp only [Array.size_toArray, List.foldlM_toArray', Array.mem_toArray]
    induction L with
    | nil   => simp; apply encodesProp_pure
    | cons hd tl ih =>
      simp
      apply bind_encodesProp
      · have := (f hd).2
        simpa using this
      · aesop⟩

-- Cayden TODO: Unit could possibly made to be β instead? Generalize later.
-- One would think that P could be of type {P : PropFun ν}. But Lean timed out synthesizing that
def guard (p : Prop) [Decidable p] {P : p → PropPred ν}
      (f : (h : p) → VEncCNF ν Unit (P h))
  : VEncCNF ν Unit (if h : p then P h else ⊤) :=
  ⟨ do if h : p then f h
  , by
    by_cases h : p
    · simp [h]; simpa using (f h).2
    · simp [h]
  ⟩

def ite (p : Prop) [Decidable p] {P : p → PropPred ν} {Q : ¬p → PropPred ν}
    (f : (h : p) → VEncCNF ν Unit (P h))
    (g : (h : ¬p) → VEncCNF ν Unit (Q h))
  : VEncCNF ν Unit (if h : p then P h else Q h) :=
  ⟨ if h : p then f h
             else g h
  , by
    by_cases h : p <;> simp [h]
    · simpa using (f h).2
    · simpa using (g h).2⟩

open PropFun in
section
def andImplyOr (hyps : Array (Literal ν)) (conc : Array (Literal ν))
  : VEncCNF ν Unit (fun τ => (∀ h ∈ hyps, τ ⊨ ↑h) → (∃ c ∈ conc, τ ⊨ ↑c)) :=
  addClause (hyps.map LitVar.negate ++ conc)
  |> mapProp (by
    ext τ
    simp [Clause.satisfies_iff, PropPred.satisfies_def]
    constructor
    · aesop
    · intro h
      by_cases h' : ∀ a ∈ hyps, τ ⊨ LitVar.toPropFun a
      · aesop
      · aesop)

def andImply (hyps : Array (Literal ν)) (conc : Literal ν)
  : VEncCNF ν Unit (fun τ => (∀ h ∈ hyps, τ ⊨ ↑h) → τ ⊨ ↑conc) :=
  andImplyOr hyps #[conc]
  |> mapProp (by simp [any])

def implyOr (hyp : Literal ν) (conc : Array (Literal ν))
  : VEncCNF ν Unit (fun τ => τ ⊨ ↑hyp → ∃ c ∈ conc, τ ⊨ ↑c) :=
  andImplyOr #[hyp] conc
  |> mapProp (by simp [all])

def orImplyOr (hyps : Array (Literal ν)) (conc : Array (Literal ν))
  : VEncCNF ν Unit (fun τ => (∃ h ∈ hyps, τ ⊨ ↑h) → (∃ c ∈ conc, τ ⊨ ↑c)) :=
  for_all hyps (fun hyp => andImplyOr #[hyp] conc)
  |> mapProp (by
    ext τ
    simp [Clause.satisfies_iff]
  )

def orImply (hyps : Array (Literal ν)) (conc : Literal ν)
  : VEncCNF ν Unit (fun τ => (∃ h ∈ hyps, τ ⊨ ↑h) → τ ⊨ ↑conc) :=
  orImplyOr hyps #[conc]
  |> mapProp (by simp [any])

def andImplyAnd (hyps : Array (Literal ν)) (concs : Array (Literal ν))
  : VEncCNF ν Unit (fun τ => (∀ h ∈ hyps, τ ⊨ ↑h) → (∀ c ∈ concs, τ ⊨ ↑c)) :=
  for_all concs (fun conc => andImplyOr hyps #[conc])
  |> mapProp (by
    ext τ
    simp [Clause.satisfies_iff]
    aesop
  )

def implyAnd (hyp : Literal ν) (concs : Array (Literal ν))
  : VEncCNF ν Unit (fun τ => τ ⊨ ↑hyp → (∀ c ∈ concs, τ ⊨ ↑c)) :=
  andImplyAnd #[hyp] concs
  |> mapProp (by simp [all])

def orImplyAnd (hyps : Array (Literal ν)) (concs : Array (Literal ν))
  : VEncCNF ν Unit (fun τ => (∃ h ∈ hyps, τ ⊨ ↑h) → (∀ c ∈ concs, τ ⊨ ↑c)) :=
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

def imply (v1 v2 : Literal ν)
  : VEncCNF ν Unit (· ⊨ ↑v1 ⇨ ↑v2) :=
  andImplyOr #[v1] #[v2]
  |> mapProp (by simp [all,any])

def biImpl (v1 v2 : Literal ν)
  : VEncCNF ν Unit (fun τ => τ ⊨ ↑v1 ↔ τ ⊨ ↑v2) :=
  seq (imply v1 v2) (imply v2 v1)
  |> mapProp (by aesop)

def defConj (v : Literal ν) (vs : Array (Literal ν))
  : VEncCNF ν Unit (fun τ => τ ⊨ ↑v ↔ (∀ v ∈ vs, τ ⊨ ↑v)) :=
  seq (implyAnd v vs) (andImply vs v)
  |> mapProp (by aesop)

def defDisj (v : Literal ν) (vs : Array (Literal ν))
  : VEncCNF ν Unit (fun τ => τ ⊨ ↑v ↔ (∃ v ∈ vs, τ ⊨ ↑v)) :=
  seq (implyOr v vs) (orImply vs v)
  |> mapProp (by aesop)

end
