/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Trestle.Encode.EncCNF
import Trestle.Model.PropPred
import Trestle.Upstream.Iterators

/-! ## Verified Encodings

This file defines `VEncCNF`,
the main type for building *verified* encodings to CNF.
This augments the regular `EncCNF` with the ability to specify
and verify what a particular `EncCNF` value actually encodes.
-/

namespace Trestle.Encode

open Model EncCNF

/-- The verified encoding monad. -/
def VEncCNF (ν) (α : Type u) (P : PropPred ν) :=
  { e : EncCNF ν α // e.encodesProp P }

namespace VEncCNF

instance instCoeEncCNF : CoeHead (VEncCNF ν α P) (EncCNF ν α) := ⟨(·.1)⟩

theorem toICnf_equisatisfiable [IndexType ν] [LawfulIndexType ν] (v : VEncCNF ν α P) :
    (∃ τ : PropAssignment _, open PropFun in τ ⊨ v.val.toICnf.toPropFun) ↔
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
  ⟨ EncCNF.addClause C, by
    intro s
    generalize he : (EncCNF.addClause C).1 s = e
    rcases e with ⟨_,s'⟩
    simp [EncCNF.addClause] at he; cases he
    simp; simp [LawfulState.addClause, dbgTraceIfShared, State.addClause]
    ⟩

def unit (l : Literal ν) : VEncCNF ν Unit l :=
  addClause #[l] |>.mapProp (by ext τ; simp [Clause.toPropFun])

@[inline]
def withTemps {ν α : Type u} (ι : Type u) [IndexType ι] [LawfulIndexType ι]
    {P : (ι → (ν ⊕ ι)) → PropPred (ν ⊕ ι)}
    (ve : (temps : ι → (ν ⊕ ι)) → VEncCNF (ν ⊕ ι) α (P temps)) (names : Option (ι → String) := none) :
    VEncCNF ν α (fun τ => ∃ (t : PropAssignment ι), P Sum.inr (τ.extend t)) :=
  ⟨EncCNF.withTemps ι (fun m => (ve m).1) names, by
    -- this proof is about relating the states pre/post running ve
    intro ls_pre ls_post'
    unfold ls_post'; clear ls_post'
    generalize retVal_def : (EncCNF.withTemps ι (fun m => (ve m).1) _).val ls_pre = retVal
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
    have ⟨vMap_pre_post, interp_pre_post⟩ := (ve Sum.inr).prop (ls_pre.withTemps names)
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
    constructor
    · rintro ⟨σ, rfl, hσ, h⟩
      apply And.intro hσ
      use (σ.map Sum.inr)
      simp [h]
    · rintro ⟨hls, t, ht⟩
      use (τ.extend t)
      simp [ht, hls]
  ⟩

@[inline]
abbrev withTemps' {ν α : Type u} (ι : Type u) [IndexType ι] [LawfulIndexType ι] {P : PropPred (ν ⊕ ι)}
    (ve : VEncCNF (ν ⊕ ι) α P) (names : Option (ι → String) := none) :
    VEncCNF ν α (fun τ => ∃ (t : PropAssignment ι), P (τ.extend t)) :=
  withTemps ι (fun _ => ve) names

@[inline]
def withTemp {ν α : Type} {P : (ν ⊕ Unit) → PropPred (ν ⊕ Unit)}
    (ve : (temp : (ν ⊕ Unit)) → VEncCNF (ν ⊕ Unit) α (P temp)) (name : Option String := none) :
    VEncCNF ν α (fun τ => ∃ t, P (.inr ()) (τ.extend t)) :=
  withTemps Unit (fun temps => ve (temps ())) (name.map fun n _ => n)

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

/-! ### Iteration

All iteration goes through `forIn`, which encodes a constraint for every element
visited by any lawful iterator (see `Trestle.Upstream.Iterators`).
The other combinators are specializations of it with nicer specs:
* `for_all arr f` iterates over an `Array`, with spec `∀ a ∈ arr, P a τ`;
* `for_univ f` iterates over an index type, with spec `∀ i, P i τ`;
* `for_pairwise arr f` iterates over pairs `i < j`, with spec `arr.Pairwise P`;
* `for_all_pairs arr f` iterates over pairs `i ≠ j`;
* `for_all_adjacent arr f` iterates over adjacent pairs, with spec `arr.toList.IsChain P`.

For other access patterns, call `forIn` directly with an iterator, e.g.
`forIn (Iterators.filter (Iterators.pairs c) r) f`, `forIn (arr.iter.filter p) f`,
or `forIn (Iterators.adjacent (IndexType.univ ι)) f`.

`VEncCNF` cannot be the monad of a `ForIn` instance (so `for a in c do ...` can't
be written directly in `VEncCNF`), because it is not a `Monad`. The spec `P` is a
type index, and `bind` needs the spec of the continuation to be independent of the
value it receives (see `VEncCNF.bind`). `ForIn.forIn`'s generic accumulator `β`
gives no such guarantee. So `forIn` below takes the iterator generically and
runs the loop with `EncCNF.forEach`, and `LawfulForIn` tells us which elements
the loop visits.
-/

/-- Encodes `f a` for every element `a` visited by the iterator `c`,
i.e., the conjunction of the `P a` for `a ∈ elems c`.

This works over any lawful iterator, such as `Array`, `List`, ranges `[a:b]`,
`IndexType.univ ι`, `Iterators.pairs c`, `Iterators.adjacent c`, `Iterators.filter c p`,
and finite `Std.Iter`s. The loop is `EncCNF.forEach`, which does not allocate `elems c`.
-/
@[inline]
def forIn {γ : Type u} {α : Type v}
    [ForIn Id γ α] [ToList γ α] [LawfulForIn Id γ α]
    (c : γ) {P : α → PropPred ν} (f : (a : α) → VEncCNF ν Unit (P a))
  : VEncCNF ν Unit (fun τ => ∀ a ∈ toList c, P a τ) :=
  ⟨EncCNF.forEach c (f · |>.1), encodesProp_forEach c (f · |>.2)⟩

/-- Encodes `f a` for every element `a` of the array `arr`.

This is `forIn` specialized to arrays. -/
@[inline]
def for_all (arr : Array α) {P : α → PropPred ν} (f : (a : α) → VEncCNF ν Unit (P a))
  : VEncCNF ν Unit (fun τ => ∀ a ∈ arr, P a τ) :=
  forIn arr f |>.mapProp (by simp)

/-- Encodes `f i` for every element `i` of an index type `ι`, as specifed by `ι.univ` and `ForIn`. -/
@[inline]
def for_univ {ι} [IndexType ι] [LawfulIndexType ι] {P : ι → PropPred ν} (f : (i : ι) → VEncCNF ν Unit (P i))
  : VEncCNF ν Unit (fun τ => ∀ i, P i τ) :=
  forIn (IndexType.univ ι) f |>.mapProp (by simp)

/-- Encodes `f a b` for every pair of elements where `a` comes strictly before `b` in `arr`. -/
@[inline]
def for_pairwise (arr : Array α) {P : α → α → PropPred ν}
    (f : (a b : α) → VEncCNF ν Unit (P a b))
  : VEncCNF ν Unit (fun τ => arr.Pairwise (P · · τ)) :=
  forIn arr.pairs (fun p => f p.1 p.2) |>.mapProp (by
    ext τ; simp only [Pairs.toList_def, Array.coll_pairs, toList_array]
    exact List.forall_mem_pairs_iff_Pairwise (R := (P · · τ)))

/-- Encodes `f a b` for every pair of elements at distinct positions in `arr`, in either order. -/
@[inline]
def for_all_pairs (arr : Array α) {P : α → α → PropPred ν}
    (f : (a b : α) → VEncCNF ν Unit (P a b))
  : VEncCNF ν Unit (fun τ => arr.Pairwise (fun a b => P a b τ ∧ P b a τ)) :=
  for_pairwise arr (fun a b => seq (f a b) (f b a))

/-- Encodes `f a b` for every pair of adjacent elements in `arr`. -/
@[inline]
def for_all_adjacent (arr : Array α) {P : α → α → PropPred ν}
    (f : (a b : α) → VEncCNF ν Unit (P a b))
  : VEncCNF ν Unit (fun τ => arr.toList.IsChain (P · · τ)) :=
  forIn arr.adjacent (fun p => f p.1 p.2) |>.mapProp (by
    ext τ; simp only [Adjacent.toList_def, Array.coll_adjacent, toList_array]
    exact List.forall_mem_adjacentPairs_iff_IsChain (R := (P · · τ)))

def guard (p : Prop) [Decidable p] {P : p → PropPred ν}
      (f : (h : p) → VEncCNF ν Unit (P h))
  : VEncCNF ν Unit (fun τ => ∀ (h : p), P h τ) :=
  ⟨ do if h : p then f h
  , by
    by_cases h : p
    · simp [h]; simpa using (f h).2
    · simp [h]; apply encodesProp_pure
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
  : VEncCNF ν Unit (fun τ => (∀ h ∈ hyps, τ ⊨ ↑h) → τ ⊨ ↑conc) :=
  addClause (hyps.map LitVar.negate ++ conc)
  |> mapProp (by
    ext τ
    simp [Clause.satisfies_iff]
    constructor
    · aesop
    · intro h
      by_cases h' : ∀ a ∈ hyps, τ ⊨ LitVar.toPropFun a
      · aesop
      · aesop)

def andImply (hyps : Array (Literal ν)) (conc : Literal ν)
  : VEncCNF ν Unit (fun τ => (∀ h ∈ hyps, τ ⊨ ↑h) → τ ⊨ ↑conc) :=
  andImplyOr hyps #[conc]
  |> mapProp (by simp)

def implyOr (hyp : Literal ν) (conc : Array (Literal ν))
  : VEncCNF ν Unit (fun τ => τ ⊨ ↑hyp → τ ⊨ ↑conc) :=
  andImplyOr #[hyp] conc
  |> mapProp (by simp)

def orImplyOr (hyps : Array (Literal ν)) (conc : Array (Literal ν))
  : VEncCNF ν Unit (fun τ => τ ⊨ ↑hyps → τ ⊨ ↑conc) :=
  for_all hyps (andImplyOr #[·] conc)
  |> mapProp (by simp [Clause.satisfies_iff (C := hyps)])

def orImply (hyps : Array (Literal ν)) (conc : Literal ν)
  : VEncCNF ν Unit (fun τ => (τ ⊨ ↑hyps) → τ ⊨ ↑conc) :=
  orImplyOr hyps #[conc]
  |> mapProp (by simp)

def andImplyAnd (hyps : Array (Literal ν)) (concs : Array (Literal ν))
  : VEncCNF ν Unit (fun τ => (∀ h ∈ hyps, τ ⊨ ↑h) → (∀ c ∈ concs, τ ⊨ ↑c)) :=
  for_all concs (andImplyOr hyps #[·])
  |> mapProp (by ext τ; simp; grind)

def implyAnd (hyp : Literal ν) (concs : Array (Literal ν))
  : VEncCNF ν Unit (fun τ => (τ ⊨ ↑hyp) → (∀ c ∈ concs, τ ⊨ ↑c)) :=
  andImplyAnd #[hyp] concs
  |> mapProp (by simp)

def orImplyAnd (hyps : Array (Literal ν)) (concs : Array (Literal ν))
  : VEncCNF ν Unit (fun τ => (∃ h ∈ hyps, τ ⊨ ↑h) → (∀ c ∈ concs, τ ⊨ ↑c)) :=
  for_all hyps (fun hyp =>
    for_all concs (fun conc =>
      andImplyOr #[hyp] #[conc]
    )
  ) |> mapProp (by ext τ; simp; grind)

def imply (v₁ v₂ : Literal ν)
  : VEncCNF ν Unit (· ⊨ ↑v₁ ⇨ ↑v₂) :=
  andImplyOr #[v₁] #[v₂]
  |> mapProp (by simp)

/-- Adds a constraint saying that `v1` is equivalent to `v2`. -/
def biImpl (v₁ v₂ : Literal ν)
  : VEncCNF ν Unit (fun τ => τ ⊨ ↑v₁ ↔ τ ⊨ ↑v₂) :=
  seq (imply v₁ v₂) (imply v₂ v₁)
  |> mapProp (by grind [LitVar.mk_toPropForm, satisfies_impl])

/-- Defines a literal `v` as a conjunction of other literals `vs`. -/
def defConj (v : Literal ν) (vs : Array (Literal ν))
  : VEncCNF ν Unit (fun τ => τ ⊨ ↑v ↔ (∀ v ∈ vs, τ ⊨ ↑v)) :=
  seq (implyAnd v vs) (andImply vs v)
  |> mapProp (by grind)

/-- Defines a literal `v` as a disjunction of other literals `vs`. -/
def defDisj (v : Literal ν) (vs : Array (Literal ν))
  : VEncCNF ν Unit (fun τ => τ ⊨ ↑v ↔ (τ ⊨ ↑vs)) :=
  seq (implyOr v vs) (orImply vs v)
  |> mapProp (by grind)

def castVar (h : ν₁ = ν₂) (ve : VEncCNF ν₁ α P) : VEncCNF ν₂ α (h ▸ P) :=
  match ve with
  | ⟨e,he⟩ => ⟨h ▸ e, by subst h; exact he⟩

end /- section -/

end VEncCNF /- namespace -/

end Trestle.Encode /- namespace -/
