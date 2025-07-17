/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Trestle.Encode.VEncCNF

/-! ## Tseitin Transform

This file implements a lightly optimized Tseitin encoding
of arbitrary `PropForm` formulas into CNF.

The formula is put into negation normal form first,
and top-level ∧ / top-level ∨ are collected into one
formula/clause respectively.
-/

namespace Trestle.Encode.Tseitin

open Model

inductive NegNormForm (ν : Type u)
| all (as : Array (NegNormForm ν))
| any (as : Array (NegNormForm ν))
| lit (l : Literal ν)
deriving Repr

namespace NegNormForm

def toPropForm (r : NegNormForm ν) : PropForm ν :=
  match r with
  | .all as => PropForm.all (
      as.attach.map (fun ⟨x,_h⟩ => toPropForm x)
    ).toList
  | .any as => PropForm.any (
      as.attach.map (fun ⟨x,_h⟩ => toPropForm x)
    ).toList
  | .lit l => LitVar.toPropForm l

def toPropFun (r : NegNormForm ν) : PropFun ν :=
  match r with
  | .all as => PropFun.all (as.attach.map (fun ⟨x,_h⟩ =>
      toPropFun x)).toList
  | .any as => PropFun.any (as.attach.map (fun ⟨x,_h⟩ =>
      toPropFun x)).toList
  | .lit l => LitVar.toPropFun l

def const (val : Bool) : NegNormForm ν :=
  match val with
  | true  => .all #[]
  | false => .any #[]

@[simp] theorem const_toPropFun
  : (const b : NegNormForm ν).toPropFun = if b then ⊤ else ⊥
  := by ext τ; cases b <;> simp [const, toPropFun]

def ofPropForm (neg : Bool) : PropForm ν → NegNormForm ν
| .tr => const (!neg)
| .fls => const neg
| .var v => .lit <| LitVar.mkLit _ v (!neg)
| .neg f => ofPropForm (!neg) f
| .conj a b =>
  if neg then
    .any #[ofPropForm neg a, ofPropForm neg b]
  else
    .all #[ofPropForm neg a, ofPropForm neg b]
| .disj a b =>
  if neg then
    .all #[ofPropForm neg a, ofPropForm neg b]
  else
    .any #[ofPropForm neg a, ofPropForm neg b]
| .impl a b =>
  if neg then
    .all #[ofPropForm false a, ofPropForm true b]
  else
    .any #[ofPropForm true a, ofPropForm false b]
| .biImpl a b =>
  -- TODO(JG): maybe both cases should have `all` node on top?
  if neg then
    .any #[
      .all #[ofPropForm false a, ofPropForm true b]
    , .all #[ofPropForm false b, ofPropForm true a]
    ]
  else
    .all #[
      .any #[ofPropForm true a, ofPropForm false b]
    , .any #[ofPropForm true b, ofPropForm false a]
    ]

theorem toPropFun_ofPropForm (f : PropForm ν)
  : toPropFun (ofPropForm neg f) =
      if neg then ⟦.neg f⟧ else ⟦f⟧ := by
  induction f generalizing neg
  case tr | fls | var | neg | conj | disj | impl | biImpl =>
    -- we ♥ aesop
    aesop (add norm 1 simp [ofPropForm,toPropFun,himp_eq,Array.attach])

-- compactify formulas by merging nested conjunctions and disjunctions
mutual
def conjuncts : NegNormForm ν → Array (NegNormForm ν)
| lit l => #[.lit l]
| all as => as.attach.flatMap (fun ⟨a,_h⟩ => conjuncts a)
| any as =>
  let disj := as.attach.flatMap (fun ⟨a,_h⟩ => disjuncts a)
  if h : disj.size = 1 then
    #[disj[0]]
  else
    #[.any disj]

def disjuncts : NegNormForm ν → Array (NegNormForm ν)
| lit l => #[.lit l]
| any as => as.attach.flatMap (fun ⟨a,_h⟩ => disjuncts a)
| all as =>
  let conj := as.attach.flatMap (fun ⟨a,_h⟩ => conjuncts a)
  if h : conj.size = 1 then
    #[conj[0]]
  else
    #[.all <| conj]
end

set_option maxHeartbeats 500000 in
set_option pp.proofs.withType false in
mutual
def toPropFun_all_conjuncts : (f : NegNormForm ν) → toPropFun (.all (conjuncts f)) = toPropFun f
| lit l => by simp [conjuncts, toPropFun, Array.attach, PropFun.all]
| all as => by
  have IH : ∀ a ∈ as, _ := fun a _h => toPropFun_all_conjuncts a
  rcases as with ⟨as⟩; simp only [Array.mem_toArray] at IH
  ext τ
  replace IH := open PropFun in fun a ha => congrArg (τ ⊨ ·) (IH a ha).symm
  simp [conjuncts, toPropFun, List.unattach, -List.map_subtype] at IH ⊢
  aesop
| any as => by
  unfold conjuncts
  lift_lets; intro disj
  have : toPropFun (any disj) = toPropFun (any as) := by
    have IH : ∀ a ∈ as, _ := fun a _h => toPropFun_any_disjuncts a
    rcases as with ⟨as⟩; simp only [Array.mem_toArray] at IH
    ext τ
    replace IH := open PropFun in fun a ha => congrArg (τ ⊨ ·) (IH a ha).symm
    simp [disj, disjuncts, toPropFun, List.unattach, -List.map_subtype] at IH ⊢
    aesop
  rw [← this]; clear this
  ext τ
  split_ifs with h
  · rw [Array.size_eq_one_iff] at h
    rcases h with ⟨a,h⟩
    simp [h, toPropFun]
  · simp [toPropFun]


def toPropFun_any_disjuncts : (f : NegNormForm ν) → toPropFun (.any (disjuncts f)) = toPropFun f
| lit l => by simp [disjuncts, toPropFun, Array.attach, PropFun.any]
| any as => by
  have IH : ∀ a ∈ as, _ := fun a _h => toPropFun_any_disjuncts a
  rcases as with ⟨as⟩; simp only [Array.mem_toArray] at IH
  ext τ
  replace IH := open PropFun in fun a ha => congrArg (τ ⊨ ·) (IH a ha).symm
  simp [disjuncts, toPropFun, List.unattach, -List.map_subtype] at IH ⊢
  aesop
| all as => by
  unfold disjuncts
  lift_lets; intro conj
  have : toPropFun (all conj) = toPropFun (all as) := by
    have IH : ∀ a ∈ as, _ := fun a _h => toPropFun_all_conjuncts a
    rcases as with ⟨as⟩; simp only [Array.mem_toArray] at IH
    ext τ
    replace IH := open PropFun in fun a ha => congrArg (τ ⊨ ·) (IH a ha).symm
    simp [conj, conjuncts, toPropFun, List.unattach, -List.map_subtype] at IH ⊢
    aesop
  rw [← this]; clear this
  ext τ
  split_ifs with h
  · rw [Array.size_eq_one_iff] at h
    rcases h with ⟨a,h⟩
    simp [h, toPropFun]
  · simp [toPropFun]
end

/-! Take a formula `f` into  -/
def normalize (f : NegNormForm ν) : Array (Array (NegNormForm ν)) :=
  let conjs := f.conjuncts
  conjs.map (fun
    | .lit l => #[NegNormForm.lit l]
    | .any fs => fs
    | .all fs =>
      -- this should never happen
      #[NegNormForm.all fs]
  )

open PropFun in
theorem satisfies_normalize (τ : PropAssignment ν) (f : NegNormForm ν) :
  τ ⊨ f.toPropFun ↔ ∀ c ∈ f.normalize, ∃ d ∈ c, τ ⊨ d.toPropFun := by
  rw [← toPropFun_all_conjuncts f]
  simp only [normalize]
  generalize f.conjuncts = conjs; clear f
  rcases conjs with ⟨conjs⟩
  simp [toPropFun]
  apply forall_congr'; intro a; apply imp_congr_right; intro ha
  split <;> simp [toPropFun]

end NegNormForm

open VEncCNF

attribute [local simp] NegNormForm.toPropFun

section encodeNNF

private def separateLits (A : Array (NegNormForm ν)) : Array (Literal ν) × Array (NegNormForm ν) :=
  ( A.filterMap (fun | .lit l => some l | _ => none)
  , A.filter (fun | .lit _ => false | _ => true)
  )

private theorem separateLits_mem_lits_iff {A : Array (NegNormForm ν)} {l : Literal ν}
  : l ∈ (separateLits A).1 ↔ (.lit l) ∈ A := by
  unfold separateLits; simp
  constructor
  · rintro ⟨f,f_mem,h⟩
    split at h <;> simp_all
  · intro h; refine ⟨_,h,?_⟩; simp

private theorem separateLits_mem_notLits_iff {A : Array (NegNormForm ν)} {a}
  : a ∈ (separateLits A).2 ↔ a ∈ A ∧ (∀ {l}, a ≠ .lit l) := by
  unfold separateLits; aesop

private theorem separateLits_sizeOf_le (A : Array (NegNormForm ν))
  : sizeOf (separateLits A).2.toList < 1 + sizeOf A := by
  have : List.Sublist (separateLits A).2.toList A.toList := by
    unfold separateLits; simp
  replace this := this.sizeOf_le
  simp [sizeOf, Array._sizeOf_1] at this ⊢
  omega

open PropFun

mutual
def encodeNNF_mkDefs
      (fs : Array (NegNormForm ν')) (emb : ν' ↪ ν)
  : VEncCNF (ν ⊕ Fin fs.size) Unit (fun τ => ∀ i,
      τ (Sum.inr i) → τ.map (Sum.inl ∘ emb) ⊨ (fs[i]).toPropFun) :=
  VEncCNF.for_all (Array.ofFn id) (fun i =>
    have : sizeOf (fs[i]) < sizeOf fs.toList := by
      apply List.sizeOf_lt_of_mem
      simp
    encodeNNF (ν := ν ⊕ Fin fs.size) (Sum.inr i) (emb.trans ⟨Sum.inl, Sum.inl_injective⟩) fs[i]
  ) |>.mapProp (by
    ext τ
    simp [Array.mem_def, PropAssignment.map, Function.Embedding.trans]
  )
termination_by sizeOf fs.toList

/-- Tseitin encoding in the general case creates temporaries for each clause -/
def encodeNNF
      (t : ν) (emb : ν' ↪ ν) (f : NegNormForm ν')
  : VEncCNF ν Unit (fun τ => τ t → τ ⊨ f.toPropFun.map emb) :=
  match f with
  | .lit l =>
      imply (LitVar.mkPos t) (LitVar.map emb l)
      |>.mapProp (by simp)
  | .all as =>
      -- in the `all` case we do not need new temps here!
      -- Plaisted-Greenbaum only requires `t -> f`,
      -- so for lits I can directly require `t -> all lits`,
      -- and for each subformula I can just call `encodeNNF` with `t` again!
      let separated := separateLits as
      let lits := separated.1
      let subfs := separated.2
      seq[
        implyAnd (Literal.pos t) (lits.map (LitVar.map emb))
      , for_all (Array.ofFn (n := subfs.size) id) (fun i =>
          encodeNNF t emb (subfs[i])
        )
      ] |>.mapProp (by
        ext τ
        simp [forall_swap (β := τ t = true), ← imp_and]; apply imp_congr_right
        rintro -
        constructor
        · rintro ⟨h1,h2⟩ a ha
          by_cases h : ∃ l, a = .lit l
          · rcases h with ⟨l,rfl⟩
            rw [← separateLits_mem_lits_iff] at ha
            specialize h1 _ ha
            simpa using h1
          · simp at h
            replace ha := separateLits_mem_notLits_iff.mpr ⟨ha, @h⟩
            rw [Array.mem_iff_getElem] at ha
            rcases ha with ⟨idx,hidx,ha⟩
            specialize h2 ⟨idx,hidx⟩
            rw [ha] at h2
            exact h2
        · intro h
          constructor
          · intro l hl
            rw [separateLits_mem_lits_iff] at hl
            specialize h _ hl
            simpa using h
          · rintro idx
            apply h
            refine (separateLits_mem_notLits_iff.mp ?_).1
            simp +zetaDelta
      )
  | .any as =>
      let separated := separateLits as
      let lits := separated.1
      let subfs := separated.2
      withTemps (Fin subfs.size) (
        seq[
          encodeNNF_mkDefs subfs emb
        , implyOr (Literal.pos <| Sum.inl t)
            (lits.map (LitVar.map <| Sum.inl ∘ emb) ++ Array.ofFn (Literal.pos <| Sum.inr ·))
        ]
      ) |>.mapProp (by
        ext τ
        constructor
        · rintro ⟨σ,rfl,h1,h2⟩ ht
          simp at ht h2 ⊢
          specialize h2 ht
          rcases h2 with ⟨l,⟨l',hl',rfl⟩|h2,hl⟩
          · rw [separateLits_mem_lits_iff] at hl'
            use (.lit l'), hl'
            simpa using hl
          · rcases h2 with ⟨i,rfl⟩
            simp at hl
            specialize h1 i hl
            have : subfs[i] ∈ subfs := by simp
            rw [separateLits_mem_notLits_iff] at this
            use subfs[i], this.1
            simpa using h1
        · intro has
          use fun
            | .inl v => τ v
            | .inr t => τ.map emb ⊨ subfs[t].toPropFun
          simp
          refine ⟨by funext; simp, fun _ => id,?_⟩
          intro ht; specialize has ht
          simp at has; rcases has with ⟨a,ha,h⟩
          by_cases hl : ∃ l, a = .lit l
          · rcases hl with ⟨l,rfl⟩
            rw [← separateLits_mem_lits_iff] at ha
            use LitVar.map (Sum.inl ∘ emb) l
            constructor
            · left; use l, ha
            · simpa using h
          · simp at hl
            have := separateLits_mem_notLits_iff.mpr ⟨ha,@hl⟩
            clear ha hl
            rw [Array.mem_iff_getElem] at this
            rcases this with ⟨i,hi,this⟩
            use Literal.pos (Sum.inr ⟨i,hi⟩)
            constructor
            · right; simp [Array.mem_def, List.mem_ofFn]
            · simp +zetaDelta [this, h]
      )
termination_by sizeOf f
decreasing_by
  · simp_wf
    have := separateLits_sizeOf_le as
    apply Nat.lt_of_lt_of_le ?_ this
    apply Nat.lt_succ_of_lt
    apply List.sizeOf_lt_of_mem
    simp
  · simp_wf
    exact separateLits_sizeOf_le as

end

def encodeNNF_top_clause (clause : Array (NegNormForm ν))
  : VEncCNF ν Unit (fun τ => ∃ f ∈ clause, τ ⊨ f.toPropFun) :=
  let separated := separateLits clause
  let lits := separated.1
  let subfs := separated.2
  withTemps (Fin subfs.size) (
    seq[
      encodeNNF_mkDefs (ν := ν) subfs ⟨id, fun _ _ h => h⟩
    , addClause (lits.map (LitVar.map Sum.inl) ++ Array.ofFn (Literal.pos <| Sum.inr ·))
    ]
  ) |>.mapProp (by
    ext τ
    simp [Clause.toPropFun, List.mem_ofFn]
    constructor
    · rintro ⟨σ,rfl,h1,⟨f,⟨l,hl,rfl⟩|⟨t,rfl⟩,h⟩⟩
      · rw [separateLits_mem_lits_iff] at hl
        refine ⟨_, hl, ?_⟩
        simpa using h
      · specialize h1 t h
        use subfs[t]
        have : subfs[t] ∈ subfs := by simp
        rw [separateLits_mem_notLits_iff] at this
        refine ⟨this.1,?_⟩
        simpa using h1
    · rintro ⟨f,hf,h⟩
      use fun
        | .inl v => τ v
        | .inr i => τ ⊨ subfs[i].toPropFun
      refine ⟨rfl,?_,?_⟩
      · simp; intro i hi; exact hi
      · by_cases hl : ∃ l, f = .lit l
        · rcases hl with ⟨l,rfl⟩
          rw [← separateLits_mem_lits_iff] at hf
          use PropFun.map Sum.inl l
          constructor
          · left; use l
          · simpa using h
        · simp at hl
          have := separateLits_mem_notLits_iff (a := f) (A := clause)
          simp [hf,hl] at this; clear hf hl
          rw [Array.mem_iff_getElem] at this
          rcases this with ⟨i,hi,rfl⟩
          use (Literal.pos (Sum.inr ⟨i,hi⟩) : Literal (ν ⊕ Fin subfs.size))
          constructor
          · right; simp
          · simpa using h
  )

def encodeNNF_top (f : NegNormForm ν)
  : VEncCNF ν Unit (· ⊨ f.toPropFun) :=
  let conjs := f.normalize
  for_all (Array.ofFn id) (fun i =>
    encodeNNF_top_clause (conjs[i])
  ) |>.mapProp (by
    funext τ
    rw [NegNormForm.satisfies_normalize]
    simp [conjs, Array.mem_iff_getElem, Fin.forall_iff]
    aesop
  )

end encodeNNF

-- nospecialize here because otherwise the compiler tries specializing it a ton
-- and that causes big slowdowns when building up VEncCNFs
open PropForm in
@[noinline,nospecialize]
def encode [DecidableEq V]
      (f : PropForm V) : VEncCNF V Unit (· ⊨ f) :=
  let nnf : NegNormForm V := NegNormForm.ofPropForm false f
  encodeNNF_top nnf
  |>.mapProp (by simp [nnf, NegNormForm.toPropFun_ofPropForm]; rfl)

end Tseitin

open Model.PropForm.Notation in
syntax "tseitin[" propform "]" : term

macro_rules
| `(tseitin[ $t ]) => `(Tseitin.encode [propform| $t ])

example [DecidableEq ν] [LitVar L ν] [LawfulLitVar L ν] (a b : ν)
    : VEncCNF ν Unit (fun τ => τ a ∧ τ b) :=
  tseitin[ {a} ∧ {b} ]
  |>.mapProp (by simp)

namespace Example

-- This is an example from Marijn's slides on optimizations for Tseitin

inductive V
| p | q | r | s | t
deriving Repr, IndexType

open V

def ex : Model.PropForm V :=
  [propform|
      (¬ (({p} ∧ {q}) ↔ {r}))
    ∧ ({s} → ({p} ∧ {t}))
  ]

example : (Tseitin.encode ex).val.toRichCnf.toICnf =
  #[
    -- d0 → p ∧ q ∧ ¬r
    #[-6, 1],
    #[-6, 2],
    #[-6, -3],
    -- d3 → r
    #[-7, 3],
    -- d3 → ¬p ∨ ¬q
    #[-7, -1, -2],
    -- d0 ∨ d3
    #[6, 7],
    -- d4 → p ∧ t
    #[-8, 1],
    #[-8, 5],
    -- ¬s ∨ d4
    #[-4, 8]
  ] := by native_decide

end Example
