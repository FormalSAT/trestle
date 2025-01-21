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
  · rw [Array.size_eq_one] at h
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
  · rw [Array.size_eq_one] at h
    rcases h with ⟨a,h⟩
    simp [h, toPropFun]
  · simp [toPropFun]
end

end NegNormForm

open VEncCNF

attribute [local simp] NegNormForm.toPropFun

section encodeNNF

def separateLits (A : Array (NegNormForm ν)) : Array (Literal ν) × Array (NegNormForm ν) :=
  ( A.filterMap (fun | .lit l => some l | _ => none)
  , A.filter (fun | .lit _ => false | _ => true)
  )

theorem separateLits_append_perm (A : Array (NegNormForm ν))
  : List.Perm ((separateLits A).1.map (NegNormForm.lit ·) ++ (separateLits A).2).toList A.toList
  := by
  rcases A with ⟨A⟩
  simp [separateLits, List.map_filterMap]
  convert List.filter_append_perm (fun | .lit _ => true | _ => false) A
  · convert List.filterMap_eq_filter ?_
    rename_i f
    cases f <;> simp [Option.guard]
  · split <;> rfl

theorem separateLits_notLits_sublist (A : Array (NegNormForm ν))
  : List.Sublist (separateLits A).2.toList A.toList := by
  unfold separateLits; simp

open List in
theorem List.Sublist.sizeOf_le [SizeOf α] {L₁ L₂ : List α} :
        L₁ <+ L₂ → sizeOf L₁ ≤ sizeOf L₂ := by
  intro h
  induction h
  · simp
  · simp; omega
  · simp; assumption

open List in
theorem List.Subperm.sizeOf_le {L₁ L₂ : List α} :
        List.Subperm L₁ L₂ → sizeOf L₁ ≤ sizeOf L₂ := by
  rintro ⟨L,h1,h2⟩
  have := List.Perm.sizeOf_eq_sizeOf h1
  have := List.Sublist.sizeOf_le h2
  omega

theorem separateLits_sizeOf_le (A : Array (NegNormForm ν))
  : sizeOf (separateLits A).2.toList < 1 + sizeOf A := by
  have := List.Sublist.sizeOf_le (separateLits_notLits_sublist A)
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
      -- TODO(JG): this can be further optimized!!!
      -- we do not need new temps here, because PG only requires `t -> f`
      -- so for temps I can directly require `t -> all lits`,
      -- and for each subformula I can just call `encodeNNF` with `t` again!
      let separated := separateLits as
      let lits := separated.1
      let subfs := separated.2
      withTemps subfs.size (
        seq[
          have : sizeOf subfs.toList < 1 + sizeOf as :=
            separateLits_sizeOf_le as
          encodeNNF_mkDefs subfs emb
        , implyAnd (Literal.pos <| Sum.inl t)
            (lits.map (LitVar.map <| Sum.inl ∘ emb) ++ Array.ofFn (Literal.pos <| Sum.inr ·))
        ]
      ) |>.mapProp (by
        ext τ
        rcases as with ⟨as⟩
        simp [Array.mem_def, List.mem_iff_get, LitVar.satisfies_iff]
        simp (config := {contextual := true}) [Fin.forall_iff]
        constructor
        case mp =>
          rintro ⟨σ,rfl,h1,h2⟩ h
          replace h2 := h2 h; clear h t
          intro i hi

          sorry
        case mpr =>
          stop
          intro h
          open PropFun in
          use fun
            | .inl v => τ v
            | .inr i => τ.map emb ⊨ (as[i]).toPropFun
          aesop)
  | .any as =>
      let separated := separateLits as
      let lits := separated.1
      let subfs := separated.2
      withTemps subfs.size (
        seq[
          have : sizeOf subfs.toList < 1 + sizeOf as :=
            separateLits_sizeOf_le as
          encodeNNF_mkDefs subfs emb
        , implyOr (Literal.pos <| Sum.inl t)
            (lits.map (LitVar.map <| Sum.inl ∘ emb) ++ Array.ofFn (Literal.pos <| Sum.inr ·))
        ]
      ) |>.mapProp (by
        stop
        ext τ
        rcases as with ⟨as⟩
        simp [Array.mem_def, List.mem_iff_get, LitVar.satisfies_iff]
        simp (config := {contextual := true}) [Fin.forall_iff, Fin.exists_iff]
        constructor
        case mp =>
          aesop
        case mpr =>
          intro h
          open PropFun in
          use fun
            | .inl v => τ v
            | .inr i => τ.map emb ⊨ (as[i]).toPropFun
          aesop)
termination_by sizeOf f

end

def encodeNNF_top_clause (f : NegNormForm ν)
  : VEncCNF ν Unit (· ⊨ f.toPropFun) :=
  let disjs := match f with
      | .any fs => fs
      | .all fs => #[.all fs]
      | .lit l => #[.lit l]
  have ⟨disjs,h⟩ : (A : Array _) ×'
                    (f.toPropFun = (NegNormForm.any A).toPropFun) :=
    ⟨disjs, by ext τ; unfold disjs; split <;> simp [NegNormForm.toPropFun]⟩
  let separated := separateLits disjs
  let lits := separated.1
  let subfs := separated.2
  withTemps subfs.size (
    seq[
      encodeNNF_mkDefs (ν := ν) subfs ⟨id, fun _ _ h => h⟩
    , addClause (lits.map (LitVar.map Sum.inl) ++ Array.ofFn (Literal.pos <| Sum.inr ·))
    ]
  ) |>.mapProp (by
    ext τ
    stop
    rw [h]; clear h
    rcases disjs with ⟨disjs⟩
    simp [List.mem_iff_get]
    constructor
    case mp =>
      rintro ⟨σ,rfl,h1,h2⟩
      simp [Clause.toPropFun, List.mem_ofFn] at h2
      rcases h2 with ⟨t,ht⟩
      use t.cast (by simp)
      simp
      apply h1
      apply ht
    case mpr =>
      rintro ⟨t,h⟩
      open PropFun in
      use fun
        | .inl v => τ v
        | .inr i => τ ⊨ (disjs[i]).toPropFun
      refine ⟨rfl,?_,?_⟩
      · aesop
      · simp [Clause.toPropFun, List.mem_ofFn]
        use t.cast (by simp), h
  )

def encodeNNF_top (f : NegNormForm ν)
  : VEncCNF ν Unit (· ⊨ f.toPropFun) :=
  let conjs := f.conjuncts
  for_all (Array.ofFn id) (fun i =>
    encodeNNF_top_clause (conjs[i])
  ) |>.mapProp (by
    funext τ
    unfold conjs
    rw [f.toPropFun_all_conjuncts.symm]
    simp [NegNormForm.toPropFun]
    simp [Array.mem_def, List.mem_iff_get]
    rw [Fin.forall_iff, Fin.forall_iff]
    simp
  )

end encodeNNF

-- nospecialize here because otherwise the compiler tries specializing it a ton
-- and that causes big slowdowns when building up VEncCNFs
open PropForm in
@[nospecialize]
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

example : (Tseitin.encode ex).val.toICnf =
  #[
    -- d0 → p ∧ q ∧ ¬r
    #[-6, 1],
    #[-6, 2],
    #[-6, -3],
    -- d2 → ¬p ∨ ¬q
    #[-8, -1, -2],
    -- d3 → r ∧ d2
    #[-7, 3],
    #[-7, 8],
    -- d0 ∨ d3
    #[6, 7],
    -- d4 → p ∧ t
    #[-9, 1],
    #[-9, 5],
    -- ¬s ∨ d4
    #[-4, 9]
  ] := by native_decide

end Example
