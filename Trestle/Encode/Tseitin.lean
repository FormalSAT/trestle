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

inductive NegNormForm (L : Type u)
| all (as : Array (NegNormForm L))
| any (as : Array (NegNormForm L))
| tr | fls
| lit (l : L)
deriving Repr

namespace NegNormForm

variable [LitVar L ν]

def toPropFun (r : NegNormForm L) : PropFun ν :=
  match r with
  | .all as => PropFun.all (as.attach.map (fun ⟨x,_h⟩ =>
      toPropFun x)).toList
  | .any as => PropFun.any (as.attach.map (fun ⟨x,_h⟩ =>
      toPropFun x)).toList
  | .lit l => LitVar.toPropFun l
  | .tr => ⊤
  | .fls => ⊥

def const (val : Bool) : NegNormForm L :=
  match val with
  | true  => .tr
  | false => .fls

@[simp] theorem const_toPropFun
  : (const b : NegNormForm L).toPropFun = if b then ⊤ else ⊥
  := by ext τ; cases b <;> simp [const, toPropFun]

def ofPropForm (neg : Bool) : PropForm ν → NegNormForm L
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

theorem toPropFun_ofPropForm [LawfulLitVar L ν] (f : PropForm ν)
  : toPropFun (L := L) (ofPropForm neg f) =
      if neg then ⟦.neg f⟧ else ⟦f⟧ := by
  induction f generalizing neg
  case tr | fls | var | neg | conj | disj | impl | biImpl =>
    -- we ♥ aesop
    aesop (add norm 1 simp [ofPropForm,toPropFun,himp_eq,Array.attach])

mutual
def conjuncts : NegNormForm L → Array (NegNormForm L)
| tr => #[]
| fls => #[fls]
| lit l => #[.lit l]
| all as => as.attach.flatMap (fun ⟨a,_h⟩ => conjuncts a)
| any as => #[.any <| as.attach.flatMap (fun ⟨a,_h⟩ => disjuncts a)]

def disjuncts : NegNormForm L → Array (NegNormForm L)
| tr => #[tr]
| fls => #[]
| lit l => #[.lit l]
| any as => as.attach.flatMap (fun ⟨a,_h⟩ => disjuncts a)
| all as => #[.all <| as.attach.flatMap (fun ⟨a,_h⟩ => conjuncts a)]
end

set_option maxHeartbeats 500000 in
set_option pp.proofs.withType false in
mutual
def toPropFun_all_conjuncts : (f : NegNormForm L) → toPropFun (.all (conjuncts f)) = toPropFun f
| tr    => by simp [conjuncts, toPropFun, Array.attach, PropFun.all]
| fls   => by simp [conjuncts, toPropFun, Array.attach, PropFun.all]
| lit l => by simp [conjuncts, toPropFun, Array.attach, PropFun.all]
| all as => by
  -- inductive hypothesis
  have IH : ∀ a ∈ as, _ := fun a _h => toPropFun_all_conjuncts a
  rcases as with ⟨as⟩; simp only [Array.mem_toArray] at IH
  ext τ
  replace IH := open PropFun in fun a ha => congrArg (τ ⊨ ·) (IH a ha).symm
  simp [conjuncts, toPropFun, List.unattach, -List.map_subtype] at IH ⊢
  aesop
| any as => by
  -- inductive hypothesis
  have IH : ∀ a ∈ as, _ := fun a _h => toPropFun_any_disjuncts a
  rcases as with ⟨as⟩; simp only [Array.mem_toArray] at IH
  ext τ
  replace IH := open PropFun in fun a ha => congrArg (τ ⊨ ·) (IH a ha).symm
  simp [conjuncts, disjuncts, toPropFun, List.unattach, -List.map_subtype] at IH ⊢
  aesop

def toPropFun_any_disjuncts : (f : NegNormForm L) → toPropFun (.any (disjuncts f)) = toPropFun f
| tr    => by simp [disjuncts, toPropFun, Array.attach, PropFun.any]
| fls   => by simp [disjuncts, toPropFun, Array.attach, PropFun.any]
| lit l => by simp [disjuncts, toPropFun, Array.attach, PropFun.any]
| any as => by
  -- inductive hypothesis
  have IH : ∀ a ∈ as, _ := fun a _h => toPropFun_any_disjuncts a
  rcases as with ⟨as⟩; simp only [Array.mem_toArray] at IH
  ext τ
  replace IH := open PropFun in fun a ha => congrArg (τ ⊨ ·) (IH a ha).symm
  simp [disjuncts, toPropFun, List.unattach, -List.map_subtype] at IH ⊢
  aesop
| all as => by
  -- inductive hypothesis
  have IH : ∀ a ∈ as, _ := fun a _h => toPropFun_all_conjuncts a
  rcases as with ⟨as⟩; simp only [Array.mem_toArray] at IH
  ext τ
  replace IH := open PropFun in fun a ha => congrArg (τ ⊨ ·) (IH a ha).symm
  simp [conjuncts, disjuncts, toPropFun, List.unattach, -List.map_subtype] at IH ⊢
  aesop
end

def cleanup : NegNormForm L → NegNormForm L
| tr => .tr
| fls => .fls
| lit l => .lit l
| all as =>
  let conj := conjuncts (.all as)
  .all conj
| any as =>
  let disj := disjuncts (.any as)
  .any disj

@[simp] theorem toPropFun_cleanup [LawfulLitVar L ν] (f : NegNormForm L)
  : toPropFun (L := L) (cleanup f) = toPropFun f := by
  apply Eq.symm -- otherwise aesop rewrites in the wrong direction
  cases f <;> simp [cleanup, toPropFun_all_conjuncts, toPropFun_any_disjuncts]


end NegNormForm

open VEncCNF

attribute [local simp] NegNormForm.toPropFun

open PropFun in
/-- Tseitin encoding in the general case creates temporaries for each clause -/
def encodeNNF_mkDefs [LitVar L ν] [LitVar L' ν'] [LawfulLitVar L ν] [DecidableEq ν]
        (t : ν) (emb : ν' ↪ ν) (f : NegNormForm L')
  : VEncCNF ν Unit (fun τ => τ t → τ ⊨ f.toPropFun.map emb) :=
  match f with
  | .tr =>
      VEncCNF.pure ()
      |>.mapProp (by simp; rfl)
  | .fls =>
      addClause #[LitVar.mkNeg t]
      |>.mapProp (by simp [Clause.toPropFun, PropFun.any])
  | .lit l =>
      imply (LitVar.mkPos t) (LitVar.map emb l)
      |>.mapProp (by simp)
  | .all as =>
      withTemps as.size (
        seq[
          for_all (Array.ofFn id) (fun i =>
            encodeNNF_mkDefs (L := Literal _)
              (.inr i) (emb.trans ⟨Sum.inl,Sum.inl_injective⟩) (as[i.val]'i.isLt)
          )
        , implyAnd (Literal.pos <| Sum.inl t) (Array.ofFn (Literal.pos <| Sum.inr ·))
        ]
      ) |>.mapProp (by
        ext τ
        rcases as with ⟨as⟩
        simp [PropAssignment.map, Array.mem_def, List.mem_iff_get,
          Function.Embedding.trans, LitVar.satisfies_iff]
        simp (config := {contextual := true}) [Fin.forall_iff]
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
  | .any as =>
      withTemps as.size (
        seq[
          for_all (Array.ofFn id) (fun i =>
            encodeNNF_mkDefs (L := Literal _)
              (.inr i) (emb.trans ⟨Sum.inl,Sum.inl_injective⟩) (as[i.val]'i.isLt)
          )
        , implyOr (Literal.pos <| Sum.inl t) (Array.ofFn (Literal.pos <| Sum.inr ·))
        ]
      ) |>.mapProp (by
        ext τ
        rcases as with ⟨as⟩
        simp [PropAssignment.map, Array.mem_def, List.mem_iff_get,
          Function.Embedding.trans, LitVar.satisfies_iff]
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

open PropFun in
def encodeNNF [LitVar L ν] [LawfulLitVar L ν] [DecidableEq ν]
        (f : NegNormForm L) : VEncCNF ν Unit (· ⊨ f.toPropFun) :=
  match f with
  | .tr => VEncCNF.pure () |>.mapProp (by funext; simp)
  | .fls => addClause #[] |>.mapProp (by simp [Clause.toPropFun])
  | .lit l => addClause #[Literal.mk (LitVar.toVar l) (LitVar.polarity l)]
        |>.mapProp (by simp [LitVar.satisfies_iff, LitVar.toVar, LitVar.polarity, Clause.toPropFun, PropFun.any])
  | .all fs =>
    for_all (Array.ofFn id) (fun i => encodeNNF (fs[i.val]'i.isLt))
    |>.mapProp (by
      funext τ
      rcases fs with ⟨fs⟩
      simp [Array.mem_def]
      simp [List.mem_iff_get])
  | .any fs =>
    withTemps fs.size (
      seq[
        for_all (Array.ofFn id) (fun i =>
          encodeNNF_mkDefs (L := Literal _)
            (.inr i) ⟨Sum.inl, Sum.inl_injective⟩ (fs[i.val]'i.isLt)
        )
      , addClause (Array.ofFn (Literal.pos <| Sum.inr ·))
      ]
    ) |>.mapProp (by
      ext τ
      rcases fs with ⟨fs⟩
      simp [Array.mem_def, Clause.satisfies_iff]
      simp [List.mem_iff_get, Fin.forall_iff, Fin.exists_iff]
      constructor
      case mp =>
        aesop
      case mpr =>
        rintro ⟨a,⟨i,hi,h⟩,c⟩
        open PropFun in
        use fun
          | .inl v => τ v
          | .inr i => τ ⊨ (fs[i]).toPropFun
        refine ⟨rfl,?_,?_⟩
        · aesop
        · use Literal.pos (Sum.inr ⟨i,hi⟩)
          aesop
    )

-- nospecialize here because otherwise the compiler tries specializing it a ton
-- and that causes big slowdowns when building up VEncCNFs
open PropForm in
@[nospecialize]
def encode [DecidableEq V]
      (f : PropForm V) : VEncCNF V Unit (· ⊨ f) :=
  let nnf : NegNormForm (Literal V) := (NegNormForm.ofPropForm false f).cleanup
  encodeNNF nnf
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
