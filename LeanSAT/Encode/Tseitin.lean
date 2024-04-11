/-
Copyright (c) 2024 The LeanSAT Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import LeanSAT.Encode.VEncCNF

/-! ## Tseitin Transform

This file implements a lightly optimized Tseitin encoding
of arbitrary `PropForm` formulas into CNF.

The formula is put into negation normal form first,
and top-level ∧ / top-level ∨ are collected into one
formula/clause respectively.
-/

namespace LeanSAT.Encode.Tseitin

open Model

inductive NegNormForm (ν : Type u)
| and (a b : NegNormForm ν)
| or (a b : NegNormForm ν)
| tr | fls
| lit (l : Literal ν)
--deriving Repr, DecidableEq

namespace NegNormForm

def toPropFun (r : NegNormForm ν) : PropFun ν :=
  match r with
  | .and a b => a.toPropFun ⊓ b.toPropFun
  | .or a b  => a.toPropFun ⊔ b.toPropFun
  | .lit l => LitVar.toPropFun l
  | .tr => ⊤
  | .fls => ⊥

def const (val : Bool) : NegNormForm ν :=
  match val with
  | true  => .tr
  | false => .fls

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
    .or (ofPropForm neg a) (ofPropForm neg b)
  else
    .and (ofPropForm neg a) (ofPropForm neg b)
| .disj a b =>
  if neg then
    .and (ofPropForm neg a) (ofPropForm neg b)
  else
    .or (ofPropForm neg a) (ofPropForm neg b)
| .impl a b =>
  if neg then
    .and (ofPropForm false a) (ofPropForm true b)
  else
    .or (ofPropForm true a) (ofPropForm false b)
| .biImpl a b =>
  if neg then
    .or
      (.and (ofPropForm false a) (ofPropForm true b))
      (.and (ofPropForm false b) (ofPropForm true a))
  else
    .and
      (.or (ofPropForm true a) (ofPropForm false b))
      (.or (ofPropForm true b) (ofPropForm false a))

theorem toPropFun_ofPropForm (f : PropForm ν)
  : toPropFun (ν := ν) (ofPropForm neg f) =
      if neg then ⟦.neg f⟧ else ⟦f⟧ := by
  induction f generalizing neg <;>
    -- we ♥ aesop
    aesop (add norm 1 simp ofPropForm)
          (add norm 1 simp toPropFun)
          (add norm 1 simp himp_eq)
          (add norm 1 simp PropFun.biImpl_eq_impls)

def cleanup : NegNormForm ν → NegNormForm ν
| tr => .tr
| fls => .fls
| lit l => .lit l
| and a b =>
  let a := cleanup a
  let b := cleanup b
  match a, b with
  | .tr, x
  | x, .tr => x
  | .fls, _
  | _, .fls => .fls
  | _, _ => .and a b
| or  a b =>
  let a := cleanup a
  let b := cleanup b
  match a, b with
  | .tr, _
  | _, .tr => .tr
  | .fls, x
  | x, .fls => x
  | _, _ => .or a b

@[simp] theorem toPropFun_cleanup (f : NegNormForm ν)
  : toPropFun (ν := ν) (cleanup f) = toPropFun f := by
  apply Eq.symm -- otherwise aesop rewrites in the wrong direction
  induction f <;>
    -- we ♥ aesop
    aesop (add norm 1 simp ofPropForm)
          (add norm 1 simp toPropFun)
          (add norm 1 simp cleanup)


end NegNormForm

open VEncCNF

attribute [local simp] NegNormForm.toPropFun

open PropFun in
/-- Tseitin encoding in the general case creates temporaries for each clause -/
def encodeNNF_mkDefs (t : ν) (emb : ν' ↪ ν) (f : NegNormForm ν')
  : VEncCNF ν Unit (fun τ => τ t ↔ τ ⊨ f.toPropFun.map emb) :=
  match f with
  | .tr =>
      addClause #[LitVar.mkPos t]
      |>.mapProp (by simp [Clause.toPropFun, PropFun.any])
  | .fls =>
      addClause #[LitVar.mkNeg t]
      |>.mapProp (by simp [Clause.toPropFun, PropFun.any])
  | .lit l =>
      biImpl (LitVar.mkPos t) (LitVar.map emb l)
      |>.mapProp (by simp)
  | .and a b =>
      withTemps 2 (
        seq[
          encodeNNF_mkDefs
            (.inr 0) (emb.trans ⟨Sum.inl,Sum.inl_injective⟩) a
        , encodeNNF_mkDefs
            (.inr 1) (emb.trans ⟨Sum.inl,Sum.inl_injective⟩) b
        , defConj (LitVar.mkPos (.inl t)) #[LitVar.mkPos (.inr 0), LitVar.mkPos (.inr 1)]
        ]
      ) |>.mapProp (by
        ext τ; simp
        constructor
        case a.mp =>
          aesop
        case a.mpr =>
          intro h
          open PropFun in
          use fun
            | .inl v => τ v
            | .inr 0 => τ.map emb ⊨ a.toPropFun
            | .inr 1 => τ.map emb ⊨ b.toPropFun
          aesop)
  | .or a b =>
      withTemps 2 (
        seq[
          encodeNNF_mkDefs
            (.inr 0) (emb.trans ⟨Sum.inl,Sum.inl_injective⟩) a
        , encodeNNF_mkDefs
            (.inr 1) (emb.trans ⟨Sum.inl,Sum.inl_injective⟩) b
        , defDisj (LitVar.mkPos (.inl t)) #[LitVar.mkPos (.inr 0), LitVar.mkPos (.inr 1)]
        ]
      ) |>.mapProp (by
        ext τ; simp
        constructor
        case a.mp =>
          aesop
        case a.mpr =>
          intro h
          open PropFun in
          use fun
            | .inl v => τ v
            | .inr 0 => τ.map emb ⊨ a.toPropFun
            | .inr 1 => τ.map emb ⊨ b.toPropFun
          aesop)

open PropFun in
def encodeNNF (f : NegNormForm ν) : VEncCNF ν Unit (· ⊨ f.toPropFun) :=
  match f with
  | .tr => VEncCNF.pure () |>.mapProp (by funext; simp)
  | .fls => addClause #[] |>.mapProp (by simp [Clause.toPropFun])
  | .lit l => addClause #[l] |>.mapProp (by simp [Clause.toPropFun, PropFun.any])
  | .and a b =>
    seq[ encodeNNF a, encodeNNF b].mapProp (by simp)
  | .or a b =>
    withTemps 2 (
      seq[ encodeNNF_mkDefs (.inr 0) ⟨Sum.inl,Sum.inl_injective⟩ a
        ,  encodeNNF_mkDefs (.inr 1) ⟨Sum.inl,Sum.inl_injective⟩ b
        ,  addClause #[LitVar.mkPos (.inr 0), LitVar.mkPos (.inr 1)]
      ]
    ) |>.mapProp (by
      apply Eq.symm -- otherwise aesop rewrites in the wrong direction
      ext τ
      simp [Clause.toPropFun]
      open PropFun in
      constructor
      case a.mp =>
        intro h
        use fun | .inl v => τ v | .inr 0 => τ ⊨ a.toPropFun | .inr 1 => τ ⊨ b.toPropFun
        aesop
      case a.mpr =>
        aesop
      )

-- nospecialize here because otherwise the compiler tries specializing it a ton
-- and that causes big slowdowns when building up VEncCNFs
open PropForm in
@[nospecialize]
def encode (f : PropForm ν) : VEncCNF ν Unit (· ⊨ f) :=
  let nnf : NegNormForm ν := (NegNormForm.ofPropForm false f).cleanup
  encodeNNF nnf
  |>.mapProp (by simp [nnf, NegNormForm.toPropFun_ofPropForm]; rfl)

end Tseitin

open Model.PropForm.Notation in
syntax "tseitin[" propform "]" : term

macro_rules
| `(tseitin[ $t ]) => `(Tseitin.encode [propform| $t ])

example (a b : ν) : VEncCNF ν Unit (fun τ => τ a ∧ τ b) :=
  tseitin[ {a} ∧ {b} ]
  |>.mapProp (by simp)
