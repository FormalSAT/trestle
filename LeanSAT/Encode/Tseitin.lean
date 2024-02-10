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

inductive NegNormForm (L : Type u)
| and (a b : NegNormForm L)
| or (a b : NegNormForm L)
| tr | fls
| lit (l : L)
deriving Repr, DecidableEq

namespace NegNormForm

variable [LitVar L ν]

def toPropFun (r : NegNormForm L) : PropFun ν :=
  match r with
  | .and a b => a.toPropFun ⊓ b.toPropFun
  | .or a b  => a.toPropFun ⊔ b.toPropFun
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

theorem toPropFun_ofPropForm [LawfulLitVar L ν] (f : PropForm ν)
  : toPropFun (L := L) (ofPropForm neg f) =
      if neg then ⟦.neg f⟧ else ⟦f⟧ := by
  induction f generalizing neg <;>
    -- we ♥ aesop
    aesop (add norm 1 simp ofPropForm)
          (add norm 1 simp toPropFun)
          (add norm 1 simp himp_eq)
          (add norm 1 simp PropFun.biImpl_eq_impls)

def cleanup : NegNormForm L → NegNormForm L
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

@[simp] theorem toPropFun_cleanup [LawfulLitVar L ν] (f : NegNormForm L)
  : toPropFun (L := L) (cleanup f) = toPropFun f := by
  apply Eq.symm -- otherwise aesop rewrites in the wrong direction
  induction f <;>
    -- we ♥ aesop
    aesop (add norm 1 simp ofPropForm)
          (add norm 1 simp toPropFun)
          (add norm 1 simp cleanup)


end NegNormForm

open VEncCNF

attribute [local simp] NegNormForm.toPropFun

/-- Tseitin encoding in the general case creates temporaries for each clause -/
def encodeNNF_mkDefs [LitVar L ν] [LitVar L' ν'] [LawfulLitVar L ν] [DecidableEq ν] [ErasedFintype ν]
        (t : ν) (emb : ν' ↪ ν) (f : NegNormForm L')
  : VEncCNF L Unit (.biImpl (.var t) (f.toPropFun.map emb)) :=
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
        , defConj (.var t) #[.temp 0, .temp 1]
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
        , defDisj (.var t) #[.temp 0, .temp 1]
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

def encodeNNF [LitVar L ν] [LawfulLitVar L ν] [DecidableEq ν] [ErasedFintype ν]
        (f : NegNormForm L) : VEncCNF L Unit f.toPropFun :=
  match f with
  | .tr => VEncCNF.pure () -- type matches by rfl
  | .fls => addClause #[]  -- type matches by rfl
  | .lit l => addClause #[l] |>.mapProp (by simp [Clause.toPropFun, PropFun.any])
  | .and a b =>
    seq[ encodeNNF a, encodeNNF b].mapProp (by simp)
  | .or a b =>
    withTemps 2 (
      seq[ encodeNNF_mkDefs (.inr 0) ⟨Sum.inl,Sum.inl_injective⟩ a
        ,  encodeNNF_mkDefs (.inr 1) ⟨Sum.inl,Sum.inl_injective⟩ b
        ,  addClause #[.temp 0, .temp 1]
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
@[nospecialize]
def encode [LitVar L V] [LawfulLitVar L V] [DecidableEq V] [ErasedFintype V]
      (f : PropForm V) : VEncCNF L Unit ⟦f⟧ :=
  let nnf : NegNormForm L := (NegNormForm.ofPropForm false f).cleanup
  encodeNNF nnf
  |>.mapProp (by simp [NegNormForm.toPropFun_ofPropForm])

end Tseitin

open Model.PropForm.Notation in
syntax "tseitin[" propform "]" : term

macro_rules
| `(tseitin[ $t ]) => `(Tseitin.encode [propform| $t ])

example [DecidableEq ν] [ErasedFintype ν] [LitVar L ν] [LawfulLitVar L ν] (a b : ν)
    : VEncCNF (ν := ν) L Unit (a ⊓ b) :=
  tseitin[ {a} ∧ {b} ]
  |>.mapProp (by simp)
