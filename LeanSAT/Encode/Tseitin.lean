import LeanSAT.Encode.VEncCNF

/-! ## Tseitin Transform

This file implements an optimized version of the Tseitin transformation
from arbitrary formulas to CNF.

Formulas are first normalized, pushing negations down to the atoms
and collecting nested ands/ors into a single multi-child and/or.
-/

namespace LeanSAT.Encode.Tseitin

open Model

inductive ReducedForm (L : Type u) : Bool → Type u
| and (fs : Array (ReducedForm L false)) : ReducedForm L true
| or  (fs : Array (ReducedForm L true )) : ReducedForm L false
| lit (l : L) : ReducedForm L b
deriving Repr

private def ReducedForm.disjuncts : ReducedForm L false → Array (ReducedForm L true)
| .or fs => fs
| .lit l => #[.lit l]

private def ReducedForm.conjuncts : ReducedForm L true → Array (ReducedForm L false)
| .and fs => fs
| .lit l => #[.lit l]

def const (val : Bool) : ReducedForm L b :=
  match b, val with
  | true , true  => .and #[]
  | true , false => .and #[.or #[]]
  | false, true  => .or #[.and #[]]
  | false, false => .or #[]

@[simp] noncomputable def reduceSize : PropForm L → Nat
| .var _ | .tr | .fls => 1
| .neg x => 1 + reduceSize x
| .conj x y | .disj x y => 1 + reduceSize x + reduceSize y
| .impl x y   => 3 + reduceSize x + reduceSize y
| .biImpl x y => 8 + 2 * (reduceSize x + reduceSize y)

@[simp] theorem reduceSize_pos : reduceSize f > 0 := by
  cases f <;> simp

variable {L : Type u} {ν : Type v} [LitVar L ν] in
mutual

/-- `reduce φ b` returns a formula equivalent
to `φ` if `b = true` or `¬φ` if `b = false`. -/
def reduce : PropForm ν → Bool → ReducedForm L b
| .neg f, neg =>
    reduce f (!neg)
| .var l, neg =>
    .lit <| LitVar.mkLit _ l (!neg)
| .tr, neg =>
    const (!neg)
| .fls, neg =>
    const ( neg)
| .conj x y, neg =>
    if neg
    then reduceDisj x y true
    else reduceConj x y false
| .disj x y, neg =>
    if neg
    then reduceConj x y true
    else reduceDisj x y false
| .impl h c, neg =>
    reduce (.disj c (.neg h)) neg
| .biImpl l r, neg =>
    reduce (.conj (.impl l r) (.impl r l)) neg

def reduceConj (x y : PropForm ν) (neg : Bool) : ReducedForm L b :=
  let blah := .and <| (reduce x neg).conjuncts ++ (reduce y neg).conjuncts
  match b with
  | true  => blah
  | false => .or #[blah]

def reduceDisj (x y : PropForm ν) (neg : Bool) : ReducedForm L b :=
  let blah := .or <| (reduce x neg).disjuncts ++ (reduce y neg).disjuncts
  match b with
  | true  => .and #[blah]
  | false => blah
end
termination_by
  reduce f neg => reduceSize f
  reduceConj x y neg => reduceSize x + reduceSize y
  reduceDisj x y neg => reduceSize x + reduceSize y

def ReducedForm.toPropFun [LitVar L V] (r : ReducedForm L b) : PropFun V :=
  match r with
  | and fs =>
    let fs' := fs.attach.map (fun ⟨x,_h⟩ => ReducedForm.toPropFun x)
    PropFun.all fs'.toList
  | or fs  =>
    let fs' := fs.attach.map (fun ⟨x,_h⟩ => ReducedForm.toPropFun x)
    PropFun.any fs'.toList
  | lit l => LitVar.toPropFun l

@[simp] theorem const_toPropFun [LitVar L ν]
  : (const b1 : ReducedForm L b2).toPropFun = if b1 then ⊤ else ⊥
  := by
  ext τ
  cases b1 <;> cases b2 <;> (
    simp [const]
    simp [ReducedForm.toPropFun, Array.mem_def, Array.attach]
  )

theorem ReducedForm.conjuncts_toPropFun [LitVar L ν] (r : ReducedForm L true)
  : r.toPropFun = (PropFun.all (r.conjuncts.toList.map toPropFun)) :=
  match r with
  | .and rs => by ext τ; simp [conjuncts, Array.mem_def, Array.attach, toPropFun]
  | .lit l => by ext τ; simp [conjuncts, Array.mem_def]; rfl

theorem ReducedForm.disjuncts_toPropFun [LitVar L ν] (r : ReducedForm L false)
  : r.toPropFun = (PropFun.any (r.disjuncts.toList.map toPropFun)) :=
  match r with
  | .or rs => by ext τ; simp [disjuncts, Array.mem_def, Array.attach, toPropFun]
  | .lit l => by ext τ; simp [disjuncts, Array.mem_def]; rfl

#eval show ReducedForm ILit true from
  reduce (.biImpl (.var 1) (.conj (.biImpl (.var 2) (.var 3)) (.biImpl (.var 4) (.var 2)))) true

#exit

/- TODO: This proof is really slow...

JG: investigated this a bit more, it seems like the proof is not actually
that slow, mutual blocks are just hard...
-/
set_option maxHeartbeats 500000 in
open PropFun in
variable {L : Type u} {ν : Type v} [LitVar L ν] [LawfulLitVar L ν] in
mutual
def reduce_toPropFun (f : PropForm ν) (neg : Bool)
  : (reduce f neg : ReducedForm L b).toPropFun = ⟦ if neg then .neg f else f ⟧ :=
  match f with
  | .neg f =>
      have := reduce_toPropFun f (!neg)
      by
        simp [reduce]; rw [this]; cases neg <;> simp
  | .var l =>
      by
        simp [reduce]
        cases neg <;> simp [ReducedForm.toPropFun, LitVar.toPropFun]
  | .tr =>
      by
        simp [reduce]
        cases neg <;> simp
  | .fls =>
      by
        simp [reduce]
        cases neg <;> simp
  | .conj x y =>
      have h1 := reduceDisj_toPropFun (b := b) x y true
      have h2 := reduceConj_toPropFun (b := b) x y false
      by
        simp [reduce]; cases neg <;> simp <;> (first | rw [h1] | rw [h2]) <;> simp
  | .disj x y =>
      have h1 := reduceConj_toPropFun (b := b) x y true
      have h2 := reduceDisj_toPropFun (b := b) x y false
      by
        simp [reduce]; cases neg <;> simp <;> (first | rw [h1] | rw [h2]) <;> simp
  | .impl h c =>
      have h' := reduce_toPropFun (b := b) (.disj c (.neg h)) neg
      by
        unfold reduce; rw [h']; clear h'
        cases neg <;> simp [BooleanAlgebra.sdiff_eq, BooleanAlgebra.himp_eq]
  | .biImpl l r =>
      have h' := reduce_toPropFun (b := b) (.conj (.impl l r) (.impl r l)) neg
      by
        unfold reduce; rw [h']; clear h'
        cases neg <;> simp [biImpl_eq_impls, BooleanAlgebra.sdiff_eq, BooleanAlgebra.himp_eq]

def reduceConj_toPropFun (x y : PropForm ν) (neg : Bool)
  : (reduceConj x y neg : ReducedForm L b).toPropFun =
      ⟦ if neg then .neg (.disj x y) else (.conj x y) ⟧
  := by
  have h1 := reduce_toPropFun (b := true) x neg
  have h2 := reduce_toPropFun (b := true) y neg
  ext τ
  have := congrArg (τ ⊨ ·) <| ReducedForm.conjuncts_toPropFun (L := L) (reduce x neg)
  rw [h1] at this
  have := congrArg (τ ⊨ ·) <| ReducedForm.conjuncts_toPropFun (L := L) (reduce y neg)
  rw [h2] at this
  clear h1 h2
  cases b <;> (
    simp [reduceConj]
    simp [ReducedForm.toPropFun, Array.mem_def, Array.attach] at *
    aesop
  )


def reduceDisj_toPropFun (x y : PropForm ν) (neg : Bool)
  : (reduceDisj x y neg : ReducedForm L b).toPropFun =
    ⟦ if neg then .neg (.conj x y) else .disj x y ⟧
  := by
  have h1 := reduce_toPropFun (b := false) x neg
  have h2 := reduce_toPropFun (b := false) y neg
  ext τ
  have := congrArg (τ ⊨ ·) <| ReducedForm.disjuncts_toPropFun (L := L) (reduce x neg)
  rw [h1] at this
  have := congrArg (τ ⊨ ·) <| ReducedForm.disjuncts_toPropFun (L := L) (reduce y neg)
  rw [h2] at this
  clear h1 h2
  cases b <;> (
    simp [reduceDisj]
    simp [ReducedForm.toPropFun, Array.mem_def, Array.attach] at *
    cases neg <;> (
      simp_all; clear this; clear this
      generalize ReducedForm.disjuncts _ = xr
      generalize ReducedForm.disjuncts _ = yr
      cases xr; cases yr
      aesop
    )
  )
end
termination_by
  reduce_toPropFun f neg => reduceSize f
  reduceConj_toPropFun x y neg => reduceSize x + reduceSize y
  reduceDisj_toPropFun x y neg => reduceSize x + reduceSize y

/-
def ReducedForm.map [LitVar L V] [LitVar L' V'] (f : V → V') : ReducedForm L b → ReducedForm L' b
| lit l => .lit (LitVar.mkLit _ (f <| LitVar.toVar l) (LitVar.polarity l))
| and rs => .and (rs.attach.map (fun ⟨r,_⟩ => map f r))
| or rs => .or (rs.attach.map (fun ⟨r,_⟩ => map f r))

@[simp]
def ReducedForm.toPropFun_map [LitVar L V] [LawfulLitVar L V] [LitVar L' V'] [LawfulLitVar L' V']
          (f : V → V') (r : ReducedForm L b)
      : toPropFun (map (L' := L') f r) = (toPropFun r).map f :=
  match r with
  | .lit l => by
    simp [map, toPropFun, LitVar.toPropFun]
    split <;> simp_all
  | .and rs =>
    have ih : ∀ r ∈ rs, toPropFun (map f r) = (toPropFun r).map f :=
      fun rf h => toPropFun_map f rf
    by
    simp [map, toPropFun]
    ext τ
    simp
    constructor
    · rintro h _ rf hrf _ rfl
      have := h (toPropFun (map f rf)) _ rf ⟨?_,rfl⟩ ?_ rfl
      · rw [ih rf hrf] at this; simpa using this
      · use hrf
      · simp [Array.mem_def, Array.attach]; use rf; simpa [Array.mem_def] using hrf
    · rintro h _ _ rf ⟨⟨hrf,h1⟩,rfl⟩ _ rfl
      rw [ih rf hrf]
      simp
      apply h
      · apply h1
      · rfl
      · apply hrf
  | .or rs =>
    have ih : ∀ r ∈ rs, toPropFun (map f r) = (toPropFun r).map f :=
      fun rf h => toPropFun_map f rf
    by
    simp [map, toPropFun]
    ext τ
    simp
    constructor
    · rintro ⟨_,⟨⟨rf,⟨hrf,h1⟩,rfl⟩,h2⟩,h4⟩
      rw [ih rf hrf] at h4; simp at h4
      refine ⟨_,⟨hrf,h1⟩,h4⟩
    · rintro ⟨rf,⟨hrf,h1⟩,h2⟩
      rw [← PropFun.satisfies_map, ← ih rf hrf] at h2
      refine ⟨_,⟨⟨rf,⟨hrf,h1⟩,rfl⟩,?_⟩,h2⟩
      simp [Array.mem_def, Array.attach]; use rf; simpa [Array.mem_def] using hrf
-/


noncomputable def tseitin [LitVar L V] [LawfulLitVar L V] [DecidableEq V] [Fintype V]
      (f : PropForm V) : VEncCNF L Unit ⟦f⟧ :=
  let red : ReducedForm L true := reduce f false
  let conjs := red.conjuncts
  sorry
  /- for_all conjs (fun conj : ReducedForm L false =>
    withTemps conj.disjuncts.size (
      let temps := List.fins conj.disjuncts.size |>.toArray
      for_all temps (fun i =>
        aux (L := EncCNF.WithTemps L conj.disjuncts.size) (V := V ⊕ Fin conj.disjuncts.size)
          (Sum.inr i)
          (ReducedForm.map Sum.inl conj.disjuncts[i]))
    )
  )
  |> mapProp (by
    sorry
  ) -/
where
  aux {b} (t : V) (f : ReducedForm L b)
      : VEncCNF L Unit (.biImpl (.var t) (f.toPropFun)) :=
    sorry
/-
    match h : f with
    | .lit l =>
      seq (addClause #[.var l, LitVar.negate <| .temp 0])
          (addClause #[LitVar.negate <| .var l, .temp 0])
      |> mapProp (by
        subst b; simp at h; subst f
        ext τ
        simp [Clause.satisfies_iff, LitVar.satisfies_iff, ReducedForm.toPropFun]
        generalize τ _ = x; generalize τ _ = y; generalize LitVar.polarity l = z
        cases y <;> cases z <;> simp)
    | .and fs =>
      --withTemps fs.size (
      --  let temps := List.fins fs.size |>.map EncCNF.WithTemps.temp
      --  seq
      --    -- temp i ↔ fs[i]
      --    (forIn temps sorry)
      --  <| seq
      --    -- temp 0 ↔ ⋀ᵢ temp i
      --    (forIn temps (fun i => addClause #[ sorry, fs[i]]))
      --    (assuming temps <| addClause #[EncCNF.WithTemps.temp 0])
      --) |> mapProp
      sorry
    | .or fs => sorry
      --do
      --let ls ← fs.subtypeSize.mapM (fun ⟨f,h⟩ =>
      --  have := Nat.le_trans h (Nat.le_add_left _ 1)
      --  aux f)
      --let t ← mkTemp
      ---- t ↔ ⋁ ls
      --assuming #[t] <| addClause ls
      --for l in ls do
      --  addClause #[-l, t]
      --return t
-/

open EncCNF in
def encodeAux {L V L' V' : Type} [LitVar L V] [LitVar L' V'] [Fintype V]
      (t : V) (f : ReducedForm L' b) (emb : L' ↪ L) :
    EncCNF L (Option L') := do
  match f with
  | .lit l => return some l
  | .and fs =>
    withTemps fs.size (do
    let fs' : Array (L ⊕ Fin fs.size) ←
      Array.ofFn (n := fs.size) id |>.mapM (fun i => do
        match ←
          encodeAux (.inr i) (fs[i] : ReducedForm L' _)
            ⟨ (.var <| emb ·)
            , by intro l1 l2 h; simp [WithTemps.var] at h; have := Sum.inl_injective h; simp_all⟩
        with
        | none => return .inr i
        | some l => return .inl (emb l))
    -- ∀ i, t → fs[i]
    for f in fs' do
      sorry
    -- ⋀i fs[i] → t
    addClause #[]
    return none
    )
  | .or fs => sorry

def encode [LitVar L V] (f : PropForm V) : EncCNF L Unit :=
  let red : ReducedForm L true := reduce f false
  let conjs := red.conjuncts
where
toplevel : Formula.NegNorm → EncCNF Unit
  | .lit l => addClause l
  | .and fs => newCtx "and." do
    for (i,⟨f,h⟩) in fs.subtypeSize.enum do
      have := Nat.le_trans h (Nat.le_add_left _ 1)
      newCtx s!"[{i}]." <| toplevel f
  | .or fs => newCtx "or." do
    let ls ← fs.enum.mapM (fun (i,f) => newCtx s!"[{i}]." <| aux f)
    addClause ls
aux : Formula.NegNorm → EncCNF Literal
  | .lit l => pure l
  | .and fs => newCtx "and." do
    let ls : List Literal ← fs.subtypeSize.enum.mapM (fun (i, ⟨f,h⟩) =>
      have := Nat.le_trans h (Nat.le_add_left _ 1)
      newCtx s!"[{i}]." <| aux f)
    let t ← mkTemp
    -- t ↔ ⋀ ls
    for l in ls do
      addClause (¬ t ∨ l)
    addClause (ls.map (·.not) ∨ t)
    return t
  | .or  fs => newCtx "or." do
    let ls ← fs.subtypeSize.enum.mapM (fun (i, ⟨f,h⟩) =>
      have := Nat.le_trans h (Nat.le_add_left _ 1)
      newCtx s!"[{i}]." <| aux f)
    let t ← mkTemp
    -- t ↔ ⋁ ls
    addClause (¬ t ∨ ls)
    for l in ls do
      addClause (¬l ∨ t)
    return t
termination_by
  toplevel f => f
  aux f => f

end Tseitin
