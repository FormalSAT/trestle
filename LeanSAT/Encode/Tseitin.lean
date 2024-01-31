import LeanSAT.Encode.VEncCNF

namespace LeanSAT.Encode.Tseitin

open Model VEncCNF

inductive ReducedForm (L : Type u) : Bool → Type u
| and (fs : Array (ReducedForm L false)) : ReducedForm L true
| or  (fs : Array (ReducedForm L true )) : ReducedForm L false
| lit (l : L) : ReducedForm L b

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
    PropFun.all fs'
  | or fs  =>
    let fs' := fs.attach.map (fun ⟨x,_h⟩ => ReducedForm.toPropFun x)
    PropFun.any fs'
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
  : r.toPropFun = (PropFun.all (r.conjuncts.map toPropFun)) :=
  match r with
  | .and rs => by ext τ; simp [conjuncts, Array.mem_def, Array.attach, toPropFun]
  | .lit l => by ext τ; simp [conjuncts, Array.mem_def]; rfl

theorem ReducedForm.disjuncts_toPropFun [LitVar L ν] (r : ReducedForm L false)
  : r.toPropFun = (PropFun.any (r.disjuncts.map toPropFun)) :=
  match r with
  | .or rs => by ext τ; simp [disjuncts, Array.mem_def, Array.attach, toPropFun]
  | .lit l => by ext τ; simp [disjuncts, Array.mem_def]; rfl

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


def tseitin [LitVar L V] [LawfulLitVar L V] [DecidableEq V] [Fintype V]
      (f : PropForm V) : VEncCNF L Unit ⟦f⟧ :=
  let red : ReducedForm L true := reduce f false
  let conjs := red.conjuncts
  forIn conjs (fun conj : ReducedForm L false =>
    let disjs := conj.disjuncts
    withTemps disjs.size (
      let temps := List.fins disjs.size |>.toArray
      forIn temps (fun i =>
        aux disjs[i] |>.map sorry))
  )
  |> mapProp (by
    sorry
  )
where
  aux {L} [LitVar L V] [LawfulLitVar L V] {b} (f : ReducedForm L b) :
      VEncCNF (EncCNF.WithTemps L 1) Unit
        (.biImpl (.var (Sum.inr 0)) (f.toPropFun.map Sum.inl)) :=
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

end Tseitin
