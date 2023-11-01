import LeanSAT.Encode.EncCNF

namespace LeanSAT.Encode.Tseitin

open Model EncCNF

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
def reduce : PropForm L → Bool → ReducedForm L b
| .neg f, neg =>
    have : sizeOf f < 1 + sizeOf f := by simp
    reduce f (!neg)
| .var l, neg =>
    .lit (if neg then (-l) else l)
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
    reduce (.disj (.neg h) c) neg
| .biImpl l r, neg =>
    reduce (.conj (.impl l r) (.impl r l)) neg

def reduceConj [LitVar L ν] (x y : PropForm L) (neg : Bool) : ReducedForm L b :=
  let blah := .and <| (reduce x neg).conjuncts ++ (reduce y neg).conjuncts
  match b with
  | true  => blah
  | false => .or #[blah]

def reduceDisj [LitVar L ν] (x y : PropForm L) (neg : Bool) : ReducedForm L b :=
  let blah := .or <| (reduce x neg).disjuncts ++ (reduce y neg).disjuncts
  match b with
  | true  => .and #[blah]
  | false => blah
end
termination_by
  reduce f neg => reduceSize f
  reduceConj x y neg => reduceSize x + reduceSize y
  reduceDisj x y neg => reduceSize x + reduceSize y

partial def tseitin (f : PropForm ILit) : EncCNF Unit := do
  let red := reduce f true
  topAnd red
where
  topAnd : ReducedForm ILit true → EncCNF Unit
    | .and fs => do
      let cs : Array IClause ← fs.subtypeSize.mapM (fun ⟨f,h⟩ =>
        have := Nat.le_trans h (Nat.le_add_left _ 1)
        topOr f)
      for c in cs do
        addClause c
    | .lit l => addClause #[l]
  topOr : ReducedForm ILit false → EncCNF IClause
    | .or fs => do
      let cs : Array ILit ← fs.subtypeSize.mapM (fun ⟨f,h⟩ =>
        have := Nat.le_trans h (Nat.le_add_left _ 1)
        aux f)
      return cs
    | .lit l => return #[l]
  aux {b} : ReducedForm ILit b → EncCNF ILit
    | .lit l => pure l
    | .and fs => do
      let ls : Array ILit ← fs.subtypeSize.mapM (fun ⟨f,h⟩ =>
        have := Nat.le_trans h (Nat.le_add_left _ 1)
        aux f)
      let t ← mkTemp
      -- t ↔ ⋀ ls
      for l in ls do
        addClause #[ -t, l]
      assuming ls <| addClause #[t]
      return t
    | .or fs => do
      let ls ← fs.subtypeSize.mapM (fun ⟨f,h⟩ =>
        have := Nat.le_trans h (Nat.le_add_left _ 1)
        aux f)
      let t ← mkTemp
      -- t ↔ ⋁ ls
      assuming #[t] <| addClause ls
      for l in ls do
        addClause #[-l, t]
      return t

end Tseitin
