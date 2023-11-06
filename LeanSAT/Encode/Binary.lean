import LeanSAT.Encode.EncCNF
import LeanSAT.Encode.Tseitin
import LeanSAT.Preprocess.BlockedClauseElim

namespace LeanSAT.Encode

open Model EncCNF Tseitin

/-- binary number represented as `width` variables.
    the least significant bit is index 0. -/
def BinNumber (width : Nat) := EncCNF.IVarBlock [width]

namespace BinNumber

instance : Inhabited (BinNumber w) := inferInstanceAs (Inhabited (EncCNF.IVarBlock _))

open PropForm.Notation

/-- formula stating that `res = x` -/
def eq (res x : BinNumber width) : PropForm ILit :=
  .conj' <| (List.fins _).map (fun i => (res.get i) ↔ (x.get i))

/-- encode constraint that `res = n (mod 2^width)`. -/
def eqConst (res : BinNumber width) (n : Nat) : PropForm ILit :=
  .conj' <|
    (List.fins width).map (fun i =>
      if (n >>> i.val) % 2 = 0 then
        (-res.get i : ILit)
      else
        res.get i
    )

/-- encode constraint that `res = x + 1 (mod 2^width)` -/
def eqSucc (res x : BinNumber width) : EncCNF (PropForm ILit) :=
  newCtx "eqSucc." do
  let carries ← mkTempBlock [width]
  return .conj' <|
    (List.fins width).bind (fun i =>
    match i.pred? with
    | none =>
      [ res.get i ↔ ¬x.get i
      , carries.get i ↔ x.get i ]
    | some i' =>
      [ res.get i ↔ (x.get i ↔ ¬ carries.get i')
      , carries.get i ↔ (x.get i ∧ carries.get i') ]
    )

/-- encode constraint `x < y` -/
def lt (x y : BinNumber width) : EncCNF (PropForm ILit) :=
  newCtx "lt." do
  let higherBitsEq ← mkTempBlock [width]
  let eqSetup : PropForm ILit :=
    .conj' <| (List.fins width).map (fun i =>
      match i.succ? with
      | none => higherBitsEq.get i
      | some i' =>
        higherBitsEq.get i ↔ higherBitsEq.get i' ∧ (x.get i' ↔ y.get i')
    )
  return .conj eqSetup <| .disj' <|
    (List.fins width).map (fun i =>
      higherBitsEq.get i ∧ ¬x.get i ∧ y.get i
    )
