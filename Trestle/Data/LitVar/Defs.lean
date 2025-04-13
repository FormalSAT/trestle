/-
Copyright (c) 2025 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.
-/

namespace Trestle

/-! ### Literals -/

/-- The type `L` is a representation of literals over variables of type `ν`. -/
@[specialize]
class LitVar (L : Type u) (ν : outParam $ Type v) where
  negate : L → L
  mkPos : ν → L
  mkNeg : ν → L := fun x => negate (mkPos x)
  toVar : L → ν
  /-- true if positive -/
  polarity : L → Bool
  -- TODO: ν moreover needs to biject with PNat (perhaps in a separate typeclass)
  -- so that we can use variable names as array indices

namespace LitVar

def mkLit (L : Type u) {ν : Type v} [LitVar L ν] (x : ν) (p : Bool) : L :=
  if p then mkPos x else mkNeg x

def map [LitVar L V] [LitVar L' V'] (f : V → V') (l : L) : L' :=
  LitVar.mkLit _ (f (LitVar.toVar l)) (LitVar.polarity l)

variable {L : Type u} {ν : Type v} [LitVar L ν]

-- controversial maybe?
instance : Coe ν L :=
  ⟨mkPos⟩

instance : Neg L :=
  ⟨negate⟩

@[simp] theorem negate_eq (l : L) : negate l = -l := rfl

instance [ToString ν] : ToString L where
  toString l := if polarity l then s!"{toVar l}" else s!"-{toVar l}"

end LitVar

/-! ### Lawful literals -/

-- TODO: see if a shorter list of axioms implies this one
open LitVar in
class LawfulLitVar (L : Type u) (ν : outParam (Type v)) [LitVar L ν] where
  toVar_negate (l : L) : toVar (-l) = toVar l
  toVar_mkPos (x : ν) : toVar (mkPos (L := L) x) = x
  toVar_mkNeg (x : ν) : toVar (mkNeg (L := L) x) = x
  polarity_negate (l : L) : polarity (-l) = !polarity l
  polarity_mkPos (x : ν) : polarity (mkPos (L := L) x) = true
  polarity_mkNeg (x : ν) : polarity (mkNeg (L := L) x) = false
  protected ext (l₁ l₂ : L) : toVar l₁ = toVar l₂ → polarity l₁ = polarity l₂ → l₁ = l₂

open LawfulLitVar in
attribute [simp] toVar_negate toVar_mkPos toVar_mkNeg polarity_negate polarity_mkPos polarity_mkNeg

open LawfulLitVar in
attribute [ext] LawfulLitVar.ext


/-! #### Sums as valid literals -/

namespace LitVar

instance [LitVar L1 V1] [LitVar L2 V2] : LitVar (L1 ⊕ L2) (V1 ⊕ V2) where
  mkPos := Sum.map (LitVar.mkPos) (LitVar.mkPos)
  mkNeg := Sum.map (LitVar.mkNeg) (LitVar.mkNeg)
  toVar := Sum.map (LitVar.toVar) (LitVar.toVar)
  polarity := fun | .inl l => LitVar.polarity l | .inr l => LitVar.polarity l
  negate := Sum.map (LitVar.negate) (LitVar.negate)

end LitVar

end Trestle
