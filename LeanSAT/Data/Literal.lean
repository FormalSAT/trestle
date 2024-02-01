import LeanSAT.Data.Cnf

namespace LeanSAT

structure Literal (ν : Type u) : Type u where
  toVar : ν
  polarity : Bool

namespace Literal

instance : LitVar (Literal ν) ν where
  mkPos := fun v => ⟨v,true⟩
  mkNeg := fun v => ⟨v,false⟩
  negate := fun ⟨v,p⟩ => ⟨v,!p⟩
  toVar := toVar
  polarity := polarity

instance : LawfulLitVar (Literal ν) ν where
  toVar_negate := by aesop
  toVar_mkPos := by aesop
  toVar_mkNeg := by aesop
  polarity_negate := by aesop
  polarity_mkPos := by aesop
  polarity_mkNeg := by aesop
  ext := by intro l1 l2; cases l1; cases l2; aesop
