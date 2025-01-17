/-

A minimal port of `IndexType` from `LeanColls`.

We are planning to remove this copy.

When generating a CNF, we need a way to map
the problem variables `ν` to variable indices `ℕ`.
We can build up this map at runtime,
but debugging is easier when this map is constant
(i.e. does not depend on the form of the CNF).

For finite types, `IndexType ν` provides a map `ν → Fin (card ν)`.
`LeanColls` also had a deriver for inductive types.
This was useful for giving a constant variable map.
But by requiring this, instead of dynamically building up the variable map,
we limit ourselves to finite variable types.

-/

import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Equiv.Defs

/-! ## Index Types

Index types are types which can serve as the index into a sequence.
Every index type is in bijection with `Fin n`.

N.B. this is equivalent to [Fintype] in mathlib, but [Fintype] has many
instances with very bad computational complexity.
-/


structure IndexType.Univ (ι : Type u)

def IndexType.univ (ι : Type u) : IndexType.Univ ι := .mk

/-instance IndexType.instFoldUnivFin : Fold (Univ (Fin n)) (Fin n) where
  fold := fun ⟨⟩ => Fin.foldl _
  foldM := fun ⟨⟩ f init => Fin.foldlM _ f init -/

class IndexType.{u,w} (ι : Type u) where
  /-- full (not early-terminating) fold over the elements of `C` -/
  fold : {β : Type w} → (cont : C) → (β → τ → β) → β → β
  /-- monadic fold over the elements of `C` -/
  foldM : {β : Type w} → {m : Type w → Type w} → [Monad m] →
      (cont : C) → (β → τ → m β) → β → m β
    := fun c f i => fold c (fun macc x => macc >>= fun acc => f acc x) (pure i)
  -- The cardinality of the universe of the index type
  card : Nat
  -- Establish a bijection with `Fin card`
  toFin : ι → Fin card
  fromFin : Fin card → ι
  -- Get a list of all index objects of this type
  toList := List.ofFn fromFin


class LawfulIndexType (ι : Type u) [I : IndexType ι]
  where
  leftInv  : Function.LeftInverse  I.fromFin I.toFin
  rightInv : Function.RightInverse I.fromFin I.toFin
  -- In case the instance provides a different operation, they must be equivalent
  toList_eq_ofFn : IndexType.toList = List.ofFn (@IndexType.fromFin _ I) := by rfl

namespace IndexType

variable [IndexType ι] [LawfulIndexType ι]

@[simp] theorem toFin_fromFin : ∀ i, toFin (ι := ι) (fromFin i) = i :=
  LawfulIndexType.rightInv

@[simp] theorem fromFin_toFin : ∀ x, fromFin (ι := ι) (toFin x) = x :=
  LawfulIndexType.leftInv

@[simp] theorem toFin_inj (i j : ι) : toFin i = toFin j ↔ i = j := by
  constructor
  · apply LawfulIndexType.leftInv.injective
  · rintro rfl; rfl

@[simp] theorem fromFin_inj (i j : Fin (IndexType.card ι)) : fromFin i = fromFin j ↔ i = j := by
  constructor
  · apply LawfulIndexType.rightInv.injective
  · rintro rfl; rfl

def toEquiv : ι ≃ Fin (IndexType.card ι) where
  toFun := IndexType.toFin
  invFun := IndexType.fromFin
  left_inv := LawfulIndexType.leftInv
  right_inv := LawfulIndexType.rightInv

theorem toFin_eq_iff (x y : ι) : toFin x = toFin y ↔ x = y := by
  constructor
  · apply toEquiv.injective
  · rintro rfl; rfl

theorem fromFin_eq_iff (x y : Fin _) : (fromFin x : ι) = fromFin y ↔ x = y := by
  constructor
  · apply toEquiv.symm.injective
  · rintro rfl; rfl

@[simp]
theorem length_toList_univ [IndexType α] [LawfulIndexType α]
  : List.length (@IndexType.toList α _) = IndexType.card α := by
  rw [LawfulIndexType.toList_eq_ofFn, List.length_ofFn]
