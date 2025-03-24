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

/- Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ProxyType


@[inline]
def Fin.pair (x : Fin m) (y : Fin n) : Fin (m * n) :=
  ⟨ x * n + y, by
    rcases x with ⟨x,hx⟩; rcases y with ⟨y,hy⟩
    simp
    calc
      _ < x * n + n := by simp [hx,hy]
      _ ≤ (x+1) * n := by rw [Nat.succ_mul]
      _ ≤ m * n := Nat.mul_le_mul_right _ hx⟩

@[inline]
def Fin.pair_left : Fin (m * n) → Fin m
| ⟨p,h⟩ =>
  ⟨ p / n, by
    rw [Nat.div_lt_iff_lt_mul]
    · exact h
    · by_contra; simp_all
  ⟩

@[inline]
def Fin.pair_right : Fin (m * n) → Fin n
| ⟨p,h⟩ =>
  ⟨ p % n, by
    apply Nat.mod_lt
    by_contra; simp_all
  ⟩

@[simp]
theorem Fin.pair_left_pair (x : Fin m) (y : Fin n) : Fin.pair_left (Fin.pair x y) = x := by
  rcases x with ⟨x,hx⟩; rcases y with ⟨y,hy⟩
  simp [pair_left, pair]
  have : n > 0 := by by_contra; simp_all
  rw [Nat.mul_comm, Nat.mul_add_div this]
  simp [hy]

@[simp]
theorem Fin.pair_right_pair (x : Fin m) (y : Fin n) : Fin.pair_right (Fin.pair x y) = y := by
  rcases x with ⟨x,hx⟩; rcases y with ⟨y,hy⟩
  simp [pair_right, pair]
  have : n > 0 := by by_contra; simp_all
  apply Nat.mod_eq_of_lt hy

@[simp]
theorem Fin.pair_left_right (p : Fin (m * n)) : Fin.pair (Fin.pair_left p) (Fin.pair_right p) = p := by
  rcases p with ⟨p,hp⟩
  simp [pair, pair_left, pair_right]
  exact Nat.div_add_mod' p n

theorem Fin.pair_succ_left (x : Fin m) (y : Fin n) : (Fin.pair (x.succ) y).val = Fin.pair x y + n := by
  simp [pair, Nat.add_mul]; ring

theorem Fin.pair_ge_left (x : Fin m) (y : Fin n) : Fin.pair x y ≥ x.val * n := by simp [pair]

/-! ## Index Types

Index types are types which can serve as the index into a sequence.
Every index type is in bijection with `Fin n`.

N.B. this is equivalent to [Fintype] in mathlib, but [Fintype] has many
instances with very bad computational complexity.
-/

namespace Trestle

class IndexType.{u} (ι : Type u) where
  card : Nat
  toFin : ι → Fin card
  fromFin : Fin card → ι

class LawfulIndexType (ι : Type u) [I : IndexType ι] where
  leftInv  : Function.LeftInverse  I.fromFin I.toFin
  rightInv : Function.RightInverse I.fromFin I.toFin

namespace IndexType

def toList (α) [IndexType α] : List α :=
  List.ofFn IndexType.fromFin

variable [IndexType ι] [LawfulIndexType ι]

@[simp] theorem toFin_fromFin
  : ∀ i, toFin (ι := ι) (fromFin i) = i
  := LawfulIndexType.rightInv

@[simp] theorem fromFin_toFin
  : ∀ x, fromFin (ι := ι) (toFin x) = x
  := LawfulIndexType.leftInv

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
  : List.length (toList α) = IndexType.card α := by
  rw [IndexType.toList]; simp

@[simp]
theorem get_toList_univ [IndexType α] [LawfulIndexType α] (i)
  : List.get (toList α) i = IndexType.fromFin (i.cast (by simp)) := by
  suffices ∀ L i (hL : L = toList (α)), List.get L i = fromFin (i.cast (by simp [hL]))
    from this _ _ rfl
  intro L i hL
  rw [toList] at hL
  subst hL
  simp [Fin.cast]

@[simp]
theorem getElem_toList_univ [IndexType α] [LawfulIndexType α] (i) (h : i < (toList α).length)
  : (toList α)[i]'h = IndexType.fromFin ⟨i,by simpa using h⟩ := by
  have := get_toList_univ (α := α) ⟨i,by simpa using h⟩
  simpa using this

@[simp]
theorem mem_toList_univ [IndexType α] [LawfulIndexType α] (x) : x ∈ (toList α) := by
  simp [toList, List.mem_ofFn]
  use toFin x
  simp

instance (priority := default) : DecidableEq ι := by
  intro x y; rw [← toFin_eq_iff]; infer_instance

instance : Fintype ι where
  elems := (toList ι).toFinset
  complete := by simp


/-! #### Transport over equivalence -/

def ofEquiv {ι} [IndexType.{_} ι'] (f : ι' ≃ ι) : IndexType.{_} ι where
  card := IndexType.card ι'
  toFin   := IndexType.toFin ∘ f.symm
  fromFin := f ∘ IndexType.fromFin

def ofEquivLawful {ι} [I' : IndexType ι'] [LI' : LawfulIndexType ι'] (f : ι' ≃ ι)
    : @LawfulIndexType ι (ofEquiv f) :=
  @LawfulIndexType.mk
    (ι := ι)
    (I := ofEquiv f)
    (leftInv  := by simp [ofEquiv]; intro; simp)
    (rightInv := by simp [ofEquiv]; intro; simp)

/-! #### Unit -/

instance : IndexType Unit where
  card := 1
  toFin := fun () => 0
  fromFin := fun 0 => ()

instance : LawfulIndexType Unit where
  leftInv := by intro; rfl
  rightInv := by rintro ⟨i,h⟩; simp [card] at h; subst h; simp [fromFin, toFin]

/-! #### Fin n -/

instance : IndexType (Fin n) where
  card := n
  toFin := id
  fromFin := id

instance : LawfulIndexType (Fin n) where
  leftInv  := by intro _; rfl
  rightInv := by intro _; rfl


section
variable {α : Type u} [IndexType.{u} α] [LawfulIndexType.{u} α]
         {β : Type v} [IndexType.{v} β] [LawfulIndexType.{v} β]

/-! #### Product -/

instance : IndexType.{max u v} (α × β) where
  card := card α * card β
  toFin := fun (a,b) => Fin.pair (toFin a) (toFin b)
  fromFin := fun p => (fromFin (Fin.pair_left p), fromFin (Fin.pair_right p))

instance : LawfulIndexType.{max u v} (α × β) where
  rightInv := by
    rintro ⟨i,hi⟩; simp [toFin, fromFin]
  leftInv := by
    rintro ⟨a,b⟩; simp [toFin, fromFin]


/-! #### Sigma -/

instance : IndexType.{max u v} ((_ : α) × β) :=
  IndexType.ofEquiv (Equiv.sigmaEquivProd α β).symm

instance : LawfulIndexType.{max u v} ((_ : α) × β) :=
  IndexType.ofEquivLawful _


/-! #### Sum -/

instance : IndexType.{max u v} (α ⊕ β) where
  card := card α + card β
  toFin := fun x =>
    match x with
    | .inl a =>
      let ⟨a,ha⟩ := toFin a
      ⟨ a, Nat.lt_add_right (card β) ha ⟩
    | .inr b =>
      let ⟨b,hb⟩ := toFin b
      ⟨ card α + b, Nat.add_lt_add_left hb _ ⟩
  fromFin := fun ⟨i,hi⟩ =>
    if h : i < card α then
      .inl (fromFin ⟨i,h⟩)
    else
      .inr (fromFin ⟨i-card α, by simp at h; exact Nat.sub_lt_left_of_lt_add h hi⟩)

instance : LawfulIndexType (α ⊕ β) where
  leftInv := by
    rintro (a|b)
      <;> simp [toFin, fromFin]
  rightInv := by
    rintro ⟨i,hi⟩
    simp [toFin, fromFin]
    if i < card α then
      simp_all
    else
      simp [*]; simp_all


end


/-! #### Generic inductives -/

section
open Lean Elab Command

macro "derive_indextype% " t:term : term => `(term| IndexType.ofEquiv (proxy_equiv% $t))
macro "derive_lawfulindextype% " t:term : term => `(term| IndexType.ofEquivLawful (proxy_equiv% $t))

def mkIndexType (declName : Name) : CommandElabM Bool := do
  let indVal ← getConstInfoInduct declName
  let cmds ← liftTermElabM do
    let header ← Deriving.mkHeader ``IndexType 0 indVal
    let lawfulBinders: TSyntaxArray `Lean.Parser.Term.bracketedBinder :=
      .mk (← Deriving.mkInstImplicitBinders ``LawfulIndexType indVal header.argNames)
    let indexType ← `(command|
      instance $header.binders:bracketedBinder* :
          IndexType $header.targetType := derive_indextype% $header.targetType)
    let lawful ← `(command|
      instance $header.binders:bracketedBinder* $lawfulBinders:bracketedBinder* :
          LawfulIndexType $header.targetType := derive_lawfulindextype% $header.targetType)
    return #[indexType, lawful]
  trace[Elab.Deriving.indextype] "instance commands:\n{cmds}"
  for cmd in cmds do
    elabCommand cmd
  return true

def mkIndexTypeInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size != 1 then
    return false -- mutually inductive types are not supported
  let declName := declNames[0]!
  mkIndexType declName

initialize
  registerDerivingHandler ``IndexType mkIndexTypeInstanceHandler
  registerTraceClass `Elab.Deriving.indextype

end
