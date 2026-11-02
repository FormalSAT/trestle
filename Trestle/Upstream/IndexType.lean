/-

A minimal port of `IndexType` from `LeanColls`.

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

Copyright (c) 2026 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio, Cayden Codel
-/

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ProxyType
import Mathlib.Data.Finset.Dedup
import Trestle.Upstream.ToStd

namespace Fin

@[inline]
def pair (x : Fin m) (y : Fin n) : Fin (m * n) :=
  ⟨ x * n + y, by
    rcases x with ⟨x,hx⟩; rcases y with ⟨y,hy⟩
    simp
    calc
      _ < x * n + n := by simp [hy]
      _ ≤ (x+1) * n := by rw [Nat.succ_mul]
      _ ≤ m * n := Nat.mul_le_mul_right _ hx⟩

@[inline]
def pair_left : Fin (m * n) → Fin m
| ⟨p,h⟩ =>
  ⟨ p / n, by
    rw [Nat.div_lt_iff_lt_mul]
    · exact h
    · by_contra; simp_all
  ⟩

@[inline]
def pair_right : Fin (m * n) → Fin n
| ⟨p,h⟩ =>
  ⟨ p % n, by
    apply Nat.mod_lt
    by_contra; simp_all
  ⟩

@[simp]
theorem pair_left_pair (x : Fin m) (y : Fin n) : pair_left (pair x y) = x := by
  rcases x with ⟨x,hx⟩; rcases y with ⟨y,hy⟩
  simp [pair_left, pair]
  have : n > 0 := by by_contra; simp_all
  rw [Nat.mul_comm, Nat.mul_add_div this]
  simp [hy]

@[simp]
theorem pair_right_pair (x : Fin m) (y : Fin n) : pair_right (pair x y) = y := by
  rcases x with ⟨x,hx⟩; rcases y with ⟨y,hy⟩
  simp [pair_right, pair]
  have : n > 0 := by by_contra; simp_all
  apply Nat.mod_eq_of_lt hy

@[simp]
theorem pair_left_right (p : Fin (m * n)) : pair (pair_left p) (pair_right p) = p := by
  rcases p with ⟨p,hp⟩
  simp [pair, pair_left, pair_right]
  exact Nat.div_add_mod' p n

theorem pair_succ_left (x : Fin m) (y : Fin n) : (Fin.pair (x.succ) y).val = Fin.pair x y + n := by
  simp [pair, Nat.add_mul]; ring

theorem pair_ge_left (x : Fin m) (y : Fin n) : pair x y ≥ x.val * n := by simp [pair]

end Fin /- namespace -/

/-! ## Index Types -/

namespace Trestle

/--
Index types are types which can serve as the index into a sequence.
Every index type is in bijection with `Fin n`.

N.B. this is equivalent to [Fintype] in mathlib, but [Fintype] has many
instances with very bad computational complexity.
-/
class IndexType (ι : Type u) where
  card : Nat
  toFin : ι → Fin card
  fromFin : Fin card → ι

class LawfulIndexType (ι : Type u) [I : IndexType ι] where
  leftInv  : Function.LeftInverse  I.fromFin I.toFin
  rightInv : Function.RightInverse I.fromFin I.toFin

namespace IndexType

variable {ι : Type u} [I : IndexType ι]

def toList (ι : Type u) [IndexType ι] : List ι :=
  List.ofFn IndexType.fromFin

def toArray (ι : Type u) [IndexType ι] : Array ι :=
  Array.ofFn IndexType.fromFin

@[simp] theorem toList_length : (toList ι).length = I.card := by simp [toList]
@[simp] theorem toArray_length : (toArray ι).size = I.card := by simp [toArray]

theorem drop_toList_of_ge_card {n : Nat} (h : n ≥ I.card) : (toList ι).drop n = [] := by
  simp [toList, h]

/-! # forIn -/

/-

A slightly different for-loop interface for index types.

Typically, `ForIn' m ρ α` loops across a collection of type `ρ`.
For example, in the case of arrays we write `for x in arr do ...`.
Ideally, we could do the same thing for index types, by replacing `arr` with
the type `ι`.

However, `for` must be able to infer the type of the loop element from the
container type, and writing `ι` is not sufficient. Instead, we can loop across
the instance `IndexType ι`, as that allows the for-loop to infer the loop type.
In other words, by treating `[IndexType ι]` as the collection and not as an
inferred type class, we can write `for x in I do ...`.

To do this, we define `univ` as the thing to iterate over.
We then supply a `ForIn'` instance to loop over the elements of the universe
from `fromFin 0` to `fromFin (card ι - 1)`.

-/

/-- All elements of `ι`, i.e., its universe. This is just the `IndexType ι` instance. -/
@[inline, reducible] def univ (ι : Type u) [I : IndexType ι] : IndexType ι := I

/-- An element of type `ι` is a member of the `IndexType ι` instance. -/
instance instMembership : Membership ι (IndexType ι) :=
  ⟨fun I i => ∃ (idx : Fin I.card), i = I.fromFin idx⟩

theorem mem_def {i : ι} : i ∈ I ↔ ∃ (idx : Fin I.card), i = I.fromFin idx := Iff.rfl

@[simp] theorem mem_univ_iff_mem {i : ι} : i ∈ univ ι ↔ i ∈ I := by rfl

theorem mem_iff_mem_toList {i : ι} : i ∈ I ↔ i ∈ I.toList := by
  simp [toList, mem_def]
  tauto

theorem mem_iff_mem_toArray {i : ι} : i ∈ I ↔ i ∈ I.toArray := by
  simp [toArray, mem_def]
  tauto

@[simp]
theorem fromFin_mem (i : Fin I.card) : I.fromFin i ∈ I := by
  simp [mem_def]

theorem mem_drop_of_mem_toList {i : ι} {n : Nat} (h : i ∈ I.toList.drop n) : i ∈ I :=
  mem_iff_mem_toList.mpr <| List.mem_of_mem_drop h

/-- Loops over the elements of the index type from `i` to `(I.card - 1)`. -/
@[specialize]
def forInLoop {m : Type v → Type w} [Monad m] {β : Type v}
    (f : (a : ι) → (a ∈ I) → β → m (ForInStep β)) (i : Nat) (b : β) : m β :=
  if h : i < I.card then do
    match ← f (I.fromFin ⟨i, h⟩) (fromFin_mem ⟨i, h⟩) b with
    | .done b => pure b
    | .yield b => forInLoop f (i + 1) b
  else
    pure b

/- NOTE: This also generates a `ForIn` instance, where `f` drops the `a ∈ I` argument. -/
instance instForIn' {m : Type v → Type w} [Monad m] : ForIn' m (IndexType ι) ι inferInstance where
  forIn' _ b f := forInLoop f 0 b

theorem forInLoop_eq_of_card_zero {m : Type v → Type w} [Monad m] {β : Type v} (i : Nat) (f) (b : β) :
    (I.card = 0) → forInLoop (I := I) (m := m) f i b = pure b := by
  intro h
  rw [forInLoop]
  simp [h]

/-- `forInLoop` is equal to iterating across the appropriate prefix `(toList ι).drop`. -/
theorem forInLoop_eq {m : Type v → Type w} [Monad m] {β : Type v}
    (f : (a : ι) → (a ∈ I) → β → m (ForInStep β)) (i : Nat) (b : β) :
    forInLoop f i b = forIn' ((toList ι).drop i) b (f · <| mem_drop_of_mem_toList ·) := by
  induction i, b using forInLoop.induct (I := I) with
  | case1 i b h ih =>
    unfold forInLoop
    simp only [List.drop_eq_getElem_cons (i := i) (l := toList ι) (by simpa), List.forIn'_cons]
    simp only [dif_pos h, toList, List.getElem_ofFn]
    congr 1; funext r; cases r
    · rfl
    · simp; apply ih
  | case2 i b h =>
    unfold forInLoop
    simp [h, drop_toList_of_ge_card (Nat.ge_of_not_lt h)]

/-- The for-loop over an `IndexType ι` is equal to iterating over its `(toList ι)`. -/
theorem forIn'_eq_forIn'_toList {ι : Type u} {m : Type v → Type w} [Monad m] {β : Type v}
    (I : IndexType ι) (b : β) (f : (a : ι) → (a ∈ I) → β → m (ForInStep β)) :
    forIn' I b f = forIn' (toList ι) b (f · <| mem_iff_mem_toList.mpr ·) :=
  forInLoop_eq f 0 b

theorem forIn_eq_forIn_toList {ι : Type u} {m : Type v → Type w} [Monad m] {β : Type v}
    (I : IndexType ι) (b : β) (f : ι → β → m (ForInStep β)) :
    forIn I b f = forIn (toList ι) b f :=
  forIn'_eq_forIn'_toList I b (fun a _ => f a)

variable [LawfulIndexType ι]

@[simp] theorem toFin_fromFin : ∀ i, toFin (ι := ι) (fromFin i) = i := LawfulIndexType.rightInv
@[simp] theorem fromFin_toFin : ∀ x, fromFin (ι := ι) (toFin x) = x := LawfulIndexType.leftInv

/-- An `IndexType ι` is isomorphic to `Fin (card ι)`, i.e., we can label each element of an `IndexType`.-/
def toEquiv : ι ≃ Fin (card ι) where
  toFun := IndexType.toFin
  invFun := IndexType.fromFin
  left_inv := LawfulIndexType.leftInv
  right_inv := LawfulIndexType.rightInv

@[simp]
theorem toFin_inj {x y : ι} : toFin x = toFin y ↔ x = y := by
  constructor
  · apply toEquiv.injective
  · rintro rfl; rfl

@[simp]
theorem fromFin_inj {x y : Fin (card ι)} : fromFin x = fromFin y ↔ x = y := by
  constructor
  · apply toEquiv.symm.injective
  · rintro rfl; rfl

omit [LawfulIndexType ι] in
@[simp]
theorem get_toList_univ (i) : List.get (toList ι) i = fromFin (i.cast (by simp)) := by
  obtain ⟨i, hi⟩ := i
  simp [toList, Fin.cast]

omit [LawfulIndexType ι] in
@[simp]
theorem getElem_toList_eq_fromFin {i} (h : i < card ι)
    : (toList ι)[i]'(by simpa) = fromFin ⟨i, by simpa using h⟩ := by
  have := get_toList_univ (ι := ι) ⟨i,by simpa using h⟩
  simpa using this

@[simp]
theorem mem_univ (i : ι) : i ∈ I := by
  rw [mem_def]
  use toFin i
  simp

@[simp]
theorem mem_toList (i) : i ∈ (toList ι) :=
  mem_iff_mem_toList.mp <| mem_univ _

@[simp]
theorem mem_toArray (i) : i ∈ (toArray ι) :=
  mem_iff_mem_toArray.mp <| mem_univ _

instance (priority := default) instDecidableEq : DecidableEq ι := by
  intro x y; rw [← toFin_inj]; infer_instance

instance instFintype : Fintype ι where
  elems := (toList ι).toFinset
  complete := by simp


/-! #### Transport over equivalence -/

@[instance_reducible]
def ofEquiv {ι} [IndexType.{_} ι'] (f : ι' ≃ ι) : IndexType.{_} ι where
  card    := IndexType.card ι'
  toFin   := IndexType.toFin ∘ f.symm
  fromFin := f ∘ IndexType.fromFin

theorem ofEquivLawful {ι} [I' : IndexType ι'] [LI' : LawfulIndexType ι'] (f : ι' ≃ ι)
    : @LawfulIndexType ι (ofEquiv f) :=
  @LawfulIndexType.mk
    (ι := ι)
    (I := ofEquiv f)
    (leftInv  := by intro x; unfold ofEquiv; simp)
    (rightInv := by intro x; unfold ofEquiv; simp)

/-! ## Empty -/

instance instEmptyIndexType : IndexType Empty where
  card := 0
  toFin := fun x => x.elim
  fromFin := fun x => x.elim0

instance instEmptyLawfulIndexType : LawfulIndexType Empty where
  leftInv := fun x => x.elim
  rightInv := by rintro ⟨i, h⟩; simp [card] at h

instance instPEmptyIndexType : IndexType PEmpty where
  card := 0
  toFin := fun x => x.elim
  fromFin := fun x => x.elim0

instance instPEmptyLawfulIndexType : LawfulIndexType PEmpty where
  leftInv := fun x => x.elim
  rightInv := by rintro ⟨i, h⟩; simp [card] at h

/-! ## Unit -/

instance instUnitIndexType : IndexType Unit where
  card := 1
  toFin := fun () => 0
  fromFin := fun 0 => ()

instance instUnitLawfulIndexType : LawfulIndexType Unit where
  leftInv := by intro; rfl
  rightInv := by rintro ⟨i, h⟩; simp [card] at h; subst h; simp [toFin]

instance instPUnitIndexType : IndexType PUnit where
  card := 1
  toFin := fun () => 0
  fromFin := fun 0 => ()

instance instPUnitLawfulIndexType : LawfulIndexType PUnit where
  leftInv := by intro; rfl
  rightInv := by rintro ⟨i, h⟩; simp [card] at h; subst h; simp [toFin]

instance instBoolIndexType : IndexType Bool where
  card := 2
  toFin := fun b => cond b 1 0
  fromFin := fun i => i = 1

instance instBoolLawfulIndexType : LawfulIndexType Bool where
  leftInv := by intro b; cases b <;> simp [toFin, fromFin]
  rightInv := by
    rintro ⟨i, h⟩; simp [toFin, fromFin]
    cases i
    · simp
    · rename_i n
      simp [card] at h
      have : n = 0 := by omega
      subst this
      simp

/-! ## Fin -/

instance instFinIndexType : IndexType (Fin n) where
  card := n
  toFin := id
  fromFin := id

instance instFinLawfulIndexType : LawfulIndexType (Fin n) where
  leftInv  := by intro _; rfl
  rightInv := by intro _; rfl


section

variable {α : Type u} [IndexType α] [LawfulIndexType α]
         {β : Type v} [IndexType β] [LawfulIndexType β]

/-! ## Product -/

instance instProductIndexType : IndexType (α × β) where
  card := card α * card β
  toFin := fun (a, b) => Fin.pair (toFin a) (toFin b)
  fromFin := fun p => (fromFin (Fin.pair_left p), fromFin (Fin.pair_right p))

instance instProductLawfulIndexType : LawfulIndexType (α × β) where
  rightInv := by rintro ⟨i, hi⟩; simp [toFin, fromFin]
  leftInv := by rintro ⟨a, b⟩; simp [toFin, fromFin]


/-! ## Sigma -/

instance instSigmaIndexType : IndexType ((_ : α) × β) :=
  IndexType.ofEquiv (Equiv.sigmaEquivProd α β).symm

instance instSigmaLawfulIndexType : LawfulIndexType ((_ : α) × β) :=
  IndexType.ofEquivLawful _


/-! ## Sum -/

instance instSumIndexType : IndexType (α ⊕ β) where
  card := card α + card β
  toFin := fun x =>
    match x with
    | .inl a =>
      let ⟨a, ha⟩ := toFin a
      ⟨ a, Nat.lt_add_right (card β) ha ⟩
    | .inr b =>
      let ⟨b, hb⟩ := toFin b
      ⟨ card α + b, Nat.add_lt_add_left hb _ ⟩
  fromFin := fun ⟨i, hi⟩ =>
    if h : i < card α then
      .inl (fromFin ⟨i, h⟩)
    else
      .inr (fromFin ⟨i - card α, by simp at h; exact Nat.sub_lt_left_of_lt_add h hi⟩)

instance instSumLawfulIndexType : LawfulIndexType (α ⊕ β) where
  leftInv := by rintro (a | b) <;> simp [toFin, fromFin]
  rightInv := by
    rintro ⟨i, hi⟩
    simp [toFin, fromFin]
    if i < card α then
      simp_all
    else
      simp [*]; simp_all

end /- section -/

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

end /- section -/
