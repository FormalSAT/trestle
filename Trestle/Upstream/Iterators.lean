/-
Copyright (c) 2026 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: Cayden Codel
-/

import Trestle.Upstream.ToStd
import Trestle.Upstream.IndexType
import Trestle.Upstream.IndexTypeInstances
import Mathlib.Data.List.Chain

/-! # Iterators

This file provides type classes for lawful iteration across collections.
The hope is to expand what can be proved with `Std.Iter`, while also being
more general and allowing for different kinds of iteration schemes.

The key definitions are:

- `ToList γ α`, a type class that provides a way to convert a collection of type `γ`
  to a list of elements of type `α`. By varying `α`, we can express different
  "iteration types" for for-loops. Specification only, not computed at runtime.
- `LawfulForIn m γ α`, a type class relating an iteration across `c : γ` and
  iteration across `(toList c)`. The specification of a "well-behaved" for-loop.

To make a new data structure iterable (e.g. the edges of a graph), give it
`ForIn`, `ToList`, and `LawfulForIn` instances, or an `Indexed` instance
to get `pairs` and `adjacent` for free.
-/

namespace List

/-
First, we define some reference implementations for the new kinds of iterators
that appear later in this file. These are usually inefficient, so don't use
them as default instances for a `ForIn` or `LawfulForIn` instance.
-/

/-! ## pairs -/

/--
  A list of all pairs of elements `(L[i], L[j])` with `i < j`,
  in increasing lexicographic order of `(i, j)`.

  Examples:
  ```
    [1, 2, 3].pairs = [(1, 2), (1, 3), (2, 3)]
    [5].pairs = []
  ```
-/
@[specialize]
def pairs : List α → List (α × α)
  | []     => []
  | a :: l => l.map (a, ·) ++ pairs l

@[simp] theorem pairs_nil : ([] : List α).pairs = [] := rfl
@[simp] theorem pairs_singleton (a : α) : [a].pairs = [] := rfl
@[simp] theorem pairs_pair (a b : α) : [a, b].pairs = [(a, b)] := rfl
@[simp] theorem pairs_cons (a : α) (l : List α) : (a :: l).pairs = l.map (a, ·) ++ l.pairs := rfl

@[simp]
theorem mem_pairs_iff {a b : α} {L : List α} : (a, b) ∈ L.pairs ↔ [a, b] <+ L := by
  induction L with
  | nil => simp
  | cons x l ih => simp [ih, List.sublist_cons_iff]; tauto

theorem forall_mem_pairs_iff_Pairwise {R : α → α → Prop} {L : List α}
    : (∀ p ∈ L.pairs, R p.1 p.2) ↔ L.Pairwise R := by
  simp [List.pairwise_iff_forall_sublist]

/-! # adjacentPairs -/

/--
  The list of all adjacent pairs of elements `(L[i], L[i + 1])` of a list `L`,
  in increasing order of `i`.

  Examples:
  ```
    [1, 2, 3, 4].adjacentPairs = [(1, 2), (2, 3), (3, 4)]
    [1].adjacentPairs = []
  ```
-/
def adjacentPairs (L : List α) : List (α × α) := L.zip L.tail

@[simp] theorem adjacentPairs_nil : ([] : List α).adjacentPairs = [] := rfl
@[simp] theorem adjacentPairs_singleton (a : α) : [a].adjacentPairs = [] := rfl
@[simp] theorem adjacentPairs_pair (a b : α) : [a, b].adjacentPairs = [(a, b)] := rfl
@[simp] theorem adjacentPairs_cons_cons (a b : α) (l : List α) :
    (a :: b :: l).adjacentPairs = (a, b) :: (b :: l).adjacentPairs := rfl

theorem adjacentPairs_eq_nil_of_length_le {L : List α} (h : L.length ≤ 1) : L.adjacentPairs = [] := by
  match L with
  | []  => rfl
  | [a] => rfl
  | (a :: b :: l) => simp at h

@[simp]
theorem mem_adjacentPairs_iff {a b : α} {L : List α}
    : (a, b) ∈ L.adjacentPairs ↔ [a, b] <:+: L := by
  unfold adjacentPairs
  induction L with
  | nil => simp
  | cons x l ih =>
    cases l with
    | nil => simpa using fun h : [a, b] <:+: [x] => by simpa using h.length_le
    | cons y l => simp_all [List.infix_cons_iff]

theorem forall_mem_adjacentPairs_iff_IsChain {R : α → α → Prop} {L : List α}
    : (∀ p ∈ L.adjacentPairs, R p.1 p.2) ↔ L.IsChain R := by
  rw [List.isChain_iff_forall_rel_of_append_cons_cons]
  simp only [Prod.forall, mem_adjacentPairs_iff, List.IsInfix]
  constructor
  · rintro h a b l₁ l₂ rfl; exact h a b ⟨l₁, l₂, by simp⟩
  · rintro h a b ⟨l₁, l₂, rfl⟩; exact h (l₁ := l₁) (l₂ := l₂) (by simp)

theorem forIn_filter [Monad m] [LawfulMonad m] (L : List α) (p : α → Bool)
    (init : β) (f : α → β → m (ForInStep β)) :
    forIn (L.filter p) init f
      = forIn L init (fun a b => if p a then f a b else pure (.yield b)) := by
  induction L generalizing init with
  | nil => simp
  | cons a l ih =>
    by_cases h : p a <;> simp [h, ih]

end List /- namespace -/


open Trestle

/-! ## Lawful `ForIn`

A for-loop is "lawful" if running the loop on a collection `c : γ` returns
the same value as looping over `c` when first converted to a `List`.

We use `ToList` to define `LawfulForIn` in this way. The benefit of
`LawfulForIn` is that we can use `List`s to reason about the correctness
of the loop, but use a lazy strategy to generate the loop at runtime,
which can lead to time/memory savings.

-/

/--
  The class representing collections `c : γ` that can be converted to an ordered `List`.

  We mainly use this class to prove that loops over `c` and `toList c` are equivalent.
  Since `toList` is used is a specification, it need not be efficient.
  See `LawfulForIn`.
-/
class ToList (γ : Type u) (α : outParam (Type v)) where
  toList : γ → List α
export ToList (toList)

/--
  Lawful for-loops.

  An instance of `ForIn m γ α` is lawful when the iteration over `c` in `m`
  is the same as iterating over the list `toList c`. In other words, forcing
  `c` into a list commutes with for-loop iteration.
-/
class LawfulForIn (m : Type u₁ → Type u₂) (γ : Type u) (α : outParam (Type v))
    [Monad m] [ForIn m γ α] [ToList γ α] : Prop where
  forIn_eq_forIn_toList : ∀ {β : Type u₁} (c : γ) (init : β) (f : α → β → m (ForInStep β)),
    forIn c init f = forIn (toList c) init f
export LawfulForIn (forIn_eq_forIn_toList)

instance instListToList : ToList (List α) α := ⟨id⟩
@[simp] theorem toList_list (L : List α) : toList L = L := rfl
instance instListLawfulForIn [Monad m] : LawfulForIn m (List α) α where
  forIn_eq_forIn_toList _ _ _ := rfl

instance instArrayToList : ToList (Array α) α := ⟨Array.toList⟩
@[simp] theorem toList_array (arr : Array α) : toList arr = arr.toList := rfl
instance instArrayLawfulForIn [Monad m] : LawfulForIn m (Array α) α where
  forIn_eq_forIn_toList := by simp

instance instRangeToList : ToList Std.Legacy.Range Nat := ⟨fun r => List.range' r.start r.size r.step⟩
@[simp] theorem toList_range (r : Std.Legacy.Range) :
    toList r = List.range' r.start r.size r.step := rfl
instance instRangeLawfulForIn [Monad m] : LawfulForIn m Std.Legacy.Range Nat where
  forIn_eq_forIn_toList := Std.Legacy.Range.forIn_eq_forIn_range'

instance instIndexTypeToList : ToList (IndexType ι) ι := ⟨fun _ => IndexType.toList ι⟩
@[simp] theorem toList_indexType (I : IndexType ι) : toList I = IndexType.toList ι := rfl
instance instIndexTypeLawfulForIn [Monad m] : LawfulForIn m (IndexType ι) ι where
  forIn_eq_forIn_toList := IndexType.forIn_eq_forIn_toList

/--
  The class for types isomorphic to `Fin n → α`. In other words, `GetElem`
  with `idx := Nat` and `valid := idx < size ·`.

  Rather than writing a new iterator per strategy and collection type
  (e.g. `Pairs` for `Array`s), we can generalize across indexed collections
  where the indexes are contiguous natural numbers up to some `size`.
  In a sense, `Indexed` bridges the gap between functions `(Fin n) → α`
  and `ForIn` instances for different iterators.
-/
class Indexed (γ : Type u) (α : outParam (Type v)) where
  size : γ → Nat
  get : (c : γ) → (i : Nat) → (i < size c) → α
export Indexed (size get)

/-- An `Indexed` collection type `γ` is lawful when its elements match its `ToList` list. -/
class LawfulIndexedToList (γ : Type u) (α : outParam (Type v)) [Indexed γ α] [ToList γ α] : Prop where
  h_len : ∀ (c : γ), (toList c).length = size c
  get_eq_getElem : ∀ (c : γ) (i : Nat) (h : i < size c), get c i h = (toList c)[i]'(by simpa [h_len])

/-- A wrapper for a collection whose iterators should be reversed. -/
structure Reverse (γ : Type u) where
  coll : γ

namespace Reverse

instance instToList [ToList γ α] : ToList (Reverse γ) α where
  toList c := (toList c.coll).reverse

instance instIndexed [Indexed γ α] : Indexed (Reverse γ) α where
  size c := Indexed.size c.coll
  get c i h := Indexed.get c.coll (size c.coll - i - 1) (by omega)

open IndexType in
instance instIndexType [IndexType ι] : IndexType (Reverse ι) where
  card := card ι
  toFin := fun i => IndexType.toFin i.coll |>.rev
  fromFin := fun idx => Reverse.mk (IndexType.fromFin idx.rev)

end Reverse /- namespace -/

/-! # Indexed -/

namespace Indexed

/- NOTE: This instance is not preferred, since `List` operations are O(n) in general. -/
instance instList : Indexed (List α) α where
  size := List.length
  get l i h := l[i]

instance instArray : Indexed (Array α) α where
  size := Array.size
  get arr i h := arr[i]

instance instVector : Indexed (Vector α n) α where
  size _ := n
  get v i h := v[i]

/-- NOTE: This instance is only useful for iteration, otherwise it's meaningless. -/
instance instFin : Indexed (Fin n) (Fin n) where
  size _ := n
  get _ i h := ⟨i, h⟩

instance instIndexType : Indexed (IndexType ι) ι where
  size _ := IndexType.card ι
  get _ i h := IndexType.fromFin ⟨i, h⟩

instance instLawfulList : LawfulIndexedToList (List α) α where
  h_len _ := rfl
  get_eq_getElem _ _ _ := rfl

instance instLawfulArray : LawfulIndexedToList (Array α) α where
  h_len _ := Array.length_toList
  get_eq_getElem _ _ _ := (Array.getElem_toList _).symm

instance instLawfulIndexType [IndexType ι] : LawfulIndexedToList (IndexType ι) ι where
  h_len _ := IndexType.toList_length
  get_eq_getElem _ _ h := (IndexType.getElem_toList_eq_fromFin h).symm

variable {γ : Type u} {α : Type v} [Indexed γ α]

instance instGetElem : GetElem γ Nat α (fun c i => i < size c) where
  getElem := get

/-- If a data type is `Indexed`, then it can be reversed. -/
instance instReversed : Indexed (Reverse γ) α where
  size c := Indexed.size c.coll
  get c i h := Indexed.get c.coll (size c.coll - i - 1) (by omega)

@[simp]
theorem length_toList [ToList γ α] [LawfulIndexedToList γ α] (c : γ) :
    (toList c).length = size c :=
  LawfulIndexedToList.h_len c

@[simp]
theorem getElem_toList [ToList γ α] [LawfulIndexedToList γ α] (c : γ) (i : Nat)
    (h : i < (toList c).length) : (toList c)[i] = get c i (by simpa using h) :=
  (LawfulIndexedToList.get_eq_getElem c i _).symm

/-- Iterate over an indexed collection from index `i` onwards. -/
@[specialize]
def forInLoop [Monad m] (c : γ) (f : α → β → m (ForInStep β)) (i : Nat) (b : β) : m β :=
  if h : i < size c then do
    match ← f (get c i h) b with
    | .done  b => pure b
    | .yield b => forInLoop c f (i+1) b
  else
    pure b
termination_by size c - i

theorem forInLoop_eq_forIn_drop [Monad m] [ToList γ α] [LawfulIndexedToList γ α]
    (c : γ) (f : α → β → m (ForInStep β)) (i : Nat) (b : β)
    : forInLoop c f i b = forIn ((toList c).drop i) b f := by
  induction i, b using forInLoop.induct c with
  | case1 i b h ih =>
    have hi : i < (toList c).length := by simpa using h
    rw [forInLoop, dif_pos h, List.drop_eq_getElem_cons hi, getElem_toList, List.forIn_cons]
    congr 1; funext r; cases r <;> simp [ih]
  | case2 i b h =>
    rw [forInLoop, dif_neg h, List.drop_eq_nil_of_le (by simpa using Nat.le_of_not_lt h)]
    simp

theorem forInLoop_eq_forIn [Monad m] [ToList γ α] [LawfulIndexedToList γ α]
    (c : γ) (f : α → β → m (ForInStep β)) (b : β)
    : forInLoop c f 0 b = forIn (toList c) b f := by
  rw [forInLoop_eq_forIn_drop, List.drop_zero]

/-! # pairs -/

@[specialize]
def pairsForInLoop [Monad m] (c : γ) (f : (α × α) → β → m (ForInStep β)) (b : β)
    (i : Nat := 0) (j : Nat := 1) : m β :=
  if hi : i < size c then
    if hj : j < size c then do
      match ← f ((get c i hi), (get c j hj)) b with
      | .done  b => pure b
      | .yield b => pairsForInLoop c f b i (j + 1)
    else
      pairsForInLoop c f b (i + 1) (i + 2)
  else
    pure b

-- TODO(10/26): Cleanup
theorem pairsForInLoop_eq_forIn_drop [Monad m] [ToList γ α] [LawfulIndexedToList γ α] (c : γ) (b : β)
    (f : (α × α) → β → m (ForInStep β)) (i j : Nat) (hi : i < size c) :
    pairsForInLoop c f b i j
      = forIn (((toList c).drop j).map (get c i hi, ·) ++ ((toList c).drop (i + 1)).pairs) b f := by
  induction b, i, j using pairsForInLoop.induct c with
  | case1 b i j hi hj ih =>
    rw [pairsForInLoop, dif_pos hi, dif_pos hj, List.drop_eq_getElem_cons (by simpa using hj),
      getElem_toList, List.map_cons, List.cons_append, List.forIn_cons]
    congr 1; funext r
    cases r with
    | done => rfl
    | yield b => exact ih b hi
  | case2 b i j hi hj ih =>
    rw [pairsForInLoop, dif_pos hi, dif_neg hj,
      List.drop_eq_nil_of_le (by simpa using Nat.le_of_not_lt hj), List.map_nil, List.nil_append]
    by_cases hi' : i + 1 < size c
    · rw [ih hi', List.drop_eq_getElem_cons (i := i + 1) (by simpa using hi'), getElem_toList,
        List.pairs_cons]
    · rw [pairsForInLoop, dif_neg hi', List.drop_eq_nil_of_le (by simpa using Nat.le_of_not_lt hi')]
      rfl
  | case3 b i j hi' => exact absurd hi hi'

-- TODO(10/26): Cleanup
theorem pairsForInLoop_eq_forIn [Monad m] [ToList γ α] [LawfulIndexedToList γ α] (c : γ) (b : β) (f : α × α → β → m (ForInStep β)) :
    pairsForInLoop c (fun a b => f a b) b 0 1 = forIn (toList c).pairs b f := by
  by_cases h : 0 < size c
  · rw [pairsForInLoop_eq_forIn_drop _ _ _ _ _ h]
    conv_rhs => rw [← List.drop_zero (l := toList c), List.drop_eq_getElem_cons (by simpa using h),
      getElem_toList, List.pairs_cons]
  · rw [pairsForInLoop, dif_neg h, List.eq_nil_of_length_eq_zero (l := toList c) (by simpa using h)]
    rfl

/-! # adjacent -/

@[specialize]
def adjacentForInLoop [Monad m] (c : γ) (f : (α × α) → β → m (ForInStep β)) (b : β) (i : Nat := 0) : m β :=
  if h : i + 1 < size c then do
    match ← f (get c i (by omega), get c (i + 1) h) b with
    | .done  b => pure b
    | .yield b => adjacentForInLoop c f b (i + 1)
  else
    pure b

theorem adjacentForInLoop_eq_forIn_drop [Monad m] [ToList γ α] [LawfulIndexedToList γ α] (c : γ) (b : β)
    (f : (α × α) → β → m (ForInStep β)) (i : Nat) :
    adjacentForInLoop c f b i = forIn ((toList c).drop i).adjacentPairs b f := by
  induction b, i using adjacentForInLoop.induct c with
  | case1 b i h ih =>
    have h' : i + 1 < (toList c).length := by simpa using h
    have e₁ : (toList c).drop (i + 1) = get c (i + 1) h :: (toList c).drop (i + 2) := by
      rw [List.drop_eq_getElem_cons h', getElem_toList]
    have e₀ : (toList c).drop i = get c i (by omega) :: (toList c).drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by omega), getElem_toList]
    rw [adjacentForInLoop, dif_pos h, e₀, e₁, List.adjacentPairs_cons_cons, List.forIn_cons]
    congr 1; funext r
    cases r with
    | done => rfl
    | yield b => rw [← e₁]; exact ih b
  | case2 b i h =>
    rw [adjacentForInLoop, dif_neg h, List.adjacentPairs_eq_nil_of_length_le (by simp; omega)]
    rfl

theorem adjacentForInLoop_eq_forIn [Monad m] [ToList γ α] [LawfulIndexedToList γ α] (c : γ) (b : β)
    (f : α × α → β → m (ForInStep β)) :
    adjacentForInLoop c f b = forIn (toList c).adjacentPairs b f := by
  rw [adjacentForInLoop_eq_forIn_drop, List.drop_zero]

/-! # reverse -/

def reverseForInLoop [Monad m] (c : γ) (f : α → β → m (ForInStep β)) (b : β) (i : Nat := 0) : m β :=
  if h : i < size c then do
    match ← f (get c (size c - 1 - i) (by omega)) b with
    | .done  b => pure b
    | .yield b => reverseForInLoop c f b (i + 1)
  else
    pure b

end Indexed /- namespace -/

/-! # pairs -/

/-- Iterates over the pairs `(c[i], c[j])` with `i < j`. -/
structure Pairs (γ : Type u) where
  /-- The underlying collection. -/
  coll : γ

namespace Pairs

private def toListNaive [ToList γ α] (c : Pairs γ) : List (α × α) :=
  List.pairs (toList c.coll)

instance instToList [ToList γ α] : ToList (Pairs γ) (α × α) where
  toList c := toListNaive c

@[simp] theorem toList_def [ToList γ α] (c : Pairs γ) : toList c = (toList c.coll).pairs := rfl

def ofList (l : List α) : Pairs (List α) := ⟨l⟩
def ofArray (arr : Array α) : Pairs (Array α) := ⟨arr⟩
def ofIndexType (ι : Type u) [IndexType ι] : Pairs (IndexType ι) := ⟨IndexType.univ ι⟩

/--
  The non-preferred for-loop instance for `Pairs`.

  If we only know how to convert a collection `c : γ` into a `List`, then we can
  just use the list. However, this will almost always be slower than
  looping across indexes, so we set the `priority` lower than default.
-/
instance (priority := default - 1) instForIn [Monad m] [ToList γ α] : ForIn m (Pairs γ) (α × α) where
  forIn c init f := forIn (toList c) init f

open Indexed in
/--
  The preferred for-loop instance for `Pairs`, assuming `γ` is `Indexed`.

  If we can access the elements of `c : γ` by index, then we can efficiently
  compute all the pairs in `c` for the loop (assuming `get` is O(1)).
-/
instance instForInIndexed [Monad m] [Indexed γ α] : ForIn m (Pairs γ) (α × α) where
  forIn c init f := pairsForInLoop c.coll f init

open Indexed in
instance instLawfulForIn [Monad m] [Indexed γ α] [ToList γ α] [LawfulIndexedToList γ α] :
    LawfulForIn m (Pairs γ) (α × α) where
  forIn_eq_forIn_toList c init f := pairsForInLoop_eq_forIn c.coll init f

end Pairs /- namespace -/

def Array.pairs : Array α → Pairs (Array α) := Pairs.ofArray
@[simp] theorem Array.coll_pairs (arr : Array α) : arr.pairs.coll = arr := rfl
-- LawfulForIn Id (Pairs (Array α)) (α × α)

/-! # adjacent -/

/-- Iterates over the adjacent pairs `(c[i], c[i+1])`. -/
structure Adjacent (γ : Type u) where
  /-- The underlying collection. -/
  coll : γ

namespace Adjacent

instance instToList [ToList γ α] : ToList (Adjacent γ) (α × α) where
  toList c := (toList c.coll).adjacentPairs

@[simp] theorem toList_def [ToList γ α] (c : Adjacent γ) : toList c = (toList c.coll).adjacentPairs := rfl

def ofList (l : List α) : Adjacent (List α) := ⟨l⟩
def ofArray (arr : Array α) : Adjacent (Array α) := ⟨arr⟩
def ofIndexType (ι : Type u) [IndexType ι] : Adjacent (IndexType ι) := ⟨IndexType.univ ι⟩

/-- The non-preferred for-loop for `Adjacent`. See `Pairs.instForIn`.  -/
instance (priority := default - 1) instForIn [Monad m] [ToList γ α] : ForIn m (Adjacent γ) (α × α) where
  forIn c init f := forIn (toList c) init f

open Indexed in
/-- The preferred for-loop instance for `Adjacent`, assuming `γ` is `Indexed`. See `Pairs.instForInIndexed`. -/
instance instForInIndexed [Monad m] [Indexed γ α] : ForIn m (Adjacent γ) (α × α) where
  forIn c init f := adjacentForInLoop c.coll f init

open Indexed in
instance instLawfulForIn [Monad m] [Indexed γ α] [ToList γ α] [LawfulIndexedToList γ α] :
    LawfulForIn m (Adjacent γ) (α × α) where
  forIn_eq_forIn_toList c init f := adjacentForInLoop_eq_forIn c.coll init f

end Adjacent /- namespace -/

def Array.adjacent : Array α → Adjacent (Array α) := Adjacent.ofArray
@[simp] theorem Array.coll_adjacent (arr : Array α) : arr.adjacent.coll = arr := rfl

def IndexType.adjacent (ι : Type u) [IndexType ι] : Adjacent (IndexType ι) := Adjacent.ofIndexType ι
@[simp] theorem IndexType.coll_adjacent (ι : Type u) [IndexType ι] :
    (IndexType.adjacent ι).coll = IndexType.univ ι := rfl
