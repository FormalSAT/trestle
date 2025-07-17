/-
Copyright (c) 2025 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: Cayden Codel
-/

import Trestle.Data.ICnf
import Experiments.SR.SetF

/-!

  Persistent partial assignments and substitutions.

  Resizable arrays that can be ``cleared'' in O(1) time by bumping a generation
  number. Each array entry stores a generation number that determines if the
  cell is set (i.e. that it is above the data structure's generation number).
  Used to implement partial assignments and substitutions by assuming that all
  variables are unset (PPA) or set to themselves (PS) at initialization.

-/

namespace Trestle

/--
  A persistent partial assignment of truth values to propositional variables.

  If used linearly, it is an efficient way of clearing out partial assignments
  when doing proof checking, tautology checking, or unit propagation.
-/
structure PS where
  gens : Array Nat
  mappings : Array Nat
  /-- The generation counter is used to avoid clearing the assignment array.
  Instead, we just bump the counter and interpret values in the array
  below the counter as unassigned. -/
  generation : { n : Nat // 0 < n }
  /-- The maximum absolute value of any entry in `assignments`. -/
  maxGen : Nat
  sizes_eq : gens.size = mappings.size
  le_maxGen : ∀ i ∈ gens, i ≤ maxGen

namespace PS

open LitVar

abbrev size (σ : PS) : Nat := σ.gens.size

/-! # map -/

@[inline, always_inline]
def IVarToMappedNat (v : IVar) : Nat :=
  v.val * 2

/--
  Because the substitution mappings must be stored as natural numbers,
  we must convert from signed `ILit`s to `Nat`s using a standard trick
  from SAT solving: multiply by 2, and add 1 if the polarity is negative.
-/
@[inline, always_inline]
def ILitToMappedNat (l : ILit) : Nat :=
  if polarity l then
    (Int.natAbs l.val) * 2
  else
    (Int.natAbs l.val) * 2 + 1

@[inline, always_inline]
def ILitFromMappedNat : Nat → ILit
  | 0 => ⟨1, by decide⟩
  | 1 => ⟨-1, by decide⟩
  | (n + 2) =>
    if n % 2 = 0 then
      ⟨n / 2 + 1, by omega⟩
    else
      ⟨-(n / 2 + 1), by omega⟩

@[inline, always_inline]
def negateMappedNat (n : Nat) : Nat :=
  if n % 2 = 0 then
    n + 1
  else
    n - 1

def MAPPED_TRUE : Nat := 0
def MAPPED_FALSE : Nat := 1

/-- A `PS` value (hence `PSV`). Used mainly for modeling purposes. -/
abbrev PSV := ILit ⊕ Bool

namespace PSV

def negate : PSV → PSV
  | Sum.inl l => Sum.inl (-l)
  | Sum.inr b => Sum.inr !b

instance instCoeIVar : Coe IVar PSV := ⟨Sum.inl ∘ mkPos⟩
instance instCoeILit : Coe ILit PSV := ⟨Sum.inl⟩
instance instCoeBool : Coe Bool PSV := ⟨Sum.inr⟩

def toMappedNat : PSV → Nat
  | Sum.inl l => ILitToMappedNat l
  | Sum.inr true => MAPPED_TRUE
  | Sum.inr false => MAPPED_FALSE

def fromMappedNat (n : Nat) : PSV :=
  match n with
  | 0 => Sum.inr true
  | 1 => Sum.inr false
  | n + 2 =>
    if n % 2 = 0 then
      Sum.inl <| mkPos ⟨n / 2 + 1, Nat.succ_pos _⟩
    else
      Sum.inl <| mkNeg ⟨n / 2 + 1, Nat.succ_pos _⟩

instance instToMappedNat : Coe PSV Nat := ⟨toMappedNat⟩
instance instFromMappedNat : Coe Nat PSV := ⟨fromMappedNat⟩

end PSV

--------------------------------------------------------------------------------

open PSV

def toString (σ : PS) : String :=
  String.intercalate ", "
    (Fin.foldl σ.size (fun str idx =>
      if σ.gens[idx] ≥ σ.generation then
        str ++ [s!"({idx}: {σ.gens[idx]}, {σ.mappings[idx]!})"]
      else
        str) [])

instance instToString : ToString PS where
  toString := toString


/-! # varValue -/

-- CC: This is used for the model of the substitution, but for performing
--     reduction, it should be faster to case on the value of the array
--     directly (or think about inlining)

/--
  Returns a mapped `Nat` directly.

  Use `MAPPED_TRUE`, `MAPPED_FALSE`, and `fromMappedNat`.
-/
--@[inline, always_inline]
def varValue_Nat (σ : PS) (v : IVar) : Nat :=
  if hi : v.index < σ.size then
    let gen := σ.gens[v.index]'hi
    if gen ≥ σ.generation then
      let n := σ.mappings[v.index]'(by rw [← σ.sizes_eq]; exact hi)
      PSV.fromMappedNat n
    else IVarToMappedNat v
  else IVarToMappedNat v

/--
  Returns the value of the variable under the substitution.

  This function is used for modeling purposes, as it uses `PSV`.
  For faster computation, use `varValue_Nat`.
-/
--@[inline, always_inline]
def varValue (σ : PS) (v : IVar) : PSV :=
  PSV.fromMappedNat <| varValue_Nat σ v

--@[inline, always_inline]
def litValue_Nat (σ : PS) (l : ILit) : Nat :=
  if polarity l then
    varValue_Nat σ (toVar l)
  else
    negateMappedNat <| varValue_Nat σ (toVar l)

--@[inline, always_inline]
def litValue (σ : PS) (l : ILit) : PSV :=
  PSV.fromMappedNat <| litValue_Nat σ l

/-! # new, reset, bump -/

/--
  Initialize to an empty partial assignment,
  supporting variables in the range `[1, maxVar]`.

  The assignment will resize dynamically if it's used with
  a variable above the initial `maxVar`.
-/
def new (n : Nat) : PS where
  gens := Array.replicate n 0
  mappings := Array.replicate n 0
  generation := ⟨1, Nat.one_pos⟩
  maxGen := 0
  sizes_eq := by simp
  le_maxGen := by simp_all [List.mem_replicate]

/-- Reset the assignment to an empty one. -/
def reset (σ : PS) : PS :=
  { σ with generation := ⟨σ.maxGen + 1, Nat.succ_pos _⟩ }

/-- Clear all temporary assignments at the current generation. -/
def bump (σ : PS) : PS :=
  { σ with generation := ⟨σ.generation.val + 1, Nat.succ_pos _⟩ }


/-! # setLit -/

/-- Helper theorem for `setVar*`. -/
theorem setVar_le_maxGen (σ : PS) (i : Nat) (gen : Nat) :
    ∀ cell ∈ (σ.gens.setF i gen 0), cell ≤ max σ.maxGen gen := by
  intro cell h_cell
  have := Array.mem_setF _ _ _ _ h_cell
  rcases this with (h | rfl | rfl)
  · have := σ.le_maxGen _ h
    exact Nat.le_trans this (Nat.le_max_left σ.maxGen gen)
  · simp only [Int.natAbs_zero, Nat.zero_le]
  · exact Nat.le_max_right _ _

/-- Sets the given literal to `true` for the current generation in the PS. -/
def setLit (σ : PS) (l : ILit) : PS :=
  let val : Nat := if polarity l then MAPPED_TRUE else MAPPED_FALSE
  let index := l.index
  let gen := σ.generation
  { σ with
    gens := σ.gens.setF index gen 0,
    mappings := σ.mappings.setF index val 0,
    maxGen := max σ.maxGen gen
    sizes_eq := by simp [σ.sizes_eq]
    le_maxGen := setVar_le_maxGen σ index gen
  }

def setVarToLit (σ : PS) (v : IVar) (l : ILit) : PS :=
  let index := v.index
  let gen := σ.generation
  { σ with
    gens := σ.gens.setF index gen 0
    mappings := σ.mappings.setF index (PSV.toMappedNat l) 0
    maxGen := max σ.maxGen gen
    sizes_eq := by simp [σ.sizes_eq]
    le_maxGen := setVar_le_maxGen σ index gen
  }

/-- Maps the variables to literals in pairs of two.  -/
def setVars (σ : PS) (A : Array (IVar × ILit)) : PS :=
  A.foldl (init := σ) (fun σ ⟨v, l⟩ => σ.setVarToLit v l)

/--
  Maps the variables to literals in pairs of two.

  If the array is not a mulitple of two, then the last entry is ignored.
-/
def setVars' (σ : PS) (A : Array ILit) : PS :=
  let rec loop (i : Nat) (σ : PS) : PS :=
    if hi : i + 1 < A.size then
      have : Array.size A - (i + 2) < Array.size A - i := Nat.sub_add_lt_sub hi (Nat.le.step Nat.le.refl)
      let v := A[i]'(Nat.lt_of_succ_lt hi)
      let l := A[i + 1]'hi
      loop (i + 2) (σ.setVarToLit (toVar v) l)
    else
      σ
  loop 0 σ

def setLits (σ : PS) (A : Array ILit) : PS :=
  A.foldl setLit σ

/-! # reduction -/

inductive ReductionResult where
  | satisfied
  | reduced
  | notReduced

open ReductionResult

/-- Evaluates the provided literal under the PS -/
@[inline, always_inline]
def seval (σ : PS) (l : ILit) : ReductionResult :=
  match σ.litValue l with
  | .inr true => .satisfied
  | .inr false => .reduced
  | .inl lit => if l ≠ lit then .reduced else .notReduced

@[inline, always_inline]
def sevalM (σ : PS) (reduced? : Bool) (l : ILit) : Except Unit Bool :=
  match σ.litValue l with
  | .inr true => .error ()
  | .inr false => .ok true
  | .inl lit => if l ≠ lit then .ok true else .ok reduced?

@[inline, always_inline]
def reduceM_Except : Except Unit Bool → ReductionResult
  | .ok true => .reduced
  | .ok false => .notReduced
  | .error _ => .satisfied

def reduceM.aux (σ : PS) (C : IClause) (reduced? : Bool) : Except Unit Bool :=
  C.foldlM (sevalM σ) reduced?

/-- Reduces a clause under the substitution, with a monadic fold. -/
def reduceM (σ : PS) (C : IClause) : ReductionResult :=
  reduceM_Except <| reduceM.aux σ C false

/-- Reduces a clause under the substitution. -/
def reduce (σ : PS) (C : IClause) : ReductionResult :=
  let rec loop (i : Nat) (reduced? : Bool) : ReductionResult :=
    if hi : i < C.size then
      let lit := C[i]'hi
      match seval σ lit with
      | satisfied => .satisfied
      | notReduced => loop (i + 1) reduced?
      | reduced => loop (i + 1) true
    else
      if reduced? then .reduced else .notReduced
  loop 0 false

end PS

end Trestle
