/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: Cayden Codel, Wojciech Nawrocki, James Gallicchio
-/

import Trestle.Data.ICnf.Defs
import Trestle.Upstream.SetF
import Trestle.Upstream.ToStd


-- CC: The only thing contained in the commented-out file in `trestle-code` is the following `Nat` proof
--import Trestle.Upstream.ToMathlib
-- Mostly used for backwards-induction proofs
theorem Nat.eq_sub_add_of_add_eq_sub {k l m n : Nat} : k + l = n - m → k = n - (m + l) := by
  omega

/-!

Persistent partial assignments (PPA).

The data structure underlying the PPA is a resizable array that can be ``cleared''
in O(1) time by bumping a generation number.
Each cell in the array stores a generation number that determines if the
cell is set (i.e. that it is above the data structure's generation number).
Used to implement partial assignments by assuming that all
variables are initially unset (PPA).

-/

namespace Trestle

/-! # Concise PPA (single array) -/

/--
  A Persistent Partial Assignment of truth values to propositional variables.

  Assuming the linearity restriction (see below) is met,
  the PPA provides a fast representation of partial assignments.
  The PPA is allocation-free as long as you initialize it
  with the actual maximum variable index in `PPA.new`.
  Otherwise, the PPA automatically resizes when a variable out of range is given.
  The PPA provides functions for unit propagation and tautology checking.

  The PPA is meant to be used persistently and linearly,
  i.e., you should keep around exactly one copy of this structure.
  Note that ensuring linearity in large functions can be tricky,
  especially when `do` notation is used.
  The only reliable method at the moment
  is to look at the dynamic behavior in a profiler
  and ensure that PPA code does not spend lots of time in `lean_copy_expand_array`.
-/
structure PPA where
  /-- For each variable, stores the generation value that variable is set for. -/
  assignment : Array Int
  /-- The generation counter is used to avoid clearing the assignment array
      when the assignment is reset.  Instead, we just bump the counter and
      interpret values in the array below the counter as unassigned. -/
  generation : { n : Nat // n > 0 }
  /-- The maximum absolute value of any entry in `assignments`. -/
  maxGen : Nat
  le_maxGen : ∀ i ∈ assignment, i.natAbs ≤ maxGen

instance : ToString PPA where
  toString τ := String.intercalate " ∧ "
    (τ.assignment.foldl (init := []) (f := fun acc a => s!"{a}" :: acc))


namespace PPA

open LitVar

/-- The number of (possible) variables tracked by the partial assignment. -/
abbrev size (τ : PPA) : Nat := τ.assignment.size

/--
  The value of the given variable in the current assignment, if assigned.
  Assignment is determined by comparing the current generation (τ.generation)
  against the generation value stored at that variable's index.
  If not assigned, returns `none`.
-/
--@[inline, always_inline]
def varValue? (τ : PPA) (v : IVar) : Option Bool :=
  match τ.assignment[v.index]? with
  | none => none
  | some n =>
    if τ.generation ≤ n.natAbs then
      some (0 < n)
    else
      none

/-- The value of the given literal in the current assignment, if assigned.
    Otherwise `none`. -/
--@[inline, always_inline]
def litValue? (τ : PPA) (l : ILit) : Option Bool :=
  τ.varValue? (toVar l) |>.map (xor !(polarity l))

protected def UNASSIGNED : UInt8 := 0
protected def TRUE : UInt8 := 1
protected def FALSE : UInt8 := 2

--@[inline, always_inline]
protected def negate (v : UInt8) : UInt8 :=
  if v = PPA.TRUE then PPA.FALSE else
  if v = PPA.FALSE then PPA.TRUE
  else PPA.UNASSIGNED

-- Alternate versions that use `UInt8`, so that Lean doesn't need to (un)box an option
--@[inline, always_inline]
def varValue?_8 (τ : PPA) (v : IVar) : UInt8 :=
  match τ.assignment[v.index]? with
  | none => PPA.UNASSIGNED
  | some n =>
    if τ.generation ≤ n.natAbs then
      if 0 < n then PPA.TRUE else PPA.FALSE
    else
      PPA.UNASSIGNED

--@[inline, always_inline]
def litValue?_8 (τ : PPA) (l : ILit) : UInt8 :=
  let res := τ.varValue?_8 (toVar l)
  if polarity l then
    res
  else
    PPA.negate res

/-! ## new, set, reset -/

/--
  The assignment will resize dynamically if it's used with
  a variable above the initial `maxVar`.
-/
def new (maxVar : Nat) : PPA where
  assignment := Array.mkArray maxVar 0
  generation := ⟨1, Nat.one_pos⟩
  maxGen := 0
  le_maxGen i h := by simp_all only [Array.mem_mkArray, ne_eq, Int.natAbs_zero, Nat.le_refl]

/-- Reset the assignment to an empty one. -/
def reset (τ : PPA) : PPA :=
  { τ with generation := ⟨τ.maxGen + 1, Nat.succ_pos _⟩ }

/-- Clear all temporary assignments at the current generation. -/
def bump (τ : PPA) : PPA :=
  { τ with generation := ⟨τ.generation + 1, Nat.succ_pos _⟩ }

/-- Helper theorem for writing the definitions of `setVar*`. -/
theorem setVar_le_maxGen (τ : PPA) (i : Nat) (b : Bool) (gen : Nat) :
    let v : Int := if b then gen else -gen
    ∀ g ∈ (τ.assignment.setF i v 0), g.natAbs ≤ max τ.maxGen gen := by
  intro v g hg
  have := Array.mem_setF _ _ _ _ hg
  rcases this with (h | h | h)
  · have := τ.le_maxGen _ h
    exact Nat.le_trans this (Nat.le_max_left τ.maxGen gen)
  · simp only [h, Int.natAbs_zero, Nat.zero_le]
  · cases b <;> simp [h, v]
    <;> exact Nat.le_max_right _ _

/-- Set the given variable to `b` for the current generation. -/
--@[inline, always_inline]
def setVar (τ : PPA) (v : IVar) (b : Bool) : PPA :=
  let g : Int := if b then τ.generation else -τ.generation
  { τ with
    assignment := τ.assignment.setF v.index g 0
    maxGen := Nat.max τ.maxGen τ.generation
    le_maxGen := setVar_le_maxGen τ v.index b τ.generation }

/-- Set the given literal to `true` for the current generation. -/
--@[inline, always_inline]
def setLit (τ : PPA) (l : ILit) : PPA :=
  τ.setVar (toVar l) (polarity l)

/-- Set the given variable to `b` for all generations until `gen`. -/
--@[inline, always_inline]
def setVarUntil (τ : PPA) (v : IVar) (b : Bool) (gen : Nat) : PPA :=
  let g : Int := if b then gen else -gen
  { τ with
    assignment := τ.assignment.setF v.index g 0
    maxGen := Nat.max τ.maxGen gen
    le_maxGen := setVar_le_maxGen τ v.index b gen }

/-- Set the given literal to `true` for all generations until `gen`. -/
--@[inline, always_inline]
def setLitUntil (τ : PPA) (l : ILit) (gen : Nat) : PPA :=
  τ.setVarUntil (toVar l) (polarity l) gen

--@[inline, always_inline]
def setVarFor (τ : PPA) (v : IVar) (b : Bool) (extraBumps : Nat) : PPA :=
  let g : Int := if b then τ.generation + extraBumps else -(τ.generation + extraBumps)
  { τ with
    assignment := τ.assignment.setF v.index g 0
    maxGen := Nat.max τ.maxGen (τ.generation + extraBumps)
    le_maxGen := setVar_le_maxGen τ v.index b (τ.generation + extraBumps) }

--@[inline, always_inline]
def setLitFor (τ : PPA) (l : ILit) (extraBumps : Nat) : PPA :=
  τ.setVarFor (toVar l) (polarity l) extraBumps

/-! # Assuming negated clauses -/

/-- Set `l ↦ ⊥` for each `l ∈ C` and leave the rest of the assignment untouched.
If the current assignment contains literals appearing in `C`, they will be overwritten. -/
def setNegatedClause (τ : PPA) (C : IClause) : PPA :=
  C.foldl (init := τ) (fun τ l => τ.setLit (-l))

/-- Same version as `setNegatedClause` that uses an index loop instead of `foldl`. -/
def setNegatedClause_loop (τ : PPA) (C : IClause) : PPA :=
  let rec loop (τ : PPA) (i : Nat) : PPA :=
    if h : i < C.size then
      loop (τ.setLit (-C[i]'h)) (i + 1)
    else
      τ
  loop τ 0

def setNegatedClauseUntil (τ : PPA) (C : IClause) (gen : Nat) : PPA :=
  C.foldl (init := τ) (fun τ l => τ.setLitUntil (-l) gen)

/-- Same version as `setNegatedClauseUntil` that uses an index loop instead of `foldl`. -/
def setNegatedClauseUntil_loop (τ : PPA) (C : IClause) (gen : Nat) : PPA :=
  let rec loop (τ : PPA) (i : Nat) : PPA :=
    if h : i < C.size then
      loop (τ.setLitUntil (-C[i]'h) gen) (i + 1)
    else
      τ
  loop τ 0

def setNegatedClauseFor (τ : PPA) (C : IClause) (extraBumps : Nat) : PPA :=
  C.foldl (init := τ) (fun τ l => τ.setLitFor (-l) extraBumps)

/-- Same version as `setNegatedClauseUntil` that uses an index loop instead of `foldl`. -/
def setNegatedClauseFor_loop (τ : PPA) (C : IClause) (extraBumps : Nat) : PPA :=
  let rec loop (τ : PPA) (i : Nat) : PPA :=
    if h : i < C.size then
      loop (τ.setLitFor (-C[i]'h) extraBumps) (i + 1)
    else
      τ
  loop τ 0

/-
  Even though we provide two versions of the negation functions above,
  we want to ensure that they are equivalent, even if the executable code
  only uses one version. Thus, the theorems below enforces a "file" invariant.

  TODO: Use @implemented_by instead?
-/

@[simp]
theorem setNegatedClause_cons (τ : PPA) (l : ILit) (ls : List ILit) :
    setNegatedClause τ { toList := l :: ls } = setNegatedClause (τ.setLit (-l)) { toList := ls } := by
  simp only [setNegatedClause, Array.foldl_cons]

theorem setNegatedClause_loop_drop (τ : PPA) {C : List ILit} {i j : Nat} :
    j = C.length - i →
      setNegatedClause_loop.loop { toList := C } τ i = setNegatedClause τ { toList := C.drop i } := by
  induction j generalizing C i τ with
  | zero =>
    intro h
    have hi : i ≥ C.length := Nat.le_of_sub_eq_zero h.symm
    rw [setNegatedClause_loop.loop]
    simp [Nat.not_lt_of_le hi, List.drop_of_length_le hi]
    simp [setNegatedClause]
  | succ j ih =>
    intro hj
    have hi : i < C.length := by
      apply Nat.lt_of_sub_pos
      rw [← hj]
      exact Nat.zero_lt_succ j
    rw [setNegatedClause_loop.loop]
    simp only [List.size_toArray, hi, ↓reduceDIte, List.getElem_toArray]
    rw [ih]
    match h_drop : C.drop i with
    | [] =>
      have := List.drop_eq_nil_iff.mp h_drop
      omega
    | (l :: ls) =>
      -- CC: Annoyingly, we cannot add `hi` to the List lemma here
      --     because `simp` will undo our progress, whereas omitting
      --     it will allow us to split the drop
      rw [← List.getElem_cons_drop] at h_drop
      · simp at h_drop
        rcases h_drop with ⟨h_Ci, h_drop⟩
        simp only [h_drop, setNegatedClause_cons]
        have : ({ toList := C } : Array ILit)[i] = C[i] := rfl
        simp only [this, h_Ci]
      · exact hi
    · exact Nat.eq_sub_add_of_add_eq_sub hj

@[simp]
theorem setNegatedClause_loop_eq_setNegatedClause (τ : PPA) (C : IClause) :
    τ.setNegatedClause_loop C = τ.setNegatedClause C := by
  rw [setNegatedClause_loop]
  exact setNegatedClause_loop_drop τ rfl


/--
  Assumes the negation of a clause into the `PPA`.
  Throws an error if a literal is already set to the opposite value.

  During proof checking, we don't want to assume the negation of a clause
  if that clause is a tautology. We avoid that case by throwing an error
  if we discover that we already set the value of
-/
def assumeNegatedClauseM (τ : PPA) (C : IClause) : Except PPA PPA :=
  C.foldlM (init := τ) (fun τ l =>
    match τ.litValue? l with
    | none       => .ok <| τ.setLit (-l)
    | some false => .ok <| τ
    | some true  => .error τ)

def assumeNegatedClauseFor (τ : PPA) (C : IClause) (bumps : Nat) : Except PPA PPA :=
  let rec loop (i : Nat) (τ : PPA) : Except PPA PPA :=
    if h : i < C.size then
      let l := C[i]'h
      match τ.litValue? l with
      | none       => loop (i + 1) (τ.setLitFor (-l) bumps)
      | some false => loop (i + 1) τ
      | some true  => .error τ
    else
      .ok τ
  loop 0 τ

def assumeNegatedClauseForM (τ : PPA) (C : IClause) (bumps : Nat) : Except PPA PPA :=
  C.foldlM (init := τ) (fun τ l =>
    match τ.litValue? l with
    | none       => .ok <| τ.setLitFor (-l) bumps
    | some false => .ok <| τ
    | some true  => .error τ)


/-! # unit propagation -/

inductive UPResult where
  | falsified
  | satisfied
  | unit (l : ILit)
  | multipleUnassignedLiterals

open UPResult

/--
  Evaluates the literal under the partial substitution.
  The `Exception` allows monadic short-circuiting.
-/
--@[inline, always_inline]
def pevalM (τ : PPA) (unit? : Option ILit) (l : ILit) : Except Bool (Option ILit) :=
  match τ.litValue? l with
  | some true => .error true
  | some false => .ok unit?
  | none =>
    match unit? with
    | none => .ok l
    | some u =>
      if u = l then .ok unit?
      -- Assume tautology cannot occur in clause, so two unassiged literals exits early
      else .error false

def unitPropM_Except : Except Bool (Option ILit) → UPResult
  | .ok none => falsified
  | .ok (some lit) => unit lit
  | .error true => satisfied
  | .error false => multipleUnassignedLiterals

def unitPropM.aux (τ : PPA) (C : IClause) (unit? : Option ILit) : Except Bool (Option ILit) :=
  C.foldlM (pevalM τ) unit?

/-- Performs unit propagaion on a clause, with a monadic fold. -/
def unitPropM (τ : PPA) (C : IClause) : UPResult :=
  unitPropM_Except <| unitPropM.aux τ C none

/-- Performs unit propagation on a clause.  -/
def unitProp (τ : PPA) (C : IClause) : UPResult :=
  let rec loop (i : Nat) (unit? : Option ILit) : UPResult :=
    if hi : i < C.size then
      -- This is essentially a clone of `pevalUP` above, except without an Exception monad
      let lit := C[i]'hi
      match τ.litValue? lit with
      | some true => .satisfied
      | some false => loop (i + 1) unit?
      | none =>
        match unit? with
        | none => loop (i + 1) (some lit)
        | some u =>
          if u = lit then loop (i + 1) unit?
          else .multipleUnassignedLiterals
    else
      match unit? with
      | none => .falsified
      | some l => .unit l
  loop 0 none

end PPA

end Trestle
