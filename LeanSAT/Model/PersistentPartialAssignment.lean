import LeanSAT.Data.ICnf

/-- A partial assignment of truth values to propositional variables.

It is meant to be kept around persistently and used linearly.
Assuming these restrictions are met,
the structure provides a fast and allocation-free representation
of partial assignments.
It provides functions for unit propagation and tautology checking. -/
structure PersistentPartialAssignment where
  assignment : Array Int
  /-- The generation counter is used to avoid clearing the assignment array.
  Instead, we just bump the counter and interpret values in the array
  below the counter as unassigned. -/
  generation : Nat
  -- h: 0 ≤ generation
  -- h: ∀ x ∈ assignment, x.natAbs ≤ generation

namespace PersistentPartialAssignment
  /-- Initialize to an empty partial assignment,
  supporting variables in the range `[1, maxVar]`.

  Note that the range determines
  which variable indices can be used with this structure
  for all time.
  For example, it is invalid to call `ppa.setLit l`
  if `ppa` was created with `maxVar < l.var`. -/
  def new (maxVar : Nat) : PersistentPartialAssignment where
    assignment := Array.mkArray maxVar 0
    generation := 1

  /-- Reset the assignment to an empty one. -/
  def reset (τ : PersistentPartialAssignment) : PersistentPartialAssignment :=
    { τ with generation := τ.generation + 1 }

  /-- Set the given literal to `true` in the assignment. -/
  def setLit (τ : PersistentPartialAssignment) (l : ILit) : PersistentPartialAssignment :=
    let v : Int := if l.polarity then τ.generation else -τ.generation
    { τ with assignment := τ.assignment.set! (l.var.val-1) v }

  /-- The value of the given literal in the current assignment, if assigned.
  Otherwise `none`. -/
  def litValue? (τ : PersistentPartialAssignment) (l : ILit) : Option Bool :=
    let v := τ.assignment.getD (l.var.val-1) 0
    if v.natAbs == τ.generation then
      some <| xor (v < 0) l.polarity
    else none

  /-- Check if the given clause is a tautology.
  The current partial assignment is ignored,
  and the assignment afterwards is unspecified. -/
  def checkTauto (τ : PersistentPartialAssignment) (C : IClause) : PersistentPartialAssignment × Bool := Id.run do
    let mut τ := τ.reset
    for l in C do
      if let some false := τ.litValue? l then
        return (τ, true)
    return (τ, false)

  /-- Set `l ↦ ⊥` for each `l ∈ C` and leave the rest of the assignment untouched.
  If the current assignment contains literals appearing in `C`, they will be overwritten. -/
  -- NB: might be easier to verify if we make this always bump p.generation; it's only used before UP anyway
  def setNegatedClause (τ : PersistentPartialAssignment) (C : IClause) : PersistentPartialAssignment :=
    C.foldl (init := τ) (fun τ l => τ.setLit (-l))

  inductive PropagateResult where
    | extended
    | contradiction
    | notUnit

  /-- If `C` is satisfied by `τ`, return `notUnit`.
  Otherwise compute the reduced clause `C' = {l ∈ C | ¬l ∉ τ}`.
  If `C' = [u]` is a unit, extend `τ` by `u` and return `extended`.
  If `C'` has become empty (is falsified), return `contradiction`.
  If `C'` is not a unit and not falsified, return `notUnit`. -/
  def propagateUnit (τ : PersistentPartialAssignment) (C : IClause) : PersistentPartialAssignment × PropagateResult := Id.run do
    let mut τ := τ
    -- The candidate for a unit.
    let mut unit? : Option ILit := none
    for l in C do
      match τ.litValue? l with
      | some true =>
        return (τ, .notUnit)
      | some false => ()
      | none =>
        if let .some u := unit? then
          if u != l then
            return (τ, .notUnit)
        unit? := some l
    match unit? with
    | none => return (τ, .contradiction)
    | some u => return (τ.setLit u, .extended)

end PersistentPartialAssignment