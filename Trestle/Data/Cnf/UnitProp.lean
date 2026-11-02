/-
Copyright (c) 2026 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Trestle.Data.Cnf.Basic
import Std.Data.HashMap

/-!

  Unit propagation on CNF formulas.

  Two implementations are provided, both of which take a formula `F` and a
  partial assignment `τ : Assign ν` and return the extended partial assignment
  along with a `UnitProp.Result`:

  - `unitPropRef`: the reference implementation. It repeatedly scans the
    formula from the top for a unit clause, extends the assignment with the
    unit literal, and starts over. It stops when a clause is falsified, or
    when a full scan finds no unit clause.

  - `unitPropWatch`: the two-watched-literal implementation. After a single
    pass over the formula to set up the watch lists, each newly assigned
    literal only visits the clauses that watch its negation.

  ## Correctness

  For both implementations, we prove that
  - the returned assignment extends the input assignment (`Assign.Extends`);
  - every derived literal is implied by `F` and `τ`: any total assignment
    satisfying `F` that agrees with `τ` also agrees with the result;
  - an `unsat` result means that no total assignment that agrees with `τ`
    satisfies `F`;
  - a `sat` result means that every total assignment that agrees with the
    result satisfies `F`. In particular, `Assign.toPropAssignment` of the
    result (which sets unassigned variables to `true`) is a model of `F`.

  For the reference implementation, we additionally prove completeness: when
  the result is not `unsat`, no clause of `F` is falsified or unit under the
  returned assignment (i.e., unit propagation has reached a fixpoint).

  The analogous completeness theorem for `unitPropWatch` requires the usual
  watched-literal invariants and is not (yet) proven here. The soundness
  proofs avoid those invariants by having `unitPropWatch` re-check, in
  constant time, that the watched literal it is moving off of is false.

-/

namespace Trestle

open Std Model PropFun

namespace UnitProp

/-- The outcome of unit propagation. -/
inductive Result where
  /-- Every clause is satisfied by the assignment. -/
  | sat
  /-- A clause was falsified, so the formula is unsatisfiable under the input assignment. -/
  | unsat
  /-- Neither of the above. -/
  | unknown
deriving DecidableEq, Repr, Inhabited

/-- A partial assignment of truth values to variables. -/
abbrev Assign (ν : Type v) [BEq ν] [Hashable ν] := HashMap ν Bool

variable {L : Type u} {ν : Type v} [LitVar L ν] [BEq ν] [Hashable ν]

/-! ### Partial assignments -/

namespace Assign

/-- The empty partial assignment. -/
@[inline]
def empty : Assign ν := {}

/-- The value of a literal under a partial assignment, if it is assigned. -/
@[inline]
def litValue (τ : Assign ν) (l : L) : Option Bool :=
  τ[LitVar.toVar l]?.map (· == LitVar.polarity l)

/-- Extend the partial assignment so that `l` is true. -/
@[inline]
def setLit (τ : Assign ν) (l : L) : Assign ν :=
  τ.insert (LitVar.toVar l) (LitVar.polarity l)

/-- The total assignment that agrees with `τ` and sets every unassigned variable to `true`. -/
def toPropAssignment (τ : Assign ν) : PropAssignment ν :=
  fun x => τ.getD x true

/-- A total assignment `σ` agrees with the partial assignment `τ`. -/
def Agrees (τ : Assign ν) (σ : PropAssignment ν) : Prop :=
  ∀ (x : ν) (b : Bool), τ[x]? = some b → σ x = b

/-- The partial assignment `τ'` extends `τ`. -/
def Extends (τ τ' : Assign ν) : Prop :=
  ∀ (x : ν) (b : Bool), τ[x]? = some b → τ'[x]? = some b

variable [LawfulBEq ν] {τ τ' : Assign ν} {σ : PropAssignment ν} {l : L}

theorem litValue_eq_none : τ.litValue l = none ↔ τ[LitVar.toVar l]? = none := by
  simp [litValue]

omit [LawfulBEq ν] in
theorem litValue_eq_some_true :
    τ.litValue l = some true ↔ τ[LitVar.toVar l]? = some (LitVar.polarity l) := by
  simp only [litValue]
  cases τ[LitVar.toVar l]? with
  | none => simp
  | some b => cases b <;> cases LitVar.polarity l <;> simp

omit [LawfulBEq ν] in
theorem litValue_eq_some_false :
    τ.litValue l = some false ↔ τ[LitVar.toVar l]? = some (!LitVar.polarity l) := by
  simp only [litValue]
  cases τ[LitVar.toVar l]? with
  | none => simp
  | some b => cases b <;> cases LitVar.polarity l <;> simp

omit [LawfulBEq ν] in
@[refl]
theorem Extends.refl (τ : Assign ν) : Extends τ τ := fun _ _ h => h

omit [LawfulBEq ν] in
@[trans]
theorem Extends.trans {τ₁ τ₂ τ₃ : Assign ν} :
    Extends τ₁ τ₂ → Extends τ₂ τ₃ → Extends τ₁ τ₃ :=
  fun h₁ h₂ x b h => h₂ x b (h₁ x b h)

omit [LawfulBEq ν] in
theorem Agrees.of_extends : Extends τ τ' → Agrees τ' σ → Agrees τ σ :=
  fun h₁ h₂ x b h => h₂ x b (h₁ x b h)

theorem extends_setLit : τ.litValue l = none → Extends τ (τ.setLit l) := by
  intro hl x b hx
  rw [litValue_eq_none] at hl
  have : (LitVar.toVar l == x) = false := by
    rw [beq_eq_false_iff_ne]
    rintro rfl
    simp [hl] at hx
  simp [setLit, HashMap.getElem?_insert, this, hx]

theorem agrees_toPropAssignment (τ : Assign ν) : Agrees τ τ.toPropAssignment := by
  intro x b h
  simp [toPropAssignment, HashMap.getD_eq_getD_getElem?, h]

omit [LawfulBEq ν] in
theorem Agrees.satisfies_of_true :
    Agrees τ σ → τ.litValue l = some true → σ ⊨ LitVar.toPropFun l := by
  intro h hl
  rw [LitVar.satisfies_iff]
  exact h _ _ (litValue_eq_some_true.mp hl)

omit [LawfulBEq ν] in
theorem Agrees.not_satisfies_of_false :
    Agrees τ σ → τ.litValue l = some false → ¬ σ ⊨ LitVar.toPropFun l := by
  intro h hl
  rw [LitVar.satisfies_iff, h _ _ (litValue_eq_some_false.mp hl)]
  cases LitVar.polarity l <;> simp

theorem Agrees.setLit : Agrees τ σ → σ ⊨ LitVar.toPropFun l → Agrees (τ.setLit l) σ := by
  intro h hl x b hx
  rw [LitVar.satisfies_iff] at hl
  simp only [Assign.setLit, HashMap.getElem?_insert] at hx
  split at hx <;> rename_i hx'
  · rw [beq_iff_eq] at hx'; subst hx'; cases hx; exact hl
  · exact h x b hx

end Assign

open Assign

/-- Every literal of the clause is false under `τ`. -/
def IsFalsified (τ : Assign ν) (C : Clause L) : Prop :=
  ∀ l ∈ C, τ.litValue l = some false

/-- Some literal of the clause is true under `τ`. -/
def IsSat (τ : Assign ν) (C : Clause L) : Prop :=
  ∃ l ∈ C, τ.litValue l = some true

/-- The clause is unit under `τ`, with unassigned literal `u`. -/
def IsUnit (τ : Assign ν) (C : Clause L) (u : L) : Prop :=
  u ∈ C ∧ τ.litValue u = none ∧ ∀ l ∈ C, l ≠ u → τ.litValue l = some false

/-- A clause that is neither unit nor falsified. -/
def IsStable (τ : Assign ν) (C : Clause L) : Prop :=
  ¬ IsFalsified τ C ∧ ∀ u, ¬ IsUnit τ C u

/-! ### Termination measure -/

section Measure

set_option warn.classDefReducibility false in
attribute [local instance 5] instDecidableEqOfLawfulBEq

variable [LawfulBEq ν]

/-- The distinct variables appearing in `F`. -/
def cnfVars (F : Cnf L) : Finset ν :=
  (F.flatten.toList.map LitVar.toVar).toFinset

/-- The number of distinct variables of `F` that are unassigned by `τ`.
    Every unit propagation step assigns one of them, so this is the
    termination measure for both implementations. -/
def numUnassigned (F : Cnf L) (τ : Assign ν) : Nat :=
  ((cnfVars F).filter (fun x => τ.contains x = false)).card

omit [Hashable ν] in
theorem mem_cnfVars {F : Cnf L} {x : ν} :
    x ∈ cnfVars F ↔ ∃ C ∈ F, ∃ l ∈ C, LitVar.toVar l = x := by
  simp [cnfVars]

omit [Hashable ν] in
theorem toVar_mem_cnfVars {F : Cnf L} {C : Clause L} {l : L} (hC : C ∈ F) (hl : l ∈ C) :
    LitVar.toVar l ∈ cnfVars F :=
  mem_cnfVars.mpr ⟨C, hC, l, hl, rfl⟩

/-- The measure is the number of distinct variables of `F`, minus the number
    of them that `τ` assigns. -/
theorem numUnassigned_eq (F : Cnf L) (τ : Assign ν) :
    numUnassigned F τ
      = (cnfVars F).card - ((cnfVars F).filter (fun x => τ.contains x = true)).card := by
  have := Finset.card_filter_add_card_filter_not (s := cnfVars F) (fun x => τ.contains x = true)
  simp only [Bool.not_eq_true] at this
  unfold numUnassigned
  omega

theorem numUnassigned_le_card (F : Cnf L) (τ : Assign ν) :
    numUnassigned F τ ≤ (cnfVars F).card :=
  Finset.card_filter_le _ _

/-- Setting any literal never increases the measure. -/
theorem numUnassigned_setLit_le (F : Cnf L) (τ : Assign ν) (l : L) :
    numUnassigned F (τ.setLit l) ≤ numUnassigned F τ := by
  apply Finset.card_le_card
  intro x
  simp only [Finset.mem_filter, setLit, HashMap.contains_insert, Bool.or_eq_false_iff]
  exact fun ⟨h₁, _, h₂⟩ => ⟨h₁, h₂⟩

/-- Setting an unassigned variable of `F` decreases the measure by exactly one. -/
theorem numUnassigned_setLit {F : Cnf L} {τ : Assign ν} {l : L}
    (hx : LitVar.toVar l ∈ cnfVars F) (hl : τ.litValue l = none) :
    numUnassigned F (τ.setLit l) + 1 = numUnassigned F τ := by
  have hc : τ.contains (LitVar.toVar l) = false := by
    simp only [litValue, Option.map_eq_none_iff] at hl
    simp [HashMap.contains_eq_isSome_getElem?, hl]
  have h_eq : (cnfVars F).filter (fun x => (τ.setLit l).contains x = false)
      = ((cnfVars F).filter (fun x => τ.contains x = false)).erase (LitVar.toVar l) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase, setLit, HashMap.contains_insert,
      Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    constructor
    · rintro ⟨h₁, h₂, h₃⟩; exact ⟨Ne.symm h₂, h₁, h₃⟩
    · rintro ⟨h₁, h₂, h₃⟩; exact ⟨h₂, Ne.symm h₁, h₃⟩
  have h_mem : LitVar.toVar l ∈ (cnfVars F).filter (fun x => τ.contains x = false) :=
    Finset.mem_filter.mpr ⟨hx, hc⟩
  unfold numUnassigned
  rw [h_eq, Finset.card_erase_of_mem h_mem]
  have := Finset.card_pos.mpr ⟨_, h_mem⟩
  omega

theorem numUnassigned_setLit_lt {F : Cnf L} {τ : Assign ν} {l : L}
    (hx : LitVar.toVar l ∈ cnfVars F) (hl : τ.litValue l = none) :
    numUnassigned F (τ.setLit l) < numUnassigned F τ := by
  have := numUnassigned_setLit hx hl
  omega

end Measure

/-! ### Reference implementation -/

/-- The status of a single clause under a partial assignment. -/
inductive ClauseStatus (L : Type u) where
  | sat
  | falsified
  | unit (l : L)
  | unknown

/-- Evaluates clause `C` under `τ`, starting from index `i`, where `u?` is the
    unassigned literal seen so far, if any. Exits early on a true literal. On a
    second (distinct) unassigned literal, only checks the rest for a true literal. -/
def evalClause (τ : Assign ν) (C : Clause L) (i : Nat := 0) (u? : Option L := none) :
    ClauseStatus L :=
  if hi : i < C.size then
    match hv : τ.litValue C[i] with
    | some true => .sat
    | some false => evalClause τ C (i + 1) u?
    | none =>
      match u? with
      | none => evalClause τ C (i + 1) (some C[i])
      | some u =>
        if u == C[i] then evalClause τ C (i + 1) (some u)
        else if C.any (τ.litValue · == some true) (i + 1) then .sat
        else .unknown
  else
    match u? with
    | none => .falsified
    | some u => .unit u
termination_by C.size - i

inductive ScanResult (L : Type u) where
  | unit (l : L)
  | conflict
  | done (allSat : Bool)

/-- Scans the clauses of `F` from index `i`, stopping at the first unit or
    falsified clause. `allSat` tracks whether every clause so far is satisfied. -/
def scan (τ : Assign ν) (F : Cnf L) (i : Nat) (allSat : Bool) : ScanResult L :=
  if hi : i < F.size then
    match evalClause τ F[i] with
    | .sat => scan τ F (i + 1) allSat
    | .falsified => .conflict
    | .unit l => .unit l
    | .unknown => scan τ F (i + 1) false
  else
    .done allSat
termination_by F.size - i

theorem evalClause_unit_mem_aux {τ : Assign ν} {C : Clause L} {i : Nat} {u? : Option L} {v : L} :
    evalClause τ C i u? = .unit v → u? = some v ∨ (v ∈ C ∧ τ.litValue v = none) := by
  fun_induction evalClause τ C i u? with
  | case1 i u? h hv => simp
  | case2 i u? h hv ih => exact ih
  | case3 i h hv _ ih =>
    intro hu
    rcases ih hu with (h' | h')
    · cases h'; exact Or.inr ⟨Array.getElem_mem h, hv⟩
    · exact Or.inr h'
  | case4 i h hv u _ hs ih =>
    exact ih
  | case5 i h hv u _ hs hany => simp
  | case6 i h hv u _ hs hany => simp
  | case7 i h => simp
  | case8 i h u => simp +contextual

theorem evalClause_unit_mem {τ : Assign ν} {C : Clause L} {v : L} :
    evalClause τ C = .unit v → v ∈ C ∧ τ.litValue v = none := by
  intro h
  rcases evalClause_unit_mem_aux h with (h | h)
  · cases h
  · exact h

theorem scan_unit {τ : Assign ν} {F : Cnf L} {i : Nat} {b : Bool} {l : L} :
    scan τ F i b = .unit l → ∃ C ∈ F, evalClause τ C = .unit l := by
  fun_induction scan τ F i b with
  | case1 i b h he ih => exact ih
  | case2 i b h he => simp
  | case3 i b h l' he =>
    intro hu; cases hu
    exact ⟨F[i], Array.getElem_mem h, he⟩
  | case4 i b h he ih => exact ih
  | case5 i b h => simp

/-- The reference implementation of unit propagation. Repeatedly scans `F`
    from the top for a unit clause, extending `τ` with its unit literal. -/
def unitPropRef [LawfulBEq ν] (F : Cnf L) (τ : Assign ν) : Assign ν × Result :=
  match _h : scan τ F 0 true with
  | .conflict => (τ, .unsat)
  | .done true => (τ, .sat)
  | .done false => (τ, .unknown)
  | .unit l => unitPropRef F (τ.setLit l)
termination_by numUnassigned F τ
decreasing_by
  rcases scan_unit _h with ⟨C, hC, hu⟩
  have ⟨h₁, h₂⟩ := evalClause_unit_mem hu
  exact numUnassigned_setLit_lt (toVar_mem_cnfVars hC h₁) h₂

/-! ### Watched-literal implementation -/

/-- The key of a literal in the watch map. -/
@[inline]
def litKey (l : L) : ν × Bool := (LitVar.toVar l, LitVar.polarity l)

structure WatchState (L : Type u) (ν : Type v) [BEq ν] [Hashable ν] where
  /-- The current partial assignment. -/
  assn : Assign ν
  /-- For each clause, the indices of its two watched literals. -/
  watchPos : Array (Nat × Nat)
  /-- For each literal, the indices of the clauses watching it. -/
  watches : HashMap (ν × Bool) (Array Nat)
  /-- The literals assigned true, in order. Propagation consumes it as a queue. -/
  trail : Array L

@[inline]
def addWatch (watches : HashMap (ν × Bool) (Array Nat)) (l : L) (ci : Nat) :
    HashMap (ν × Bool) (Array Nat) :=
  watches.alter (litKey l) (fun ws? => some ((ws?.getD #[]).push ci))

/-- Finds an index `k` of `C`, other than `i₁` and `i₂`, whose literal is not
    false under `τ` and is not `w`. -/
def findReplacement (τ : Assign ν) (C : Clause L) (i₁ i₂ : Nat) (w : L) (k : Nat) :
    Option (Nat × L) :=
  if hk : k < C.size then
    if k != i₁ && k != i₂ && τ.litValue C[k] != some false && !(C[k] == w) then
      some (k, C[k])
    else
      findReplacement τ C i₁ i₂ w (k + 1)
  else
    none
termination_by C.size - k

inductive WatchOutcome (L : Type u) where
  /-- Leave the watch where it is. -/
  | keep
  /-- Move the watch to `l`, with new watch positions `pos`. -/
  | moved (pos : Nat × Nat) (l : L)
  /-- The clause is unit, with unit literal `l`. -/
  | unit (l : L)
  | conflict

/-- Visits clause `C`, whose watched literal at index `fi` was just made false.
    The other watched literal is at index `wi`. -/
@[inline]
def visitCore (τ : Assign ν) (C : Clause L) (fi wi : Nat)
    (hf : fi < C.size) (hw : wi < C.size) : WatchOutcome L :=
  -- Defensive check, so that soundness does not depend on the watch invariants
  if τ.litValue C[fi] != some false then .keep
  else
    let w := C[wi]
    if τ.litValue w == some true then .keep
    else
      match findReplacement τ C fi wi w 0 with
      | some (k, l) => .moved (wi, k) l
      | none => if (τ.litValue w).isNone then .unit w else .conflict

/-- Visits clause `C`, one of whose watched literals is `fl`, which was just made false. -/
@[inline]
def visitClause (τ : Assign ν) (C : Clause L) (pos : Nat × Nat) (fl : L) :
    WatchOutcome L :=
  if h : pos.1 < C.size ∧ pos.2 < C.size then
    if C[pos.1] == fl then visitCore τ C pos.1 pos.2 h.1 h.2
    else visitCore τ C pos.2 pos.1 h.2 h.1
  else .keep

/-- Visits each clause in the watch list `ws` of the literal `nl`, which was
    just made false. Returns the new state, and whether a conflict was found. -/
def processWatches (F : Cnf L) (nl : L) (ws : Array Nat) (i : Nat) (kept : Array Nat)
    (st : WatchState L ν) : WatchState L ν × Bool :=
  if hi : i < ws.size then
    let ci := ws[i]
    if hc : ci < F.size ∧ ci < st.watchPos.size then
      match visitClause st.assn F[ci] st.watchPos[ci] nl with
      | .keep => processWatches F nl ws (i + 1) (kept.push ci) st
      | .moved pos l =>
        processWatches F nl ws (i + 1) kept
          { st with watchPos := st.watchPos.set ci pos hc.2,
                    watches := addWatch st.watches l ci }
      | .unit w =>
        processWatches F nl ws (i + 1) (kept.push ci)
          { st with assn := st.assn.setLit w, trail := st.trail.push w }
      | .conflict => (st, true)
    else
      processWatches F nl ws (i + 1) kept st
  else
    ({ st with watches := st.watches.insert (litKey nl) kept }, false)
termination_by ws.size - i

theorem visitCore_unit_mem {τ : Assign ν} {C : Clause L} {fi wi : Nat}
    {hf : fi < C.size} {hw : wi < C.size} {w : L} :
    visitCore τ C fi wi hf hw = .unit w → w ∈ C ∧ τ.litValue w = none := by
  unfold visitCore
  dsimp only
  split; · simp
  split; · simp
  split; · simp
  split <;> rename_i h_isNone
  · intro h; cases h
    exact ⟨Array.getElem_mem _, Option.isNone_iff_eq_none.mp h_isNone⟩
  · simp

theorem visitClause_unit_mem {τ : Assign ν} {C : Clause L} {pos : Nat × Nat} {fl w : L} :
    visitClause τ C pos fl = .unit w → w ∈ C ∧ τ.litValue w = none := by
  unfold visitClause
  split
  · split <;> exact visitCore_unit_mem
  · simp

/-- Each literal that `processWatches` pushes onto the trail assigns a
    previously unassigned variable of `F`. -/
theorem processWatches_measure [LawfulBEq ν] {F : Cnf L} {nl : L} {ws : Array Nat}
    {i : Nat} {kept : Array Nat} {st : WatchState L ν} :
    numUnassigned F (processWatches F nl ws i kept st).1.assn
        + (processWatches F nl ws i kept st).1.trail.size
      = numUnassigned F st.assn + st.trail.size := by
  fun_induction processWatches F nl ws i kept st with
  | case1 i kept st hi ci hc h ih => exact ih
  | case2 i kept st hi ci hc pos l h ih => exact ih
  | case3 i kept st hi ci hc w h ih =>
    have ⟨h₁, h₂⟩ := visitClause_unit_mem h
    have := numUnassigned_setLit (toVar_mem_cnfVars (Array.getElem_mem hc.1) h₁) h₂
    simp only [Array.size_push] at ih
    omega
  | case4 => rfl
  | case5 i kept st hi ci hc ih => exact ih
  | case6 => rfl

theorem processWatches_measure_of_eq [LawfulBEq ν] {F : Cnf L} {nl : L} {ws : Array Nat}
    {i : Nat} {kept : Array Nat} {st : WatchState L ν} {r : WatchState L ν × Bool}
    (h : processWatches F nl ws i kept st = r) :
    numUnassigned F r.1.assn + r.1.trail.size = numUnassigned F st.assn + st.trail.size :=
  h ▸ processWatches_measure

/-- One round of propagation: processes the trail literals at indices `qhead`
    up to (not including) `stop`. Literals that the round itself adds to the
    trail are left for the next round. Returns whether a conflict was found. -/
def propagateRound (F : Cnf L) (qhead stop : Nat) (st : WatchState L ν) :
    WatchState L ν × Bool :=
  if h : qhead < stop ∧ qhead < st.trail.size then
    let nl := -st.trail[qhead]
    match processWatches F nl (st.watches.getD (litKey nl) #[]) 0 #[] st with
    | (st', true) => (st', true)
    | (st', false) => propagateRound F (qhead + 1) stop st'
  else
    (st, false)
termination_by stop - qhead

theorem propagateRound_measure [LawfulBEq ν] {F : Cnf L} {qhead stop : Nat}
    {st : WatchState L ν} :
    numUnassigned F (propagateRound F qhead stop st).1.assn
        + (propagateRound F qhead stop st).1.trail.size
      = numUnassigned F st.assn + st.trail.size := by
  fun_induction propagateRound F qhead stop st with
  | case1 qhead st h nl st' hp => exact processWatches_measure_of_eq hp
  | case2 qhead st h nl st' hp ih => rw [ih]; exact processWatches_measure_of_eq hp
  | case3 => rfl

/-- Propagates in rounds, starting with the trail literals from `qhead` on.
    If a round adds no literals to the trail, propagation is complete.
    Otherwise, the round assigned at least one unassigned variable of `F`,
    so `numUnassigned` decreases. Returns whether a conflict was found. -/
def propagate [LawfulBEq ν] (F : Cnf L) (qhead : Nat) (st : WatchState L ν) :
    WatchState L ν × Bool :=
  match _h : propagateRound F qhead st.trail.size st with
  | (st', true) => (st', true)
  | (st', false) =>
    if _h_grow : st.trail.size < st'.trail.size then propagate F st.trail.size st'
    else (st', false)
termination_by numUnassigned F st.assn
decreasing_by
  have := @propagateRound_measure _ _ _ _ _ _ F qhead st.trail.size st
  rw [_h] at this
  dsimp only at this
  omega

/-- Finds an index `k` or later of `C` whose literal is not `l`. -/
def findOther (C : Clause L) (l : L) (k : Nat) : Option (Nat × L) :=
  if hk : k < C.size then
    if C[k] == l then findOther C l (k + 1) else some (k, C[k])
  else
    none
termination_by C.size - k

/-- Sets up the watches for clauses `i` onward. The two watched literals of a
    clause must be distinct, so clauses whose literals are all the same are
    treated as unit clauses and assigned immediately. Empty clauses are
    conflicts. Returns whether a conflict was found. -/
def initWatches (F : Cnf L) (i : Nat) (st : WatchState L ν) : WatchState L ν × Bool :=
  if hi : i < F.size then
    if h0 : 0 < F[i].size then
      let l := F[i][0]
      match hf : findOther F[i] l 1 with
      | some (j, l') =>
        initWatches F (i + 1)
          { st with watchPos := st.watchPos.push (0, j),
                    watches := addWatch (addWatch st.watches l i) l' i }
      | none =>
        match hv : st.assn.litValue l with
        | some true => initWatches F (i + 1) { st with watchPos := st.watchPos.push (0, 0) }
        | some false => (st, true)
        | none =>
          initWatches F (i + 1)
            { st with watchPos := st.watchPos.push (0, 0),
                      assn := st.assn.setLit l, trail := st.trail.push l }
    else
      (st, true)
  else
    (st, false)
termination_by F.size - i

/-- Unit propagation using two watched literals per clause. -/
def unitPropWatch [LawfulBEq ν] (F : Cnf L) (τ : Assign ν) : Assign ν × Result :=
  let trail := τ.fold (fun acc x b => acc.push (LitVar.mkLit L x b)) #[]
  let st₀ : WatchState L ν := { assn := τ, watchPos := Array.mkEmpty F.size, watches := {}, trail }
  match initWatches F 0 st₀ with
  | (st, true) => (st.assn, .unsat)
  | (st, false) =>
    match propagate F 0 st with
    | (st', true) => (st'.assn, .unsat)
    | (st', false) =>
      if Array.all F (fun C => C.any (st'.assn.litValue · == some true)) then (st'.assn, .sat)
      else (st'.assn, .unknown)

/-! ### Correctness -/

section Correctness

/-! #### Clause-level semantics -/

theorem IsFalsified.not_satisfies {τ : Assign ν} {σ : PropAssignment ν} {C : Clause L} :
    IsFalsified τ C → τ.Agrees σ → ¬ σ ⊨ C.toPropFun := by
  intro hC hσ h
  rcases Clause.satisfies_iff.mp h with ⟨l, hl, h⟩
  exact hσ.not_satisfies_of_false (hC l hl) h

theorem IsSat.satisfies {τ : Assign ν} {σ : PropAssignment ν} {C : Clause L} :
    IsSat τ C → τ.Agrees σ → σ ⊨ C.toPropFun := by
  rintro ⟨l, hl, h⟩ hσ
  exact Clause.satisfies_iff.mpr ⟨l, hl, hσ.satisfies_of_true h⟩

theorem IsUnit.forall {τ : Assign ν} {C : Clause L} {u : L} :
    IsUnit τ C u → ∀ l ∈ C, l = u ∨ τ.litValue l = some false := by
  rintro ⟨_, _, h⟩ l hl
  by_cases h_eq : l = u
  · exact Or.inl h_eq
  · exact Or.inr (h l hl h_eq)

/-- If all literals of `C` other than `u` are false, then any total assignment
    satisfying `C` that agrees with `τ` also agrees with `τ` extended by `u`. -/
theorem Assign.Agrees.setLit_of_unit [LawfulBEq ν] {τ : Assign ν} {σ : PropAssignment ν}
    {C : Clause L} {u : L} :
    (∀ l ∈ C, l = u ∨ τ.litValue l = some false) →
    τ.Agrees σ → σ ⊨ C.toPropFun → (τ.setLit u).Agrees σ := by
  intro hC hσ h
  rcases Clause.satisfies_iff.mp h with ⟨l, hl, h⟩
  rcases hC l hl with (rfl | hf)
  · exact hσ.setLit h
  · exact absurd h (hσ.not_satisfies_of_false hf)

/-- The partial assignment `τ` extends `τ₀` with literals implied by `F`. -/
def Sound (F : Cnf L) (τ₀ τ : Assign ν) : Prop :=
  τ₀.Extends τ ∧ ∀ σ, σ ⊨ F.toPropFun → τ₀.Agrees σ → τ.Agrees σ

theorem Sound.refl (F : Cnf L) (τ : Assign ν) : Sound F τ τ :=
  ⟨Extends.refl τ, fun _ _ h => h⟩

theorem Sound.setLit_of_unit [LawfulBEq ν] {F : Cnf L} {τ₀ τ : Assign ν} {C : Clause L}
    {u : L} :
    Sound F τ₀ τ → C ∈ F → τ.litValue u = none →
    (∀ l ∈ C, l = u ∨ τ.litValue l = some false) → Sound F τ₀ (τ.setLit u) := by
  rintro ⟨h_ext, h_agree⟩ hC hu h_unit
  refine ⟨h_ext.trans (extends_setLit hu), fun σ hσ hτ₀ => ?_⟩
  exact (h_agree σ hσ hτ₀).setLit_of_unit h_unit (Cnf.satisfies_iff.mp hσ C hC)

theorem Sound.unsat_of_falsified {F : Cnf L} {τ₀ τ : Assign ν} {C : Clause L} :
    Sound F τ₀ τ → C ∈ F → IsFalsified τ C → ∀ σ, τ₀.Agrees σ → ¬ σ ⊨ F.toPropFun := by
  rintro ⟨_, h_agree⟩ hC h_false σ hτ₀ hσ
  exact h_false.not_satisfies (h_agree σ hσ hτ₀) (Cnf.satisfies_iff.mp hσ C hC)

/-! #### Reference implementation -/

theorem evalClause_falsified_aux {τ : Assign ν} {C : Clause L} {i : Nat} {u? : Option L} :
    evalClause τ C i u? = .falsified →
      u? = none ∧ ∀ j (hj : j < C.size), i ≤ j → τ.litValue C[j] = some false := by
  fun_induction evalClause τ C i u? with
  | case1 i u? h hv => simp
  | case2 i u? h hv ih =>
    intro hf
    have ⟨h₁, h₂⟩ := ih hf
    refine ⟨h₁, fun j hj hij => ?_⟩
    rcases Nat.lt_or_eq_of_le hij with (hij | rfl)
    · exact h₂ j hj hij
    · exact hv
  | case3 i h hv _ ih =>
    intro hf; simpa using (ih hf).1
  | case4 i h hv u _ hs ih =>
    intro hf; simpa using (ih hf).1
  | case5 i h hv u _ hs hany => simp
  | case6 i h hv u _ hs hany => simp
  | case7 i h =>
    intro _
    exact ⟨rfl, fun j hj hij => absurd (Nat.lt_of_le_of_lt hij hj) h⟩
  | case8 i h u => simp

theorem evalClause_sat {τ : Assign ν} {C : Clause L} {i : Nat} {u? : Option L} :
    evalClause τ C i u? = .sat → IsSat τ C := by
  fun_induction evalClause τ C i u? with
  | case1 i u? h hv => intro _; exact ⟨C[i], Array.getElem_mem h, hv⟩
  | case2 i u? h hv ih => exact ih
  | case3 i h hv _ ih => exact ih
  | case4 i h hv u _ hs ih =>
    exact ih
  | case5 i h hv u _ hs hany =>
    intro _
    rcases Array.any_iff_exists.mp hany with ⟨j, hj, _, _, hp⟩
    exact ⟨C[j], Array.getElem_mem hj, by simpa using hp⟩
  | case6 i h hv u _ hs hany => simp
  | case7 i h => simp
  | case8 i h u => simp

theorem evalClause_unit_aux [LawfulBEq ν] [LawfulLitVar L ν] {τ : Assign ν} {C : Clause L}
    {i : Nat} {u? : Option L} {v : L} :
    evalClause τ C i u? = .unit v →
      (∀ u, u? = some u → v = u)
      ∧ ∀ j (hj : j < C.size), i ≤ j → C[j] ≠ v → τ.litValue C[j] = some false := by
  fun_induction evalClause τ C i u? with
  | case1 i u? h hv => simp
  | case2 i u? h hv ih =>
    intro hu
    have ⟨h₁, h₂⟩ := ih hu
    refine ⟨h₁, fun j hj hij hne => ?_⟩
    rcases Nat.lt_or_eq_of_le hij with (hij | rfl)
    · exact h₂ j hj hij hne
    · exact hv
  | case3 i h hv _ ih =>
    intro hu
    have ⟨h₁, h₂⟩ := ih hu
    cases h₁ _ rfl
    refine ⟨by simp, fun j hj hij hne => ?_⟩
    rcases Nat.lt_or_eq_of_le hij with (hij | rfl)
    · exact h₂ j hj hij hne
    · exact absurd rfl hne
  | case4 i h hv u _ hs ih =>
    intro hu
    have ⟨h₁, h₂⟩ := ih hu
    cases h₁ _ rfl
    rw [LitVar.beq_iff_eq] at hs
    refine ⟨h₁, fun j hj hij hne => ?_⟩
    rcases Nat.lt_or_eq_of_le hij with (hij | rfl)
    · exact h₂ j hj hij hne
    · exact absurd hs.symm hne
  | case5 i h hv u _ hs hany => simp
  | case6 i h hv u _ hs hany => simp
  | case7 i h => simp
  | case8 i h u =>
    intro hu; cases hu
    refine ⟨fun u' h' => ?_, fun j hj hij => absurd (Nat.lt_of_le_of_lt hij hj) h⟩
    cases h'; rfl

theorem evalClause_unknown_aux [LawfulBEq ν] {τ : Assign ν} {C : Clause L} {i : Nat}
    {u? : Option L} :
    evalClause τ C i u? = .unknown →
      (∀ u, u? = some u → ∃ l ∈ C, l ≠ u ∧ τ.litValue l = none)
      ∧ (u? = none → ∃ l₁ ∈ C, ∃ l₂ ∈ C, l₁ ≠ l₂
            ∧ τ.litValue l₁ = none ∧ τ.litValue l₂ = none) := by
  fun_induction evalClause τ C i u? with
  | case1 i u? h hv => simp
  | case2 i u? h hv ih => exact ih
  | case3 i h hv _ ih =>
    intro hu
    rcases (ih hu).1 _ rfl with ⟨l', h₁, h₂, h₃⟩
    exact ⟨by simp, fun _ => ⟨C[i], Array.getElem_mem h, l', h₁, Ne.symm h₂, hv, h₃⟩⟩
  | case4 i h hv u _ hs ih =>
    intro hu
    rcases (ih hu).1 _ rfl with ⟨l', h₁, h₂, h₃⟩
    exact ⟨fun u' hu' => by cases hu'; exact ⟨l', h₁, h₂, h₃⟩, by simp⟩
  | case5 i h hv u _ hs hany => simp
  | case6 i h hv u _ hs hany =>
    intro _
    refine ⟨fun u' hu' => ?_, by simp⟩
    cases hu'
    refine ⟨C[i], Array.getElem_mem h, fun h_eq => hs ?_, hv⟩
    simp [h_eq]
  | case7 i h => simp
  | case8 i h u => simp

theorem evalClause_falsified {τ : Assign ν} {C : Clause L} :
    evalClause τ C = .falsified → IsFalsified τ C := by
  intro h l hl
  rcases Array.mem_iff_getElem.mp hl with ⟨j, hj, rfl⟩
  exact (evalClause_falsified_aux h).2 j hj (Nat.zero_le _)

theorem evalClause_unit [LawfulBEq ν] [LawfulLitVar L ν] {τ : Assign ν} {C : Clause L}
    {u : L} :
    evalClause τ C = .unit u → IsUnit τ C u := by
  intro h
  have ⟨h₁, h₂⟩ := evalClause_unit_mem h
  refine ⟨h₁, h₂, fun l hl => ?_⟩
  rcases Array.mem_iff_getElem.mp hl with ⟨j, hj, rfl⟩
  exact (evalClause_unit_aux h).2 j hj (Nat.zero_le _)

theorem evalClause_unknown [LawfulBEq ν] {τ : Assign ν} {C : Clause L} :
    evalClause τ C = .unknown → ∃ l₁ ∈ C, ∃ l₂ ∈ C, l₁ ≠ l₂
      ∧ τ.litValue l₁ = none ∧ τ.litValue l₂ = none :=
  fun h => (evalClause_unknown_aux h).2 rfl

theorem evalClause_stable [LawfulBEq ν] {τ : Assign ν} {C : Clause L} :
    evalClause τ C = .sat ∨ evalClause τ C = .unknown → IsStable τ C := by
  rintro (h | h)
  · rcases evalClause_sat h with ⟨l, hl, h⟩
    refine ⟨fun hf => by simp [hf l hl] at h, fun u ⟨_, hu, hu'⟩ => ?_⟩
    by_cases h_eq : l = u
    · subst h_eq; simp [hu] at h
    · simp [hu' l hl h_eq] at h
  · rcases evalClause_unknown h with ⟨l₁, h₁, l₂, h₂, hne, hv₁, hv₂⟩
    refine ⟨fun hf => by simp [hf l₁ h₁] at hv₁, fun u ⟨_, _, hu⟩ => ?_⟩
    by_cases h_eq : l₁ = u
    · subst h_eq; simp [hu l₂ h₂ (Ne.symm hne)] at hv₂
    · simp [hu l₁ h₁ h_eq] at hv₁

theorem scan_conflict {τ : Assign ν} {F : Cnf L} {i : Nat} {b : Bool} :
    scan τ F i b = .conflict → ∃ C ∈ F, IsFalsified τ C := by
  fun_induction scan τ F i b with
  | case1 i b h he ih => exact ih
  | case2 i b h he => intro _; exact ⟨F[i], Array.getElem_mem h, evalClause_falsified he⟩
  | case3 i b h l he => simp
  | case4 i b h he ih => exact ih
  | case5 i b h => simp

theorem scan_done [LawfulBEq ν] {τ : Assign ν} {F : Cnf L} {i : Nat} {b b' : Bool} :
    scan τ F i b = .done b' →
      (∀ j (hj : j < F.size), i ≤ j → IsStable τ F[j])
      ∧ (b' = true → b = true ∧ ∀ j (hj : j < F.size), i ≤ j → IsSat τ F[j]) := by
  fun_induction scan τ F i b with
  | case1 i b h he ih =>
    intro hd
    have ⟨h₁, h₂⟩ := ih hd
    refine ⟨fun j hj hij => ?_, fun hb => ⟨(h₂ hb).1, fun j hj hij => ?_⟩⟩
    · rcases Nat.lt_or_eq_of_le hij with (hij | rfl)
      · exact h₁ j hj hij
      · exact evalClause_stable (Or.inl he)
    · rcases Nat.lt_or_eq_of_le hij with (hij | rfl)
      · exact (h₂ hb).2 j hj hij
      · exact evalClause_sat he
  | case2 i b h he => simp
  | case3 i b h l he => simp
  | case4 i b h he ih =>
    intro hd
    have ⟨h₁, h₂⟩ := ih hd
    refine ⟨fun j hj hij => ?_, fun hb => absurd (h₂ hb).1 (by simp)⟩
    rcases Nat.lt_or_eq_of_le hij with (hij | rfl)
    · exact h₁ j hj hij
    · exact evalClause_stable (Or.inr he)
  | case5 i b h =>
    intro hd; cases hd
    have h_none : ∀ j, j < F.size → i ≤ j → False :=
      fun j hj hij => h (Nat.lt_of_le_of_lt hij hj)
    exact ⟨fun j hj hij => (h_none j hj hij).elim,
      fun hb => ⟨hb, fun j hj hij => (h_none j hj hij).elim⟩⟩

/-- The combined specification of `unitPropRef`. -/
theorem unitPropRef_spec [LawfulBEq ν] [LawfulLitVar L ν] (F : Cnf L) (τ : Assign ν) :
    Sound F τ (unitPropRef F τ).1
    ∧ ((unitPropRef F τ).2 = .unsat → ∃ C ∈ F, IsFalsified (unitPropRef F τ).1 C)
    ∧ ((unitPropRef F τ).2 = .sat → ∀ C ∈ F, IsSat (unitPropRef F τ).1 C)
    ∧ ((unitPropRef F τ).2 ≠ .unsat → ∀ C ∈ F, IsStable (unitPropRef F τ).1 C) := by
  suffices ∀ τ', Sound F τ τ' →
      Sound F τ (unitPropRef F τ').1
      ∧ ((unitPropRef F τ').2 = .unsat → ∃ C ∈ F, IsFalsified (unitPropRef F τ').1 C)
      ∧ ((unitPropRef F τ').2 = .sat → ∀ C ∈ F, IsSat (unitPropRef F τ').1 C)
      ∧ ((unitPropRef F τ').2 ≠ .unsat → ∀ C ∈ F, IsStable (unitPropRef F τ').1 C) from
    this τ (Sound.refl F τ)
  have mem {P : Clause L → Prop} (h : ∀ j (hj : j < F.size), 0 ≤ j → P F[j]) :
      ∀ C ∈ F, P C := by
    intro C hC
    rcases Array.mem_iff_getElem.mp hC with ⟨j, hj, rfl⟩
    exact h j hj (Nat.zero_le _)
  intro τ' hτ'
  induction hn : numUnassigned F τ' using Nat.strong_induction_on generalizing τ' with
  | _ n ih =>
  rw [unitPropRef]
  split <;> rename_i h
  · rcases scan_conflict h with ⟨C, hC, hf⟩
    exact ⟨hτ', fun _ => ⟨C, hC, hf⟩, by simp, by simp⟩
  · have ⟨h₁, h₂⟩ := scan_done h
    exact ⟨hτ', by simp, fun _ => mem (h₂ rfl).2, fun _ => mem h₁⟩
  · have ⟨h₁, _⟩ := scan_done h
    exact ⟨hτ', by simp, by simp, fun _ => mem h₁⟩
  · rcases scan_unit h with ⟨C, hC, hu⟩
    have h_unit := evalClause_unit hu
    refine ih _ ?_ _ (hτ'.setLit_of_unit hC h_unit.2.1 h_unit.forall) rfl
    rw [← hn]
    exact numUnassigned_setLit_lt (toVar_mem_cnfVars hC h_unit.1) h_unit.2.1

theorem unitPropRef_extends [LawfulBEq ν] [LawfulLitVar L ν] (F : Cnf L) (τ : Assign ν) :
    τ.Extends (unitPropRef F τ).1 :=
  (unitPropRef_spec F τ).1.1

/-- Every literal derived by `unitPropRef` is implied by `F` and `τ`. -/
theorem unitPropRef_sound [LawfulBEq ν] [LawfulLitVar L ν] (F : Cnf L) (τ : Assign ν) :
    ∀ σ, σ ⊨ F.toPropFun → τ.Agrees σ → (unitPropRef F τ).1.Agrees σ :=
  (unitPropRef_spec F τ).1.2

theorem unitPropRef_unsat [LawfulBEq ν] [LawfulLitVar L ν] {F : Cnf L} {τ : Assign ν} :
    (unitPropRef F τ).2 = .unsat → ∀ σ, τ.Agrees σ → ¬ σ ⊨ F.toPropFun := by
  intro h
  rcases (unitPropRef_spec F τ).2.1 h with ⟨C, hC, hf⟩
  exact (unitPropRef_spec F τ).1.unsat_of_falsified hC hf

theorem unitPropRef_sat [LawfulBEq ν] [LawfulLitVar L ν] {F : Cnf L} {τ : Assign ν} :
    (unitPropRef F τ).2 = .sat → ∀ σ, (unitPropRef F τ).1.Agrees σ → σ ⊨ F.toPropFun := by
  intro h σ hσ
  exact Cnf.satisfies_iff.mpr fun C hC => ((unitPropRef_spec F τ).2.2.1 h C hC).satisfies hσ

/-- On a `sat` result, the returned assignment (with unassigned variables set
    to `true`) is a model of `F`. -/
theorem unitPropRef_sat_model [LawfulBEq ν] [LawfulLitVar L ν] {F : Cnf L} {τ : Assign ν} :
    (unitPropRef F τ).2 = .sat → (unitPropRef F τ).1.toPropAssignment ⊨ F.toPropFun :=
  fun h => unitPropRef_sat h _ (agrees_toPropAssignment _)

/-- Completeness: when `unitPropRef` does not find a conflict, no clause is
    unit or falsified under the returned assignment. -/
theorem unitPropRef_fixpoint [LawfulBEq ν] [LawfulLitVar L ν] {F : Cnf L} {τ : Assign ν} :
    (unitPropRef F τ).2 ≠ .unsat → ∀ C ∈ F, IsStable (unitPropRef F τ).1 C :=
  (unitPropRef_spec F τ).2.2.2

/-! #### Watched-literal implementation -/

theorem findReplacement_none [LawfulBEq ν] [LawfulLitVar L ν] {τ : Assign ν} {C : Clause L}
    {i₁ i₂ : Nat} {w : L} {k : Nat} :
    findReplacement τ C i₁ i₂ w k = none →
      ∀ j (hj : j < C.size), k ≤ j →
        j = i₁ ∨ j = i₂ ∨ τ.litValue C[j] = some false ∨ C[j] = w := by
  fun_induction findReplacement τ C i₁ i₂ w k with
  | case1 k hk h => simp
  | case2 k hk h ih =>
    intro hr j hj hkj
    rcases Nat.lt_or_eq_of_le hkj with (hkj | rfl)
    · exact ih hr j hj hkj
    · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', not_and] at h
      by_cases h₁ : k = i₁; · exact Or.inl h₁
      by_cases h₂ : k = i₂; · exact Or.inr (Or.inl h₂)
      by_cases h₃ : τ.litValue C[k] = some false; · exact Or.inr (Or.inr (Or.inl h₃))
      refine Or.inr (Or.inr (Or.inr ?_))
      have := h ⟨⟨h₁, h₂⟩, h₃⟩
      simp at this
      exact this
  | case3 k hk => intro _ j hj hkj; omega

theorem visitCore_spec [LawfulBEq ν] [LawfulLitVar L ν] {τ : Assign ν} {C : Clause L}
    {fi wi : Nat} {hf : fi < C.size} {hw : wi < C.size} :
    (∀ w, visitCore τ C fi wi hf hw = .unit w →
      τ.litValue w = none ∧ ∀ l ∈ C, l = w ∨ τ.litValue l = some false)
    ∧ (visitCore τ C fi wi hf hw = .conflict → IsFalsified τ C) := by
  unfold visitCore
  dsimp only
  split; · simp
  rename_i h_fi
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h_fi
  split; · simp
  rename_i h_wi
  split; · simp
  rename_i h_none
  have h_all : ∀ l ∈ C, l = C[wi] ∨ τ.litValue l = some false := by
    intro l hl
    rcases Array.mem_iff_getElem.mp hl with ⟨j, hj, rfl⟩
    rcases findReplacement_none h_none j hj (Nat.zero_le _) with (rfl | rfl | h | h)
    · exact Or.inr h_fi
    · exact Or.inl rfl
    · exact Or.inr h
    · exact Or.inl h
  split <;> rename_i h_isNone
  · refine ⟨fun w hw => ?_, by simp⟩
    cases hw
    exact ⟨Option.isNone_iff_eq_none.mp h_isNone, h_all⟩
  · refine ⟨by simp, fun _ l hl => ?_⟩
    rcases h_all l hl with (rfl | h)
    · revert h_wi h_isNone
      cases τ.litValue C[wi] with
      | none => simp
      | some b => cases b <;> simp
    · exact h

theorem visitClause_spec [LawfulBEq ν] [LawfulLitVar L ν] {τ : Assign ν} {C : Clause L}
    {pos : Nat × Nat} {fl : L} :
    (∀ w, visitClause τ C pos fl = .unit w →
      τ.litValue w = none ∧ ∀ l ∈ C, l = w ∨ τ.litValue l = some false)
    ∧ (visitClause τ C pos fl = .conflict → IsFalsified τ C) := by
  unfold visitClause
  split
  · split
    · exact visitCore_spec
    · exact visitCore_spec
  · simp

theorem processWatches_spec [LawfulBEq ν] [LawfulLitVar L ν] {F : Cnf L} {τ₀ : Assign ν}
    {nl : L} {ws : Array Nat} {i : Nat} {kept : Array Nat} {st : WatchState L ν} :
    Sound F τ₀ st.assn →
      Sound F τ₀ (processWatches F nl ws i kept st).1.assn
      ∧ ((processWatches F nl ws i kept st).2 = true →
          ∀ σ, τ₀.Agrees σ → ¬ σ ⊨ F.toPropFun) := by
  fun_induction processWatches F nl ws i kept st with
  | case1 i kept st hi ci hc h ih => exact ih
  | case2 i kept st hi ci hc pos l h ih => exact ih
  | case3 i kept st hi ci hc w h ih =>
    intro hs
    have ⟨h₁, h₂⟩ := (visitClause_spec.1 w h)
    exact ih (hs.setLit_of_unit (Array.getElem_mem hc.1) h₁ h₂)
  | case4 i kept st hi ci hc h =>
    intro hs
    exact ⟨hs, fun _ => hs.unsat_of_falsified (Array.getElem_mem hc.1) (visitClause_spec.2 h)⟩
  | case5 i kept st hi ci hc ih => exact ih
  | case6 i kept st hi => intro hs; exact ⟨hs, by simp⟩

theorem processWatches_spec_of_eq [LawfulBEq ν] [LawfulLitVar L ν] {F : Cnf L}
    {τ₀ : Assign ν} {nl : L} {ws : Array Nat} {i : Nat} {kept : Array Nat}
    {st : WatchState L ν} {r : WatchState L ν × Bool}
    (h : processWatches F nl ws i kept st = r) (hs : Sound F τ₀ st.assn) :
    Sound F τ₀ r.1.assn ∧ (r.2 = true → ∀ σ, τ₀.Agrees σ → ¬ σ ⊨ F.toPropFun) :=
  h ▸ processWatches_spec hs

theorem propagateRound_spec [LawfulBEq ν] [LawfulLitVar L ν] {F : Cnf L} {τ₀ : Assign ν}
    {qhead stop : Nat} {st : WatchState L ν} :
    Sound F τ₀ st.assn →
      Sound F τ₀ (propagateRound F qhead stop st).1.assn
      ∧ ((propagateRound F qhead stop st).2 = true →
          ∀ σ, τ₀.Agrees σ → ¬ σ ⊨ F.toPropFun) := by
  fun_induction propagateRound F qhead stop st with
  | case1 qhead st h nl st' hp => intro hs; exact processWatches_spec_of_eq hp hs
  | case2 qhead st h nl st' hp ih => intro hs; exact ih (processWatches_spec_of_eq hp hs).1
  | case3 qhead st h => intro hs; exact ⟨hs, by simp⟩

theorem propagateRound_spec_of_eq [LawfulBEq ν] [LawfulLitVar L ν] {F : Cnf L}
    {τ₀ : Assign ν} {qhead stop : Nat} {st : WatchState L ν} {r : WatchState L ν × Bool}
    (h : propagateRound F qhead stop st = r) (hs : Sound F τ₀ st.assn) :
    Sound F τ₀ r.1.assn ∧ (r.2 = true → ∀ σ, τ₀.Agrees σ → ¬ σ ⊨ F.toPropFun) :=
  h ▸ propagateRound_spec hs

theorem propagate_spec [LawfulBEq ν] [LawfulLitVar L ν] {F : Cnf L} {τ₀ : Assign ν}
    {qhead : Nat} {st : WatchState L ν} :
    Sound F τ₀ st.assn →
      Sound F τ₀ (propagate F qhead st).1.assn
      ∧ ((propagate F qhead st).2 = true → ∀ σ, τ₀.Agrees σ → ¬ σ ⊨ F.toPropFun) := by
  fun_induction propagate F qhead st with
  | case1 qhead st st' h => intro hs; exact propagateRound_spec_of_eq h hs
  | case2 qhead st st' h _ ih => intro hs; exact ih (propagateRound_spec_of_eq h hs).1
  | case3 qhead st st' h _ => intro hs; exact ⟨(propagateRound_spec_of_eq h hs).1, by simp⟩

omit [Hashable ν] in
theorem findOther_none [LawfulBEq ν] [LawfulLitVar L ν] {C : Clause L} {l : L} {k : Nat} :
    findOther C l k = none → ∀ j (hj : j < C.size), k ≤ j → C[j] = l := by
  fun_induction findOther C l k with
  | case1 k hk h ih =>
    intro hr j hj hkj
    rcases Nat.lt_or_eq_of_le hkj with (hkj | rfl)
    · exact ih hr j hj hkj
    · simp at h; exact h
  | case2 k hk h => simp
  | case3 k hk => intro _ j hj hkj; omega

theorem initWatches_spec [LawfulBEq ν] [LawfulLitVar L ν] {F : Cnf L} {τ₀ : Assign ν}
    {i : Nat} {st : WatchState L ν} :
    Sound F τ₀ st.assn →
      Sound F τ₀ (initWatches F i st).1.assn
      ∧ ((initWatches F i st).2 = true → ∀ σ, τ₀.Agrees σ → ¬ σ ⊨ F.toPropFun) := by
  fun_induction initWatches F i st with
  | case1 => assumption
  | case2 => assumption
  | case3 i st hi h0 l hf h =>
    intro hs
    refine ⟨hs, fun _ => hs.unsat_of_falsified (Array.getElem_mem hi) ?_⟩
    intro l' hl'
    rcases Array.mem_iff_getElem.mp hl' with ⟨j, hj, rfl⟩
    rcases Nat.eq_zero_or_pos j with (rfl | hj')
    · exact h
    · rw [findOther_none hf j hj hj']; exact h
  | case4 i st hi h0 l hf h ih =>
    intro hs
    refine ih (hs.setLit_of_unit (Array.getElem_mem hi) h ?_)
    intro l' hl'
    rcases Array.mem_iff_getElem.mp hl' with ⟨j, hj, rfl⟩
    rcases Nat.eq_zero_or_pos j with (rfl | hj')
    · exact Or.inl rfl
    · exact Or.inl (findOther_none hf j hj hj')
  | case5 i st hi h0 =>
    intro hs
    refine ⟨hs, fun _ => hs.unsat_of_falsified (Array.getElem_mem hi) ?_⟩
    intro l hl
    rcases Array.mem_iff_getElem.mp hl with ⟨j, hj, _⟩
    omega
  | case6 i st hi => intro hs; exact ⟨hs, by simp⟩

/-- The combined specification of `unitPropWatch`. -/
theorem unitPropWatch_spec [LawfulBEq ν] [LawfulLitVar L ν] (F : Cnf L) (τ : Assign ν) :
    Sound F τ (unitPropWatch F τ).1
    ∧ ((unitPropWatch F τ).2 = .unsat → ∀ σ, τ.Agrees σ → ¬ σ ⊨ F.toPropFun)
    ∧ ((unitPropWatch F τ).2 = .sat → ∀ C ∈ F, IsSat (unitPropWatch F τ).1 C) := by
  unfold unitPropWatch
  dsimp only
  have h_init := initWatches_spec (F := F) (i := 0)
    (st := { assn := τ, watchPos := Array.mkEmpty F.size, watches := {},
             trail := τ.fold (fun acc x b => acc.push (LitVar.mkLit L x b)) #[] })
    (Sound.refl F τ)
  split <;> rename_i st h
  · rw [h] at h_init
    exact ⟨h_init.1, fun _ => h_init.2 rfl, by simp⟩
  · rw [h] at h_init
    have h_prop := propagate_spec (qhead := 0) h_init.1
    split <;> rename_i st' h_eq <;> rw [h_eq] at h_prop
    · exact ⟨h_prop.1, fun _ => h_prop.2 rfl, by simp⟩
    · have := h_prop
      split <;> rename_i h_all
      · refine ⟨this.1, by simp, fun _ C hC => ?_⟩
        rw [Array.all_eq_true'] at h_all
        have := h_all C hC
        rw [Array.any_eq_true'] at this
        rcases this with ⟨l, hl, h⟩
        exact ⟨l, hl, by simpa using h⟩
      · exact ⟨this.1, by simp, by simp⟩

theorem unitPropWatch_extends [LawfulBEq ν] [LawfulLitVar L ν] (F : Cnf L) (τ : Assign ν) :
    τ.Extends (unitPropWatch F τ).1 :=
  (unitPropWatch_spec F τ).1.1

/-- Every literal derived by `unitPropWatch` is implied by `F` and `τ`. -/
theorem unitPropWatch_sound [LawfulBEq ν] [LawfulLitVar L ν] (F : Cnf L) (τ : Assign ν) :
    ∀ σ, σ ⊨ F.toPropFun → τ.Agrees σ → (unitPropWatch F τ).1.Agrees σ :=
  (unitPropWatch_spec F τ).1.2

theorem unitPropWatch_unsat [LawfulBEq ν] [LawfulLitVar L ν] {F : Cnf L} {τ : Assign ν} :
    (unitPropWatch F τ).2 = .unsat → ∀ σ, τ.Agrees σ → ¬ σ ⊨ F.toPropFun :=
  (unitPropWatch_spec F τ).2.1

theorem unitPropWatch_sat [LawfulBEq ν] [LawfulLitVar L ν] {F : Cnf L} {τ : Assign ν} :
    (unitPropWatch F τ).2 = .sat → ∀ σ, (unitPropWatch F τ).1.Agrees σ → σ ⊨ F.toPropFun := by
  intro h σ hσ
  exact Cnf.satisfies_iff.mpr fun C hC => ((unitPropWatch_spec F τ).2.2 h C hC).satisfies hσ

/-- On a `sat` result, the returned assignment (with unassigned variables set
    to `true`) is a model of `F`. -/
theorem unitPropWatch_sat_model [LawfulBEq ν] [LawfulLitVar L ν] {F : Cnf L} {τ : Assign ν} :
    (unitPropWatch F τ).2 = .sat → (unitPropWatch F τ).1.toPropAssignment ⊨ F.toPropFun :=
  fun h => unitPropWatch_sat h _ (agrees_toPropAssignment _)

end Correctness

end UnitProp

export UnitProp (unitPropRef unitPropWatch)

end Trestle
