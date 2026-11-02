/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Std
import Trestle.Data.Cnf
import Trestle.Data.ICnf
import Trestle.Data.Literal
import Trestle.Data.HashAssn
import Trestle.Upstream.ToStd
import Trestle.Data.RichCnf
import Trestle.Model.Quantifiers
import Trestle.Model.PropPred
import Trestle.Upstream.IndexType
import Trestle.Upstream.IndexTypeInstances
import Trestle.Upstream.Iterators

open Std

namespace Trestle.Encode

open Model

namespace EncCNF

/-- State for an encoding.

We need to parameterize by literal type `L` (and variable `ν`),
because otherwise we need to prove everywhere that clauses are "within range"
-/
@[ext]
structure State (ν : Type u) where
  nextVar : IVar
  cnf : RichICnf
  vMap : ν → IVar
  vNames : Std.TreeMap IVar String compare

/-- Lawfulness conditions on encoding state. -/
@[ext]
structure LawfulState (ν) extends State ν where
  cnfVarsLt : ∀ c ∈ cnf.toCnf, ∀ l ∈ c, (LitVar.toVar l) < nextVar
  vMapLt : ∀ v, vMap v < nextVar
  vMapInj : vMap.Injective

end EncCNF /- namespace -/

/-- Encoding monad.

This requires quite a few invariants to be held.
It receives and produces lawful states, and
`nextVar` is nondecreasing.
-/
def EncCNF (ν) (α) :=
  { sa : StateM (EncCNF.LawfulState ν) α //
    ∀ s, s.nextVar ≤ (sa s).2.nextVar }

namespace EncCNF

variable {ν : Type u} {L : Type v} [LitVar L ν]

namespace State

@[simp]
def toPropFun (s : State ν) : PropFun IVar :=
  s.cnf.toCnf.toPropFun

-- extract_closed off because otherwise the empty array becomes a shared object...
set_option compiler.extract_closed false in
def new (nextVar : IVar) (f : ν → IVar) (vNames : List (ν × String) := []) : State ν := {
  nextVar,
  cnf := #[]
  vMap := f
  vNames := vNames.foldl (init := .empty) (fun acc (v,n) => acc.insert (f v) n)
}

def addClause (C : Clause L) (st : State ν) : State ν :=
  let mappedC := C.map st.vMap
  { st with
    cnf :=
      let cnf := dbgTraceIfShared "State.addClause: cnf is shared (performance bug!)" st.cnf
      cnf.addClause mappedC
  }

@[simp]
theorem toPropFun_addClause (C : Clause L) (st : State ν)
    : (addClause C st).toPropFun = st.toPropFun ⊓ (PropFun.vmap st.vMap C) := by
  simp [dbgTraceIfShared, addClause]

def addComment (comment : String) (st : State ν) : State ν :=
  { st with
    cnf := st.cnf.addComment comment
  }

@[simp]
theorem toPropFun_addComment (comment) (st : State ν)
    : (addComment comment st).toPropFun = st.toPropFun := by
  simp [addComment]

end State /- namespace -/

namespace LawfulState

instance instCoeState : Coe (LawfulState ν) (State ν) := ⟨LawfulState.toState⟩

theorem semVars_toPropFun_cnf_lt (s : LawfulState ν)
    : ∀ v ∈ s.toPropFun.semVars, v < s.nextVar := by
  intro v h
  replace h := Cnf.mem_semVars_toPropFun h
  rcases h with ⟨C,hC,h⟩
  replace h := Clause.mem_semVars_toPropFun h
  rcases h with ⟨l,hl,rfl⟩
  apply s.cnfVarsLt _ hC _ hl

open PropFun in
/-- The interpretation of an `EncCNF` state is the
formula's interpretation, but with all temporaries
existentially quantified away.
-/
noncomputable def interp (s : LawfulState ν) : PropPred ν :=
  fun τ => ∃ (σ : PropAssignment IVar), τ = PropAssignment.map s.vMap σ ∧ σ ⊨ s.toPropFun

def new (nextVar : IVar) (f : ν ↪ IVar) (h : ∀ v, f v < nextVar) (names : List (ν × String) := [])
    : LawfulState ν := {
  State.new nextVar f names with
  cnfVarsLt := by intro c hc _ _; simp [State.new, RichCnf.toCnf] at hc
  vMapLt := h
  vMapInj := f.injective
}

@[simp]
theorem interp_new (vars) (f : ν ↪ IVar) (h) (names)
  : interp (new vars f h names) = fun _ => True := by
  ext τ
  simp [new, State.new, interp, Cnf.toPropFun, RichCnf.toCnf]
  apply τ.exists_preimage

@[simp]
theorem toState_new (vars) (f : ν ↪ IVar) (h) (names)
  : (new vars f h names).toState = State.new vars f names := rfl

def addClause (C : Clause L) : LawfulState ν → LawfulState ν
| {toState, vMapLt, vMapInj, cnfVarsLt} => {
  toState := toState.addClause C
  vMapLt,
  vMapInj,
  cnfVarsLt := by
    intro c hc v hv
    simp [State.addClause, Cnf.addClause] at hc
    rcases hc with hc|hc
    · exact cnfVarsLt _ hc _ hv
    · subst_vars; simp [Clause.map] at hv
      rcases hv with ⟨l,hv,rfl⟩
      simp [LitVar.map]; apply vMapLt
}

open PropFun in
@[simp]
theorem interp_addClause (C : Clause L) (s : LawfulState ν)
  : interp (addClause C s) = fun τ => interp s τ ∧ (τ ⊨ ↑C) := by
  ext τ
  simp [addClause, interp, State.addClause]
  rw [← exists_and_right]
  apply exists_congr; intro σ
  aesop

def addComment (comm : String) : LawfulState ν → LawfulState ν
| {toState, vMapLt, vMapInj, cnfVarsLt} => {
  toState := toState.addComment comm
  vMapLt
  vMapInj
  cnfVarsLt := by
    intro c hc v hv
    simp [State.addComment] at hc ⊢
    apply cnfVarsLt <;> assumption
}

@[simp] theorem interp_addComment (comm : String) (s : LawfulState ν)
  : interp (addComment comm s) = interp s := by
  ext τ
  simp [addComment, interp, State.addComment]

@[simp] theorem vMap_addComment (comm : String) (s : LawfulState ν)
  : (addComment comm s).vMap = s.vMap := by
  simp [addComment, State.addComment]

end LawfulState /- namespace -/

instance instMonad : Monad (EncCNF ν) where
  pure a := ⟨pure a, by simp [pure, StateT.pure]⟩
  bind | ⟨sa,h⟩, f => ⟨bind sa (f · |>.1), by
    intro s
    simp [bind, StateT.bind]
    split
    next a s' hs' =>
    apply Nat.le_trans (m := s'.nextVar.val)
    · have := h s
      rw [hs', IVar.le_def] at this
      exact this
    · exact (f a).2 s'
    ⟩

instance instLawfulMonad : LawfulMonad (EncCNF ν) where
  map_const := by simp [Functor.mapConst, Functor.map]
  id_map := by intros; simp [Functor.map]; split; rfl
  seqLeft_eq := by
    intros; simp [Functor.map]; rfl
  seqRight_eq := by
    intros; simp [Functor.map]; rfl
  pure_seq := by
    intros; simp [Functor.map]; rfl
  bind_pure_comp := by
    intros; simp [Functor.map]; rfl
  bind_map := by
    intros; simp [Functor.map]; rfl
  pure_bind := by
    intros; simp [bind]; rfl
  bind_assoc := by
    intros; simp [bind]; rfl

/-! Conversion theorems between `EncCNF` and `StateM`. -/

@[simp] theorem val_pure (a : α) : (pure a : EncCNF ν α).1 = (pure a : StateM (LawfulState ν) α) := rfl

@[simp] theorem val_bind (x : EncCNF ν α) (k : α → EncCNF ν β) :
    (x >>= k).1 = x.1 >>= (fun a => (k a).1) := by
  rcases x; rfl

@[simp] theorem val_map (g : α → β) (x : EncCNF ν α) : (g <$> x).1 = g <$> x.1 :=
  map_eq_of_pure_bind (·.1) val_pure val_bind g x

def run [IndexType ν] [LawfulIndexType ν] (e : EncCNF ν α) (names : List (ν × String) := []) : α × LawfulState ν :=
  e.1.run <| LawfulState.new
    (nextVar := .ofIndex (IndexType.card ν))
    (f := .trans IndexType.toEquiv.toEmbedding <|
          .trans Fin.valEmbedding
          ⟨IVar.ofIndex, by intro a b; simp [IVar.ofIndex_inj]⟩ )
    (h := by
      intro v
      rw [IVar.lt_def]
      simp only [Function.Embedding.trans_apply, Function.Embedding.coeFn_mk,
        Fin.valEmbedding_apply, IVar.ofIndex]
      exact Nat.succ_lt_succ (IndexType.toEquiv v).isLt)
    (names := names)

def runUnit {ν : Type} [IndexType ν] [LawfulIndexType ν] (e : EncCNF ν Unit) (names : List (ν × String) := []) : LawfulState ν :=
  run e names |>.2

def toRichICnf [IndexType ν] [LawfulIndexType ν] (e : EncCNF ν α) : RichICnf :=
  (run e).2.cnf

def toICnf [IndexType ν] [LawfulIndexType ν] (e : EncCNF ν α) : ICnf :=
  (run e).2.cnf.toCnf

def addClause {ν L : Type} [LitVar L ν] (C : Clause L) : EncCNF ν Unit :=
  ⟨ fun s => ((), s.addClause C)
  , by simp [LawfulState.addClause, State.addClause]⟩

def addComment {ν : Type} (comm : String) : EncCNF ν Unit :=
  ⟨ fun s => ((), s.addComment comm)
  , by simp [LawfulState.addComment, State.addComment] ⟩

def newCtx {ν α : Type} (name : String) (inner : EncCNF ν α) : EncCNF ν α := do
  addComment s!"start: {name}"
  let res ← inner
  addComment s!"end: {name}"
  return res

def addUnit {ν L : Type} [LitVar L ν] (l : L) : EncCNF ν Unit := addClause #[l]

def blockAssn {ν L : Type} [LitVar L ν] [BEq ν] [Hashable ν] (a : HashAssn L) : EncCNF ν Unit :=
  addClause (a.toLitArray.map (- ·))

def addAssn {ν L : Type} [LitVar L ν] [BEq ν] [Hashable ν] (a : HashAssn L) : EncCNF ν Unit := do
  for l in a.toLitArray do
    addUnit l

/-! ### Temporaries -/

namespace State

/--
  Allocates space for the temporary variables in the universe of `IndexType ι`.

  Note: This function must be marked `@[inline]` to prevent a memory-sharing slowdown.
  If it is NOT marked inline, then the `s.vMap` projection will not run until after the
  inner encoding has been run, which leads to a copied CNF.
-/
@[inline]
def withTemps [IndexType ι] (s : State ν) (names : Option (ι → String) := none) : State (ν ⊕ ι) where
  cnf := s.cnf
  nextVar := s.nextVar + IndexType.card ι
  vMap := vMap s.vMap s.nextVar
  vNames :=
    match names with
    | none => s.vNames
    | some nameF =>
      Fin.foldl (IndexType.card ι) (init := s.vNames) (fun acc t =>
        let i : ι := IndexType.fromFin t
        acc.insert (vMap s.vMap s.nextVar <| Sum.inr i) (nameF i)
      )
-- !!!!! an old version of this code passed the entire state `s` to
-- this `vMap` helper, which would cause the state to become shared
-- every time `State.withTemps` was called! yikes!!!
where vMap (vMap nextVar x) :=
  match x with
  | Sum.inl v => vMap v
  | Sum.inr i => nextVar + (IndexType.toFin i).val

@[simp] theorem cnf_withTemps [IndexType ι] (s : State ν) (names)
  : (State.withTemps s (ι := ι) names).cnf = s.cnf := rfl
@[simp] theorem nextVar_withTemps [IndexType ι] (s : State ν) (names)
  :  (withTemps s (ι := ι) names).nextVar = s.nextVar + IndexType.card ι := rfl
@[simp] theorem vMap_withTemps [IndexType ι] (s : State ν) (names)
  : (withTemps s (ι := ι) names).vMap = withTemps.vMap s.vMap s.nextVar := rfl

def withoutTemps (vMap : ν → IVar) (s : State (ν ⊕ ι)) : State ν where
  nextVar := s.nextVar
  vMap := vMap
  vNames := s.vNames
  cnf := s.cnf

@[simp] theorem cnf_withoutTemps (vMap : ν → IVar) (s : State (ν ⊕ ι)) :
    (State.withoutTemps vMap s).cnf = s.cnf := rfl
@[simp] theorem nextVar_withoutTemps (vMap : ν → IVar) (s : State (ν ⊕ ι)) :
    (State.withoutTemps vMap s).nextVar = s.nextVar := rfl
@[simp] theorem vMap_withoutTemps (vMap : ν → IVar) (s : State (ν ⊕ ι)) :
    (State.withoutTemps vMap s).vMap = vMap := rfl

end State /- namespace -/

namespace LawfulState

@[inline, inherit_doc State.withTemps]
def withTemps [IndexType ι] [LawfulIndexType ι] (s : LawfulState ν) (names : Option (ι → String) := none)
  : LawfulState (ν ⊕ ι) where
  toState := s.toState.withTemps names
  cnfVarsLt := by
    simp [State.withTemps]
    intro c hc l hl
    apply Nat.le_trans
    · exact s.cnfVarsLt c hc l hl
    · simp
  vMapLt := by
    simp [State.withTemps, State.withTemps.vMap]
    intro v; apply Nat.le_trans
    · apply s.vMapLt
    · simp
  vMapInj := by
    intro v₁ v₂
    simp [State.withTemps, State.withTemps.vMap]
    rcases v₁ with (v₁|i₁) <;> rcases v₂ with (v₂|i₂) <;> simp
    · apply s.vMapInj
    all_goals (
      intro h
      replace h := Subtype.ext_iff.mp h
    )
    · have := s.vMapLt v₁
      rw [IVar.lt_def] at this
      rw [IVar.val_addNat] at h
      omega
    · have := s.vMapLt v₂
      rw [IVar.lt_def] at this
      rw [IVar.val_addNat] at h
      omega
    · simp [Fin.val_eq_val] at h
      exact h

@[simp] theorem cnf_withTemps [IndexType ι] [LawfulIndexType ι] (s : LawfulState ν) (names) :
    (s.withTemps (ι := ι) names).cnf = s.cnf := rfl
@[simp] theorem nextVar_withTemps [IndexType ι] [LawfulIndexType ι] (s : LawfulState ν) (names) :
    (s.withTemps (ι := ι) names).nextVar = s.nextVar + IndexType.card ι := rfl
@[simp] theorem vMap_withTemps [IndexType ι] [LawfulIndexType ι] (s : LawfulState ν) (names) :
    (s.withTemps (ι := ι) names).vMap = State.withTemps.vMap s.vMap s.nextVar := rfl

@[simp]
theorem interp_withTemps [IndexType ι] [LawfulIndexType ι] (s : LawfulState ν) (names)
    : (s.withTemps (ι := ι) names).interp = fun τ => s.interp (τ.map Sum.inl) := by
  ext τ
  simp [interp, withTemps, State.withTemps]
  constructor
  · rintro ⟨σ,rfl,h⟩
    use σ; simp [h]
    ext v; simp [State.withTemps.vMap]
  · rintro ⟨σ,h1,h2⟩
    have ⟨σ',hσ'⟩ := τ.exists_preimage ⟨State.withTemps.vMap s.vMap s.nextVar, (LawfulState.withTemps s names).vMapInj⟩
    cases hσ'
    simp [PropAssignment.map] at h2 ⊢
    use σ.setMany
      (Finset.univ.image (State.withTemps.vMap (ι := ι) s.vMap s.nextVar <| Sum.inr ·))
      σ'
    constructor
    · ext vot
      rcases vot with (v|t)
      · have := congrFun h1 v
        simp at this; simp [this]; clear this h2
        simp [State.withTemps.vMap]
        rw [PropAssignment.setMany_not_mem]
        simp; intro x
        have := s.vMapLt v
        intro h_con
        replace h_con := congrArg Subtype.val h_con
        rw [IVar.lt_def] at this
        simp at h_con; omega
      · simp [State.withTemps.vMap]
        rw [PropAssignment.setMany_mem]
        · rfl
        · simp
    · apply (Model.PropFun.agreeOn_semVars _).mpr h2
      intro v hv
      simp at hv
      have := semVars_toPropFun_cnf_lt _ _ hv
      rw [PropAssignment.setMany_not_mem]
      simp [State.withTemps.vMap]
      intro v' h_con
      replace h_con := congrArg Subtype.val h_con
      rw [IVar.lt_def] at this
      simp at h_con; omega

def withoutTemps (s : LawfulState (ν ⊕ ι)) (vMap : ν → IVar) (vMapLt : ∀ v, vMap v < s.nextVar) (vMapInj : vMap.Injective)
    : LawfulState ν where
  toState := s.toState.withoutTemps vMap
  cnfVarsLt := by
    simp [State.withoutTemps]
    intro c hc l hl
    apply Nat.le_trans
    · exact s.cnfVarsLt c hc l hl
    · simp
  vMapLt := by
    simp [State.withoutTemps]
    apply vMapLt
  vMapInj := by
    intro v1 v2
    simp [State.withoutTemps]
    apply vMapInj

@[simp] theorem cnf_withoutTemps (s : LawfulState (ν ⊕ ι))
    {vMap : ν → IVar} {vMapLt : ∀ v, vMap v < s.nextVar} {vMapInj : vMap.Injective}
    : (LawfulState.withoutTemps s vMap vMapLt vMapInj).cnf = s.cnf := rfl
@[simp] theorem nextVar_withoutTemps (s : LawfulState (ν ⊕ ι))
    {vMap : ν → IVar} {vMapLt : ∀ v, vMap v < s.nextVar} {vMapInj : vMap.Injective}
    : (LawfulState.withoutTemps s vMap vMapLt vMapInj).nextVar = s.nextVar := rfl
@[simp] theorem vMap_withoutTemps (s : LawfulState (ν ⊕ ι))
    {vMap : ν → IVar} {vMapLt : ∀ v, vMap v < s.nextVar} {vMapInj : vMap.Injective}
    : (LawfulState.withoutTemps s vMap vMapLt vMapInj).vMap = vMap := rfl

theorem interp_withoutTemps
    (s : LawfulState (ν ⊕ ι))
    {vMap : ν → IVar} {vMapLt : ∀ v, vMap v < s.nextVar} {vMapInj : vMap.Injective}
    (h : vMap = s.vMap ∘ Sum.inl)
    : LawfulState.interp (LawfulState.withoutTemps s vMap vMapLt vMapInj) =
        fun τ => ∃ σ, τ = σ.map Sum.inl ∧ LawfulState.interp s σ
  := by
  ext τ
  cases h
  simp [LawfulState.withoutTemps, State.withoutTemps, interp]
  rfl

end LawfulState /- namespace -/

theorem nextVar_mono_of_eq {e : EncCNF ν α} (h : e.1 s = (a, s')) :
    s.nextVar ≤ s'.nextVar := by
  have := h ▸ e.2 s
  exact this

/-- Takes an encoding `e` that can use the newly-allocated temporary variables in `temps`
    and returns an encoding on just the base variable type `ν`. -/
def withTemps (ι) [IndexType ι] [LawfulIndexType ι] (e : (temps : ι → (ν ⊕ ι)) → EncCNF (ν ⊕ ι) α)
      (names : Option (ι → String) := none) : EncCNF ν α :=
  ⟨ fun s =>
    let vMap := s.vMap
    let vMapInj := s.vMapInj
    let tempify := s.withTemps names
    match h : (e Sum.inr).1 tempify with
    | (a,s') =>
    (a, s'.withoutTemps vMap (by
        intro v; rw [IVar.lt_def]
        apply Nat.lt_of_lt_of_le (m := s.nextVar.val)
        · apply s.vMapLt
        · apply Nat.le_trans (m := tempify.nextVar.val)
          · simp [tempify, LawfulState.withTemps, State.withTemps]
          · rw [← IVar.le_def]
            exact (e Sum.inr).nextVar_mono_of_eq h
      ) vMapInj)
  , by
    simp [LawfulState.withoutTemps, State.withoutTemps]
    intro s; split; simp; have := (e Sum.inr).nextVar_mono_of_eq ‹_›
    simp [LawfulState.withTemps, State.withTemps] at this
    apply Nat.le_trans (m := (s.nextVar + IndexType.card ι).val)
    · apply Nat.le_add_right
    · exact (PNat.coe_le_coe ..).mp this⟩

/-- Takes an encoding `e` that can use newly-allocated temporary variables (that must be manually constructed)
    and returns an encoding on just the base variable type `ν`. -/
abbrev withTemps' (ι) [IndexType ι] [LawfulIndexType ι] (e : EncCNF (ν ⊕ ι) α) (names : Option (ι → String) := none) : EncCNF ν α :=
  withTemps ι (fun _ => e) names

@[simp]
theorem withTemps'_eq_withTemps {ι} [IndexType ι] [LawfulIndexType ι] (e : EncCNF (ν ⊕ ι) α) (names : Option (ι → String) := none)
    : withTemps' ι e names = withTemps ι (fun _ => e) names := by
  simp [withTemps, withTemps']; rfl

abbrev freshn {ν α : Type} (n : Nat) (e : (temps : Fin n → (ν ⊕ Fin n)) → EncCNF (ν ⊕ Fin n) α)
      (names : Option (Fin n → String) := none) : EncCNF ν α :=
  withTemps (Fin n) e names

abbrev freshn' {ν α : Type} (n : Nat) (e : EncCNF (ν ⊕ Fin n) α)
      (names : Option (Fin n → String) := none) : EncCNF ν α :=
  withTemps' (Fin n) e names

/-- Takes an encoding `e` with a single temporary variable (passed to the encoding as an argument)
    and returns an encoding on just the base variable type `ν`. -/
@[inline]
def withTemp {ν α : Type} (e : (temp : (ν ⊕ Unit)) → EncCNF (ν ⊕ Unit) α) (name : Option String := none) : EncCNF ν α :=
  withTemps Unit (fun temps => e (temps ())) (name.map fun n _ => n)

/-! ### Iteration -/

section ForEach

variable {ν : Type} {γ : Type w} {α : Type x} [ForIn Id γ α]

/-- The state function of `forEach`: threads the encoder state through `f a`
for every element `a` visited by `c`, as a loop in `Id`. -/
@[inline]
def forInImpl (c : γ) (f : α → EncCNF ν Unit) (s : LawfulState ν) : LawfulState ν :=
  Id.run (ForIn.forIn c s (fun a s => pure (.yield ((f a).1 s).2)))

variable [ToList γ α] [LawfulForIn Id γ α]

/-- The state function of `forEach`, as a fold over `elems c`. -/
theorem forIn_state_eq_foldl (c : γ) (f : α → EncCNF ν Unit) (s : LawfulState ν) :
    forInImpl c f s = (toList c).foldl (fun s a => ((f a).1 s).2) s := by
  rw [forInImpl, forIn_eq_forIn_toList (m := Id), List.forIn_pure_yield_eq_foldl]; rfl

/--
  Runs `f a` for every element `a` visited by the iterator `c`, in order.

  This works over any lawful iterator, such as `Array`, `List`, ranges `[a:b]`,
  index type universes, `IndexType.univ ι`, and finite `Std.Iter`s.

  For efficiency, the loop runs in `Id`, with the encoder state as the loop accumulator.
  (Running `for a in c do f a` in the `EncCNF` state monad instead compiles to a loop
  that allocates a closure per iteration.) It does not allocate the list `elems c`.
  Its specification is `forEach_eq_forM`.
-/
@[inline]
def forEach (c : γ) (f : α → EncCNF ν Unit) : EncCNF ν Unit :=
  ⟨ fun s => ((), forInImpl c f s)
  , by
    intro s
    dsimp only
    rw [forIn_state_eq_foldl]
    induction toList c generalizing s with
    | nil => exact Nat.le_refl _
    | cons a L ih => exact Nat.le_trans ((f a).2 s) (ih _) ⟩

/-- `forEach c f` runs `f` on each element of `elems c` in order. -/
theorem forEach_eq_forM (c : γ) (f : α → EncCNF ν Unit) :
    forEach c f = (toList c).forM f := by
  apply Subtype.ext; funext s
  show ((), forInImpl c f s) = _
  rw [forIn_state_eq_foldl]
  induction toList c generalizing s with
  | nil => rfl
  | cons a L ih => exact ih _

end ForEach /- section -/

/-! ### Encoding propositions -/

/-- `e` encodes proposition `P` -/
def encodesProp (e : EncCNF ν α) (P : PropPred ν) : Prop :=
  ∀ (st : LawfulState ν),
    let s' := (e.1 st).2
    s'.vMap = st.vMap ∧
    ∀ (τ : PropAssignment ν), s'.interp τ ↔ st.interp τ ∧ (open PropPred in τ ⊨ P)

/-- If `e` encodes `P`, then `P` is satisfiable iff `e.toICnf` is satisfiable -/
theorem encodesProp_equisatisfiable [IndexType ν] [LawfulIndexType ν]
          (e : EncCNF ν α) (P : PropPred ν) (h : encodesProp e P)
  : (∃ τ : PropAssignment ν   , open PropPred in τ ⊨ P) ↔
    (∃ τ : PropAssignment IVar, open PropFun  in τ ⊨ e.toICnf.toPropFun) := by
  simp [EncCNF.toICnf, run, StateT.run]
  generalize hls : LawfulState.new _ _ _ _ = ls
  have := h ls
  generalize hls' : e.1 ls = ls' at this
  obtain ⟨_, ls'⟩ := ls'
  simp only at this ⊢
  rcases this with ⟨-,h3⟩
  rw [←hls] at h3; simp at h3
  clear hls' hls
  simp_rw [← h3]
  simp [LawfulState.interp]

theorem bind_encodesProp (e1 : EncCNF ν α) (f : α → EncCNF ν β)
  : e1.encodesProp P → (∀ s, (f (e1.1 s).1).encodesProp Q) →
    (e1 >>= f).encodesProp (P ⊓ Q)
  := by
  intro hP hQ s
  simp [encodesProp] at hP hQ
  -- specialize hypotheses to the first state `s`
  rcases e1 with ⟨e1,he1⟩
  replace hP := hP s
  replace hQ := hQ s
  simp [Bind.bind, StateT.bind] at hP hQ ⊢
  replace he1 := he1 s
  -- give name to the next state `s'`
  generalize hs' : e1 s = s' at *
  rcases s' with ⟨a,s'⟩
  simp at *
  -- give name to the next state machine
  generalize he2 : (f a) = e2 at *
  rcases e2 with ⟨e2,he2⟩
  -- specialize hypotheses to this state `s'`
  replace hQ := hQ s'
  simp at *
  -- give name to the next state `s''`
  generalize hs'' : e2 s' = s'' at *
  rcases s'' with ⟨b,s''⟩
  open PropPred in --necessary because simp doesn't simp thru scoped instances not in scope
  simp at hP hQ ⊢
  -- once again we ♥ aesop
  aesop

@[simp] theorem encodesProp_pure (a : α) : encodesProp (pure a : EncCNF ν α) ⊤ := by
  intro s; simp [Pure.pure, StateT.pure]

theorem encodesProp_map (e1 : EncCNF ν α) (f : α → β)
  : (f <$> e1).encodesProp P ↔ e1.encodesProp P
  := by
  constructor
  · intro h s
    specialize h s
    intro s'
    extract_lets s'' at h
    suffices s' = s'' by rw [this]; exact h
    rfl
  · intro h
    rw [map_eq_pure_bind]
    rw [show P = P ⊓ ⊤ by simp]
    apply bind_encodesProp
    · exact h
    simp

/-- Running `f a` for each `a ∈ L` encodes the conjunction of the `P a`. -/
theorem encodesProp_forM {ν : Type} {P : α → PropPred ν} (L : List α) {f : α → EncCNF ν Unit}
    (hf : ∀ a, (f a).encodesProp (P a)) :
    (L.forM f).encodesProp (fun τ => ∀ a ∈ L, P a τ) := by
  induction L with
  | nil =>
    show encodesProp (pure ()) _
    rw [show (fun τ => ∀ a ∈ [], P a τ) = ⊤ by ext; simp]; simp
  | cons a L ih =>
    show encodesProp (f a >>= fun _ => L.forM f) _
    rw [show (fun τ => ∀ b ∈ a :: L, P b τ) = P a ⊓ (fun τ => ∀ b ∈ L, P b τ) by
      ext τ; simp]
    exact bind_encodesProp _ _ (hf a) (fun _ => ih)

/-- `forEach c f` encodes the conjunction of the `P a` for `a ∈ elems c`. -/
theorem encodesProp_forEach {ν : Type} {γ : Type w} {α : Type x}
    [ForIn Id γ α] [ToList γ α] [LawfulForIn Id γ α]
    (c : γ) {P : α → PropPred ν} {f : α → EncCNF ν Unit} (hf : ∀ a, (f a).encodesProp (P a)) :
    (forEach c f).encodesProp (fun τ => ∀ a ∈ toList c, P a τ) := by
  rw [forEach_eq_forM]; exact encodesProp_forM _ hf

end EncCNF /- namespace -/

end Trestle.Encode /- namespace -/
