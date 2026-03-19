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
import Trestle.Upstream.IndexType
import Trestle.Upstream.IndexTypeInstances

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
  cnf : RichCnf
  vMap : ν → IVar
  vNames : Batteries.RBMap IVar String compare

namespace State

@[simp]
def toPropFun (s : State ν) : PropFun IVar := s.cnf.toICnf.toPropFun

-- extract_closed off because otherwise the empty array becomes a shared object...
set_option compiler.extract_closed false in
def new (nextVar : IVar) (f : ν → IVar) (vNames : List (ν × String)) : State ν := {
  nextVar,
  cnf := #[]
  vMap := f
  vNames := vNames.foldl (init := .empty) (fun acc (v,n) => acc.insert (f v) n)
}

def addClause (C : Clause (Literal ν)) (s : State ν) : State ν :=
  match s with
  | {nextVar, cnf, vMap, vNames} => {
    nextVar, vMap, vNames
    cnf :=
      let cnf :=
        dbgTraceIfShared
          "State.addClause: cnf is shared (performance bug!)"
          cnf
      cnf.addClause (C.map _ vMap)
  }

@[simp] theorem toPropFun_addClause (C : Clause (Literal ν)) (s)
  : (addClause C s).toPropFun = s.toPropFun ⊓ (PropFun.map s.vMap C)
  := by
  simp [dbgTraceIfShared, addClause]


def addComment (comment : String) (s : State ν) : State ν :=
  match s with
  | {nextVar, cnf, vMap, vNames} => {
    nextVar, vMap, vNames
    cnf := cnf.addComment comment
  }

@[simp] theorem toPropFun_addComment (comment) (s : State ν) :
      (addComment comment s).toPropFun = s.toPropFun := by
  simp [addComment]

--instance : ToString (State ν) := ⟨toString ∘ State.cnf⟩

end State

/-- Lawfulness conditions on encoding state. -/
@[ext]
structure LawfulState (ν) extends State ν where
  cnfVarsLt : ∀ c ∈ cnf.toICnf, ∀ l ∈ c, (LitVar.toVar l) < nextVar
  vMapLt : ∀ v, vMap v < nextVar
  vMapInj : vMap.Injective

namespace LawfulState

instance : Coe (LawfulState ν) (State ν) := ⟨LawfulState.toState⟩

theorem semVars_toPropFun_cnf_lt (s : LawfulState ν)
  : ∀ v ∈ s.toPropFun.semVars, v < s.nextVar := by
  intro v h
  replace h := Cnf.mem_semVars_toPropFun _ _ h
  rcases h with ⟨C,hC,h⟩
  replace h := Clause.mem_semVars_toPropFun _ _ h
  rcases h with ⟨l,hl,rfl⟩
  apply s.cnfVarsLt _ hC _ hl


variable [LitVar L ν]

open PropFun in
/-- The interpretation of an `EncCNF` state is the
formula's interpretation, but with all temporaries
existentially quantified away.
-/
noncomputable def interp (s : LawfulState ν) : PropAssignment ν → Prop :=
  fun τ => ∃ σ, τ = PropAssignment.map s.vMap σ ∧ σ ⊨ s.toPropFun

def new (nextVar : IVar) (f : ν ↪ IVar) (h : ∀ v, f v < nextVar) (names : List (ν × String))
    : LawfulState ν := {
  State.new nextVar f names with
  cnfVarsLt := by intro c hc _ _; simp [State.new, RichCnf.toICnf] at hc
  vMapLt := h
  vMapInj := f.injective
}

@[simp]
theorem interp_new (vars) (f : ν ↪ IVar) (h) (names)
  : interp (new vars f h names) = fun _ => True := by
  ext τ
  simp [new, State.new, interp, Cnf.toPropFun, RichCnf.toICnf]
  apply τ.exists_preimage

@[simp]
theorem toState_new (vars) (f : ν ↪ IVar) (h) (names)
  : (new vars f h names).toState = State.new vars f names := rfl


def addClause (C : Clause (Literal ν)) : LawfulState ν → LawfulState ν
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
@[simp] theorem interp_addClause
        (C : Clause (Literal ν)) (s : LawfulState ν)
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

end LawfulState

end EncCNF

/-- Encoding monad.

This requires quite a few invariants to be held.
It receives and produces lawful states, and
`nextVar` is nondecreasing.
-/
def EncCNF (ν) (α) :=
  { sa : StateM (EncCNF.LawfulState ν) α //
    ∀ s, s.nextVar ≤ (sa s).2.nextVar }

namespace EncCNF

variable {ν}

instance : Monad (EncCNF ν) where
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

instance : LawfulMonad (EncCNF ν) where
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

def run [IndexType ν] [LawfulIndexType ν] (e : EncCNF ν α) (names : List (ν × String) := []) : α × LawfulState ν :=
  e.1.run <| LawfulState.new
    (nextVar := .ofIndex (IndexType.card ν))
    (f := .trans IndexType.toEquiv.toEmbedding <|
          .trans Fin.valEmbedding
          ⟨IVar.ofIndex,by intro a b; simp [IVar.ofIndex_inj]⟩ )
    (h := by intro v; simp)
    (names := names)

def runUnit [IndexType ν] [LawfulIndexType ν] (e : EncCNF ν Unit) (names : List (ν × String) := []) : LawfulState ν :=
  run e names |>.2

def toRichCnf [IndexType ν] [LawfulIndexType ν] (e : EncCNF ν α) : RichCnf :=
  (run e).2.cnf

def toICnf [IndexType ν] [LawfulIndexType ν] (e : EncCNF ν α) : ICnf :=
  (run e).2.cnf.toICnf

def addClause (C : Clause (Literal ν)) : EncCNF ν Unit :=
  ⟨ fun s => ((), s.addClause C)
  , by simp [LawfulState.addClause, State.addClause]⟩

def addComment (comm : String) : EncCNF ν Unit :=
  ⟨ fun s => ((), s.addComment comm)
  , by simp [LawfulState.addComment, State.addComment] ⟩

def newCtx (name : String) (inner : EncCNF ν α) : EncCNF ν α := do
  addComment s!"start: {name}"
  let res ← inner
  addComment s!"end: {name}"
  return res

def unit (l : Literal ν) : EncCNF ν Unit := addClause #[l]

def blockAssn [BEq ν] [Hashable ν] (a : HashAssn (Literal ν)) : EncCNF ν Unit :=
  addClause (a.toLitArray.map (- ·))

def addAssn [BEq ν] [Hashable ν] (a : HashAssn (Literal ν)) : EncCNF ν Unit := do
  for l in a.toLitArray do
    unit l


/-! ### Temporaries -/

def State.withTemps [IndexType ι] (s : State ν) (names : Option (ι → String)) : State (ν ⊕ ι) where
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
where vMap (vMap nextVar x):=
  match x with
  | Sum.inl v => vMap v
  | Sum.inr i => nextVar + (IndexType.toFin i).val

@[simp] theorem State.cnf_withTemps [IndexType ι] (s : State ν) :
    (State.withTemps s (ι := ι) names).cnf = s.cnf
  := by simp [State.withTemps]

def LawfulState.withTemps [IndexType ι] [LawfulIndexType ι] (s : LawfulState ν) (names : Option (ι → String))
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
    intro v1 v2
    simp [State.withTemps]
    rcases v1 with (v1|i1) <;> rcases v2 with (v2|i2) <;> simp [State.withTemps.vMap]
    · apply s.vMapInj
    · have := s.vMapLt v1; rw [IVar.lt_def] at this; rw [Subtype.ext_iff, IVar.val_addNat]; omega
    · have := s.vMapLt v2; rw [IVar.lt_def] at this; rw [Subtype.ext_iff, IVar.val_addNat]; omega
    · rw [Subtype.ext_iff]; simp [IVar.val_addNat]
      rw [Fin.val_eq_val, IndexType.toFin_eq_iff]
      exact id

@[simp] theorem LawfulState.vMap_withTemps [IndexType ι] [LawfulIndexType ι] (s : LawfulState ν) :
    (s.withTemps (ι := ι) names).vMap = State.withTemps.vMap s.vMap s.nextVar
  := by simp [LawfulState.withTemps, State.withTemps]

@[simp]
theorem LawfulState.interp_withTemps [IndexType ι] [LawfulIndexType ι] (s : LawfulState ν)
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
        rw [←Subtype.val_inj]; rw [IVar.lt_def] at this
        simp; omega
      · simp [State.withTemps.vMap]
    · apply (Model.PropFun.agreeOn_semVars _).mpr h2
      intro v hv
      simp at hv
      have := semVars_toPropFun_cnf_lt _ _ hv
      rw [PropAssignment.setMany_not_mem]
      simp [State.withTemps.vMap]
      intro v'
      rw [←Subtype.val_inj]; rw [IVar.lt_def] at this
      simp; omega


def State.withoutTemps (vMap : ν → IVar) (s : State (ν ⊕ ι)) : State ν where
  nextVar := s.nextVar
  vMap := vMap
  vNames := s.vNames
  cnf := s.cnf

@[simp] theorem State.vMap_withoutTemps (s : State _) :
    (State.withoutTemps (ν := ν) (ι := ι) vm s).vMap = vm
  := by simp [State.withoutTemps]

def LawfulState.withoutTemps (s : LawfulState (ν ⊕ ι))
    (vMap : ν → IVar) (vMapLt : ∀ v, vMap v < s.nextVar) (vMapInj : vMap.Injective)
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

@[simp] theorem LawfulState.vMap_withoutTemps (s : LawfulState (ν ⊕ ι))
    {vMap : ν → IVar} {vMapLt : ∀ v, vMap v < s.nextVar} {vMapInj : vMap.Injective}
    : (LawfulState.withoutTemps s vMap vMapLt vMapInj).vMap = vMap
  := by simp [LawfulState.withoutTemps]

theorem LawfulState.interp_withoutTemps
    (s : LawfulState (ν ⊕ ι))
    {vMap : ν → IVar} {vMapLt : ∀ v, vMap v < s.nextVar} {vMapInj : vMap.Injective}
    (h : vMap = s.vMap ∘ Sum.inl)
    : LawfulState.interp (LawfulState.withoutTemps s vMap vMapLt vMapInj) =
        fun τ => ∃ σ, τ = σ.map Sum.inl ∧ LawfulState.interp s σ
  := by
  ext τ
  cases h
  simp [LawfulState.withoutTemps, State.withoutTemps, interp]
  aesop

def nextVar_mono_of_eq {e : EncCNF ν α} (h : e.1 s = (a, s')) :
    s.nextVar ≤ s'.nextVar := by
  have := h ▸ e.2 s
  exact this

def withTemps (ι) [IndexType ι] [LawfulIndexType ι] (e : EncCNF (ν ⊕ ι) α) (names : Option (ι → String) := none) : EncCNF ν α :=
  ⟨ fun s =>
    let vMap := s.vMap
    let vMapInj := s.vMapInj
    let tempify := s.withTemps names
    match h : e.1 tempify with
    | (a,s') =>
    (a, s'.withoutTemps vMap (by
        intro v; rw [IVar.lt_def]
        apply Nat.lt_of_lt_of_le (m := s.nextVar.val)
        · apply s.vMapLt
        · apply Nat.le_trans (m := tempify.nextVar.val)
          · simp [tempify, LawfulState.withTemps, State.withTemps]
          · rw [← IVar.le_def]
            exact e.nextVar_mono_of_eq h
      ) vMapInj)
  , by simp [LawfulState.withoutTemps, State.withoutTemps]
       intro s; split; simp; have := e.nextVar_mono_of_eq ‹_›
       simp [LawfulState.withTemps, State.withTemps] at this
       apply Nat.le_trans (m := (s.nextVar + IndexType.card ι).val)
       · apply Nat.le_add_right
       · exact (PNat.coe_le_coe ..).mp this⟩
