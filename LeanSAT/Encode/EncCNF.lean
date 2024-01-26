import Std
import LeanSAT.Data.Cnf
import LeanSAT.Data.ICnf
import LeanSAT.Data.HashAssn
import LeanSAT.Upstream.ToStd
import LeanSAT.Model.Quantifiers

open Std

namespace LeanSAT.Encode

open Model

namespace EncCNF

/-- State for an encoding.

We need to parameterize by literal type `L` (and variable `ν`),
because otherwise we need to prove everywhere that clauses are "within range"
-/
@[ext]
structure State (L ν : Type u) where
  nextVar : PNat
  cnf : ICnf
  vMap : ν → IVar
  /-- assume `¬assumeVars` in each new clause -/
  assumeVars : Clause L

namespace State

def new (vars : PNat) (f : ν → IVar) : State L ν := {
  nextVar := vars
  cnf := #[]
  vMap := f
  assumeVars := #[]
}

def addClause [LitVar L ν] (C : Clause L) : State L ν → State L ν
| {nextVar, cnf, vMap, assumeVars} => {
  nextVar := nextVar
  vMap := vMap
  assumeVars := assumeVars
  cnf := cnf.addClause ((Clause.or assumeVars C).map _ vMap)
}

@[simp] theorem toPropFun_addClause [LitVar L ν] (C : Clause L) (s)
  : (addClause C s).cnf.toPropFun = s.cnf.toPropFun ⊓ PropFun.map s.vMap (s.assumeVarsᶜ ⇨ C)
  := by
  simp [addClause, BooleanAlgebra.himp_eq, sup_comm]

instance : ToString (State L ν) := ⟨toString ∘ State.cnf⟩

end State

/-- Lawfulness conditions on encoding state. -/
@[ext]
structure LawfulState (L ν) extends State L ν where
  cnfVarsLt : ∀ c ∈ cnf, ∀ l ∈ c, (LitVar.toVar l) < nextVar
  vMapLt : ∀ v, vMap v < nextVar
  vMapInj : vMap.Injective

namespace LawfulState

instance : Coe (LawfulState L ν) (State L ν) := ⟨LawfulState.toState⟩

theorem semVars_toPropFun_cnf_lt (s : LawfulState L ν)
  : ∀ v ∈ s.cnf.toPropFun.semVars, v < s.nextVar := by
  intro v h
  replace h := Cnf.mem_semVars_toPropFun _ _ h
  rcases h with ⟨C,hC,h⟩
  replace h := Clause.mem_semVars_toPropFun _ _ h
  rcases h with ⟨l,hl,rfl⟩
  apply s.cnfVarsLt _ hC _ hl

/-- Thanks to `vInjLt` we know `V` is `Fintype`. -/
noncomputable def fintype (s : LawfulState L ν) : Fintype ν :=
  Fintype.ofInjective (β := Fin s.nextVar)
    (fun v => ⟨s.vMap v, s.vMapLt ..⟩)
    (by intro v1 v2 h
        apply s.vMapInj
        simpa [PNat.val, ← Subtype.ext_iff] using h)

variable [DecidableEq ν] [Fintype ν] [LitVar L ν]

/-- The interpretation of an `EncCNF` state is the
formula's interpretation, but with all temporaries
existentially quantified away.
-/
noncomputable def interp (s : LawfulState L ν) : PropFun ν :=
  let φ := s.cnf.toPropFun
  have varsLt : ∀ v ∈ φ.semVars, v < s.nextVar := by
    intro v hv
    have ⟨C, hC, L, h1, h2⟩ := Cnf.semVars_toPropFun _ hv
    have := s.cnfVarsLt C hC L h1
    rw [h2] at this
    exact this
  φ.attach.map (fun ⟨v,h⟩ => Fin.mk v (varsLt _ h))
    |>.existsInv (fun v => ⟨s.vMap v, s.vMapLt _⟩)

def new (vars : PNat) (f : ν ↪ IVar) (h : ∀ v, f v < vars) : LawfulState L ν := {
  State.new vars f with
  cnfVarsLt := by intro c hc _ _; simp [State.new, Array.mem_def] at hc
  vMapLt := h
  vMapInj := f.injective
}

set_option pp.proofs.withType false in
@[simp]
theorem interp_new (vars) (f : ν ↪ IVar) (h)
  : interp (new (L := L) vars f h) = ⊤ := by
  ext τ
  simp [new, State.new, interp]
  use τ.preimage ⟨fun v => ⟨f v, h v⟩, by
    intro _ _ _; simp_all⟩
  simp [Cnf.toPropFun]

def addClause (C : Clause L) (s : LawfulState L ν) : LawfulState L ν where
  toState := s.toState.addClause C
  vMapLt := s.vMapLt
  vMapInj := s.vMapInj
  cnfVarsLt := by
    intro c hc v hv
    simp [State.addClause, Cnf.addClause, Clause.or, LitVar.map] at hc
    cases hc
    · apply cnfVarsLt; repeat assumption
    · subst_vars; simp [Clause.map] at hv
      rcases hv with ⟨a,_|_,rfl⟩
      · simp [LitVar.map]; apply vMapLt
      · simp [LitVar.map]; apply vMapLt

set_option pp.proofs.withType false in
set_option trace.Meta.isDefEq true in
@[simp]
theorem interp_addClause
        (C : Clause L) (s : LawfulState L ν)
  : interp (addClause C s) = interp s ⊓ ((s.assumeVars)ᶜ ⇨ C) := by
  ext τ
  simp [-PropFun.satisfies_impl, addClause, interp]
  rw [PropAssignment.map_eq_map]
  stop
  constructor
  · rintro ⟨σ,⟨σ',hσ',h1,h2⟩,rfl⟩
    simp [State.addClause] at σ
    constructor
    · use σ
      constructor
      · use σ'
        simp [*]
        ext ⟨v,hv⟩
        have := congrFun hσ' ⟨v,?_⟩
        · simpa using this
        · simp [State.addClause]; sorry
      · simp [State.addClause]
    · apply (PropFun.agreeOn_semVars _).mpr h2
      intro v hv
      simp at hv
      sorry
  · sorry

end LawfulState

end EncCNF

/-- Encoding monad.

This requires quite a few invariants to be held.
It receives and produces lawful states, and
never decreases the `nextVar`.
-/
def EncCNF (L) [LitVar L ν] (α) :=
  { sa : StateM (EncCNF.LawfulState L ν) α //
    ∀ s, s.nextVar ≤ (sa s).2.nextVar }

namespace EncCNF

variable {L} [LitVar L ν]

instance : Monad (EncCNF L) where
  pure a := ⟨pure a, by simp [pure, StateT.pure]⟩
  bind | ⟨sa,h⟩, f => ⟨bind sa (f · |>.1), by
    intro s
    simp [bind, StateT.bind]
    split
    next a s' hs' =>
    apply Nat.le_trans (m := s'.nextVar)
    · have := h s
      rw [hs'] at this
      exact this
    · exact (f a).2 s'
    ⟩

def newCtx (name : String) (inner : EncCNF L α) : EncCNF L α := do
  let res ← inner
  return res

def addClause (C : Clause L) : EncCNF L Unit :=
  ⟨ fun s =>
    ((), s.addClause C), by simp [LawfulState.addClause, State.addClause]⟩

/-- runs `e`, adding `ls` to each generated clause -/
def unlessOneOf (ls : Array L) (e : EncCNF L α) : EncCNF L α :=
  ⟨ fun state =>
    let oldAssumes := state.assumeVars
    let newState := { state with
      assumeVars := oldAssumes.or ls
    }
    let (res, newState) := e.1 newState
    (res, {newState with
      assumeVars := oldAssumes
    }),
    by intro s; simp; split; next a s' hs' =>
      simp; have := hs' ▸ e.2 _; simpa using this⟩

def assuming [LawfulLitVar L ν] (ls : Array L) (e : EncCNF L α) : EncCNF L α :=
  unlessOneOf (ls.map (- ·)) e

def blockAssn [BEq ν] [Hashable ν] (a : HashAssn L) : EncCNF L Unit :=
  addClause (a.toLitArray.map (- ·))

def addAssn [BEq ν] [Hashable ν] (a : HashAssn L) : EncCNF L Unit := do
  for l in a.toLitArray do
    addClause #[l]


/-! ### Temporaries -/

def WithTemps (L n) := L ⊕ Fin n × Bool

instance : LitVar (WithTemps L n) (ν ⊕ Fin n) where
  negate | Sum.inl l => Sum.inl (LitVar.negate l)
         | Sum.inr (i,p) => Sum.inr (i,!p)
  mkPos | Sum.inl v => Sum.inl (LitVar.mkPos v)
        | Sum.inr v => Sum.inr (v,true)
  mkNeg | Sum.inl v => Sum.inl (LitVar.mkNeg v)
        | Sum.inr v => Sum.inr (v,false)
  toVar | Sum.inl l => Sum.inl (LitVar.toVar l)
        | Sum.inr (i,_) => Sum.inr i
  polarity | Sum.inl l => LitVar.polarity l
           | Sum.inr (_,p) => p

instance [LawfulLitVar L ν] : LawfulLitVar (WithTemps L n) (ν ⊕ Fin n) where
  toVar_negate := by intro l; cases l <;> simp [LitVar.toVar]
  toVar_mkPos := by intro v; cases v <;> simp [LitVar.toVar]
  toVar_mkNeg := by intro v; cases v <;> simp [LitVar.toVar]
  polarity_negate := by intro l; cases l <;> simp [LitVar.polarity]
  polarity_mkPos := by intro v; cases v <;> simp [LitVar.polarity]
  polarity_mkNeg := by intro v; cases v <;> simp [LitVar.polarity]
  ext := by
    intro l1 l2 h1 h2
    cases l1 <;> cases l2
      <;> simp [LitVar.toVar, LitVar.polarity] at h1 h2
      <;> congr
      <;> ext
    repeat simp only [*]

def State.withTemps (s : State L ν) : State (WithTemps L n) (ν ⊕ Fin n) where
  nextVar := ⟨s.nextVar + n, by simp⟩
  cnf := s.cnf
  vMap := vMap
  assumeVars := s.assumeVars.map _ (Sum.inl ·)
where vMap (x) :=
  match x with
  | Sum.inl v => s.vMap v
  | Sum.inr i => ⟨s.nextVar + i, by simp⟩

@[simp] theorem State.cnf_withTemps (s : State L ν) :
    (State.withTemps s (n := n)).cnf = s.cnf
  := by simp [State.withTemps]

def LawfulState.withTemps (s : LawfulState L ν)
  : LawfulState (WithTemps L n) (ν ⊕ Fin n) where
  toState := s.toState.withTemps
  cnfVarsLt := by
    simp [State.withTemps]
    intro c hc l hl
    apply Nat.lt_of_lt_of_le
    · exact s.cnfVarsLt c hc l hl
    · simp; apply Nat.le_add_right
  vMapLt := by
    simp [State.withTemps]
    constructor
    · intro v; apply Nat.lt_of_lt_of_le
      · apply s.vMapLt
      · simp; apply Nat.le_add_right
    · intro a; apply (PNat.mk_lt_mk ..).mpr; simp
  vMapInj := by
    intro v1 v2
    simp [State.withTemps]
    cases v1 <;> cases v2 <;> simp
    · apply s.vMapInj
    · intro h; simp [State.withTemps.vMap] at h; have := h ▸ s.vMapLt _; simp [← PNat.coe_lt_coe] at this
    · intro h; simp [State.withTemps.vMap] at h; have := h.symm ▸ s.vMapLt _; simp [← PNat.coe_lt_coe] at this
    · simp [State.withTemps.vMap]; rw [Subtype.mk_eq_mk]
      intro h
      apply Fin.eq_of_veq; apply Nat.add_left_cancel h

@[simp] theorem LawfulState.interp_withTemps [DecidableEq ν] (s : LawfulState L ν) (n)
  : (s.withTemps (n := n)).interp = s.interp.map Sum.inl := by
  simp [interp, withTemps, State.withTemps]
  generalize hφ : s.cnf.toPropFun = φ
  ext τ
  simp [PropFun.existQuantInv]
  rw [PropFun.satisfies_invImage, PropFun.satisfies_invImage]
  convert PropFun.agreeOn_semVars _ using 3
  · ext i; simp [State.withTemps.vMap, not_or]
    intro hi _h t
    replace hi := semVars_toPropFun_cnf_lt _ _ (hφ.symm ▸ hi)
    apply ne_of_gt
    apply Nat.lt_of_lt_of_le; apply hi
    simp [← PNat.coe_le_coe]; exact Nat.le_add_right ↑s.nextVar ↑t
  · infer_instance
  · intro v hv
    simp at hv; replace hv := PropFun.semVars_existQuantSet _ _ hv
    simp at hv
    rcases hv with ⟨hv,h⟩
    have := semVars_toPropFun_cnf_lt _ _ (hφ.symm ▸ hv)
    rcases h with (⟨v,rfl⟩|⟨t,rfl⟩)
    · simp [State.withTemps.vMap]; congr
      simp [State.withTemps.vMap]; congr
      simp
    · exfalso; simp [State.withTemps.vMap, ←PNat.coe_lt_coe] at this


def State.withoutTemps (vMap : ν → IVar) (assumeVars : Array L) (s : State (WithTemps L n) (ν ⊕ Fin n)) : State L ν where
  nextVar := s.nextVar
  cnf := s.cnf
  vMap := vMap
  assumeVars := assumeVars

@[simp] theorem State.vMap_withoutTemps (s : State _ _) :
    (State.withoutTemps (L := L) (ν := ν) (n := n) vm av s).vMap = vm
  := by simp [State.withoutTemps]

@[simp] theorem State.assumeVars_withoutTemps (s : State _ _) :
    (State.withoutTemps (L := L) (ν := ν) (n := n) vm av s).assumeVars = av
  := by simp [State.withoutTemps]

def LawfulState.withoutTemps (s : LawfulState (WithTemps L n) (ν ⊕ Fin n))
    (vMap : ν → IVar) (vMapLt : ∀ v, vMap v < s.nextVar) (vMapInj : vMap.Injective)
    (assumeVars : Array L)
    : LawfulState L ν where
  toState := s.toState.withoutTemps vMap assumeVars
  cnfVarsLt := by
    simp [State.withoutTemps]
    intro c hc l hl
    apply Nat.lt_of_lt_of_le
    · exact s.cnfVarsLt c hc l hl
    · simp
  vMapLt := by
    simp [State.withoutTemps]
    apply vMapLt
  vMapInj := by
    intro v1 v2
    simp [State.withoutTemps]
    apply vMapInj

@[simp] theorem LawfulState.vMap_withoutTemps (s : LawfulState (WithTemps L n) (ν ⊕ Fin n))
    {vMap : ν → IVar} {vMapLt : ∀ v, vMap v < s.nextVar} {vMapInj : vMap.Injective}
    : (LawfulState.withoutTemps s vMap vMapLt vMapInj av).vMap = vMap
  := by simp [LawfulState.withoutTemps]

@[simp] theorem LawfulState.assumeVars_withoutTemps (s : LawfulState (WithTemps L n) (ν ⊕ Fin n))
    {vMap : ν → IVar} {vMapLt : ∀ v, vMap v < s.nextVar} {vMapInj : vMap.Injective}
    : (LawfulState.withoutTemps s vMap vMapLt vMapInj av).assumeVars = av
  := by simp [LawfulState.withoutTemps]

theorem LawfulState.interp_withoutTemps [DecidableEq ν]
    (s : LawfulState (WithTemps L n) (ν ⊕ Fin n))
    {vMap : ν → IVar} {vMapLt : ∀ v, vMap v < s.nextVar} {vMapInj : vMap.Injective}
    (h : vMap = s.vMap ∘ Sum.inl)
    : LawfulState.interp (LawfulState.withoutTemps s vMap vMapLt vMapInj av) =
      @PropFun.existQuantInv _ _ _ ⟨Sum.inl, Sum.inl_injective⟩
        ((LawfulState.withoutTemps s vMap vMapLt vMapInj av).fintype) s.interp
  := by
  cases h
  simp [LawfulState.withoutTemps, State.withoutTemps, interp]
  sorry

def nextVar_mono_of_eq {e : EncCNF L α} (h : e.1 s = (a, s')) :
    s.nextVar ≤ s'.nextVar := by
  have := h ▸ e.2 s
  exact this

def withTemps (n) (e : EncCNF (WithTemps L n) α) : EncCNF L α :=
  ⟨ fun s =>
    let vMap := s.vMap
    let vMapInj := s.vMapInj
    let assumeVars := s.assumeVars
    match h : e.1 s.withTemps with
    | (a,s') =>
    (a, s'.withoutTemps vMap (by
        intro v; simp; apply Nat.lt_of_lt_of_le (m := s.nextVar)
        · apply s.vMapLt
        · have := e.nextVar_mono_of_eq h
          apply Nat.le_trans (m := s.nextVar + n)
          · simp
          · exact (PNat.coe_le_coe ..).mp this
      ) vMapInj assumeVars)
  , by simp [LawfulState.withoutTemps, State.withoutTemps]
       intro s; split; simp; have := e.nextVar_mono_of_eq ‹_›
       simp [LawfulState.withTemps, State.withTemps] at this
       apply Nat.le_trans (m := s.nextVar + n)
       · apply Nat.le_add_right
       · exact (PNat.coe_le_coe ..).mp this⟩
