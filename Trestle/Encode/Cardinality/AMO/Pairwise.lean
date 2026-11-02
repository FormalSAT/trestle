/-
Copyright (c) 2026 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio, Cayden Codel
-/

import Trestle.Encode.Cardinality.AMO.Defs
import Trestle.Data.Cnf.Consistent

namespace Trestle.Encode.Cardinality

open VEncCNF Model PropFun

def amoPairwise (lits : Array (Literal ν)) :
  VEncCNF ν Unit (atMostOne (Multiset.ofList lits.toList)) := (
    for_pairwise lits fun i j => imply i (-j)
  ).mapProp (by ext τ; rw [amo_iff_Pairwise]; simp)

/--
  The pairwise at-most-one encoding.

  An O(n²) encoding comprising binary clauses of every pair of literals.
  Formally,

    ∀ x,y ∈ lits, x ≠ y → (¬x ∨ ¬y)

  The only way to satisfy the encoding is to never have any pair of literals
  both set to false in the assignment. Thus, at most one literal is true.
-/
def amoPairwise₂ (lits : Array (Literal ν)) :
    VEncCNF ν Unit (atMostOne (Multiset.ofList lits.toList)) := (
  -- for every pair i < j of indices into `lits`, they can't both be true
  for_univ fun (i : Fin lits.size) =>
    for_univ fun (j : Fin lits.size) =>
      guard (i < j) fun _ =>
        addClause #[-lits[i], -lits[j]]
  ).mapProp (by
    ext τ; rw [amo_iff]
    simp [Fin.forall_iff]
    constructor
    · intro h i i_range j j_range i_sat j_sat
      wlog le : i ≤ j generalizing i j
      · rw [eq_comm]; apply this j j_range i i_range j_sat i_sat (by omega)
      if i = j then assumption else
      have := h i i_range j j_range (by omega)
      simp [i_sat, j_sat] at this
    · intro h i i_range j j_range lt
      have := h i i_range j j_range
      simp only [show ¬ i = j by omega, imp_false] at this
      by_cases hi : τ ⊨ LitVar.toPropFun lits[i] <;> simp_all
  )

instance pairwiseAMOEncoding : AMOEncoding ν where
  encoding := amoPairwise

instance pairwise₂AMOEncoding : AMOEncoding ν where
  encoding := amoPairwise₂

/-! ### Consistency and arc-consistency

The pairwise encoding is arc-consistent (when the literals are over distinct variables):
as soon as one literal is set true, unit propagation sets every other literal false,
and as soon as two literals are set true, unit propagation derives a conflict.
-/

section ArcConsistency

open Cnf
open scoped _root_.List

/--
  The clauses of the pairwise AMO encoding: `¬a ∨ ¬b` for every pair of literals
  `a = lits[i]`, `b = lits[j]` with `i < j`.

  These are exactly the clauses that `amoPairwise lits` adds (see `amoPairwise_cnf`).
-/
def amoPairwiseCnf (lits : Array (Literal ν)) : Cnf (Literal ν) :=
  (lits.toList.pairs.map fun p => #[-p.1, -p.2]).toArray

theorem mem_amoPairwiseCnf {lits : Array (Literal ν)} {C : Clause (Literal ν)} :
    C ∈ amoPairwiseCnf lits ↔ ∃ a b, [a, b] <+ lits.toList ∧ C = #[-a, -b] := by
  simp [amoPairwiseCnf, List.mem_pairs_iff, eq_comm]

/-- Two distinct members of a list appear in it as a pair, in some order. -/
private theorem sublist_pair_of_ne {L : List α} {a b : α} (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b) :
    [a, b] <+ L ∨ [b, a] <+ L := by
  induction L with
  | nil => simp at ha
  | cons x L ih =>
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact absurd rfl hab
    · exact .inl (List.cons_sublist_cons.mpr (List.singleton_sublist.mpr hb))
    · exact .inr (List.cons_sublist_cons.mpr (List.singleton_sublist.mpr ha))
    · rcases ih ha hb with h | h
      · exact .inl (h.cons x)
      · exact .inr (h.cons x)

private theorem mem_of_sublist_left {lits : Array (Literal ν)} {a b : Literal ν}
    (h : [a, b] <+ lits.toList) : a ∈ lits := by
  simpa using h.subset (by simp : a ∈ [a, b])

private theorem mem_of_sublist_right {lits : Array (Literal ν)} {a b : Literal ν}
    (h : [a, b] <+ lits.toList) : b ∈ lits := by
  simpa using h.subset (by simp : b ∈ [a, b])

/-- Two literals at positions `i < j` cannot both be true under an AMO model. -/
private theorem not_amo_of_sublist {lits : Array (Literal ν)} {τ : PropAssignment ν}
    {a b : Literal ν} (hab : [a, b] <+ lits.toList)
    (ha : τ ⊨ LitVar.toPropFun a) (hb : τ ⊨ LitVar.toPropFun b) :
    ¬ atMostOne (Multiset.ofList lits.toList) τ := by
  rw [amo_iff_Pairwise]
  simp only [LitVar.mk_toPropForm]
  intro h
  exact List.pairwise_iff_forall_sublist.mp h hab ha hb

/-- An AMO model is one in which no two literals at positions `i < j` are both true. -/
private theorem amo_of_sublist {lits : Array (Literal ν)} {τ : PropAssignment ν}
    (h : ∀ a b, [a, b] <+ lits.toList → τ ⊨ LitVar.toPropFun a → τ ⊭ LitVar.toPropFun b) :
    atMostOne (Multiset.ofList lits.toList) τ := by
  rw [amo_iff_Pairwise]
  simp only [LitVar.mk_toPropForm]
  exact List.pairwise_iff_forall_sublist.mpr (h _ _)

private theorem amo_congr {lits : Array (Literal ν)} {τ σ : PropAssignment ν}
    (h : ∀ a ∈ lits, (τ ⊨ LitVar.toPropFun a ↔ σ ⊨ LitVar.toPropFun a)) :
    atMostOne (Multiset.ofList lits.toList) τ ↔ atMostOne (Multiset.ofList lits.toList) σ := by
  rw [amo_iff_Pairwise, amo_iff_Pairwise]
  simp only [LitVar.mk_toPropForm]
  constructor
  · intro hp
    exact List.Pairwise.imp_of_mem (fun ha hb hab hσa => by
      rw [← h _ (by simpa using hb)]
      exact hab ((h _ (by simpa using ha)).mpr hσa)) hp
  · intro hp
    exact List.Pairwise.imp_of_mem (fun ha hb hab hτa => by
      rw [h _ (by simpa using hb)]
      exact hab ((h _ (by simpa using ha)).mp hτa)) hp

/-- Two literals at positions `i < j` that are both true under `ρ` give a conflict. -/
private theorem unitConflict_of_sublist {lits : Array (Literal ν)} {ρ : PartialAssignment ν}
    {a b : Literal ν} (hab : [a, b] <+ lits.toList) (ha : ρ.SatLit a) (hb : ρ.SatLit b) :
    (amoPairwiseCnf lits).UnitConflict ρ := by
  refine ⟨#[-a, -b], mem_amoPairwiseCnf.mpr ⟨a, b, hab, rfl⟩, ?_⟩
  intro l hl
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl <;> rw [LitVar.neg_neg] <;> exact .assn ‹_›

/-- If `a` is true under `ρ`, then unit propagation derives `¬b` for every other literal `b`. -/
private theorem unitDerives_neg {lits : Array (Literal ν)} {ρ : PartialAssignment ν}
    {a b : Literal ν} (ha : a ∈ lits) (hb : b ∈ lits) (hab : a ≠ b) (haρ : ρ.SatLit a) :
    (amoPairwiseCnf lits).UnitDerives ρ (-b) := by
  have hderiv : ∀ C : Clause (Literal ν), C ∈ amoPairwiseCnf lits → -b ∈ C →
      (∀ l ∈ C, l = -a ∨ l = -b) → (amoPairwiseCnf lits).UnitDerives ρ (-b) := by
    intro C hC hbC hC'
    refine .unit hC hbC ?_
    intro l hl hne
    rcases hC' l hl with rfl | rfl
    · rw [LitVar.neg_neg]; exact .assn haρ
    · exact absurd rfl hne
  rcases sublist_pair_of_ne (L := lits.toList) (by simpa using ha) (by simpa using hb) hab with h | h
  · exact hderiv _ (mem_amoPairwiseCnf.mpr ⟨a, b, h, rfl⟩) (by simp) (by simp)
  · exact hderiv _ (mem_amoPairwiseCnf.mpr ⟨b, a, h, rfl⟩) (by simp) (by simp)

open Classical in
/-- Extends `ρ` by setting every unassigned literal of `lits` to false. -/
private noncomputable def falsify (lits : Array (Literal ν)) (ρ : PartialAssignment ν) :
    PropAssignment ν :=
  fun v => (ρ v).getD
    (if h : ∃ a ∈ lits, LitVar.toVar a = v then !LitVar.polarity h.choose else false)

private theorem falsify_extends {lits : Array (Literal ν)} {ρ : PartialAssignment ν} :
    (falsify lits ρ).Extends ρ := by
  intro v b h; simp [falsify, h]

/-- If `lits` contains no complementary literals, then the only literals of `lits`
    that are true under `falsify lits ρ` are those that are true under `ρ`. -/
private theorem satLit_of_falsify {lits : Array (Literal ν)} {ρ : PartialAssignment ν}
    (hneg : ∀ l ∈ lits, -l ∉ lits) {a : Literal ν} (ha : a ∈ lits)
    (h : falsify lits ρ ⊨ LitVar.toPropFun a) : ρ.SatLit a := by
  rw [LitVar.satisfies_iff] at h
  unfold falsify at h
  cases hρ : ρ (LitVar.toVar a) with
  | some b =>
    simp only [hρ, Option.getD_some] at h
    simp [PartialAssignment.SatLit, hρ, h]
  | none =>
    exfalso
    simp only [hρ, Option.getD_none] at h
    have hex : ∃ a' ∈ lits, LitVar.toVar a' = LitVar.toVar a := ⟨a, ha, rfl⟩
    rw [dif_pos hex] at h
    obtain ⟨ha', hvar⟩ := hex.choose_spec
    rcases LitVar.toVar_eq_iff.mp hvar with heq | heq
    · rw [heq] at h; simp at h
    · exact hneg a ha (heq ▸ ha')

/--
  The pairwise AMO encoding is consistent: whenever a partial assignment `ρ` cannot be
  extended to a model of `atMostOne lits`, unit propagation derives a conflict.

  The literals of `lits` may repeat, but must not contain complementary pairs.
  (For example, the encoding of `atMostOne [x, ¬x, y, ¬y]`, which is unsatisfiable,
  does not derive a conflict under the empty assignment.)
-/
theorem amoPairwiseCnf_consistent {lits : Array (Literal ν)} (hneg : ∀ l ∈ lits, -l ∉ lits) :
    (amoPairwiseCnf lits).Consistent (atMostOne (Multiset.ofList lits.toList)) Set.univ := by
  intro ρ _ hP
  by_contra hconf
  apply hP
  refine ⟨falsify lits ρ, falsify_extends, amo_of_sublist ?_⟩
  intro a b hab ha hb
  exact hconf (unitConflict_of_sublist hab
    (satLit_of_falsify hneg (mem_of_sublist_left hab) ha)
    (satLit_of_falsify hneg (mem_of_sublist_right hab) hb))

/--
  The pairwise AMO encoding is arc-consistent for literals over distinct variables:
  it is consistent, and for every partial assignment `ρ` that can be extended
  to a model of `atMostOne lits`, unit propagation derives every literal that
  `atMostOne lits` and `ρ` entail.
-/
theorem amoPairwiseCnf_arcConsistent {lits : Array (Literal ν)}
    (hvars : (lits.toList.map LitVar.toVar).Nodup) :
    (amoPairwiseCnf lits).ArcConsistent (atMostOne (Multiset.ofList lits.toList)) Set.univ := by
  classical
  have hinj : ∀ a ∈ lits, ∀ b ∈ lits, LitVar.toVar a = LitVar.toVar b → a = b :=
    fun a ha b hb h => List.inj_on_of_nodup_map hvars (by simpa using ha) (by simpa using hb) h
  have hneg : ∀ l ∈ lits, -l ∉ lits :=
    fun l hl hl' => LitVar.neg_ne_self l (hinj _ hl' _ hl (by simp))
  refine ⟨amoPairwiseCnf_consistent hneg, ?_⟩
  intro ρ _ hP l _ hent
  cases hx : ρ (LitVar.toVar l) with
  | some b => exact .assn (hent.satLit_of_assigned hP hx)
  | none =>
  by_cases hb : ∃ b ∈ lits, LitVar.toVar b = LitVar.toVar l
  · obtain ⟨b, hb, hbl⟩ := hb
    have hb_free : ρ (LitVar.toVar b) = none := hbl ▸ hx
    by_cases ha : ∃ a ∈ lits, ρ.SatLit a
    · -- Some literal `a` is true, so every other literal is propagated false
      obtain ⟨a, ha, haρ⟩ := ha
      have hab : a ≠ b := by
        rintro rfl; simp [PartialAssignment.SatLit, hb_free] at haρ
      rcases LitVar.toVar_eq_iff.mp hbl with heq | heq
      · -- `l = b` contradicts that `a` is true in a model
        exfalso
        subst heq
        obtain ⟨τ, hτ, hPτ⟩ := hP
        rcases sublist_pair_of_ne (L := lits.toList) (by simpa using ha) (by simpa using hb) hab with h | h
        · exact not_amo_of_sublist h (hτ.satisfies haρ) (hent τ hτ hPτ) hPτ
        · exact not_amo_of_sublist h (hent τ hτ hPτ) (hτ.satisfies haρ) hPτ
      · have := unitDerives_neg ha hb hab haρ
        rwa [heq, LitVar.neg_neg] at this
    · -- No literal is true, so `b` is unconstrained
      exfalso
      push Not at ha
      have hfalse : ∀ a ∈ lits, falsify lits ρ ⊭ LitVar.toPropFun a :=
        fun a ha' h => ha a ha' (satLit_of_falsify hneg ha' h)
      rcases LitVar.toVar_eq_iff.mp hbl with heq | heq
      · -- `l = b`, but there is a model with every literal false
        have hamo : atMostOne (Multiset.ofList lits.toList) (falsify lits ρ) :=
          amo_of_sublist fun a _ hab h => absurd h (hfalse a (mem_of_sublist_left hab))
        exact hfalse b hb (heq ▸ hent _ falsify_extends hamo)
      · -- `l = ¬b`, but there is a model with only `b` true
        obtain ⟨τ, hτdef⟩ : ∃ τ, τ = (falsify lits ρ).set (LitVar.toVar b) (LitVar.polarity b) :=
          ⟨_, rfl⟩
        have hτb : τ ⊨ LitVar.toPropFun b := hτdef ▸ LitVar.satisfies_set _ _
        have hτ : ∀ a ∈ lits, τ ⊨ LitVar.toPropFun a → a = b := by
          intro a ha' h
          by_cases hv : LitVar.toVar a = LitVar.toVar b
          · exact hinj a ha' b hb hv
          · rw [LitVar.satisfies_iff, hτdef, PropAssignment.get_set_of_ne (Ne.symm hv)] at h
            exact absurd (LitVar.satisfies_iff.mpr h) (hfalse a ha')
        have hamo : atMostOne (Multiset.ofList lits.toList) τ := by
          refine amo_of_sublist fun a a' hab h h' => ?_
          obtain rfl := hτ a (mem_of_sublist_left hab) h
          obtain rfl := hτ a' (mem_of_sublist_right hab) h'
          have := (List.Nodup.of_map _ hvars).sublist hab
          simp at this
        have := hent τ (hτdef ▸ falsify_extends.set hb_free _) hamo
        rw [show l = -b by rw [heq, LitVar.neg_neg], LitVar.satisfies_neg] at this
        exact this hτb
  · -- The variable of `l` does not occur in `lits`, so it is unconstrained
    exfalso
    push Not at hb
    refine PartialAssignment.not_entails_of_flip hP hx (fun τ hτ => ?_) hent
    refine (amo_congr fun a ha => ?_).mp hτ
    rw [LitVar.satisfies_iff, LitVar.satisfies_iff,
      PropAssignment.get_set_of_ne (Ne.symm (hb a ha))]

/-! #### The clauses produced by the encoder -/

/-- Adding one clause per element of `ps` appends those clauses (with the variables mapped
    by the encoder's variable map), and leaves the variable map unchanged. -/
private theorem foldl_addClause {α : Type} (g : α → Clause (Literal ν)) (ps : List α)
    (s : EncCNF.LawfulState ν) :
    (ps.foldl (fun s p => ((EncCNF.addClause (g p) : EncCNF ν Unit).1 s).2) s).cnf.toCnf
        = s.cnf.toCnf ++ (ps.map fun p => Clause.map s.vMap (g p)).toArray
    ∧ (ps.foldl (fun s p => ((EncCNF.addClause (g p) : EncCNF ν Unit).1 s).2) s).vMap
        = s.vMap := by
  induction ps generalizing s with
  | nil => simp
  | cons p ps ih =>
    obtain ⟨ih₁, ih₂⟩ := ih (s.addClause (g p))
    have hv : (s.addClause (g p)).vMap = s.vMap := by
      simp [EncCNF.LawfulState.addClause, EncCNF.State.addClause]
    have hc : (s.addClause (g p)).cnf.toCnf = s.cnf.toCnf.push (Clause.map s.vMap (g p)) := by
      simp [EncCNF.LawfulState.addClause, EncCNF.State.addClause, dbgTraceIfShared, Cnf.addClause]
    rw [List.foldl_cons]
    refine ⟨?_, ?_⟩
    · show (List.foldl _ (s.addClause (g p)) ps).cnf.toCnf = _
      rw [ih₁, hc, hv]
      simp
    · show (List.foldl _ (s.addClause (g p)) ps).vMap = _
      rw [ih₂, hv]

/-- Running `amoPairwise lits` adds exactly the clauses of `amoPairwiseCnf lits`,
    with the variables mapped by the encoder's variable map. -/
theorem amoPairwise_cnf (lits : Array (Literal ν)) (s : EncCNF.LawfulState ν) :
    ((amoPairwise lits).1.1 s).2.cnf.toCnf
      = s.cnf.toCnf ++ (amoPairwiseCnf lits).mapVars s.vMap := by
  show (EncCNF.forInImpl lits.pairs
      (fun p => EncCNF.addClause (#[p.1].map LitVar.negate ++ #[-p.2])) s).cnf.toCnf = _
  rw [EncCNF.forIn_state_eq_foldl, (foldl_addClause _ _ s).1]
  simp [amoPairwiseCnf, Cnf.mapVars, Function.comp_def]

/-- The pairwise AMO encoding, as emitted by the encoder from any state `s`,
    is consistent for `atMostOne lits` over the encoder's variables for `lits`. -/
theorem amoPairwise_consistent {lits : Array (Literal ν)} (hneg : ∀ l ∈ lits, -l ∉ lits)
    (s : EncCNF.LawfulState ν) :
    ((amoPairwise lits).1.1 s).2.cnf.toCnf.Consistent
      (fun σ => atMostOne (Multiset.ofList lits.toList) (σ.map s.vMap)) (Set.range s.vMap) := by
  rw [amoPairwise_cnf, ← Set.image_univ]
  exact ((amoPairwiseCnf_consistent hneg).mapVars s.vMapInj).of_subset
    fun _ hC => Array.mem_append_right _ hC

/-- The pairwise AMO encoding, as emitted by the encoder from any state `s`,
    is arc-consistent for `atMostOne lits` over the encoder's variables for `lits`
    (when `lits` are over distinct variables).

    In particular, under any partial assignment to the variables of `lits` that violates
    `atMostOne lits`, unit propagation on the entire emitted formula derives a conflict
    (see `Cnf.ArcConsistent.unitConflict`). -/
theorem amoPairwise_arcConsistent {lits : Array (Literal ν)}
    (hvars : (lits.toList.map LitVar.toVar).Nodup) (s : EncCNF.LawfulState ν) :
    ((amoPairwise lits).1.1 s).2.cnf.toCnf.ArcConsistent
      (fun σ => atMostOne (Multiset.ofList lits.toList) (σ.map s.vMap)) (Set.range s.vMap) := by
  rw [amoPairwise_cnf, ← Set.image_univ]
  exact ((amoPairwiseCnf_arcConsistent hvars).mapVars s.vMapInj).append_left _

end ArcConsistency

end Trestle.Encode.Cardinality /- namespace -/
