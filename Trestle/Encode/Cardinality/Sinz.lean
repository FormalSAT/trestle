/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Trestle.Encode.Cardinality.Defs
import Trestle.Encode.Tseitin
import Trestle.Solver.Dimacs

namespace Trestle.Encode.Cardinality

/-

# Sinz Cardinality Encoding

-/

open VEncCNF Model PropFun

theorem List.countP_eq_countP_range (P : α → Bool) (L : List α) :
  List.countP P L = List.countP (P L[·]) (List.finRange L.length) := by
  rw [eq_comm]
  calc  List.countP (P L[·]) (List.finRange L.length)
    _ = List.countP P (List.map (L[·]) (List.finRange L.length)) := by rw [List.countP_map]; rfl
    _ = List.countP P (List.ofFn (L[·])) := by rw [List.ofFn_eq_map]
    _ = List.countP P L := by simp

theorem List.countP_eq_one_of_nodup (P : α → Bool) (L : List α) (nodup : L.Nodup) :
    List.countP P L = 1 ↔ ∃! l ∈ L, P l := by
  induction L
  case nil => simp
  case cons x tl ih =>
  specialize ih nodup.tail
  if P x then
    simp [ExistsUnique, *]
    have : ∀ a ∈ tl, a ≠ x := by intro; rw [ne_comm]; simpa using nodup.rel_head_tail
    simp +contextual [this]
  else
    have : ∀ l, ¬ (l = x ∧ P l = true) := by simp [*]
    simp [*, or_and_right]

open List in
theorem exactly_one_iff_unique_idx (lits : Array (Literal ν)) (τ) :
  (exactly 1 (Multiset.ofList lits.toList)) τ ↔
    ∃! i, ∃ _:i < lits.size, τ ⊨ LitVar.toPropFun lits[i] := by
  --have := Classical.decEq ν
  rcases lits with ⟨lits⟩
  simp [card]
  rw [List.countP_eq_countP_range,
      List.countP_eq_one_of_nodup]
  case nodup => apply List.nodup_finRange
  simp; unfold ExistsUnique; simp [Fin.exists_iff, Fin.forall_iff]


/-! ###  Sinz sequential counter exactly one. -/
def sinzExactlyOne.spec (lits : Array (Literal ν)) (pos : lits.size > 0)
      : PropPred (ν ⊕ Fin lits.size) := fun τ =>
  let lit (i : Nat) (hi : i < lits.size := by omega) : Bool :=
    τ ⊨ LitVar.toPropFun (LitVar.map (L' := Literal ν ⊕ Literal (Fin lits.size)) Sum.inl lits[i])
  let tmp (i : Nat) (hi : i < lits.size := by omega) : Bool := τ (.inr ⟨i,hi⟩)
  -- tmp i true iff there is exactly 1 true literal among lits[j] for j ≤ i
  (∀ (i) (_: i+1 < lits.size), tmp i → tmp (i+1)) ∧
  (lit 0 ↔ tmp 0) ∧
  (∀ (i) (_: i+1 < lits.size), lit (i+1) ↔ (¬tmp i ∧ tmp (i+1))) ∧
  (tmp (lits.size-1))

theorem sinzExactlyOne.correct (lits : Array (Literal ν)) (pos : lits.size > 0) :
    ∀ τ : PropAssignment ν, (∃ σ, τ = σ.map Sum.inl ∧ spec lits pos σ) ↔ exactly 1 (Multiset.ofList lits.toList) τ := by
  intro τ
  rw [exactly_one_iff_unique_idx]
  constructor
  · rintro ⟨σ, τdef, ⟨mono,hd_def,tl_def,last⟩⟩
    -- the temps are monotonically increasing
    replace mono : ∀ {i₁ i₂} (_ : i₁ ≤ i₂ ∧ i₂ < lits.size),
        σ (.inr ⟨i₁,by omega⟩) ≤ σ (.inr ⟨i₂,by omega⟩) := by
      rintro i₁ i₂ ⟨le,lt⟩
      induction i₂ using Nat.strong_induction_on
      next i₂ ih =>
      if is_ne : i₁ = i₂ then subst i₂; simp else
      trans σ (Sum.inr ⟨i₂-1,by omega⟩)
      · apply ih <;> omega
      · have := mono (i₂-1) (by omega)
        simp [show i₂-1+1 = i₂ by omega] at this
        exact this

    -- if one index satisfies, it is unique
    by_cases ∃ i, ∃ _: i < lits.size, τ ⊨ LitVar.toPropFun lits[i]
    case pos h =>
      rcases h with ⟨i₁,i₁_range,i₁_sat⟩
      use i₁, ⟨i₁_range,i₁_sat⟩
      rintro i₂ ⟨i₂_range,i₂_sat⟩
      wlog is_le : i₁ ≤ i₂ generalizing i₁ i₂
      · rw [eq_comm]; apply this <;> first | assumption | omega
      by_contra is_ne
      have is_lt : i₁ < i₂ := by omega
      clear is_ne is_le
      -- now we start making claims about σ
      subst τ
      have tmp1 : σ (.inr ⟨i₁,by omega⟩) = true := by
        if eq_z : i₁ = 0 then
          simp [eq_z] at i₁_sat ⊢
          simpa [← hd_def] using i₁_sat
        else
          have : i₁-1+1 = i₁ := by omega
          specialize tl_def (i₁-1) (by omega)
          simp [this, i₁_sat] at tl_def
          exact tl_def.2
      have i2_pred : i₂-1+1 = i₂ := by omega
      specialize @mono i₁ (i₂-1) (by omega)
      have tmp2 : σ (.inr ⟨i₂-1,by omega⟩) = false := by
        have := tl_def (i₂-1) (by omega) |>.mp (by simp [i2_pred, i₂_sat]) |>.1
        simpa using this
      -- contradiction!
      simp [tmp1, tmp2, Bool.le_iff_imp] at mono
    -- if no indices satisfy, contradiction
    case neg h =>
      subst τ
      push_neg at h
      exfalso
      suffices ∀ (i) (_: i < lits.size), σ (.inr ⟨i,by omega⟩) = false by
        specialize this (lits.size-1) (by omega)
        simp [this] at last
      intro i i_lt
      induction i
      case zero =>
        simpa [h] using hd_def
      case succ i ih =>
        specialize ih (by omega)
        specialize tl_def i (by omega)
        simpa [h, ih] using tl_def
  · rintro ⟨i,⟨i_range,i_sat⟩,i_uniq⟩
    let σ : PropAssignment (ν ⊕ Fin lits.size) :=
      fun | Sum.inl v => τ v | .inr t => t ≥ i
    have τeq : σ ∘ Sum.inl = τ := by ext; simp [σ]
    refine ⟨σ,τeq.symm,⟨?mono,?hd_def,?tl_def,?last⟩⟩
    case mono => simp [σ]; intros; omega
    case hd_def =>
      simp [τeq, σ]
      if iz : i = 0 then
        simpa [iz] using i_sat
      else
        specialize i_uniq 0; simp [Ne.symm iz] at i_uniq
        specialize i_uniq (by omega)
        simp [iz, i_uniq]
    case tl_def =>
      intro i' i'_range
      simp [τeq, σ]
      if eq: i' + 1 = i then
        simp [eq, i_sat]; omega
      else
        rw [← Nat.succ_le_iff, ← Nat.eq_iff_le_and_ge]
        simp [eq]
        intro; apply eq; apply i_uniq
        simp [*]
    case last =>
      simp [σ]; omega

open Encode in
def sinzExactlyOne [DecidableEq ν] (lits : Array (Literal ν))
    : VEncCNF ν Unit (exactly 1 (Multiset.ofList lits.toList)) :=
  if h : lits.size > 0 then
    VEncCNF.withTemps (Fin lits.size) (body h)
    |>.mapProp (by ext τ; apply sinzExactlyOne.correct)
  else
    (VEncCNF.addClause #[]).mapProp (by
      have : lits = #[] := by
        apply Array.eq_empty_of_size_eq_zero; omega
      subst lits; ext τ; simp [card])
where
  body (h) : VEncCNF _ Unit (sinzExactlyOne.spec lits h) :=
    let lit (i) (h : i < lits.size := by omega) : Literal (ν ⊕ Fin lits.size) :=
      LitVar.map Sum.inl lits[i]
    let tmp (i) (h : i < lits.size := by omega) : Literal (ν ⊕ Fin lits.size) :=
      Literal.pos <| Sum.inr ⟨i,h⟩
    seq[
        VEncCNF.for_all (Array.finRange lits.size) (fun i =>
          VEncCNF.guard (i+1 < lits.size) fun h =>
            tseitin[ {tmp i} → {tmp (i+1)}])
      , tseitin[ {lit 0} ↔ {tmp 0} ]
      , VEncCNF.for_all (Array.finRange lits.size) (fun i =>
          VEncCNF.guard (i+1 < lits.size) fun h =>
            seq[
              tseitin[ {lit (i+1)} → ¬{tmp i} ],
              tseitin[ {lit (i+1)} → {tmp (i+1)} ],
              tseitin[ (¬{tmp i} ∧ {tmp (i+1)}) → {lit (i+1)}]
            ])
      , VEncCNF.addClause #[ tmp (lits.size-1) ]
    ] |>.mapProp (by
      ext τ
      unfold sinzExactlyOne.spec
      congrm ?_ ∧ ?_ ∧ ?_ ∧ ?_
      · simp [Array.mem_def, Fin.forall_iff, tmp]; aesop
      · simp [lit, tmp, ← PropFun.satisfies_mk]
        rw [PropFun.satisfies_conj, PropFun.satisfies_impl, PropFun.satisfies_impl]
        simp [← iff_iff_implies_and_implies]
      · simp [Array.mem_def, Fin.forall_iff, tmp, lit, ← PropFun.satisfies_mk]
        apply forall_congr'; intro i
        rw [forall_swap]; apply forall_congr'; intro hi
        have : i < lits.size := by omega
        conv =>
          lhs; rhs
          rw [PropFun.satisfies_impl, PropFun.satisfies_impl, PropFun.satisfies_impl,
              PropFun.satisfies_conj, PropFun.satisfies_neg]
          simp
        aesop
      · simp [tmp]
    )


/--
info: p cnf 13 11
-11 12 0
-12 13 0
-1 11 0
-11 1 0
-2 -11 0
-2 12 0
11 -12 2 0
-3 -12 0
-3 13 0
12 -13 3 0
13 0
-/
#guard_msgs in
#eval! (show VEncCNF (Fin 10) Unit _ from
          sinzExactlyOne #[Literal.pos 0, Literal.pos 1, Literal.pos 2]
        ).1.run.2.cnf |> Solver.Dimacs.printRichCnf (IO.print)
