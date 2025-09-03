/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.Encoding.CNF
import Experiments.Keller.Euclidean.GraphReduction
import Experiments.Keller.G8_Clique

import Experiments.Solver.Builtin

namespace Keller

theorem conjectureIn_of_cnf_unsat {n : Nat} (hn : n ≥ 2) (h : Euclidean.conjectureIn n) :
  ¬(Encoding.CNF.fullEncoding (n+1) (2^n)).val.toICnf.Sat → Euclidean.conjectureIn (n+1) := by
  intro unsat
  match n with
  | n+2 =>
  rw [Euclidean.euclideanConjecture_iff_graphConjecture] at h ⊢
  constructor; intro ex

  generalize hs : 2^(n+2) = s at ex
  let s' := s-2; have : s = s' + 2 := by subst s; rw [Nat.sub_add_cancel]; apply Nat.le_pow; simp

  have ⟨tc⟩ :=
    SymmBreak.C3Zeros.ofClique (n := n+1) (s := s')
      (by rw [← this]; exact ⟨(·.normS.elim h.elim)⟩)
      (by rw [← this]; exact ex)
  have sat := Encoding.Spec.cliqueToAssn_satisfies_fullSpec tc
  generalize Encoding.Spec.cliqueToAssn _ = assn at sat
  generalize s' + 2 = s_ at assn sat this; subst s_ s
  clear * - sat unsat

  apply unsat; clear unsat
  unfold Trestle.Cnf.Sat Trestle.Model.PropFun.Sat
  rw [Trestle.Encode.VEncCNF.toICnf_equisatisfiable]
  exact ⟨assn, sat⟩

/-! ## Positive Results -/

theorem conjectureIn_2 : Euclidean.conjectureIn 2 := by
  rw [Euclidean.euclideanConjecture_iff_graphConjecture]

  suffices ¬Trestle.Cnf.Sat (Encoding.CNF.baseEncoding 2 2).val.toICnf by
    unfold Trestle.Cnf.Sat Trestle.Model.PropFun.Sat at this
    rw [Trestle.Encode.VEncCNF.toICnf_equisatisfiable] at this
    refine ⟨fun K => this ⟨_,Encoding.Spec.cliqueToAssn_satisfies_baseSpec K⟩⟩
  trestle_unsat

theorem conjectureIn_3 : Euclidean.conjectureIn 3 := by
  apply conjectureIn_of_cnf_unsat (by decide) conjectureIn_2
  trestle_unsat

theorem conjectureIn_4 : Euclidean.conjectureIn 4 := by
  apply conjectureIn_of_cnf_unsat (by decide) conjectureIn_3
  trestle_unsat

theorem conjectureIn_5 : Euclidean.conjectureIn 5 := by
  apply conjectureIn_of_cnf_unsat (by decide) conjectureIn_4
  trestle_unsat

/--
info: 'Keller.conjectureIn_5' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in
#print axioms conjectureIn_5

theorem conjectureIn_6 : Euclidean.conjectureIn 6 := by
  apply conjectureIn_of_cnf_unsat (by decide) conjectureIn_5
  sorry
  --trestle_unsat

/--
info: 'Keller.conjectureIn_6' depends on axioms: [propext, sorryAx, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in
#print axioms conjectureIn_6

theorem conjectureIn_7 : Euclidean.conjectureIn 7 := sorry

def coloring8 : KColoring 8 2 := G8_clique.toKClique (by native_decide)

/--
info: 'Keller.coloring8' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in
#print axioms coloring8

theorem conjectureIn_ge_8 (hn : n ≥ 8) : ¬ Euclidean.conjectureIn n := by
  match n with
  | n+1 =>
  rw [Euclidean.euclideanConjecture_iff_graphConjecture]
  rw [not_isEmpty_iff]
  exact coloring8.liftN (by simp) (by simp) hn |>.normS

/--
info: 'Keller.conjectureIn_ge_8' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in
#print axioms conjectureIn_ge_8
