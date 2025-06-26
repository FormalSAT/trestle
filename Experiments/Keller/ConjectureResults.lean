/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.Encoding.CNF
import Experiments.Keller.G8_Clique

import Experiments.Solver.Builtin

namespace Keller

theorem conjectureIn_of_cnf_unsat {n : Nat} (h : conjectureIn (n+1)) :
  ¬(Encoding.CNF.fullEncoding (n+2) (2^(n+1))).val.toICnf.Sat → conjectureIn (n+2) := by
  intro unsat
  unfold conjectureIn
  by_contra ex
  simp at ex
  rcases ex with ⟨c⟩
  generalize s_def : 2^(n+1) = s at c unsat
  have : 2 ≤ s := by subst s; apply Nat.le_self_pow; simp
  match s, this with
  | s+2, _ =>
  have ⟨tc⟩ := SymmBreak.C3Zeros.ofClique h c
  have sat := Encoding.Spec.cliqueToAssn_satisfies_fullSpec tc
  apply unsat; clear unsat
  unfold Trestle.Cnf.Sat Trestle.Model.PropFun.Sat
  rw [Trestle.Encode.VEncCNF.toICnf_equisatisfiable]
  refine ⟨_, sat⟩

/-! ## Positive Results -/

theorem conjectureIn_2 : conjectureIn 2 := by
  unfold conjectureIn
  rw [← KCliqueData.checkAll_iff_isempty_kclique]
  native_decide

theorem conjectureIn_3 : conjectureIn 3 := by
  apply conjectureIn_of_cnf_unsat conjectureIn_2
  trestle_unsat

theorem conjectureIn_4 : conjectureIn 4 := by
  apply conjectureIn_of_cnf_unsat conjectureIn_3
  trestle_unsat

theorem conjectureIn_5 : conjectureIn 5 := by
  apply conjectureIn_of_cnf_unsat conjectureIn_4
  trestle_unsat

/--
info: 'Keller.conjectureIn_5' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in
#print axioms conjectureIn_5

theorem conjectureIn_6 : conjectureIn 6 := by
  apply conjectureIn_of_cnf_unsat conjectureIn_5
  sorry
  --trestle_unsat

/--
info: 'Keller.conjectureIn_6' depends on axioms: [propext, sorryAx, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in
#print axioms conjectureIn_6

theorem conjectureIn_7 : conjectureIn 7 := sorry

theorem not_conjectureIn_8 : ¬ conjectureIn 8 := by
  apply G8_clique.check_implies_not_conjecture (by decide)
  native_decide

-- TODO(JG): finish this proof
theorem not_conjectureIn_ge_8 : n ≥ 8 → ¬ conjectureIn 8 := by
  sorry
