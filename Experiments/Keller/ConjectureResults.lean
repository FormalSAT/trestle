/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.Encoding
import Experiments.Keller.G8_Clique

import Experiments.Solver.Builtin

namespace Keller

theorem conjectureIn_of_cnf_unsat {n : Nat} (h : conjectureIn (n+2)) :
  (Encoding.fullEncoding (n+3) (2^(n+2))).val.toICnf.Unsat → conjectureIn (n+3) := by
  intro unsat
  unfold conjectureIn
  by_contra ex
  simp at ex
  rcases ex with ⟨c⟩
  have : 2 ≤ 2^(n+2) := Nat.le_self_pow (by simp) _
  have ⟨tc⟩ := SymmBreak.C3Zeros.ofClique (s := 2^(n+1)-2) h (by omega) (cast (by congr; omega) c)
  have := Encoding.cliqueToAssn_satisfies_fullSpec
  unfold Trestle.ICnf.Unsat Trestle.ICnf.Sat Trestle.Model.PropFun.satisfiable
  rw [Trestle.Encode.EncCNF.encodesProp_equisatisfiable]
  sorry

/-! ## Positive Results -/

theorem conjectureIn_2 : conjectureIn 2 := by
  unfold conjectureIn
  rw [← KCliqueData.checkAll_iff_isempty_kclique]
  native_decide

#print axioms conjectureIn_2

theorem conjectureIn_3 : conjectureIn 3 := by

  sorry
theorem conjectureIn_4 : conjectureIn 4 := sorry
theorem conjectureIn_5 : conjectureIn 5 := sorry
theorem conjectureIn_6 : conjectureIn 6 := sorry
theorem conjectureIn_7 : conjectureIn 7 := sorry

theorem not_conjectureIn_8 : ¬ conjectureIn 8 := by
  apply G8_clique.check_implies_not_conjecture (by decide)
  native_decide

-- TODO(JG): finish this proof
theorem not_conjectureIn_ge_8 : n ≥ 8 → ¬ conjectureIn 8 := by
  sorry
