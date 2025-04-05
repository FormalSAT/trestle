/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.G8_Clique

namespace Keller

/-! ## Positive Results -/

theorem conjectureIn_2 : conjectureIn 2 := by
  unfold conjectureIn
  rw [← KCliqueData.checkAll_iff_isempty_kclique]
  native_decide
#print axioms conjectureIn_2

theorem conjectureIn_3 : conjectureIn 3 := sorry
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
