/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.G8_Clique

namespace Keller

theorem not_conjectureIn_8 : ¬ conjectureIn 8 := by
  apply G8_clique.checkAll_implies_not_conjecture
  native_decide
