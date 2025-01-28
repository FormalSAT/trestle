/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.Autos

namespace Keller

/-! ## Symmetry Breaking verified by SR -/

def canonicalCases := #[
  (0, 1, 1, 0, 0, 1),
  (0, 1, 1, 0, 1, 1),
  (0, 1, 1, 0, 2, 1),
  (0, 1, 1, 1, 0, 0),
  (0, 1, 1, 1, 0, 2),
  (0, 1, 1, 1, 1, 0),
  (0, 1, 1, 1, 1, 1),
  (0, 1, 1, 1, 1, 2),
  (0, 1, 1, 1, 2, 0),
  (0, 1, 1, 1, 2, 1),
  (0, 1, 1, 1, 2, 2),
  (0, 1, 1, 2, 1, 1),
  (0, 1, 1, 2, 2, 1),
  (1, 1, 0, 0, 1, 1),
  (1, 1, 0, 0, 2, 1),
  (1, 1, 0, 2, 1, 1),
  (1, 1, 0, 2, 2, 1),
  (1, 1, 1, 1, 1, 1),
  (1, 1, 1, 1, 1, 2),
  (1, 1, 1, 1, 2, 2),
  (1, 1, 1, 2, 2, 1),
  (1, 1, 2, 0, 2, 1),
  (1, 1, 2, 1, 2, 1),
  (1, 1, 2, 1, 2, 2),
  (2, 1, 1, 2, 2, 1),
  (1, 1, 2, 0, 3, 1),
  (1, 1, 2, 1, 3, 1),
  (1, 1, 2, 1, 3, 2) ]

