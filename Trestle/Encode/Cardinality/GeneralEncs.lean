/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Trestle.Encode.Cardinality.Defs

namespace Trestle.Encode.Cardinality

-- TODO(JG): this entire folder needs some reorganizing...

open VEncCNF Model PropFun

/--
  The pairwise at-most-one encoding.

  An O(n²) encoding comprising binary clauses of every pair of literals.
  Formally,

    ∀ x,y ∈ lits, x ≠ y → (¬x ∨ ¬y)

  The only way to satisfy the encoding is to never have any pair of literals
  both set to false in the assignment. Thus, at most one literal is true.
-/
@[inline] def atLeastOne (lits : Array (Literal ν)) :
    VEncCNF ν Unit (atLeast 1 (Multiset.ofList lits.toList)) :=
  addClause lits
  |>.mapProp (by
    ext τ
    simp [Clause.satisfies_iff, card]
  )
