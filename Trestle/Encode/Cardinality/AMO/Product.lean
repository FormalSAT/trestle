/-
Copyright (c) 2026 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: Cayden Codel
-/

import Trestle.Encode.Cardinality.AMO.Pairwise
import Mathlib.Data.Set.Card

namespace Trestle.Encode.Cardinality

/-!

# Chen's product encoding

Chen's product encoding [Chen, SAT 2010] of `AtMostOne(x₁, …, xₙ)`
places the literals in a `p × p` grid, where `p = ⌈√n⌉`.
Each literal implies an auxiliary variable for its row and one for its column.
Then at most one literal is true iff at most one row and at most one column are selected,
which is encoded recursively with the product encoding.

We follow the *graph perspective* on the product encoding from
Krapivin, Przybocki & Subercaseaux, *Near-Optimal Encodings of Cardinality Constraints*
(arXiv:2603.28954), §3.1. The literals are the edges of a graph. Each edge implies
auxiliary variables for its two endpoints, and a constraint `Q` on the set of selected vertices
ensures that at most one edge is selected (`amoGraph`).
The product encoding uses the complete bipartite graph between rows and columns,
and `Q` says that at most one row and at most one column are selected.
The multipartite encoding (see `Multipartite.lean`) uses a complete multipartite graph.

-/

open VEncCNF Model PropFun

/-! ### Counting over `Array.ofFn` -/

theorem card_ofFn (f : Fin m → Literal ν) (τ : PropAssignment ν) :
    card (List.ofFn f : Multiset _) τ = {i | τ ⊨ ↑(f i)}.ncard := by
  rw [Set.ncard_eq_toFinset_card']
  simp [card, List.ofFn_eq_map, ← List.countP_eq_length_filter, Finset.card, Finset.filter_val,
    Fin.univ_def, List.countP_map, Function.comp_def]

@[simp] theorem atMost_ofFn (k : Nat) (f : Fin m → Literal ν) (τ : PropAssignment ν) :
    atMost k (Array.ofFn f).toList τ ↔ {i | τ ⊨ ↑(f i)}.ncard ≤ k := by
  simp [card_ofFn]

@[simp] theorem atMost_ofFn_push (k : Nat) (f : Fin m → Literal ν) (l : Literal ν) (τ) :
    atMost k ((Array.ofFn f).push l).toList τ ↔
      {i | τ ⊨ ↑(f i)}.ncard + (if τ ⊨ LitVar.toPropFun l then 1 else 0) ≤ k := by
  simp [card_ofFn]

/-! ### The graph encoding -/

section Graph

variable {ν V : Type} [IndexType V] [LawfulIndexType V]

/-- The *graph encoding* of `AtMostOne(lits)` (arXiv:2603.28954, §3.1).

The literal `lits[i]` is an edge of a graph on the vertices `V`, with endpoints `ends i`.
Each vertex gets an auxiliary variable, which is implied by each of its edges.
Then `enc` constrains the set of selected vertices by `Q`,
which must allow the endpoints of no edge (`Q_none`) or of one edge (`Q_one`),
and forbid the endpoints of two distinct edges (`Q_two`) and all their supersets (`Q_mono`). -/
def amoGraph (lits : Array (Literal ν)) (ends : Fin lits.size → V × V)
    (Q : Set V → Prop) (enc : VEncCNF (ν ⊕ V) Unit (fun σ => Q {v | σ (.inr v)}))
    (Q_mono : ∀ S T, S ⊆ T → Q T → Q S)
    (Q_none : Q ∅)
    (Q_one : ∀ i, Q {(ends i).1, (ends i).2})
    (Q_two : ∀ i j, Q {(ends i).1, (ends i).2, (ends j).1, (ends j).2} → i = j) :
    VEncCNF ν Unit (atMostOne (Multiset.ofList lits.toList)) :=
  withTemps' V (seq
    (for_univ fun i : Fin lits.size =>
      implyAnd (LitVar.map .inl lits[i]) #[.pos (.inr (ends i).1), .pos (.inr (ends i).2)])
    enc)
  |>.mapProp (by
    ext τ
    rw [amo_iff]
    constructor
    · rintro ⟨σ, rfl, h_ends, hQ⟩ i hi j hj hi_sat hj_sat
      have := h_ends ⟨i, hi⟩ (by simpa using hi_sat)
      have := h_ends ⟨j, hj⟩ (by simpa using hj_sat)
      have := Q_two ⟨i, hi⟩ ⟨j, hj⟩ (Q_mono _ _ (by simp_all [Set.insert_subset_iff]) hQ)
      simpa using this
    · intro h
      by_cases h_sat : ∃ i : Fin lits.size, τ ⊨ ↑lits[i]
      · obtain ⟨i, hi⟩ := h_sat
        refine ⟨τ.extend (decide <| · ∈ ({(ends i).1, (ends i).2} : Set V)), rfl, ?_, ?_⟩
        rotate_left; · convert Q_one i; ext; simp
        intro j hj
        obtain rfl := Fin.ext <| h j j.isLt i i.isLt (by simpa using hj) hi
        simp
      · refine ⟨τ.extend fun _ => false, rfl, ?_, by simpa⟩
        intro j hj
        exact absurd ⟨j, by simpa using hj⟩ h_sat)

end Graph

/-! ### The product encoding -/

/-- Chen's product encoding of `AtMostOne(lits)`.

Literal `lits[i]` sits in the `i`-th cell `(r, c)` of a `p × p` grid, where `p = ⌈√n⌉`.
It implies the auxiliary variables for row `r` and column `c`.
Then at most one row and at most one column are selected, recursively.
Small cases (`n ≤ 4`) use the pairwise encoding. -/
def amoProduct (lits : Array (Literal ν)) :
    VEncCNF ν Unit (atMostOne (Multiset.ofList lits.toList)) :=
  if h : lits.size ≤ 4 then amoPairwise lits else
  let p := (lits.size - 1).sqrt + 1
  have := Nat.lt_succ_sqrt (lits.size - 1)
  let cell (i : Fin lits.size) : Fin p × Fin p := IndexType.fromFin ⟨i, by
    show _ < p * p; simp only [p, Nat.succ_eq_add_one] at *; omega⟩
  amoGraph lits (fun i => (.inl (cell i).1, .inr (cell i).2))
    (fun S => (Sum.inl ⁻¹' S).Subsingleton ∧ (Sum.inr ⁻¹' S).Subsingleton)
    (seq
      (amoProduct <| Array.ofFn fun r => .pos (.inr (.inl r)))
      (amoProduct <| Array.ofFn fun c => .pos (.inr (.inr c)))
    |>.mapProp (by ext σ; simp only [atMostOne, atMost_ofFn]; simp [Set.preimage]))
    (fun _ _ hST hT => ⟨hT.1.anti (Set.preimage_mono hST), hT.2.anti (Set.preimage_mono hST)⟩)
    (by simp)
    (fun i => by constructor <;> intro x hx y hy <;> simp_all)
    (fun i j ⟨hr, hc⟩ => by
      have := hr (x := (cell i).1) (by simp) (y := (cell j).1) (by simp)
      have := hc (x := (cell i).2) (by simp) (y := (cell j).2) (by simp)
      have : cell i = cell j := Prod.ext ‹_› ‹_›
      simpa [cell, Fin.ext_iff] using this)
termination_by lits.size
decreasing_by
  all_goals
    have := Nat.sqrt_lt_self (n := lits.size - 1) (by omega)
    simp only [Array.size_ofFn]; omega

instance productAMOEncoding : AMOEncoding ν where
  encoding := amoProduct

end Trestle.Encode.Cardinality /- namespace -/
