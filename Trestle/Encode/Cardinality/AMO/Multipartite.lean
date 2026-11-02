/-
Copyright (c) 2026 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: Cayden Codel
-/

import Trestle.Encode.Cardinality.AMO.Product
import Trestle.Encode.Cardinality.Totalizer

namespace Trestle.Encode.Cardinality

/-!

# Subercaseaux's multipartite encoding

The multipartite encoding of `AtMostOne(x₁, …, xₙ)` from
Krapivin, Przybocki & Subercaseaux, *Near-Optimal Encodings of Cardinality Constraints*
(arXiv:2603.28954), §3.2, uses `2n + 2√(2n) + O(∛n)` clauses.

Like the product encoding, it is a graph encoding (see `amoGraph`).
The literals are the edges of a complete multipartite graph with `p` parts of `q` vertices each.
Each edge implies its two endpoints, and the key insight is that at most one edge is selected iff
(a) at most one vertex of each part is selected, and
(b) at most two parts contain a selected vertex.
For (a), part `k` gets an auxiliary variable `zₖ`, implied by the part's vertices,
and the vertices of part `k` satisfy `AtMostOne` (the paper's `AtMostOne′(vertices; zₖ)`).
Following `amoCut4`, both are encoded at once as `AtMostOne(vertices of part k, ¬zₖ)`
with the product encoding. As a Boolean function this is the same constraint as `AtMostOne′`,
so it keeps the product encoding's propagation properties. It also uses fewer clauses than
the paper's construction (Lemma 1), which adds one clause `rᵢ → zₖ` per row of the grid.
For (b), the `zₖ` satisfy `AtMost 2` (by the totalizer encoding).

To lay out the edges, we take an odd number `p = 2h + 1` of parts. Then every pair of parts
is `{k, k + d + 1 (mod p)}` for exactly one part `k` and one `d < h`.
So the edges are indexed by `(k, d, a, b)`, the edge
between vertex `a` of part `k` and vertex `b` of part `k + d + 1 (mod p)`.

-/

open VEncCNF Model PropFun

namespace Multipartite

/-- The part `d + 1` steps after part `k`, cyclically, of the `2h + 1` parts. -/
def next (k : Fin (2 * h + 1)) (d : Fin h) : Fin (2 * h + 1) :=
  if hk : k.val + d + 1 < 2 * h + 1 then ⟨k + d + 1, hk⟩ else ⟨k + d + 1 - (2 * h + 1), by omega⟩

theorem next_val (k : Fin (2 * h + 1)) (d : Fin h) : (next k d).val =
    if k.val + d + 1 < 2 * h + 1 then k.val + d + 1 else k.val + d + 1 - (2 * h + 1) := by
  unfold next; split <;> rfl

theorem next_ne (k : Fin (2 * h + 1)) (d : Fin h) : next k d ≠ k := by
  simp only [ne_eq, Fin.ext_iff, next_val]; split <;> omega

theorem next_inj {k : Fin (2 * h + 1)} {d d' : Fin h} : next k d = next k d' → d = d' := by
  simp only [Fin.ext_iff, next_val]; split <;> split <;> omega

/-- Two parts are not each other's `next`: each pair of parts appears once. -/
theorem next_next (k : Fin (2 * h + 1)) (d d' : Fin h) : next (next k d) d' ≠ k := by
  simp only [ne_eq, Fin.ext_iff, next_val]; split_ifs <;> omega

/-- The endpoints of edge `(k, d, a, b)`: vertex `a` of part `k` and vertex `b` of part `next k d`. -/
def ends : Fin (2 * h + 1) × Fin h × Fin q × Fin q → (Fin (2 * h + 1) × Fin q) × (Fin (2 * h + 1) × Fin q)
  | (k, d, a, b) => ((k, a), (next k d, b))

theorem eq_or_eq_of_ncard_le_two {s : Set α} [Finite α] (hs : s.ncard ≤ 2)
    {a b c : α} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hab : a ≠ b) : c = a ∨ c = b := by
  by_contra hc'
  have := (Set.two_lt_ncard_iff).mpr ⟨a, b, c, ha, hb, hc, hab, by grind⟩
  omega

/-- The key insight: the selected vertices `S` are the endpoints of at most one edge iff
at most one vertex of each part is selected, and at most two parts have a selected vertex. -/
def Key (S : Set (Fin (2 * h + 1) × Fin q)) : Prop :=
  (∀ k, (Prod.mk k ⁻¹' S).Subsingleton) ∧ (Prod.fst '' S).ncard ≤ 2

theorem key_mono {S T : Set (Fin (2 * h + 1) × Fin q)} (hST : S ⊆ T) (hT : Key T) : Key S :=
  ⟨fun k => (hT.1 k).anti (Set.preimage_mono hST),
    (Set.ncard_le_ncard (Set.image_mono hST)).trans hT.2⟩

theorem key_one (e : Fin (2 * h + 1) × Fin h × Fin q × Fin q) :
    Key {(ends e).1, (ends e).2} := by
  obtain ⟨k, d, a, b⟩ := e
  refine ⟨fun k' x hx y hy => ?_, ?_⟩
  · have := next_ne k d; simp [ends] at hx hy; grind
  · simpa [ends, Set.image_insert_eq] using Set.ncard_insert_le k {next k d}

theorem key_two (e e' : Fin (2 * h + 1) × Fin h × Fin q × Fin q) :
    Key {(ends e).1, (ends e).2, (ends e').1, (ends e').2} → e = e' := by
  obtain ⟨k, d, a, b⟩ := e
  obtain ⟨k', d', a', b'⟩ := e'
  rintro ⟨h_part, h_parts⟩
  simp only [ends, Set.image_insert_eq, Set.image_singleton] at h_part h_parts
  have hk' := eq_or_eq_of_ncard_le_two h_parts (a := k) (b := next k d) (c := k')
    (by simp) (by simp) (by simp) (next_ne k d).symm
  have hl' := eq_or_eq_of_ncard_le_two h_parts (a := k) (b := next k d) (c := next k' d')
    (by simp) (by simp) (by simp) (next_ne k d).symm
  rcases hk' with hk' | hk' <;> subst k' <;> rcases hl' with hl' | hl'
  · exact absurd hl' (next_ne _ _)
  · have := next_inj hl'; subst d'
    have := h_part k (x := a) (by simp) (y := a') (by simp)
    have := h_part (next k d) (x := b) (by simp) (y := b') (by simp)
    simp_all
  · exact absurd hl' (next_next _ _ _)
  · exact absurd hl' (next_ne _ _)

end Multipartite

open Multipartite in
/-- The multipartite encoding of `AtMostOne(lits)` on the complete multipartite graph
with `p = 2h + 1` parts of `q` vertices each, which has `p * h * q * q` edges.
Literal `lits[i]` is the `i`-th edge. -/
def amoMultipartiteWith (h q : Nat) (lits : Array (Literal ν))
    (hn : lits.size ≤ (2 * h + 1) * (h * (q * q))) :
    VEncCNF ν Unit (atMostOne (Multiset.ofList lits.toList)) :=
  let edge (i : Fin lits.size) : Fin (2 * h + 1) × Fin h × Fin q × Fin q :=
    IndexType.fromFin ⟨i, by show _ < (2 * h + 1) * (h * (q * q)); omega⟩
  amoGraph lits (ends ∘ edge) Key
    (withTemps' (Fin (2 * h + 1)) (seq
      (for_univ fun k =>
        amoProduct <| (Array.ofFn fun a => .pos (.inl (.inr (k, a)))).push (.neg (.inr k)))
      (totalizerAtMost 2 <| Array.ofFn fun k => .pos (.inr k)))
    |>.mapProp (by
      ext σ
      simp only [atMostOne, atMost_ofFn_push, atMost_ofFn]
      simp [Key]
      constructor
      · rintro ⟨σ, rfl, h_part, h_z⟩
        simp only [PropAssignment.get_map]
        refine ⟨fun k => ?_, le_trans (Set.ncard_le_ncard ?_) h_z⟩
        · have := h_part k
          rw [← Set.ncard_le_one_iff_subsingleton]; omega
        rintro _ ⟨⟨k, a⟩, ha, rfl⟩
        have := h_part k
        have := (Set.ncard_pos (s := {a | σ (.inl (.inr (k, a)))})).mpr ⟨a, ha⟩
        grind
      · rintro ⟨h_part, h_z⟩
        refine ⟨σ.extend (fun k => decide (∃ a, σ (.inr (k, a)))), rfl, fun k => ?_, ?_⟩
        · by_cases hk : ∃ a, σ (.inr (k, a))
          · simpa [hk] using h_part k
          · simp_all
        · convert h_z using 2; ext; simp))
    (fun _ _ => key_mono) (by simp [Key]) (fun _ => key_one _)
    (fun i j hQ => by simpa [edge, Fin.ext_iff] using key_two _ _ hQ)

/-- Subercaseaux's multipartite encoding of `AtMostOne(lits)`.

As in the paper, there are `p ≈ ⁶√n + 1` parts, except that `p = 2h + 1` is odd.
Then each part gets the fewest vertices `q` that make room for all `n` edges, so `q ≈ √2 ∛n`.
Small cases (`n ≤ 64`) use the product encoding. -/
def amoMultipartite (lits : Array (Literal ν)) :
    VEncCNF ν Unit (atMostOne (Multiset.ofList lits.toList)) :=
  if hn : lits.size ≤ 64 then amoProduct lits else
  have h_ex : ∃ h, lits.size ≤ (2 * h) ^ 6 :=
    ⟨lits.size, by have := Nat.le_self_pow (n := 6) (by omega) (2 * lits.size); omega⟩
  let h := Nat.find h_ex
  have hh : 0 < h := Nat.find_pos h_ex |>.mpr (by show ¬ _ ≤ (2 * 0) ^ 6; omega)
  have q_ex : ∃ q, lits.size ≤ (2 * h + 1) * (h * (q * q)) :=
    ⟨lits.size, by
      have := Nat.le_mul_self lits.size
      have := Nat.le_mul_of_pos_left (lits.size * lits.size) hh
      have := Nat.le_mul_of_pos_left (h * (lits.size * lits.size)) (by omega : 0 < 2 * h + 1)
      omega⟩
  amoMultipartiteWith h (Nat.find q_ex) lits (Nat.find_spec q_ex)

instance multipartiteAMOEncoding : AMOEncoding ν where
  encoding := amoMultipartite

end Trestle.Encode.Cardinality /- namespace -/
