/-
Copyright (c) 2026 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: Cayden Codel
-/

import Trestle.Encode.Cardinality.Defs

namespace Trestle.Encode.Cardinality

/-!

# Totalizer encoding

The totalizer [Bailleux & Boufkhad, CP 2003] counts the true literals of `lits` in unary.
It builds a binary tree over `lits`. Each node has a *counter* `o₁, …, oₙ`,
where `n` is the number of leaves under the node, and `oᵢ` is true iff
at least `i` of those leaves are true. A leaf is its own counter.
An internal node gets fresh variables for its counter,
and `merge` sums the counters `a₁, …, aₚ` and `b₁, …, b_q` of its children into it
with the clauses, for `0 ≤ i ≤ p` and `0 ≤ j ≤ q`,

  `aᵢ ∧ bⱼ → oᵢ₊ⱼ`   and   `oᵢ₊ⱼ₊₁ → aᵢ₊₁ ∨ bⱼ₊₁`

where `a₀, b₀, o₀` are true and `aₚ₊₁, b_q₊₁, oₙ₊₁` are false.
(In the code, counters are indexed from `0`, so `o i` is `oᵢ₊₁`.)

`totalizer` constrains the root's counter to the number of true literals of `lits`.
Cardinality constraints add unit clauses on the root's counter (see `totalizerBetween`).

See also Joshi, Martins & Manquinho, *Generalized Totalizer Encoding for
Pseudo-Boolean Constraints*, CP 2015 (arXiv:1507.05920).

-/

open VEncCNF Model PropFun

namespace Totalizer

variable {ν : Type} {n p q : Nat}

/-- The number of true literals of `lits`. -/
abbrev count (lits : Fin n → Literal ν) (τ : PropAssignment ν) : Nat :=
  card (Multiset.ofList (List.ofFn lits)) τ

/-- `out` is `c` in unary: `out i` is true iff `i < c`. -/
def IsUnary (out : Fin n → Literal ν) (c : Nat) (τ : PropAssignment ν) : Prop :=
  ∀ i, τ ⊨ LitVar.toPropFun (out i) ↔ i.val < c

/-- The literal of the counter `out` that says the count is at least `i`,
as an array of zero or one literals. It is empty for `i = 0` and `i > n`,
which is true as a conjunction (the count is at least `0`),
and false as a disjunction (the count is at most `n`). -/
def ge (out : Fin n → Literal ν) (i : Nat) : Array (Literal ν) :=
  if h : 0 < i ∧ i ≤ n then #[out ⟨i - 1, by omega⟩] else #[]

/-- The clauses that sum the counters `a` and `b` into the counter `o`:
`a ≥ i ∧ b ≥ j → o ≥ i + j` and `o ≥ i + j + 1 → a ≥ i + 1 ∨ b ≥ j + 1`. -/
def Merge (a : Fin p → Literal ν) (b : Fin q → Literal ν) (o : Fin n → Literal ν) : PropPred ν :=
  fun τ => ∀ i ≤ p, ∀ j ≤ q,
    (0 < i + j → (∀ l ∈ ge a i ++ ge b j, τ ⊨ LitVar.toPropFun l) →
      ∃ l ∈ ge o (i + j), τ ⊨ LitVar.toPropFun l) ∧
    (i + j < n → (∀ l ∈ ge o (i + j + 1), τ ⊨ LitVar.toPropFun l) →
      ∃ l ∈ ge a (i + 1) ++ ge b (j + 1), τ ⊨ LitVar.toPropFun l)

/-- Sums the counters `a` and `b` into the counter `o`:
if `a` and `b` are `ca` and `cb` in unary, then `o` is `ca + cb` in unary (see `merge_iff`). -/
def merge (a : Fin p → Literal ν) (b : Fin q → Literal ν) (o : Fin n → Literal ν) :
    VEncCNF ν Unit (Merge a b o) :=
  (for_all (Array.range (p + 1)) fun i =>
    for_all (Array.range (q + 1)) fun j =>
      seq
        (VEncCNF.guard (0 < i + j) fun _ =>
          andImplyOr (ge a i ++ ge b j) (ge o (i + j)))
        (VEncCNF.guard (i + j < n) fun _ =>
          andImplyOr (ge o (i + j + 1)) (ge a (i + 1) ++ ge b (j + 1))))
  |>.mapProp (by ext τ; simp [Merge, Nat.lt_succ_iff, Clause.satisfies_iff])

/-- Fresh variables for the counter of `n` literals. At most one literal is its own counter. -/
def numOuts (n : Nat) : Nat := if n ≤ 1 then 0 else n

/-- The counter of `lits`. It uses the fresh variables `t` if there are at least two literals. -/
def counter (lits : Fin n → Literal ν) (t : Fin (numOuts n) → ν) : Fin n → Literal ν :=
  if h : n ≤ 1 then lits else fun i => .pos (t (i.cast (by simp [numOuts, h])))

/-! ### Lemmas -/

theorem count_le (lits : Fin n → Literal ν) (τ) : count lits τ ≤ n := by
  simp only [count, card, Multiset.coe_countP]
  exact (List.countP_le_length ..).trans (by simp)

theorem count_map (f : ν → ν') (lits : Fin n → Literal ν) (τ : PropAssignment ν') :
    count (LitVar.map f ∘ lits) τ = count lits (τ.map f) := by
  simp only [count, card, Multiset.coe_countP]
  rw [← List.map_ofFn, List.countP_map]
  simp [Function.comp_def]

theorem count_split (lits : Fin n → Literal ν) (m) (hm : m ≤ n) (τ) :
    count lits τ = count (fun i : Fin m => lits ⟨i, by omega⟩) τ
      + count (fun i : Fin (n - m) => lits ⟨m + i, by omega⟩) τ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  simp [count, card, List.ofFn_add]
  rfl

theorem isUnary_map (f : ν → ν') (out : Fin n → Literal ν) (c) (τ : PropAssignment ν') :
    IsUnary (LitVar.map f ∘ out) c τ ↔ IsUnary out c (τ.map f) := by
  simp [IsUnary]

theorem forall_ge_iff {out : Fin n → Literal ν} (h : IsUnary out c τ) (i) :
    (∀ l ∈ ge out i, τ ⊨ LitVar.toPropFun l) ↔ (i ≤ n → i ≤ c) := by
  unfold ge; split <;> simp [h _] <;> omega

theorem exists_ge_iff {out : Fin n → Literal ν} (h : IsUnary out c τ) (hc : c ≤ n) (i) :
    (∃ l ∈ ge out i, τ ⊨ LitVar.toPropFun l) ↔ 0 < i ∧ i ≤ c := by
  unfold ge; split <;> simp [h _] <;> omega

@[simp] theorem ge_succ (out : Fin n → Literal ν) (k : Fin n) : ge out (k + 1) = #[out k] := by
  simp [ge, Nat.add_one_le_iff]

theorem merge_iff {a : Fin p → Literal ν} {b : Fin q → Literal ν} {o : Fin n → Literal ν}
    (ha : IsUnary a ca τ) (hb : IsUnary b cb τ) (hca : ca ≤ p) (hcb : cb ≤ q) (hn : n = p + q) :
    Merge a b o τ ↔ IsUnary o (ca + cb) τ := by
  simp +contextual only [Merge, Array.mem_append, or_imp, forall_and, or_and_right, exists_or,
    forall_ge_iff ha, forall_ge_iff hb, exists_ge_iff ha hca, exists_ge_iff hb hcb, true_implies]
  constructor
  · rintro ⟨hup, hdown⟩ k
    constructor
    · intro hk
      by_contra hlt
      obtain ⟨i, j, hij, hi, hj, hia, hjb⟩ :
          ∃ i j, i + j = k.val ∧ i ≤ p ∧ j ≤ q ∧ ca ≤ i ∧ cb ≤ j :=
        ⟨max ca (k - q), k - max ca (k - q), by omega⟩
      have := hdown i hi j hj (by omega) (by simpa [hij] using hk)
      omega
    · intro hlt
      obtain ⟨i, j, hij, hi, hj, hia, hjb⟩ :
          ∃ i j, i + j = k.val + 1 ∧ i ≤ p ∧ j ≤ q ∧ i ≤ ca ∧ j ≤ cb :=
        ⟨min ca (k + 1), k + 1 - min ca (k + 1), by omega⟩
      simpa [hij] using hup i hi j hj (by omega) ⟨hia, hjb⟩
  · intro h
    simp only [forall_ge_iff h, exists_ge_iff h (by omega)]
    constructor <;> intros <;> omega

theorem isUnary_counter {lits : Fin n → Literal ν} {t : Fin (numOuts n) → ν}
    (ht : ∀ i, τ (t i) = decide (i.val < count lits τ)) :
    IsUnary (counter lits t) (count lits τ) τ := by
  unfold counter
  split
  · intro i
    match n, lits, i with
    | 1, lits, 0 => by_cases h : τ ⊨ LitVar.toPropFun (lits 0) <;> simp [count, h]
  · intro i; simp [ht]

/-- The fresh variables for the children's counters of a node over `n` literals. -/
abbrev Temps (n : Nat) := Fin (numOuts (n / 2) + numOuts (n - n / 2))

end Totalizer

open Totalizer in
/-- The totalizer: constrains the counter of `lits` (with fresh variables `t`)
to the number of true literals of `lits`, in unary. -/
def totalizer (lits : Fin n → Literal ν) (t : Fin (numOuts n) → ν) :
    VEncCNF ν Unit (fun τ => IsUnary (counter lits t) (count lits τ) τ) :=
  if h : n ≤ 1 then
    VEncCNF.pure () |>.mapProp (by
      ext τ; simp only [Pi.top_apply, Prop.top_eq_true, true_iff]
      exact isUnary_counter fun i => absurd i.isLt (by simp [numOuts, h]))
  else
    let L : Fin (n / 2) → Literal ν := fun i => lits ⟨i, by omega⟩
    let R : Fin (n - n / 2) → Literal ν := fun i => lits ⟨n / 2 + i, by omega⟩
    let L' : Fin (n / 2) → Literal (ν ⊕ Temps n) := LitVar.map Sum.inl ∘ L
    let R' : Fin (n - n / 2) → Literal (ν ⊕ Temps n) := LitVar.map Sum.inl ∘ R
    let tL : Fin (numOuts (n / 2)) → ν ⊕ Temps n := Sum.inr ∘ Fin.castAdd _
    let tR : Fin (numOuts (n - n / 2)) → ν ⊕ Temps n := Sum.inr ∘ Fin.natAdd _
    withTemps' (Temps n) (
      seq (totalizer L' tL) <|
      seq (totalizer R' tR) <|
      merge (counter L' tL) (counter R' tR) (LitVar.map Sum.inl ∘ counter lits t))
    |>.mapProp (by
      ext τ
      constructor
      · rintro ⟨σ, rfl, hL, hR, hM⟩
        have := (merge_iff hL hR (count_le ..) (count_le ..) (by omega)).mp hM
        rwa [isUnary_map, count_map, count_map, ← count_split _ _ (by omega)] at this
      · intro hτ
        let σ : PropAssignment (ν ⊕ Temps n) :=
          τ.extend (Fin.addCases (decide <| ·.val < count L τ) (decide <| ·.val < count R τ))
        have hL := isUnary_counter (τ := σ) (lits := L') (t := tL) (by simp [σ, L', tL, count_map])
        have hR := isUnary_counter (τ := σ) (lits := R') (t := tR) (by simp [σ, R', tR, count_map])
        refine ⟨σ, rfl, hL, hR, (merge_iff hL hR (count_le ..) (count_le ..) (by omega)).mpr ?_⟩
        rwa [isUnary_map, count_map, count_map, ← count_split _ _ (by omega)])
termination_by n

open Totalizer in
/-- The totalizer encoding of `lo ≤ card lits ≤ hi`. -/
def totalizerBetween (lo hi : Nat) (lits : Array (Literal ν)) :
    VEncCNF ν Unit (fun τ => lo ≤ card lits.toList τ ∧ card lits.toList τ ≤ hi) :=
  let lits' : Fin lits.size → Literal (ν ⊕ Fin (numOuts lits.size)) :=
    LitVar.map Sum.inl ∘ (lits[·])
  let out := counter lits' Sum.inr
  withTemps' _ (
    seq (totalizer lits' Sum.inr) <|
    -- the count is at least `lo`
    seq (VEncCNF.guard (0 < lo) fun _ => addClause (ge out lo)) <|
    -- the count is not at least `hi + 1`
    for_all (ge out (hi + 1)) fun l => unit (-l))
  |>.mapProp (by
    ext τ
    have hcount (σ : PropAssignment (ν ⊕ _)) (hσ : σ.map Sum.inl = τ) :
        count lits' σ = card lits.toList τ := by
      simp only [lits', count_map, hσ]
      simp [count, ← Array.toList_ofFn]
    simp only [out, Clause.satisfies_iff]
    constructor
    · rintro ⟨σ, rfl, hU, hlo, hhi⟩
      have hc := count_le lits' σ
      have := (exists_ge_iff hU hc (hi + 1)).not.mp (by simpa using hhi)
      simp only [exists_ge_iff hU hc] at hlo
      rw [← hcount σ rfl]
      omega
    · rintro ⟨hlo, hhi⟩
      let σ : PropAssignment (ν ⊕ Fin (numOuts lits.size)) :=
        τ.extend (decide <| ·.val < card lits.toList τ)
      have hU := isUnary_counter (lits := lits') (t := Sum.inr) (τ := σ)
        (by simp [σ, hcount σ rfl])
      have hc := count_le lits' σ
      have := hcount σ rfl
      refine ⟨σ, rfl, hU, fun _ => (exists_ge_iff hU hc lo).mpr (by omega), ?_⟩
      simpa using (exists_ge_iff hU hc (hi + 1)).not.mpr (by omega))

/-- The totalizer encoding of `card lits ≤ k`. -/
def totalizerAtMost (k : Nat) (lits : Array (Literal ν)) :
    VEncCNF ν Unit (atMost k (Multiset.ofList lits.toList)) :=
  totalizerBetween 0 k lits |>.mapProp (by ext τ; simp)

/-- The totalizer encoding of `card lits ≥ k`. -/
def totalizerAtLeast (k : Nat) (lits : Array (Literal ν)) :
    VEncCNF ν Unit (atLeast k (Multiset.ofList lits.toList)) :=
  totalizerBetween k lits.size lits |>.mapProp (by
    ext τ
    have : card lits.toList τ ≤ lits.size := by
      simpa [card] using List.countP_le_length (l := lits.toList)
    simp; omega)

/-- The totalizer encoding of `card lits = k`. -/
def totalizerExactly (k : Nat) (lits : Array (Literal ν)) :
    VEncCNF ν Unit (exactly k (Multiset.ofList lits.toList)) :=
  totalizerBetween k k lits |>.mapProp (by ext τ; simp; omega)

end Trestle.Encode.Cardinality
