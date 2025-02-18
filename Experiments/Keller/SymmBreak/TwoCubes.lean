/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.Autos

namespace Keller.SymmBreak

/-! ## First Three Cubes

Any Keller clique can be mapped to a Keller clique where
`c_0`, `c_1`, and the first five coordinates of `c_3` are fixed.
This argument relies on the veracity
of the Keller conjecture for the previous dimension.
-/


def TwoCubes.c0_colors : Vector (Fin (s+2)) (n+2) :=
  ⟨Array.mkArray (n+2) 0, by simp⟩

@[simp] theorem TwoCubes.c0_colors_j (j : Nat) (hj : j < (n+2)) : (c0_colors (s := s))[j] = 0 := by
  simp [c0_colors]

def TwoCubes.c1_colors : Vector (Fin (s+2)) (n+2) :=
  ⟨#[0,1] ++ Array.mkArray n 0, by simp; omega⟩

@[simp] theorem TwoCubes.c1_colors_j (j : Nat) (hj : j < (n+2)) :
    (c1_colors (s := s))[j] = if j = 1 then 1 else 0 := by
  simp [c1_colors, Array.getElem_append]
  rcases j with ⟨(_|_|_),h⟩ <;> simp [Nat.succ_lt_succ_iff, Fin.ext_iff]

structure TwoCubes (n s) where
  kclique : KClique (n+2) (s+2)
  c0 : kclique.get 0 = TwoCubes.c0_colors
  c1 : kclique.get 1 = TwoCubes.c1_colors

namespace TwoCubes

theorem pick_pair {n s} (kclique : KClique (n+2) (s+1)) (h : conjectureIn (n+1))
  : ∃ a ∈ kclique.val, ∃ b ∈ kclique.val,
    ∃ (j₁ j₂ : Fin (n+2)), j₁ ≠ j₂ ∧
      ∀ (j : ℕ) (h : j < n + 2),
        (j ≠ ↑j₁ ↔ a.bv[j] = b.bv[j]) ∧
        (j ≠ ↑j₂ ↔ a.colors[j] = b.colors[j])
  := by
  -- construct a K_0 in smaller graph, using vertices with last bit 0 in bigger graph
  let K_0 : Finset (KVertex (n+1) (s+1)) := (Finset.univ (α := BitVec (n+1)))
    |>.map ⟨fun i =>
        let i' := i.cons false
        let v := kclique.get i'
        ⟨i, v.take (n+1) |>.cast (by omega)⟩
      , by
        intro x1 x2 heq
        simp at heq; exact heq.1⟩
  have K_0_card : K_0.card = (2^(n+1)) := by simp [K_0]
  -- K_0 must not be a clique, because the conjecture holds in that dimension
  have K_0_not_clique : ¬ _ := (h (s+1)).false ∘ Subtype.mk K_0
  -- find the vertices in K_0 which are the not adjacent
  have ⟨⟨i₁,c₁⟩, hv₁, ⟨i₂,c₂⟩, hv₂, hne, hnotadj⟩ :
    ∃ x ∈ K_0, ∃ x_1 ∈ K_0, ¬x = x_1 ∧ ¬KAdj x x_1 := by
    simpa [KClique, SimpleGraph.isNClique_iff, K_0_card,
      SimpleGraph.isClique_iff, Set.Pairwise] using K_0_not_clique
  -- simplify hv₁ hv₂ based on the def of K_0
  simp only [K_0, Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk,
      KVertex.mk.injEq, true_and, exists_eq_left] at hv₁ hv₂
  clear K_0_card K_0_not_clique h K_0

  -- the indices in smaller graph must be diff
  have i_diff : i₁ ≠ i₂ := by
    intro contra; subst hv₁ hv₂; simp [contra] at hne
  clear hne
  -- name the corresponding colors in bigger graph
  generalize hk₁ : KClique.get _ _ = k₁ at hv₁
  generalize hk₂ : KClique.get _ _ = k₂ at hv₂
  subst hv₁ hv₂
  -- the corresponding vertices are adjacent in big graph
  have : KAdj ⟨i₁.cons false, k₁⟩ ⟨i₂.cons false,k₂⟩ := by
    subst hk₁ hk₂
    apply kclique.isClique
    iterate 2 (apply KClique.get_mem)
    simp [i_diff]
  -- by def of adjacency, we get a j₁, j₂ in big graph
  rcases this with ⟨⟨j₁,hj₁⟩,is_diff_at_j1,ks_same,⟨j₂,hj₂⟩,js_diff,diff_at_j2⟩
  simp only [ne_eq, Fin.getElem_fin, Fin.mk.injEq] at *
  -- j₁ can't be the last dimension because the big graph bitvecs are the same there!
  have : j₁ ≠ n+1 := by intro contra; simp [BitVec.getElem_cons, contra] at is_diff_at_j1
  replace hj₁ : j₁ < n+1 := by omega
  -- now we know the small graph i's are different at index j₁
  replace is_diff_at_j1 : i₁[j₁] ≠ i₂[j₁] := by
    simpa [BitVec.getElem_cons, this] using is_diff_at_j1
  clear this
  -- but since small graph i's are not adjacent, they must be equal everywhere other than j₁
  simp only [KAdj, Fin.getElem_fin, ne_eq, Vector.getElem_cast, Vector.getElem_take, not_exists,
    not_and, not_or, Decidable.not_not] at hnotadj
  specialize hnotadj ⟨j₁, hj₁⟩ is_diff_at_j1 ks_same
  -- Therefore, to satisfy `diff_at_j2`, `j₂` must be `n+1`
  by_cases this : j₂ = n+1
  case neg =>
    exfalso
    replace hj₂ : j₂ < n+1 := by omega
    specialize hnotadj ⟨j₂,hj₂⟩
    simp [js_diff] at hnotadj
    simp [BitVec.getElem_cons, Nat.ne_of_lt hj₂, hnotadj.2] at diff_at_j2
    apply diff_at_j2 hnotadj.1
  subst this
  -- and we can sensibly conclude the big graph colors differ at `n+1`
  replace diff_at_j2 : ¬k₁[n + 1] = k₂[n + 1] := by
    simpa [BitVec.getElem_cons] using diff_at_j2

  -- Ok! We have all the info we need to fill the goal!
  use ⟨i₁.cons false, k₁⟩, (hk₁ ▸ kclique.get_mem ..),
      ⟨i₂.cons false, k₂⟩, (hk₂ ▸ kclique.get_mem ..),
      ⟨j₁,‹_›⟩, ⟨n+1, by omega⟩
  simp [js_diff]
  rintro j -
  by_cases eq_j1 : j = j₁
  · -- TODO BitVec.getElem_cons is a bad rewrite rule...
    simp_all [BitVec.getElem_cons]; simpa [← BitVec.getLsbD_eq_getElem]
  · by_cases eq_last : j = n+1
    · simp_all [BitVec.getElem_cons]
    · specialize hnotadj ⟨j, by omega⟩ (by simp; exact Ne.symm eq_j1)
      simp_all [BitVec.getElem_cons]; exact hnotadj.1

/-- The automorphism that reorders any columns `j₁`, `j₂`
to the first and second column, respectively. -/
def reorder_j1_j2 (j₁ j₂ : Fin (n+2)) := Equiv.Perm.setAll [(0,j₁), (1,j₂)]

namespace reorder_j1_j2
variable {j1 j2 : Fin (n+2)} (h : j1 ≠ j2)
include h

@[simp] theorem app_0 : reorder_j1_j2 j1 j2 0 = j1 := by
  unfold reorder_j1_j2; apply Equiv.setAll_eq_of_mem <;> simp [h]
@[simp] theorem eq_j1 : reorder_j1_j2 j1 j2 j = j1 ↔ j = 0 := by
  rw [← (reorder_j1_j2 j1 j2).apply_eq_iff_eq (x := j), app_0 h]

@[simp] theorem app_1  : reorder_j1_j2 j1 j2 1 = j2 := by
  unfold reorder_j1_j2; apply Equiv.setAll_eq_of_mem <;> simp [h]
@[simp] theorem eq_j2 : reorder_j1_j2 j1 j2 j = j2 ↔ j = 1 := by
  rw [← (reorder_j1_j2 j1 j2).apply_eq_iff_eq (x := j), app_1 h]

end reorder_j1_j2

/-- The automorphism which moves v₁ to ⟨0,[0*]⟩ and v₂ to ⟨1,[0,1,0*]⟩,
assuming v₁ and v₂ have the same bits at j ≠ 0 and the same colors at j ≠ 1. -/
def auto {n s} (v₁ v₂ : KVertex (n+2) (s+2)) : KAuto (n+2) (s+2) :=
  (KAuto.flip v₁.bv)
  |>.trans (KAuto.permute fun j =>
    if j = 1 then
      Equiv.Perm.setAll [(v₁.colors[j], 0), (v₂.colors[j], 1)]
    else
      Equiv.Perm.setAll [(v₁.colors[j], 0)]
  )

section auto
variable {v₁ v₂ : KVertex (n+2) (s+2)}
      (h : ∀ j (h : j < n+2),
          (j ≠ 0 ↔ v₁.bv[j] = v₂.bv[j]) ∧
          (j ≠ 1 ↔ v₁.colors[j] = v₂.colors[j]))
include h

theorem auto_v₁ : (auto v₁ v₂).toFun v₁ = ⟨0, c0_colors⟩ := by
  ext1
  · unfold auto; simp [KVertex.bv_flip]
  · ext1 j hj
    specialize h j hj
    simp [auto, KVertex.colors_permute]
    split <;> (apply Equiv.Perm.setAll_eq_of_mem <;> simp_all [Fin.ext_iff])

theorem auto_v₂ : (auto v₁ v₂).toFun v₂ = ⟨1, c1_colors⟩ := by
  ext1
  · apply BitVec.eq_of_getElem_eq
    intro j hj
    specialize h j hj
    replace h := h.1
    unfold auto; simp [KVertex.bv_flip]
    by_cases j = 0 <;> aesop
  · ext1 j hj
    specialize h j hj
    replace h := h.2
    unfold auto; simp [KVertex.colors_permute, Vector.mkVector]
    if hj : j = 1 then
      simp [hj, Array.getElem_append]
      apply Equiv.setAll_eq_of_mem
      case is_distinct => simpa [hj] using h
      case os_distinct => simp
      simp
    else
      simp [hj] at h
      simp [← Fin.val_eq_val ⟨j,_⟩, hj, h, Array.getElem_append]
      apply Equiv.setAll_eq_of_mem <;> simp

end auto

theorem ofClique {n s} (k : KClique (n+2) (s+2)) (h : conjectureIn (n+1))
  : Nonempty (TwoCubes n s) := by
  have ⟨a, a_mem, b, b_mem, j₁, j₂, hne, same_on⟩ := pick_pair k h
  -- apply the reordering automorphism to get vs2, k2, a2, b2
  let k2 := k.map (KAuto.reorder <| reorder_j1_j2 j₁ j₂)
  let a2 := (KAuto.reorder (reorder_j1_j2 j₁ j₂)).toFun a
  let b2 := (KAuto.reorder (reorder_j1_j2 j₁ j₂)).toFun b
  have a2_mem : a2 ∈ k2.val := by apply Finset.mem_map_of_mem; exact a_mem
  have b2_mem : b2 ∈ k2.val := by apply Finset.mem_map_of_mem; exact b_mem
  replace same_on : ∀ (j : ℕ) (h : j < n + 2),
      (j ≠ 0 ↔ a2.bv[j] = b2.bv[j]) ∧
      (j ≠ 1 ↔ a2.colors[j] = b2.colors[j]) := by
    intro j hj
    simp [a2, b2, KVertex.bv_reorder, KVertex.colors_reorder]
    constructor
    · rw [← (same_on _ _).1, not_iff_not, Fin.val_eq_val,
        reorder_j1_j2.eq_j1 hne, ← Fin.val_eq_val]
      rfl
    · rw [← (same_on _ _).2, not_iff_not, Fin.val_eq_val,
        reorder_j1_j2.eq_j2 hne, ← Fin.val_eq_val]
      rfl

  -- apply the "move to all 0s" automorphism to get vs3, k3
  let k3 := k2.map (auto a2 b2)

  -- k3 is the clique we want! just have to prove 0 ↦ 0*, 1 ↦ 0,1,0*
  refine ⟨{kclique := k3, c0 := ?c0, c1 := ?c1}⟩
  case c0 =>
    rw [KClique.get_eq_iff_mem]; simp [k3, KClique.map]
    use a2, a2_mem
    apply auto_v₁; exact same_on
  case c1 =>
    rw [KClique.get_eq_iff_mem]; simp [k3, KClique.map]
    use b2, b2_mem
    apply auto_v₂; exact same_on

/-! ### Useful TwoCubes theorems -/

@[simp] theorem c0_j (tc : TwoCubes n s) {j : Nat} {hj : j < (n+2)}
    : (tc.kclique.get 0#(n+2))[j] = 0 := by
  simpa using congrArg (·[j]) tc.c0

@[simp] theorem c1_j (tc : TwoCubes n s) {j} {hj : j < (n+2)}
    : (tc.kclique.get 1#(n+2))[j] = if j = 1 then 1 else 0 := by
  simpa using congrArg (·[j]) tc.c1


/-- We can reorder columns without affecting the first two cubes,
so long as 0 and 1 aren't reordered. -/
def reorder (f : Equiv.Perm (Fin (n+2)))
      (fixed_0 : f 0 = 0) (fixed_1 : f 1 = 1)
      (tc : TwoCubes n s) : TwoCubes n s where
  kclique := tc.kclique.map (KAuto.reorder f)
  c0 := by
    -- this one is true for any reordering regardless of fixed_0/fixed_1
    ext1 j hj
    simp [KClique.get_map_reorder]
    convert tc.c0_j (j := f ⟨j,hj⟩) (hj := Fin.isLt _)
    apply BitVec.eq_of_getElem_eq; simp
  c1 := by
    -- the bitvec after mapping is still 1
    have : (BitVec.ofFn fun j => (1#(n+2))[(f.symm j).val]) = 1#(n+2) := by
      apply BitVec.eq_of_getElem_eq
      intro j hj
      simp only [BitVec.getElem_ofFn, BitVec.getElem_one, decide_eq_decide]
      conv => lhs; rhs; rw [show 0 = Fin.val (n := n+2) 0 by simp]
      rw [← Fin.ext_iff, Equiv.symm_apply_eq, fixed_0, Fin.ext_iff]
      simp only [Nat.zero_lt_succ, Fin.val_ofNat_of_lt]
    -- therefore...
    ext1 j hj
    simp only [KClique.get_map_reorder, BitVec.ofNat_eq_ofNat, Fin.getElem_fin, Vector.getElem_ofFn]
    conv => enter [1,1,2]; rw [this]
    simp only [tc.c1_j, c1_colors_j]
    congr 1
    conv => lhs; rhs; rw [show 1 = Fin.val (n := n+2) (f 1) by simp [fixed_1]]
    rw [← Fin.ext_iff, Equiv.apply_eq_iff_eq]; simp [Fin.ext_iff]

@[simp] theorem kclique_reorder (tc : TwoCubes n s) :
  (tc.reorder f fixed_0 fixed_1).kclique = tc.kclique.map (KAuto.reorder f) := rfl

/-- We can permute colors without affecting the first two cubes,
so long as 0 is fixed on all columns and 1 is fixed on column 1. -/
def permute (f : Fin (n+2) → Equiv.Perm (Fin (s+2)))
      (fixed_0 : ∀ j, (f j) 0 = 0) (fixed_1 : (f 1) 1 = 1)
      (tc : TwoCubes n s) : TwoCubes n s where
  kclique := tc.kclique.map (KAuto.permute f)
  c0 := by
    ext1 j hj
    simp [KClique.get_map_permute]
    apply fixed_0
  c1 := by
    ext j hj
    simp [KClique.get_map_permute]
    if h : j = 1 then
      simp [h, fixed_1]
    else
      simp [h, fixed_0]

@[simp] theorem kclique_permute (tc : TwoCubes n s) :
  (tc.permute f fixed_0 fixed_1).kclique = tc.kclique.map (KAuto.permute f) := rfl

/-- We can swap two neighboring indices without affecting the first two cubes,
so long as the swap is in column > 2 and the color is not 0. -/
def flipAt (j : Fin (n+2)) (k : Fin (s+2)) (j_ge : j.val ≥ 2) (k_ne_0 : k ≠ 0)
      (tc : TwoCubes n s) : TwoCubes n s where
  kclique := tc.kclique.map (KAuto.flipAt j k)
  c0 := by
    ext1 j' hj'
    simp [KClique.get_map_flipAt, k_ne_0.symm]
  c1 := by
    ext j' hj'
    simp [KClique.get_map_flipAt, show j.val ≠ 1 by omega, k_ne_0.symm]

@[simp] theorem kclique_flipAt (tc : TwoCubes n s) :
  (tc.flipAt j k j_ge k_ne_0).kclique = tc.kclique.map (KAuto.flipAt j k) := rfl

end TwoCubes



private lemma bv_3_getElem (n j : Nat) (h : j < n)
    : (BitVec.ofNat n 3)[j] = decide (j = 0 ∨ j = 1) := by
  simp [BitVec.getElem_ofNat]
  match j with
  | 0 => simp
  | 1 => simp [Nat.testBit_succ]
  | j+2 => simp [Nat.testBit_succ]

private lemma bv_3_eq_above_2 (n j : Nat) (h : j < n) (j_ge : j ≥ 2) :
  (BitVec.ofNat n 3)[j] = false := by
  rw [bv_3_getElem]; simp; omega

private lemma swap_preserves_earlier {a b : Fin n} (hab : a ≤ b) (hia : i < a) :
      Equiv.swap a b i = i := by
  apply Equiv.swap_apply_of_ne_of_ne
  · exact Fin.ne_of_lt hia
  · apply Fin.ne_of_lt; exact Fin.lt_of_lt_of_le hia hab

private lemma swap_eq_earlier_iff {a b : Fin n} (hab : a ≤ b) (hia : i < a) :
      ∀ j, Equiv.swap a b j = i ↔ j = i := by
  intro j
  rw [Equiv.swap_apply_eq_iff, swap_preserves_earlier hab hia]

private lemma swap_later_stays_later (a b : Fin n) (h : a ≤ b) :
      ∀ i ≥ a, Equiv.swap a b i ≥ a := by
  intro i hi
  rw [Equiv.swap_apply_def]
  aesop

private lemma swap_at_least_stays_at_least (a b : Fin n) (hab : a ≤ b) {k} (hk : k < a) :
      ∀ i ≥ k, Equiv.swap a b i ≥ k := by
  intro i hi
  by_cases h : i < a
  case pos => rw [swap_preserves_earlier hab h]; exact hi
  case neg =>
    simp at h
    have := swap_later_stays_later a b hab i h
    omega

private lemma three_lt : 3 < 2^(n+2) :=
  Nat.lt_of_lt_of_le (m := 2^2) (by simp)
    (Nat.pow_le_pow_right (by decide) (by simp))

private lemma seven_lt : 7 < 2^(n+3+2) := by
    apply Nat.lt_of_lt_of_le (m := 32); decide
    simp [Nat.pow_add, Nat.mul_assoc]; apply Nat.le_mul_of_pos_left
    exact Nat.two_pow_pos n

private lemma eleven_lt : 11 < 2^(n + 3 + 2) := by
  apply Nat.lt_of_lt_of_le (m := 2^5)
  · decide
  · apply Nat.pow_le_pow_right
    · decide
    · omega

private lemma nineteen_lt : 19 < 2^(n + 3 + 2) := by
  apply Nat.lt_of_lt_of_le (m := 2^5)
  · decide
  · apply Nat.pow_le_pow_right
    · decide
    · omega

private lemma three_xor_four : 3#(n+3+2) ^^^ 4#(n+3+2) = 7#(n+3+2) := by
  simp [bv_toNat]
  repeat (
    rw [Nat.mod_eq_of_lt <|
      Nat.lt_of_lt_of_le (m := 2^5) (by decide) (Nat.pow_le_pow_right (by decide) (by omega)) ]
  )
  decide

private lemma three_xor_eight : 3#(n+3+2) ^^^ 8#(n+3+2) = 11#(n+3+2) := by
  simp [bv_toNat]
  repeat (
    rw [Nat.mod_eq_of_lt <|
      Nat.lt_of_lt_of_le (m := 2^5) (by decide) (Nat.pow_le_pow_right (by decide) (by omega)) ]
  )
  decide


/-! ### First (Nontrivial) nonzero element in c3

In this section we show that given `c0` and `c1` from `TwoCubes`,
`c3` must start with `⟨0,1⟩` and must have another nonzero element at `j ≥ 2`.

Then, we can reorder columns to get `c3[2] ≠ 0`.
-/
section first_nonzero

namespace TwoCubes
variable (tc : TwoCubes n s)

theorem c3_1 : (tc.kclique.get 3#(n+2))[1] = 1 := by
  have := tc.kclique.get_adj_one_diff (i₁ := 1) (i₂ := 3) (j₁ := 1)
      (by simp [bv_toNat]; decide)
      (by simp [bv_toNat]; rintro ⟨(_|_|_),_⟩ <;> simp [Nat.testBit_succ])
  replace this := this.1
  rw [tc.c1, eq_comm] at this
  simpa [Array.getElem_append] using this

theorem c3_0 : (tc.kclique.get 3#(n+2))[0] = 0 := by
  have := tc.kclique.get_adj (i₁ := 0) (i₂ := 3)
      (by simp [bv_toNat, Nat.pow_add, Nat.mul_comm _ 4, Nat.mod_mul])
  rcases this with ⟨⟨j1,w1⟩,bs_ne_at_j1,cs_eq_at_j1,-⟩
  dsimp at *

  -- s-gap is < 2 because 0 and 3 are the same above that
  have : j1 < 2 := by
    rcases j1 with (_|_|_) <;> try decide
    revert bs_ne_at_j1
    simp [bv_toNat]
    simp +contextual [Nat.testBit_succ, Nat.testBit_one_eq_true_iff_self_eq_zero]

  -- s-gap cannot be at 1 because we already assigned c3[1] to 1
  have : j1 ≠ 1 := by
    have := congrArg (·[1]) tc.c0
    have := c3_1 tc
    rintro rfl; simp_all

  -- only option left for s-gap is 0
  have : j1 = 0 := by omega

  subst this
  rw [← cs_eq_at_j1]
  simp only [TwoCubes.c0_j]

/-- c3 must have a nonzero element at j ≥ 2-/
theorem c3_has_nonzero : ∃ j₂ : Fin _, j₂.val ≥ 2 ∧ (tc.kclique.get 3)[j₂] ≠ 0 := by
  -- since c1 and c3 are only diff at `j₁ = 1`, the colors must differ at another place
  have := tc.kclique.get_adj_one_diff (i₁ := 1) (i₂ := 3) (j₁ := 1)
      (by simp [bv_toNat]; decide)
      (by simp [bv_toNat]; rintro ⟨(_|_|_),_⟩ <;> simp [Nat.testBit_succ])
  rcases this with ⟨-,j2,js_ne,h2⟩
  -- the diff can't be 0 because we already know c1[0] = c3[0]
  have j2_ne_0 : j2 ≠ 0 := by rintro rfl; revert h2; rw [tc.c1]; simp [c3_0, Array.getElem_append]
  have j2_ge_2 : ¬ j2.val < 2 := (by simp_all [Fin.ext_iff]; omega)
  use j2, (by omega)
  contrapose! h2
  rw [tc.c1]
  simp_all [Fin.ext_iff]

/-- We can always apply an automorphism to get a clique with c3[2] ≠ 0 -/
theorem c3_2 (tc : TwoCubes (n+3) s) : ∃ tc' : TwoCubes (n+3) s, (tc'.kclique.get 3)[2] ≠ 0 := by
  have ⟨j₂, j₂_ge, spec⟩ := c3_has_nonzero tc
  -- move column j₂ to 2
  use tc.reorder (Equiv.swap ⟨2,by omega⟩ j₂) ?fixed_0 ?fixed_1
  case fixed_0 | fixed_1 =>
    apply swap_preserves_earlier
    · assumption
    · simp [Fin.lt_def]

  -- the new c3[2] should be the old c3[j₂]
  convert spec; clear spec
  -- rewriting some definitions, we really just need to show the swap keeps 3 at 3
  rw [TwoCubes.kclique_reorder, KClique.get_map_reorder, Vector.getElem_ofFn, Equiv.swap_apply_left]
  congr

  apply BitVec.eq_of_getElem_eq; intro j hj
  simp [bv_3_getElem, Fin.val_eq_iff_lt_and_eq]
  rw [Bool.eq_iff_iff]; simp
  iterate 2 ( rw [swap_eq_earlier_iff j₂_ge (by simp [Fin.lt_def])] )
  simp [Fin.ext_iff]

end TwoCubes
end first_nonzero

/-! ### Second (Nontrivial) nonzero element in c3

First we show that `c7` must start with `⟨0,1,c3[2]⟩`,
and must differ from `c3` at some column `j ≥ 3` (ie `c7[j] ≠ c3[j]`).

Then, we reorder `j` to 3.
If `c3[3]` is nonzero we are done; otherwise, we know `c7[3] ≠ 0`
so we flip `c3` and `c7` on column 2 to get the nonzero into `c3`.
-/
section second_nonzero

namespace TwoCubes
variable (tc : TwoCubes (n+3) s)

/- we know c7 has s gap with c3 at 2 -/
theorem c7_2 : (tc.kclique.get 7)[2] = (tc.kclique.get 3)[2] := by
  apply And.left
  apply tc.kclique.get_adj_one_diff 2
  · simp [bv_toNat]; decide
  · rintro ⟨j, hj⟩; simp [bv_toNat, hj]
    rcases j with (_|_|_|_) <;> simp [Nat.testBit_succ]
    rfl

variable (c3_2 : (tc.kclique.get 3)[2] ≠ 0) include c3_2

/- therefore c7 has s gap with c1 at 1 -/
theorem c7_1 : (tc.kclique.get 7)[1] = 1 := by
  have ⟨⟨j₁,hj⟩, bit_diff, h, dont_care⟩ :=
    tc.kclique.get_adj (i₁ := 7) (i₂ := 1)
      (by simp [bv_toNat, Nat.mod_eq_of_lt, seven_lt])
  clear dont_care
  simp [bv_toNat, hj] at bit_diff
  -- 0 the bits are not diff, 2 the colors are already not zero, 3+ the bits are not diff
  match j₁ with
  | 0 => simp at bit_diff
  | 1 => have := tc.c1_j (hj := hj); simp_all
  | 2 => have := c7_2 tc; simp_all
  | n+3 => simp [Nat.testBit_succ] at bit_diff

/- therefore c7 has s gap with c0 at 0 -/
theorem c7_0 : (tc.kclique.get 7)[0] = 0 := by
  have ⟨⟨j₁,hj⟩, bit_diff, h, dont_care⟩ := tc.kclique.get_adj (i₁ := 7) (i₂ := 0) (by simp [bv_toNat, Nat.mod_eq_of_lt, seven_lt])
  clear dont_care
  simp [bv_toNat, hj] at bit_diff
  -- 0 the bits are not diff, 2 the colors are already not zero, 3+ the bits are not diff
  match j₁ with
  | 0 => have := tc.c0_j (hj := hj); simp_all
  | 1 => have := c7_1 tc c3_2; simp_all
  | 2 => have := c7_2 tc; simp_all
  | n+3 => simp [Nat.testBit_succ] at bit_diff

/- and there is another nonzero element in c7 since it is different from c3 -/
theorem c7_diff_c3 : ∃ j₂ : Fin _, j₂.val ≥ 3 ∧ (tc.kclique.get 7)[j₂.val] ≠ (tc.kclique.get 3)[j₂.val] := by
  -- since c7 and c3 are only diff at `j₁ = 2`, the colors must differ at another place
  have := tc.kclique.get_adj_one_diff (i₁ := 7) (i₂ := 3) (j₁ := ⟨2, by omega⟩)
      (by simp [bv_toNat]; decide)
      (by simp [bv_toNat]; rintro ⟨(_|_|_|_),_⟩ <;> simp [Nat.testBit_succ])
  rcases this with ⟨-,⟨j2,hj⟩,js_ne,h2⟩
  -- the diff can't be 0 or 1 because we already know c7[0] = c3[0] and c7[1] = c3[1]
  match j2 with
  | 0 => have := c7_0 tc c3_2; have := c3_0 tc; simp_all
  | 1 => have := c7_1 tc c3_2; have := c3_1 tc; simp_all
  | 2 => contradiction
  | j2+3 =>
    use ⟨j2+3, hj⟩, (by simp)
    simpa using h2

seal BitVec.ofNat in
theorem c3_3 : ∃ tc' : TwoCubes (n+3) s, (tc'.kclique.get 3)[2] ≠ 0 ∧ (tc'.kclique.get 3)[3] ≠ 0 := by
  have ⟨j₂, j₂_ge_3, h_ne_at_j2⟩ := c7_diff_c3 tc c3_2
  -- we move j₂ to 3
  let tc' : TwoCubes _ _ := tc.reorder (Equiv.swap ⟨3,by omega⟩ j₂) ?fixed_0 ?fixed_1
  case fixed_0 | fixed_1 =>
    apply swap_preserves_earlier
    · simp [Fin.le_def, j₂_ge_3]
    · simp [Fin.lt_def]

  -- c3_2 still holds
  replace c3_2 : (tc'.kclique.get 3)[2] ≠ 0 := by
    unfold tc'
    simp [KClique.get_map_reorder]
    convert c3_2
    · apply BitVec.eq_of_getElem_eq; intro j hj
      simp; rw [swap_3_eq_3]; simpa using j₂_ge_3
    · rw [swap_preserves_earlier j₂_ge_3 (by simp)]

  -- and now h_ne_at_j2 talks about column 3!
  replace h_ne_at_j2 : (tc'.kclique.get 7)[3] ≠ (tc'.kclique.get 3)[3] := by
    unfold tc'
    simp [KClique.get_map_reorder]
    convert h_ne_at_j2
    · apply BitVec.eq_of_getElem_eq; intro j hj; simp
      rw [swap_7_eq_7]; simpa using j₂_ge_3
    · apply BitVec.eq_of_getElem_eq; intro j hj; simp
      rw [swap_3_eq_3]; simpa using j₂_ge_3

  clear_value tc'; clear tc

  -- if we already are nonzero then woohoo!
  if h : (tc'.kclique.get 3)[3] ≠ 0 then use tc'
  -- otherwise we're gonna move c7 to c3 via `flipAt`
  else
  rw [not_ne_iff] at h; rw [h] at h_ne_at_j2; clear h
  use tc'.flipAt ⟨2, by omega⟩ (tc'.kclique.get 3)[2] (by simp) c3_2

  have three_xor_four := three_xor_four (n := n)
  have c72 := c7_2 tc'
  simp_all [KClique.get_map_flipAt]; exact c3_2

where
  swap_3_eq_3 {j₂ : Fin (n+3+2)} {j₂_ge_3 : j₂ ≥ ⟨3,by omega⟩}
    (j : Fin _)
    : (3#(n + 3 + 2))[(((Equiv.swap (⟨3, by omega⟩ : Fin _) j₂) j) : Nat)] = (3#(n+3+2))[j.val] := by
    if j.val < 3 then
      conv => enter [1,2]; rw [swap_preserves_earlier j₂_ge_3 (by simp [Fin.lt_def, *])]
    else
      have := swap_later_stays_later ⟨3, by omega⟩ j₂ j₂_ge_3 j (by simp [Fin.le_def]; omega)
      simp [Fin.le_def] at this
      rw [Bool.eq_iff_iff]; simp [bv_3_getElem]
      omega

  swap_7_eq_7 {j₂ : Fin (n+3+2)} {j₂_ge_3 : j₂ ≥ ⟨3,by omega⟩}
    (j : Fin _)
    : (7#(n + 3 + 2))[((Equiv.swap (⟨3, by omega⟩ : Fin _) j₂) j : Nat)] = (7#(n+3+2))[j.val] := by
    rcases j with ⟨j,hj⟩
    if j_lt_3 : j < 3 then
      simp
      conv => enter [1,2]; rw [swap_preserves_earlier j₂_ge_3 (by simp [Fin.lt_def, *])]
    else
      have x_ge := swap_later_stays_later ⟨3, by omega⟩ j₂ j₂_ge_3 ⟨j,hj⟩ (by simp [Fin.le_def]; omega)
      generalize ((Equiv.swap _ _) (⟨j,hj⟩ : Fin _)) = x at *
      rcases x with ⟨x,_⟩
      simp [Fin.le_def] at x_ge j_lt_3 ⊢
      simp [BitVec.getElem_eq_testBit_toNat, *]
      rw [← Nat.sub_add_cancel x_ge, ← Nat.sub_add_cancel j_lt_3]
      simp [Nat.testBit_succ]

end TwoCubes
end second_nonzero

/-! ### Third (Nontrivial) nonzero element in c3

This is the most complicated argument in the file.

At this point the clique looks like:

```
  j = 0   1   2   3   4
c0  | 0 | 0 | 0 | 0 | 0
c1  |_0_| 1 | 0 | 0 | 0
c3  |_0_|_1_| x | y | ?
c7  |_0_|_1_|_x_| ? | ?
c11 |_0_|_1_| ? |_y_| ?
```

Here `x` and `y` are nonzero, and underlines indicate the true bits in each index.
The `c11[0]`, `c11[1]`, and `c11[3]` claims are proven below.

Note that in order for `c7` and `c11` to be adjacent,
we have an `s`-gap at either 2 or 3, meaning either `c11[2] = x` or `c7[3] = y`.
Either way, one of these indices matches `c3` on the first four colors,
therefore they must have a difference at `j ≥ 4`.

We reorder `j` to 4. Note that after reordering,
we still have one of `c7` and `c11` matching `c3` on the first four colors.

If `c3[4]` is nonzero we are done.
Otherwise, the index `i ∈ [7,11]` that matches `c3` has `ci[4] ≠ 0`.
So, we flip `c3` and `ci` at the appropriate column to get our third nonzero in `c3`.
-/

section third_nonzero

namespace TwoCubes
variable (tc : TwoCubes (n+3) s)

/- we know c11 has s gap with c3 at 3 -/
theorem c11_3 : (tc.kclique.get 11)[3] = (tc.kclique.get 3)[3] := by
  refine tc.kclique.get_adj_one_diff 3 ?_ ?_ |>.left
  · simp [bv_toNat]; decide
  · rintro ⟨j, hj⟩; simp [bv_toNat, hj, Fin.ext_iff]
    rcases j with (_|_|_|_|_) <;> simp [Nat.testBit_succ]

variable (c3_3 : (tc.kclique.get 3)[3] ≠ 0) include c3_3

/- therefore c7 has s gap with c1 at 1 -/
theorem c11_1 : (tc.kclique.get 11)[1] = 1 := by
  have ⟨⟨j₁,hj⟩, bit_diff, h, dont_care⟩ :=
    tc.kclique.get_adj (i₁ := 11) (i₂ := 1)
      (by simp [bv_toNat, Nat.mod_eq_of_lt, eleven_lt])
  clear dont_care
  simp [bv_toNat, hj] at bit_diff
  -- 3 the colors are already not zero, and the other bits are not diff
  match j₁ with
  | 1 => have := tc.c1_j (hj := hj); simp_all
  | 3 => have := c11_3 tc; simp_all
  | 0 | 2 | n+4 =>
    simp [Nat.testBit_succ] at bit_diff

/- therefore c7 has s gap with c0 at 0 -/
theorem c11_0 : (tc.kclique.get 11)[0] = 0 := by
  have ⟨⟨j₁,hj⟩, bit_diff, h, dont_care⟩ :=
    tc.kclique.get_adj (i₁ := 11) (i₂ := 0)
      (by simp [bv_toNat, Nat.mod_eq_of_lt, eleven_lt])
  clear dont_care
  simp [bv_toNat, hj] at bit_diff
  -- 2 the bits are not diff, 1 and 3 the colors are already not eq, 4+ the bits are not diff
  match j₁ with
  | 0 => have := tc.c0_j (hj := hj); simp_all
  | 1 => have := c11_1 tc c3_3; simp_all
  | 3 => have := c11_3 tc; simp_all
  | 2 | n+4 =>
    simp [Nat.testBit_succ] at bit_diff

variable (c3_2 : (tc.kclique.get 3)[2] ≠ 0) include c3_2

seal BitVec.ofNat in
/-- Either `c7` or `c11` are identical to `c3` on `j < 4` and therefore have a diff at some `j ≥ 4`. -/
theorem c7_or_11_diff_c3 :
    ∃ i : BitVec (n+3+2), (i = 7 ∨ i = 11) ∧ (∀ j (h : j < 4), (tc.kclique.get i)[j] = (tc.kclique.get 3#(_))[j]) ∧
    ∃ j : Fin _, j.val ≥ 4 ∧ (tc.kclique.get i)[j] ≠ (tc.kclique.get 3)[j] := by
  -- c7_2 and c11_3 are equiv to c3_2 and c3_3
  have c7_2 := c7_2 tc
  have c11_3 := c11_3 tc
  -- then, b/c c7 and c11 are adjacent, either c7_3 = c3_3 or c11_2 = c3_2
  have : (tc.kclique.get 7)[3] = (tc.kclique.get 3)[3] ∨
        (tc.kclique.get 11)[2] = (tc.kclique.get 3)[2] := by
    have ⟨j1,bv_ne_at_j1,cs_eq_at_j1,j2⟩ :=
      tc.kclique.get_adj (i₁ := 7) (i₂ := 11)
        (by simp [bv_toNat, Nat.mod_eq_of_lt, seven_lt, eleven_lt])
    clear j2
    -- we need the clear * - so that omega does not pull j1 into the proof term
    replace bv_ne_at_j1 : j1 = ⟨2,by clear * -; omega⟩ ∨ j1 = ⟨3, by clear * -; omega⟩ := by
      rcases j1 with ⟨j1,_⟩
      match j1 with
      | 2 | 3 => simp
      | 0 | 1 | _j1+4 =>
        simp [bv_toNat, Nat.mod_eq_of_lt, seven_lt, eleven_lt, Nat.testBit_succ] at bv_ne_at_j1
    rcases bv_ne_at_j1 with (rfl|rfl)
    · right; rw [← c7_2]; exact cs_eq_at_j1.symm
    · left; rw [← c11_3]; exact cs_eq_at_j1
  -- so either c7 or c11 are equal to c3 on j < 4
  replace this : ∃ i : BitVec _, (i = 7 ∨ i = 11) ∧
      (∀ j (h : j < 4), (tc.kclique.get i)[j] = (tc.kclique.get 3#(_))[j]) := by
    rcases this with (woop|woop)
    · refine ⟨_, .inl rfl, fun j h => ?_⟩
      rcases h with (_|_|_|_|h)
      · exact woop
      · exact c7_2
      · rw [c7_1 tc c3_2, c3_1 tc]
      · rw [c7_0 tc c3_2, c3_0 tc]
      · nomatch h
    · refine ⟨_, .inr rfl, fun j h => ?_⟩
      rcases h with (_|_|_|_|h)
      · exact c11_3
      · exact woop
      · rw [c11_1 tc c3_3, c3_1 tc]
      · rw [c11_0 tc c3_3, c3_0 tc]
      · nomatch h

  rcases this with ⟨i,i_cases, i_eq_c3_lt_4⟩

  have ⟨j1,i_diff_j1⟩ : ∃ j1, i ^^^ 3#(_) = .oneAt j1 := by
      rcases i_cases with (rfl|rfl)
      · use 2; simp [bv_toNat, Nat.mod_eq_of_lt, seven_lt, three_lt]
      · use 3; simp [bv_toNat, Nat.mod_eq_of_lt, eleven_lt, three_lt]

  -- whichever is equivalent, has a difference with c3 at j ≥ 4 bc adjacent
  have ⟨j,j_ge_4,diff_j⟩ : ∃ j : Fin (n+3+2), j.val ≥ 4 ∧
      (tc.kclique.get i)[j] ≠ (tc.kclique.get 3#(_))[j] := by
    have := tc.kclique.get_adj_of_xor_eq (i₁ := i) (i₂ := 3) j1 i_diff_j1
    rcases this with ⟨cs_eq_j1,j2,js_ne,ne_j2⟩
    use j2
    constructor
    · by_contra h; specialize i_eq_c3_lt_4 j2 (by omega); contradiction
    · exact ne_j2
  clear i_diff_j1 j1

  use i, i_cases, i_eq_c3_lt_4, j, j_ge_4, diff_j

seal BitVec.ofNat in
theorem c7_or_11_diff_at_4 :
  ∃ tc' : TwoCubes (n+3) s,
    (tc'.kclique.get 3)[2] ≠ 0 ∧ (tc'.kclique.get 3)[3] ≠ 0 ∧
    ∃ i : BitVec _, (i = 7 ∨ i = 11) ∧
    (∀ j (h : j < 4), (tc'.kclique.get i)[j] = (tc'.kclique.get 3#(_))[j]) ∧
    (tc'.kclique.get i)[4] ≠ (tc'.kclique.get 3)[4] := by
  have ⟨i, i_cases, i_eq_c3, j, j_ge, spec⟩ := c7_or_11_diff_c3 tc c3_3 c3_2

  -- let's move `j` to `4`!

  -- 3 isn't going to move when we swap `4` with `j`
  have mapped_3_eq_3 : (BitVec.ofFn fun j_1 => (3#(_))[(Equiv.swap ⟨4,by omega⟩ j) j_1]) = 3 := by
    apply BitVec.eq_of_getElem_eq; intro j' hj'
    simp only [Equiv.symm_swap, BitVec.getElem_ofFn]
    by_cases j'_lt : j' < 2
    case pos =>
      have := swap_preserves_earlier (a := ⟨4,by omega⟩) (b := j) (i := ⟨j',hj'⟩)
        (by simpa using j_ge) (by simp [Fin.lt_def]; omega)
      conv => enter [1,2]; rw [this]
      simp
    case neg =>
      replace j'_lt : j' ≥ 2 := by omega
      simp only [BitVec.ofNat_eq_ofNat, Fin.getElem_fin]
      rw [bv_3_eq_above_2 _ _ _ j'_lt, bv_3_eq_above_2]
      have := swap_at_least_stays_at_least (a := 4) (b := j) (k := 2) (i := ⟨j',hj'⟩)
        (hab := by simpa using j_ge) (hk := by simp [Fin.lt_def]) (by simpa using j'_lt)
      simpa using this

  have mapped_i_eq_i : (BitVec.ofFn fun j_1 => i[(Equiv.swap ⟨4,by omega⟩ j) j_1]) = i := by
    have i_bits_false : ∀ (j') (hj' : j' < n+3+2), j' ≥ 4 → i[j'] = false := by
      intro j' hj' h
      conv => lhs; arg 2; rw [← Nat.sub_add_cancel h]
      rcases i_cases with (rfl|rfl) <;> simp [bv_toNat] <;> simp [Nat.testBit_succ]

    apply BitVec.eq_of_getElem_eq; intro j' hj'; simp
    if h : j' < 4 then
      congr; rw [swap_preserves_earlier (by simpa using j_ge) (by simpa [Fin.lt_def] using h)]
    else
      have : j' ≥ 4 := by omega
      have := swap_later_stays_later ⟨4,by omega⟩ j (by simpa using j_ge) ⟨j',hj'⟩ (this)
      simp_all [Fin.le_def]

  refine ⟨tc.reorder (Equiv.swap ⟨4,by omega⟩ j) ?fixed_0 ?fixed_1, ?c3_2, ?c3_3,
          i, i_cases, ?i_eq_c3, ?i_ne_c3⟩
  case fixed_0 | fixed_1 =>
    apply swap_preserves_earlier
    · simpa using j_ge
    · simp [Fin.lt_def]

  -- c3[2] still ≠ 0
  case c3_2 =>
    rw [tc.kclique_reorder, KClique.get_map_reorder, Vector.getElem_ofFn, Fin.getElem_fin]
    convert c3_2
    rw [Fin.val_eq_iff_lt_and_eq]; use (by simp)
    rw [swap_eq_earlier_iff j_ge (by simp [Fin.lt_def])]
  -- c3[3] still ≠ 0
  case c3_3 =>
    rw [tc.kclique_reorder, KClique.get_map_reorder, Vector.getElem_ofFn, Fin.getElem_fin]
    convert c3_3
    rw [Fin.val_eq_iff_lt_and_eq]; use (by simp)
    rw [swap_eq_earlier_iff j_ge (by simp [Fin.lt_def])]

  -- for `j' < 4`, ci[j'] is still equal to c3[j']
  case i_eq_c3 =>
    intro j' hj'
    specialize i_eq_c3 j' hj'
    have := swap_preserves_earlier (a := ⟨4,by omega⟩) (b := j) (i := ⟨j',by omega⟩)
      (by simpa using j_ge) (by simpa [Fin.lt_def] using hj')
    simp only [TwoCubes.kclique_reorder, KClique.get_map_reorder, Equiv.symm_swap,
      Vector.getElem_ofFn, this]
    simp_all

  -- and ci[4] is not equal to c3[4]
  case i_ne_c3 =>
    simp [KClique.get_map_reorder, Equiv.swap_apply_left]
    simp_all

seal BitVec.ofNat in
/-- We can further apply automorphisms to get a clique with c3[4] ≠ 0 -/
theorem c3_4 : ∃ tc' : TwoCubes (n+3) s,
      (tc'.kclique.get 3)[2] ≠ 0 ∧ (tc'.kclique.get 3)[3] ≠ 0 ∧ (tc'.kclique.get 3)[4] ≠ 0 := by
  -- by previous lemma, c7 or c11 have a diff with c3
  have := c7_or_11_diff_at_4 tc c3_3 c3_2
  clear c3_3 c3_2 tc

  rcases this with ⟨tc, c3_2, c3_3, i, i_cases, i_eq_c3, i_ne_c3⟩

  -- if c3_4 ≠ 0 then we are done already
  if c3_4 : (tc.kclique.get 3)[4] ≠ 0 then use tc else
  push_neg at c3_4; rw [c3_4] at i_ne_c3; clear c3_4

  -- otherwise we swap c7/c11 to c3

  rcases i_cases with (rfl|rfl)
  case inl =>
    -- swap c7 with c3
    use tc.flipAt ⟨2, by omega⟩ (tc.kclique.get 3)[2] (by simp) c3_2
    simp at i_eq_c3
    simp [KClique.get_map_flipAt, three_xor_four, i_eq_c3]
    exact ⟨c3_2, c3_3, i_ne_c3⟩
  case inr =>
    -- swap c11 with c3
    use tc.flipAt ⟨3, by omega⟩ (tc.kclique.get 3)[3] (by simp) c3_3
    simp at i_eq_c3
    simp [KClique.get_map_flipAt, three_xor_eight, i_eq_c3]
    exact ⟨c3_2, c3_3, i_ne_c3⟩

end TwoCubes
end third_nonzero


/-! ### Fully symmetry-broken c3 -/

structure ThreeCubes (n s) extends TwoCubes (n+3) s where
  c3 : ∀ i : Fin (n+5), i.val ∈ [2,3,4] → (kclique.get 3)[i] = 1

namespace ThreeCubes

theorem ofTwoCubes (tc : TwoCubes (n+3) s) : Nonempty (ThreeCubes n s) := by
  -- We can get a clique with `c3[2], c3[3], c3[4] ≠ 0`
  have ⟨tc2,h2⟩ := tc.c3_2
  have ⟨tc3,h3⟩ := tc2.c3_3 h2
  have ⟨tc4,h4⟩ := tc3.c3_4 h3.2 h3.1
  clear! tc tc2 tc3
  -- just summarizing that info in the way we want for `ThreeCubes`
  replace h4 : ∀ i : Fin (n+5), i.val ∈ [2,3,4] → (tc4.kclique.get 3)[i] ≠ 0 := by
    rintro ⟨i,hi⟩ h; simp at h
    rcases h with (_|_|_) <;>
      (subst i; first | exact h4.1 | exact h4.2.1 | exact h4.2.2 )
  -- Now we permute colors to make all those nonzero elements *actually* 1
  let tc := tc4.permute
      (fun i =>
        if i.val ∈ [2,3,4] then
          Equiv.Perm.setAll [((tc4.kclique.get 3)[i], 1)]
        else Equiv.refl _)
      ?fixed_0 ?fixed_1
  case fixed_0 =>
    intro j; dsimp; split
    next h =>
      specialize h4 j h
      apply Equiv.Perm.setAll_eq_of_not_mem
      · simpa using h4.symm
      · simp
    · simp
  case fixed_1 => simp

  -- and then show that `c3[2], c3[3], c3[4] = 1` now
  refine ⟨{toTwoCubes := tc, c3 := ?c3}⟩
  case c3 =>
  rintro ⟨i, hi⟩ i_mem_234
  unfold tc; rw [TwoCubes.kclique_permute, KClique.get_map_permute]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, i_mem_234, if_true]
  specialize h4 _ i_mem_234
  apply Equiv.Perm.setAll_eq_of_mem <;> simp

theorem ofClique (clique : KClique (n+5) (s+2)) (h : conjectureIn (n+4)) : Nonempty (ThreeCubes n s) := by
  have ⟨tc⟩ := TwoCubes.ofClique clique h
  exact ofTwoCubes tc

variable (tc : ThreeCubes n s)

theorem c3_2 : (tc.kclique.get 3)[2] = 1 := tc.c3 2 (by simp)
theorem c3_3 : (tc.kclique.get 3)[3] = 1 := tc.c3 3 (by simp)
theorem c3_4 : (tc.kclique.get 3)[4] = 1 := tc.c3 4 (by simp)

theorem c7_0 : (tc.kclique.get 7)[0] = 0 := tc.toTwoCubes.c7_0 (by rw [tc.c3_2]; simp)
theorem c7_1 : (tc.kclique.get 7)[1] = 1 := tc.toTwoCubes.c7_1 (by rw [tc.c3_2]; simp)
theorem c7_2 : (tc.kclique.get 7)[2] = 1 := by rw [tc.toTwoCubes.c7_2]; exact tc.c3_2

theorem c11_0 : (tc.kclique.get 11)[0] = 0 := tc.toTwoCubes.c11_0 (by rw [tc.c3_3]; simp)
theorem c11_1 : (tc.kclique.get 11)[1] = 1 := tc.toTwoCubes.c11_1 (by rw [tc.c3_3]; simp)
theorem c11_3 : (tc.kclique.get 11)[3] = 1 := by rw [tc.toTwoCubes.c11_3]; exact tc.c3_3

/-- s-gap between c3 and c19 must be at 4, thus we know c19[4] = 1 -/
theorem c19_4 : (tc.kclique.get 19)[4] = 1 := by
  rw [← c3_4]
  refine tc.kclique.get_adj_one_diff 4 ?_ ?_ |>.left
  · simp [bv_toNat]; decide
  · rintro ⟨j, hj⟩; simp [bv_toNat, hj, Fin.ext_iff]
    rcases j with (_|_|_|_|_|_) <;> simp [Nat.testBit_succ]

/-- s-gap between c1 and c19 must be at 1, so c19[1] = 1 -/
theorem c19_1 : (tc.kclique.get 19)[1] = 1 := by
  have ⟨⟨j₁,hj⟩, bit_diff, h, dont_care⟩ :=
    tc.kclique.get_adj (i₁ := 19) (i₂ := 1)
      (by simp [bv_toNat, Nat.mod_eq_of_lt, nineteen_lt])
  clear dont_care
  simp [bv_toNat, hj] at bit_diff
  -- we want j₁ = 1. for j₁ = 4, the colors are already ≠, and all other j₁ have same bits
  match j₁ with
  | 1 => have := tc.c1_j (hj := hj); simp_all
  | 4 => have := tc.c19_4; simp_all
  | 0 | 2 | 3 | n+5 =>
    simp [Nat.testBit_succ] at bit_diff

/-- s-gap between c0 and c19 must be at 0, so c19[0] = 0. -/
theorem c19_0 : (tc.kclique.get 19)[0] = 0 := by
  have ⟨⟨j₁,hj⟩, bit_diff, h, dont_care⟩ :=
    tc.kclique.get_adj (i₁ := 19) (i₂ := 0)
      (by simp [bv_toNat, Nat.mod_eq_of_lt, nineteen_lt])
  clear dont_care
  simp [bv_toNat, hj] at bit_diff
  -- we want j₁ = 0. for j₁ ∈ [1, 4], the colors are already ≠, and all other j₁ have same bits
  match j₁ with
  | 0 => have := tc.c0_j (hj := hj); simp_all
  | 1 => have := tc.c19_1; simp_all
  | 4 => have := tc.c19_4; simp_all
  | 2 | 3 | n+5 =>
    simp [Nat.testBit_succ] at bit_diff

end ThreeCubes
