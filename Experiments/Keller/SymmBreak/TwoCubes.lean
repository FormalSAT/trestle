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
  simp [KClique, SimpleGraph.isNClique_iff, K_0_card,
      SimpleGraph.isClique_iff, Set.Pairwise] at K_0_not_clique
  clear K_0_card h
  rcases K_0_not_clique with ⟨⟨i₁,c₁⟩, hv₁, ⟨i₂,c₂⟩, hv₂, hne, hnotadj⟩
  simp [K_0] at hv₁ hv₂; clear K_0
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
  simp [KAdj] at this hnotadj
  -- by def of adjacency, we get a j₁, j₂ in big graph
  rcases this with ⟨⟨j₁,hj₁⟩,is_diff_at_j1,ks_same,⟨j₂,hj₂⟩,js_diff,h⟩
  simp_all
  -- the i's are different at index j₁
  have : j₁ ≠ n+1 := by intro contra; simp [BitVec.getElem_cons, contra] at is_diff_at_j1
  replace hj₁ : j₁ < n+1 := by omega
  simp [BitVec.getElem_cons, this] at is_diff_at_j1
  clear this
  specialize hnotadj ⟨j₁, hj₁⟩ is_diff_at_j1 ks_same
  -- j₂ must be n+1, because vertices in small graph are not adjacent
  by_cases this : j₂ = n+1
  case neg =>
    exfalso
    replace hj₂ : j₂ < n+1 := by omega
    specialize hnotadj ⟨j₂,hj₂⟩
    simp [js_diff] at hnotadj
    simp [BitVec.getElem_cons, Nat.ne_of_lt hj₂, hnotadj.2] at h
    apply h hnotadj.1
  subst this
  simp [BitVec.getElem_cons] at h

  -- Ok! We have all the info we need to fill the goal!
  use ⟨i₁.cons false, k₁⟩, (hk₁ ▸ kclique.get_mem ..),
      ⟨i₂.cons false, k₂⟩, (hk₂ ▸ kclique.get_mem ..),
      ⟨j₁,‹_›⟩, ⟨n+1, by omega⟩
  simp [js_diff]
  rintro j -
  by_cases eq_j1 : j = j₁
  · simp_all [BitVec.getElem_cons]
  · by_cases eq_last : j = n+1
    · simp_all [BitVec.getElem_cons]
    · specialize hnotadj ⟨j, by omega⟩ (by simp; exact Ne.symm eq_j1)
      simp_all [BitVec.getElem_cons]; exact hnotadj.1

/-- The automorphism that reorders any columns `j₁`, `j₂`
to the first and second column, respectively. -/
def reorder (j₁ j₂ : Fin (n+2)) := Equiv.Perm.setAll [(0,j₁), (1,j₂)]

section reorder
variable {j1 j2 : Fin (n+2)} (h : j1 ≠ j2)
include h

@[simp] theorem reorder_0 : reorder j1 j2 0 = j1 := by
  unfold reorder; apply Equiv.setAll_eq_of_mem <;> simp [h]
@[simp] theorem reorder_eq_j1 : reorder j1 j2 j = j1 ↔ j = 0 := by
  rw [← (reorder j1 j2).apply_eq_iff_eq (x := j), reorder_0 h]

@[simp] theorem reorder_1  : reorder j1 j2 1 = j2 := by
  unfold reorder; apply Equiv.setAll_eq_of_mem <;> simp [h]
@[simp] theorem reorder_eq_j2 : reorder j1 j2 j = j2 ↔ j = 1 := by
  rw [← (reorder j1 j2).apply_eq_iff_eq (x := j), reorder_1 h]

end reorder

/-- The automorphism which moves v₁ to ⟨0,[0*]⟩ and v₂ to ⟨1,[0,1,0*]⟩ -/
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
  let k2 := k.map (KAuto.reorder <| reorder j₁ j₂)
  let a2 := (KAuto.reorder (reorder j₁ j₂)).toFun a
  let b2 := (KAuto.reorder (reorder j₁ j₂)).toFun b
  have a2_mem : a2 ∈ k2.val := by apply Finset.mem_map_of_mem; exact a_mem
  have b2_mem : b2 ∈ k2.val := by apply Finset.mem_map_of_mem; exact b_mem
  replace same_on : ∀ (j : ℕ) (h : j < n + 2),
      (j ≠ 0 ↔ a2.bv[j] = b2.bv[j]) ∧
      (j ≠ 1 ↔ a2.colors[j] = b2.colors[j]) := by
    intro j hj
    simp [a2, b2, KVertex.bv_reorder, KVertex.colors_reorder]
    constructor
    · rw [← (same_on _ _).1, not_iff_not, Fin.val_eq_val,
        reorder_eq_j1 hne, ← Fin.val_eq_val]
      rfl
    · rw [← (same_on _ _).2, not_iff_not, Fin.val_eq_val,
        reorder_eq_j2 hne, ← Fin.val_eq_val]
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

@[simp] theorem c0_j (tc : TwoCubes n s) {j : Nat} {hj : j < (n+2)}
    : (tc.kclique.get 0#(n+2))[j] = 0 := by
  simpa using congrArg (·[j]) tc.c0

@[simp] theorem c1_j (tc : TwoCubes n s) {j} {hj : j < (n+2)}
    : (tc.kclique.get 1#(n+2))[j] = if j = 1 then 1 else 0 := by
  simpa using congrArg (·[j]) tc.c1

end TwoCubes


namespace ThreeCubes

private theorem bv_3_getElem (n j : Nat) (h : j < n)
    : (BitVec.ofNat n 3)[j] = decide (j = 0 ∨ j = 1) := by
  simp [BitVec.getElem_ofNat]
  match j with
  | 0 => simp
  | 1 => simp [Nat.testBit_succ]
  | j+2 => simp [Nat.testBit_succ]

theorem swap_preserves_earlier {a b : Fin n} (hab : a ≤ b) (hia : i < a) :
      Equiv.swap a b i = i := by
  apply Equiv.swap_apply_of_ne_of_ne
  · exact Fin.ne_of_lt hia
  · apply Fin.ne_of_lt; exact Fin.lt_of_lt_of_le hia hab

theorem swap_eq_earlier_iff {a b : Fin n} (hab : a ≤ b) (hia : i < a) :
      ∀ j, Equiv.swap a b j = i ↔ j = i := by
  intro j
  rw [Equiv.swap_apply_eq_iff, swap_preserves_earlier hab hia]

theorem swap_later_stays_later (a b : Fin n) (h : a ≤ b) :
      ∀ i ≥ a, Equiv.swap a b i ≥ a := by
  intro i hi
  rw [Equiv.swap_apply_def]
  aesop


section c3
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

end c3

section first_nonzero

/-- We can always apply an automorphism to get a clique with c3[2] ≠ 0 -/
theorem c3_2 (tc : TwoCubes (n+3) s):
    ∃ tc' : TwoCubes (n+3) s, (tc'.kclique.get 3)[2] ≠ 0 := by
  have ⟨j₂, j₂_ge, spec⟩ := c3_has_nonzero tc
  refine ⟨{
    kclique := tc.kclique.map (KAuto.reorder <| Equiv.swap 2 j₂)
    c0 := ?c0
    c1 := ?c1
  }, ?point⟩
  case c0 =>
    simp [KClique.get_map_reorder]
    suffices BitVec.ofFn _ = 0#(n+5) by
      rw (occs := .pos [1]) [this]
      ext; simp
    apply BitVec.eq_of_getElem_eq; simp
  case c1 =>
    rw [KClique.get_map_reorder]
    suffices BitVec.ofFn _ = 1#(n+5) by
      rw [this]
      ext i hi; simp; congr 2
      simp [Fin.val_eq_iff_lt_and_eq]
      rw [swap_eq_earlier_iff j₂_ge (by simp [Fin.lt_def])]
      simp [Fin.ext_iff]
    apply BitVec.eq_of_getElem_eq; intro j hj
    simp [Fin.val_eq_iff_lt_and_eq, Equiv.symm_apply_eq]
    rw [swap_eq_earlier_iff j₂_ge (by simp [Fin.lt_def])]
    simp [Fin.ext_iff]
  case point =>
    -- the new c3[2] should be the old c3[j₂]
    convert spec; clear spec
    simp
    rw (occs := .pos [1]) [KClique.get_map_reorder]
    simp
    congr 2
    apply BitVec.eq_of_getElem_eq; intro j hj
    simp [bv_3_getElem, Fin.val_eq_iff_lt_and_eq]
    rw [Bool.eq_iff_iff]; simp
    iterate 2 ( rw [swap_eq_earlier_iff j₂_ge (by simp [Fin.lt_def])] )
    simp [Fin.ext_iff]

end first_nonzero

section c7
variable (tc : TwoCubes (n+3) s)

theorem seven_lt : 7 < 2^(n+3+2) := by
    apply Nat.lt_of_lt_of_le (m := 32); decide
    simp [Nat.pow_add, Nat.mul_assoc]; apply Nat.le_mul_of_pos_left
    exact Nat.two_pow_pos n

/- we know c7 has s gap with c3 at 2 -/
theorem c7_2 : (tc.kclique.get 7)[2] = (tc.kclique.get 3)[2] := by
  apply And.left
  apply tc.kclique.get_adj_one_diff 2
  · simp [bv_toNat]; decide
  · rintro ⟨j, hj⟩; simp [bv_toNat, hj]
    rcases j with (_|_|_|_) <;> simp [Nat.testBit_succ]
    rfl

variable (h32 : (tc.kclique.get 3)[2] ≠ 0) include h32

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
  | 1 => have := c7_1 tc h32; simp_all
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
  | 0 => have := c7_0 tc h32; have := c3_0 tc; simp_all
  | 1 => have := c7_1 tc h32; have := c3_1 tc; simp_all
  | 2 => contradiction
  | j2+3 =>
    use ⟨j2+3, hj⟩, (by simp)
    simpa using h2

end c7

section second_nonzero

private lemma second_nonzero.swap_3_eq_3 {j₂ : Fin (n+3+2)} {j₂_ge_3 : j₂ ≥ ⟨3,by omega⟩}
    (j : Fin _)
    : (3#(n + 3 + 2))[(((Equiv.swap (⟨3, by omega⟩ : Fin _) j₂) j) : Nat)] = (3#(n+3+2))[j.val] := by
  if j.val < 3 then
    conv => enter [1,2]; rw [swap_preserves_earlier j₂_ge_3 (by simp [Fin.lt_def, *])]
  else
    have := swap_later_stays_later ⟨3, by omega⟩ j₂ j₂_ge_3 j (by simp [Fin.le_def]; omega)
    simp [Fin.le_def] at this
    rw [Bool.eq_iff_iff]; simp [bv_3_getElem]
    omega

private lemma second_nonzero.swap_7_eq_7 {j₂ : Fin (n+3+2)} {j₂_ge_3 : j₂ ≥ ⟨3,by omega⟩}
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


theorem c3_3 (tc : TwoCubes (n+3) s) (h2 : (tc.kclique.get 3)[2] ≠ 0) :
    ∃ tc' : TwoCubes (n+3) s, (tc'.kclique.get 3)[2] ≠ 0 ∧ (tc'.kclique.get 3)[3] ≠ 0 := by
  have ⟨j₂, j₂_ge_3, h_ne_at_j2⟩ := c7_diff_c3 tc h2
  -- we move j₂ to 3, while preserving all the other facts we know about tc
  let tc' : TwoCubes _ _ := {
    kclique := tc.kclique.map (KAuto.reorder <| Equiv.swap ⟨3,by omega⟩ j₂)
    c0 := ?c0
    c1 := ?c1
  }
  case c0 =>
    simp [KClique.get_map_reorder]
    suffices BitVec.ofFn _ = 0#(n+5) by
      rw (occs := .pos [1]) [this]
      ext; simp
    apply BitVec.eq_of_getElem_eq; intro j hj; simp
  case c1 =>
    rw [KClique.get_map_reorder]
    suffices BitVec.ofFn _ = 1#(n+5) by
      rw [this]
      ext i hi; simp; congr 2
      simp [Fin.val_eq_iff_lt_and_eq]
      rw [swap_eq_earlier_iff j₂_ge_3 (by simp [Fin.lt_def])]
      simp [Fin.ext_iff]
    apply BitVec.eq_of_getElem_eq; intro j hj
    simp [Fin.val_eq_iff_lt_and_eq, Equiv.symm_apply_eq]
    rw [swap_eq_earlier_iff j₂_ge_3 (by simp [Fin.lt_def])]
    simp [Fin.ext_iff]

  replace h2 : (tc'.kclique.get 3)[2] ≠ 0 := by
    unfold tc'
    simp [KClique.get_map_reorder]
    convert h2
    · apply BitVec.eq_of_getElem_eq; intro j hj
      simp; rw [second_nonzero.swap_3_eq_3]; simpa using j₂_ge_3
    · rw [swap_preserves_earlier j₂_ge_3 (by simp)]
  replace h_ne_at_j2 : (tc'.kclique.get 7)[3] ≠ (tc'.kclique.get 3)[3] := by
    unfold tc'
    simp [KClique.get_map_reorder]
    convert h_ne_at_j2
    · apply BitVec.eq_of_getElem_eq; intro j hj; simp
      rw [second_nonzero.swap_7_eq_7]; simpa using j₂_ge_3
    · apply BitVec.eq_of_getElem_eq; intro j hj; simp
      rw [second_nonzero.swap_3_eq_3]; simpa using j₂_ge_3

  clear_value tc'; clear tc

  -- if we already are nonzero then woohoo!
  if h : (tc'.kclique.get 3)[3] ≠ 0 then use tc' else
  -- otherwise we're gonna move c7 to c3 by swapping
  rw [not_ne_iff] at h; rw [h] at h_ne_at_j2; clear h
  use {
    kclique := tc'.kclique.map (KAuto.flipAt ⟨2, by omega⟩ (tc'.kclique.get 3)[2])
    c0 := ?c0
    c1 := ?c1
  }
  case c0 =>
    rw [KClique.get_map_flipAt]
    simp at h2
    simp [Ne.symm h2]
    exact tc'.c0
  case c1 =>
    rw [KClique.get_map_flipAt]
    simp at h2
    simp [Ne.symm h2]
    exact tc'.c1

  have : 3#(n+3+2) ^^^ 4#(n+3+2) = 7#(n+3+2) := by
    simp [bv_toNat]
    repeat (
      rw [Nat.mod_eq_of_lt <|
        Nat.lt_of_lt_of_le (m := 2^5) (by decide) (Nat.pow_le_pow_right (by decide) (by omega)) ]
    )
    decide
  have c72 := c7_2 tc'
  simp_all [KClique.get_map_flipAt]; exact h2

end second_nonzero

section third_nonzero

variable (tc : TwoCubes (n+3) s)

lemma eleven_lt : 11 < 2^(n + 3 + 2) := by
  apply Nat.lt_of_lt_of_le (m := 2^5)
  · decide
  · apply Nat.pow_le_pow_right
    · decide
    · omega

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

theorem c3_4 (c3_2 : (tc.kclique.get 3)[2] ≠ 0) :
    ∃ tc' : TwoCubes (n+3) s, (tc'.kclique.get 3)[2] ≠ 0 ∧ (tc'.kclique.get 3)[3] ≠ 0 ∧ (tc'.kclique.get 3)[4] ≠ 0 := by
  -- have c7_0 = 0, c7_1 = 1, c7_2 = c3_2 again
  have c7_0 := c7_0 tc c3_2
  have c7_1 := c7_1 tc c3_2
  have c7_2 := c7_2 tc
  -- also have c11_0 = 0, c11_1 = 1, c11_3 = c3_3
  have c11_0 := c11_0 tc c3_3
  have c11_1 := c11_1 tc c3_3
  have c11_3 := c11_3 tc
  -- then, b/c c7 and c11 are adjacent, either c7_3 = c3_3 or c11_2 = c3_2
  --have : (tc.kclique.get 7)[3] = (tc.kclique.get 3)[3] ∨
  --      (tc.kclique.get 11)[2] = (tc.kclique.get 3)[2] := sorry
  -- either c7 or c11 are equal to c3 on j < 4

  -- whichever is equivalent, has a difference with c3 at j ≥ 4
  -- if c3_4 ≠ 0 then we are done already
  -- otherwise we swap c7/c11 to c3
  sorry

end third_nonzero

end ThreeCubes

structure ThreeCubes (n s) extends TwoCubes (n+3) s where
  c3 : ∀ i : Fin (n+5), i.val ∈ [2,3,4] → (kclique.get 3)[i] = 1

namespace ThreeCubes

/-- This is just an arbitrary number that decreases
as we get more ones into the `{2,3,4}` coordinates of `c3`. -/
def countSymmOnes (tc : TwoCubes (n+3) s) : Nat :=
  if (tc.kclique.get 3)[2] ≠ 1 then 3
  else if (tc.kclique.get 3)[3] ≠ 1 then 2
  else if (tc.kclique.get 3)[4] ≠ 1 then 1
  else 0

theorem countSymmOnes_eq_3 (tc : TwoCubes (n+3) s)
    : countSymmOnes tc = 3 → (tc.kclique.get 3)[2] ≠ 1 := by
  unfold countSymmOnes
  aesop

theorem countSymmOnes_lt_3 (tc : TwoCubes (n+3) s)
    : (tc.kclique.get 3)[2] = 1 → countSymmOnes tc < 3 := by
  unfold countSymmOnes
  aesop


theorem countSymmOnes_eq_2 (tc : TwoCubes (n+3) s)
    : countSymmOnes tc = 2 → (tc.kclique.get 3)[3] ≠ 1 := by
  unfold countSymmOnes
  aesop

theorem countSymmOnes_eq_0 (tc : TwoCubes (n+3) s) : countSymmOnes tc = 0 →
    (tc.kclique.get 3)[2] = 1 ∧ (tc.kclique.get 3)[3] = 1 ∧ (tc.kclique.get 3)[4] = 1 := by
  unfold countSymmOnes
  aesop


theorem ofTwoCubes (tc : TwoCubes (n+3) s) : Nonempty (ThreeCubes n s) := by
  have ⟨tc2,h2⟩ := c3_2 tc
  have ⟨tc3,h3⟩ := c3_3 tc2 h2
  have ⟨tc4,h4⟩ := c3_4 tc3 h3.1 h3.2
  clear! tc tc2 tc3
  replace h4 : ∀ i : Fin (n+5), i.val ∈ [2,3,4] → (tc4.kclique.get 3)[i] ≠ 0 := by
    rintro ⟨i,hi⟩ h; simp at h
    rcases h with (_|_|_) <;>
      (subst i; first | exact h4.1 | exact h4.2.1 | exact h4.2.2 )
  exact ⟨{
    kclique := tc4.kclique.map (KAuto.permute fun i =>
        if i.val ∈ [2,3,4] then
          Equiv.Perm.setAll [((tc4.kclique.get 3)[i], 1)]
        else Equiv.refl _
      )
    c0 := by
      rw [KClique.get_map_permute, tc4.c0]
      ext j hj
      rw [Vector.getElem_ofFn]
      split
      next h =>
        rw [← Fin.ext_iff]; apply Equiv.Perm.setAll_eq_of_not_mem
        · specialize h4 ⟨j,hj⟩ h
          simpa using h4.symm
        · simp
      · rfl
    c1 := by
      rw [KClique.get_map_permute, tc4.c1]
      ext j hj
      rw [Vector.getElem_ofFn]
      split
      next h =>
        have : (TwoCubes.c1_colors (s := s))[j] = 0 := by
          simp [Fin.ext_iff] at h; rcases h with (_|_|_) <;> simp [*]
        rw [← Fin.ext_iff]
        simp [this]; apply Equiv.Perm.setAll_eq_of_not_mem
        · specialize h4 ⟨j,hj⟩ h
          simpa using h4.symm
        · simp
      · rfl
    c3 := by
      rintro ⟨i, hi⟩ i_mem_234
      rw [KClique.get_map_permute]
      simp only [Fin.getElem_fin, Vector.getElem_ofFn, i_mem_234, if_true]
      specialize h4 _ i_mem_234
      apply Equiv.Perm.setAll_eq_of_mem <;> simp
  }⟩

end ThreeCubes
