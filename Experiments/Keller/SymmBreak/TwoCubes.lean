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


abbrev TwoCubes.c0_colors : Vector (Fin (s+2)) (n+2) :=
  ⟨Array.mkArray (n+2) 0, by simp⟩

abbrev TwoCubes.c1_colors : Vector (Fin (s+2)) (n+2) :=
  ⟨#[0,1] ++ Array.mkArray n 0, by simp; omega⟩

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
    unfold auto; simp [KVertex.colors_permute, Vector.mkVector]
    split <;> (apply Equiv.setAll_eq_of_mem <;> simp_all [Fin.ext_iff])

theorem auto_v₂ : (auto v₁ v₂).toFun v₂ = ⟨1, c1_colors⟩ := by
  ext1 <;> ext1 j hj <;> specialize h j hj
  · replace h := h.1
    unfold auto; simp [KVertex.bv_flip]
    by_cases j = 0 <;> aesop
  · replace h := h.2
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
      trans 0
      · apply Equiv.setAll_eq_of_mem <;> simp
      · split
        · have : j = 0 := by omega
          simp [this]
        · rfl

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

end TwoCubes

structure ThreeCubes (n s) extends TwoCubes (n+3) s where
  c3 : ∀ i : Fin (n+5), i ∈ [2,3,4] → (kclique.get 3)[i] = 1

namespace ThreeCubes

private theorem bv_3_getElem (n j : Nat) (hn : n ≥ 2) (h : j < n)
    : (BitVec.ofNat n 3)[j] = decide (j = 0 ∨ j = 1) := by
  simp [BitVec.getElem_eq_testBit_toNat, h, Nat.testBit]
  match n, hn, h with
  | n+2, hn, h =>
  match j with
  | 0 => simp [h]
  | 1 => simp [Nat.shiftRight_one, Nat.pow_succ, Nat.mod_mul_left_div_self]
  | j+2 => simp [Nat.shiftRight_succ_inside, Nat.pow_succ, Nat.mod_mul_left_div_self]

theorem c3_1 (tc : TwoCubes n s) : (tc.kclique.get 3)[1] = 1 := by
  have := tc.kclique.isClique (tc.kclique.get_mem 1) (tc.kclique.get_mem 3)
    (by simp [BitVec.ofNat_eq_of_width_ge (minWidth := 2)])
  rcases this with ⟨j1,bs_ne_at_j1,cs_eq_at_j1,-⟩
  dsimp at *
  have : j1 = 1 := by
    simp [bv_3_getElem] at bs_ne_at_j1
    simp [Fin.ext_iff, bs_ne_at_j1]
  clear bs_ne_at_j1
  subst this; simp at cs_eq_at_j1
  rw [← cs_eq_at_j1]
  clear cs_eq_at_j1
  have := congrArg (·[1]) tc.c1
  simp [Array.getElem_append_left] at this
  exact this

theorem c3_0 (tc : TwoCubes n s) : (tc.kclique.get 3)[0] = 0 := by
  have := tc.kclique.isClique (tc.kclique.get_mem 0) (tc.kclique.get_mem 3)
    (by simp [BitVec.ofNat_eq_of_width_ge (minWidth := 2)])
  rcases this with ⟨j1,bs_ne_at_j1,cs_eq_at_j1,-⟩
  dsimp at *
  have : j1 ≠ 1 := by
    rintro rfl
    have := congrArg (·[1]) tc.c0
    have := c3_1 tc
    simp_all
  have : j1 = 0 := by
    simp [Fin.ext_iff] at this ⊢; simp [bv_3_getElem, this] at bs_ne_at_j1
    exact bs_ne_at_j1
  clear bs_ne_at_j1
  subst this; simp at cs_eq_at_j1
  rw [← cs_eq_at_j1]
  clear cs_eq_at_j1
  have := congrArg (·[0]) tc.c0
  simp [Array.getElem_append_left] at this
  exact this

theorem c3_j2 (tc : TwoCubes n s) : ∃ j2 : Fin _, (tc.kclique.get 3)[j2] ≠ 0 := by
  have := tc.kclique.isClique (tc.kclique.get_mem 1) (tc.kclique.get_mem 3)
    (by simp [BitVec.ofNat_eq_of_width_ge (minWidth := 2)])
  rcases this with ⟨j1,bv_eq_at_j1,-,j2,js_ne,h2⟩
  dsimp at *
  have j1_eq_1 : j1 = 1 := by
    simp [bv_3_getElem] at bv_eq_at_j1; rw [Fin.ext_iff]; exact bv_eq_at_j1.1
  clear bv_eq_at_j1
  subst j1_eq_1
  rw [eq_comm, Fin.ext_iff] at js_ne; dsimp at js_ne
  simp [bv_3_getElem, js_ne] at h2
  have := tc.c1; simp at this; rw [this] at h2; clear this
  simp [] at h2
  sorry

/-- Count how many dimensions the `c3` color is 0 at. -/
def countC3Zeros (tc : TwoCubes n s) : Nat :=
  Finset.univ.filter (fun j : Fin (n+2) => (tc.kclique.get 3)[j] = 0)
  |>.card

open Classical in
theorem ofTwoCubes (tc : TwoCubes (n+3) s) : Nonempty (ThreeCubes n s) := by
  -- Pick the TwoCubes instance with the smallest `countC3Zeros`
  let p := fun zs => ∃ tc : TwoCubes (n+3) s, countC3Zeros tc = zs
  have ⟨tc', tc'_count_eq_lam⟩ := Nat.find_spec (p := p) ⟨_, tc, rfl⟩
  have tc'_min := fun m => Nat.find_min (p := p) ⟨_, tc, rfl⟩ (m := m)
  -- lam is the number of zeros (smallest possible)
  generalize Nat.find (p := p) _ = lam at tc'_count_eq_lam tc'_min
  clear tc; simp [p] at *; clear p

  -- call the set of zero indices `zeroDims`
  unfold countC3Zeros at tc'_count_eq_lam
  generalize htemp : @Finset.filter _ _ = temp at tc'_count_eq_lam
  generalize h : temp _ = zeroDims at tc'_count_eq_lam htemp
  subst htemp

  -- 0 ∈ zeroDims, 1 ∉ zeroDims
  have zero_mem : 0 ∈ zeroDims := sorry
  have one_mem  : 1 ∉ zeroDims := sorry

  have ⟨j,this⟩ := c3_j2 tc'
  have j_mem    : j ∉ zeroDims := sorry
  /-
      0   1   j
c0  | 0 | 0 | 0 | 0 | 0 |
c1  |_0_| 1 | 0 | 0 | 0 |
c3  |_0_|_1_|   |   |   |
c7  |_ _|_ _|_ _|   |   |
c11 |_ _|_ _|   |_ _|   |
c19 |_ _|_ _|   |   |_ _|
  -/
  -- lam ≤ n+5
  have : lam ≤ n+5 := by
    subst lam zeroDims
    trans; apply Finset.card_filter_le; simp
  -- lam ≠ n+5
  sorry

end ThreeCubes
