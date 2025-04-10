/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.Autos

namespace Keller.SymmBreak

/-! ## First Two Cubes

Any Keller clique can be mapped to a Keller clique with `c_0` and `c_1` fixed.
The justification relies on the veracity of
the Keller conjecture for the previous dimension.
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
        (j ≠ ↑j₁ ↔ a.idx[j] = b.idx[j]) ∧
        (j ≠ ↑j₂ ↔ a.color[j] = b.color[j])
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
  have K_0_not_clique : ¬ (KGraph (n+1) (s+1)).IsNClique (2^(n+1)) K_0 := by
    intro hcontra; rw [conjectureIn_iff_forall_isEmpty] at h
    exact (h _).false (Subtype.mk K_0 hcontra)
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
  -- name the corresponding color in bigger graph
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
  simp only [KAdj, Fin.getElem_fin, Vector.take_eq_extract, Nat.add_one_sub_one,
    Vector.extract_eq_pop, Vector.cast_cast, Vector.cast_rfl, Vector.getElem_pop',
    not_exists, not_and] at hnotadj
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
  -- and we can sensibly conclude the big graph color differ at `n+1`
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
    simp_all [BitVec.getElem_cons]
  · by_cases eq_last : j = n+1
    · simp_all [BitVec.getElem_cons]
    · specialize hnotadj ⟨j, by omega⟩ (by simp; exact Ne.symm eq_j1)
      simp_all [BitVec.getElem_cons]

/-- The automorphism that reorders any columns `j₁`, `j₂`
to the first and second column, respectively. -/
def permColumns_j1_j2 (j₁ j₂ : Fin (n+2)) := Equiv.Perm.setAll [(0,j₁), (1,j₂)]

namespace permColumns_j1_j2
variable {j1 j2 : Fin (n+2)} (h : j1 ≠ j2)
include h

@[simp] theorem app_0 : permColumns_j1_j2 j1 j2 0 = j1 := by
  unfold permColumns_j1_j2; apply Equiv.setAll_eq_of_mem <;> simp [h]
@[simp] theorem eq_j1 : permColumns_j1_j2 j1 j2 j = j1 ↔ j = 0 := by
  rw [← (permColumns_j1_j2 j1 j2).apply_eq_iff_eq (x := j), app_0 h]

@[simp] theorem app_1  : permColumns_j1_j2 j1 j2 1 = j2 := by
  unfold permColumns_j1_j2; apply Equiv.setAll_eq_of_mem <;> simp [h]
@[simp] theorem eq_j2 : permColumns_j1_j2 j1 j2 j = j2 ↔ j = 1 := by
  rw [← (permColumns_j1_j2 j1 j2).apply_eq_iff_eq (x := j), app_1 h]

end permColumns_j1_j2

/-- The automorphism which moves v₁ to ⟨0,[0*]⟩ and v₂ to ⟨1,[0,1,0*]⟩,
assuming v₁ and v₂ have the same bits at j ≠ 0 and the same color at j ≠ 1. -/
def auto {n s} (v₁ v₂ : KVertex (n+2) (s+2)) : KAuto (n+2) (s+2) :=
  (KAuto.flip v₁.idx)
  |>.trans (KAuto.permColors fun j =>
    if j = 1 then
      Equiv.Perm.setAll [(v₁.color[j], 0), (v₂.color[j], 1)]
    else
      Equiv.Perm.setAll [(v₁.color[j], 0)]
  )

section auto
variable {v₁ v₂ : KVertex (n+2) (s+2)}
      (h : ∀ j (h : j < n+2),
          (j ≠ 0 ↔ v₁.idx[j] = v₂.idx[j]) ∧
          (j ≠ 1 ↔ v₁.color[j] = v₂.color[j]))
include h

theorem auto_v₁ : (auto v₁ v₂).toFun v₁ = ⟨0, c0_colors⟩ := by
  ext1
  · unfold auto; simp [KVertex.bv_flip]
  · ext1 j hj
    specialize h j hj
    simp [auto, KVertex.colors_permColors]
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
    unfold auto; simp [KVertex.colors_permColors, Vector.mkVector]
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

theorem ofClique (h : conjectureIn (n+1)) (k : KClique (n+2) (s+2))
  : Nonempty (TwoCubes n s) := by
  have ⟨a, a_mem, b, b_mem, j₁, j₂, hne, same_on⟩ := pick_pair k h
  -- apply the permColumns automorphism to get vs2, k2, a2, b2
  let k2 := k.map (KAuto.permColumns <| permColumns_j1_j2 j₁ j₂)
  let a2 := (KAuto.permColumns (permColumns_j1_j2 j₁ j₂)).toFun a
  let b2 := (KAuto.permColumns (permColumns_j1_j2 j₁ j₂)).toFun b
  have a2_mem : a2 ∈ k2.val := by apply Finset.mem_map_of_mem; exact a_mem
  have b2_mem : b2 ∈ k2.val := by apply Finset.mem_map_of_mem; exact b_mem
  replace same_on : ∀ (j : ℕ) (h : j < n + 2),
      (j ≠ 0 ↔ a2.idx[j] = b2.idx[j]) ∧
      (j ≠ 1 ↔ a2.color[j] = b2.color[j]) := by
    intro j hj
    simp [a2, b2, KVertex.bv_permColumns, KVertex.colors_permColumns]
    constructor
    · rw [← (same_on _ _).1, not_iff_not, Fin.val_eq_val,
        permColumns_j1_j2.eq_j1 hne, ← Fin.val_eq_val]
      rfl
    · rw [← (same_on _ _).2, not_iff_not, Fin.val_eq_val,
        permColumns_j1_j2.eq_j2 hne, ← Fin.val_eq_val]
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
def permColumns (f : Equiv.Perm (Fin (n+2)))
      (fixed_0 : f 0 = 0) (fixed_1 : f 1 = 1)
      (tc : TwoCubes n s) : TwoCubes n s where
  kclique := tc.kclique.map (KAuto.permColumns f)
  c0 := by
    -- this one is true for any reordering regardless of fixed_0/fixed_1
    ext1 j hj
    simp [KClique.get_map_permColumns]
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
    simp only [KClique.get_map_permColumns, BitVec.ofNat_eq_ofNat, Fin.getElem_fin, Vector.getElem_ofFn]
    conv => enter [1,1,2]; rw [this]
    simp only [tc.c1_j, c1_colors_j]
    congr 1
    conv => lhs; rhs; rw [show 1 = Fin.val (n := n+2) (f 1) by simp [fixed_1]]
    rw [← Fin.ext_iff, Equiv.apply_eq_iff_eq]; simp [Fin.ext_iff]

@[simp] theorem kclique_permColumns (tc : TwoCubes n s) :
  (tc.permColumns f fixed_0 fixed_1).kclique = tc.kclique.map (KAuto.permColumns f) := rfl

/-- We can permute color without affecting the first two cubes,
so long as 0 is fixed on all columns and 1 is fixed on column 1. -/
def permColors (f : Fin (n+2) → Equiv.Perm (Fin (s+2)))
      (fixed_0 : ∀ j, (f j) 0 = 0) (fixed_1 : (f 1) 1 = 1)
      (tc : TwoCubes n s) : TwoCubes n s where
  kclique := tc.kclique.map (KAuto.permColors f)
  c0 := by
    ext1 j hj
    simp [KClique.get_map_permColors]
    apply fixed_0
  c1 := by
    ext j hj
    simp [KClique.get_map_permColors]
    if h : j = 1 then
      simp [h, fixed_1]
    else
      simp [h, fixed_0]

@[simp] theorem kclique_permColors (tc : TwoCubes n s) :
  (tc.permColors f fixed_0 fixed_1).kclique = tc.kclique.map (KAuto.permColors f) := rfl

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
