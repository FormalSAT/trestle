import Experiments.Keller.Autos

namespace Keller

structure SB0 (n s) where
  kclique : KClique n s

structure SB1 (n s) extends SB0 (n+2) (s+1) where
  c0 : kclique.get 0 = ⟨Array.mkArray (n+2) 0, by simp⟩
  c1 : kclique.get 1 = ⟨#[0,1] ++ Array.mkArray n 0, by simp; omega⟩

theorem SB0.pick_pair {n s} (x : SB0 (n+2) (s+1)) (h : conjectureIn (n+1))
  : ∃ (i₁ i₂ : BitVec (n+2)) (j₁ j₂ : Fin (n+2)), j₁ ≠ j₂ ∧ ∀ j (h : j < n+2),
      (j ≠ j₁ ↔ i₁[j] = i₂[j]) ∧
      (j ≠ j₂ ↔ (x.kclique.get i₁)[j] = (x.kclique.get i₂)[j])
  := by
  let K_0 : Finset (KVertex (n+1) (s+1)) := (Finset.univ (α := BitVec (n+1)))
    |>.map ⟨fun i =>
        let i' := i.cons false
        let v := x.kclique.get i'
        ⟨i, v.take (n+1) |>.cast (by omega)⟩
      , by
        intro x1 x2 heq
        simp at heq; exact heq.1⟩
  have K_0_card : K_0.card = (2^(n+1)) := by simp [K_0]
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
    apply x.kclique.isClique
    iterate 2 (apply KClique.get_mem)
    simp [i_diff]
  simp [KAdj] at this hnotadj
  rcases this with ⟨⟨j₁,hj₁⟩,is_have_diff,ks_same,⟨j₂,hj₂⟩,js_diff,h⟩
  simp_all
  -- the i's are different at index j₁
  have : j₁ ≠ n+1 := by intro contra; simp [BitVec.getElem_cons, contra] at is_have_diff
  simp [BitVec.getElem_cons, this] at is_have_diff
  replace hj₁ : j₁ < n+1 := by omega
  clear this
  specialize hnotadj ⟨j₁, hj₁⟩ is_have_diff ks_same
  -- j₂ must be n+1
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
  -- now we fill the goal
  use (i₁.cons false), (i₂.cons false), ⟨j₁,‹_›⟩, ⟨n+1, by omega⟩
  simp [hk₁, hk₂, js_diff]
  rintro j -
  by_cases eq_j1 : j = j₁
  · simp_all [BitVec.getElem_cons]
  · by_cases eq_last : j = n+1
    · simp_all [BitVec.getElem_cons]
    · specialize hnotadj ⟨j, by omega⟩ (by simp; exact Ne.symm eq_j1)
      simp_all [BitVec.getElem_cons]; exact hnotadj.1

def SB0.reorder (j₁ j₂ : Fin (n+2)) := KAuto.swap [(0,j₁), (1,j₂)]

@[simp] theorem SB0.reorder_0 (j1 j2 : Fin (n+2)) : reorder j1 j2 0 = j1 := by
  simp [reorder]
@[simp] theorem SB0.reorder_eq_j1 (j1 j2 : Fin (n+2)) : reorder j1 j2 j = j1 ↔ j = 0 := by
  conv => lhs; rhs; rw [← SB0.reorder_0 j1 j2]
  rw [Equiv.apply_eq_iff_eq]
@[simp] theorem SB0.reorder_1 (j1 j2 : Fin (n+2)) (h : j1 ≠ j2) : reorder j1 j2 1 = j2 := by
  simp [reorder]; rw [KAuto.swap_eq_of_mem] <;> simp [h]
@[simp] theorem SB0.reorder_eq_j2 (j1 j2 : Fin (n+2)) (h : j1 ≠ j2) : reorder j1 j2 j = j2 ↔ j = 1 := by
  conv => lhs; rhs; rw [← SB0.reorder_1 j1 j2 h]
  rw [Equiv.apply_eq_iff_eq]

/-- The automorphism which moves v₁ to ⟨0,[0*]⟩ and v₂ to ⟨1,[0,1,0*]⟩ -/
def SB0.auto {n s} (v₁ v₂ : KVertex (n+2) (s+2)) : KAuto (n+2) (s+2) :=
  (KAuto.flip v₁.bv)
  |>.trans (KAuto.permute fun j =>
    if j = 1 then
      KAuto.swap [(v₁.colors[j], 0), (v₂.colors[j], 1)]
    else
      KAuto.swap [(v₁.colors[j], 0)]
  )

theorem SB0.auto_v₁ {v₁ v₂ : KVertex (n+2) (s+2)} :
      (SB0.auto v₁ v₂).toFun v₁ = ⟨0, Vector.mkVector _ 0⟩ := by
  ext j hj
  · unfold auto; simp [KVertex.bv_flip]
  · unfold auto; simp [KVertex.colors_permute, Vector.mkVector]
    if hj : j = 1 then
      simp [hj]
    else
      simp [← Fin.val_eq_val, hj]

theorem SB0.auto_v₂ {v₁ v₂ : KVertex (n+2) (s+2)}
      (h : ∀ j (h : j < n+2),
          (j ≠ 0 ↔ v₁.bv[j] = v₂.bv[j]) ∧
          (j ≠ 1 ↔ v₁.colors[j] = v₂.colors[j])) :
      (SB0.auto v₁ v₂).toFun v₂ = ⟨1, ⟨#[0,1] ++ Array.mkArray n 0, by simp; omega⟩⟩ := by
  ext j hj <;> specialize h j hj
  · replace h := h.1
    unfold auto; simp [KVertex.bv_flip]
    by_cases j = 0 <;> aesop
  · replace h := h.2
    unfold auto; simp [KVertex.colors_permute, Vector.mkVector]
    if hj : j = 1 then
      simp [hj, Array.getElem_append]
      simp [hj] at h
      rw [KAuto.swap_eq_of_mem]
      case is_distinct => simp [h]
      case os_distinct => simp
      case pair_mem => simp; right; rfl
      rfl
    else
      simp [hj] at h
      simp [← Fin.val_eq_val, hj, h, Array.getElem_append]
      split
      · have : j = 0 := by omega
        simp [this]
      · rfl

theorem SB0.to_SB1 {n s} (k : SB0 (n+2) (s+2)) (h : conjectureIn (n+1))
  : Nonempty (SB1 n (s+1)) := by
  have ⟨ai, bi, j₁, j₂, hne, same_on⟩ := k.pick_pair h
  -- clean up the context a *bunch*
  -- TODO(JG): just change pick_pair to be in the form I actually want it in
  clear h; rcases k with ⟨k⟩
  generalize a_mem_vs : k.get ai = a_cs at same_on
  generalize b_mem_vs : k.get bi = b_cs at same_on
  rw [KClique.get_eq_iff_mem] at a_mem_vs b_mem_vs
  generalize ha : KVertex.mk ai a_cs = a at a_mem_vs
  generalize hb : KVertex.mk bi b_cs = b at b_mem_vs
  simp [KVertex.ext_iff] at ha hb
  rcases ha with ⟨rfl,rfl⟩; rcases hb with ⟨rfl,rfl⟩
  -- okay, context is now pretty reasonable
  -- apply the reordering automorphism to get vs2, k2, a2, b2
  let k2 := k.map (KAuto.reorder <| SB0.reorder j₁ j₂)
  let a2 := (KAuto.reorder (reorder j₁ j₂)).toFun a
  let b2 := (KAuto.reorder (reorder j₁ j₂)).toFun b
  -- apply the "move to all 0s" automorphism to get vs3, k3
  let k3 := k2.map (SB0.auto a2 b2)

  -- k3 is the clique we want! just have to prove 0 ↦ 0*, 1 ↦ 0,1,0*
  refine ⟨{kclique := k3, c0 := ?c0, c1 := ?c1}⟩
  case c0 =>
    rw [KClique.get_eq_iff_mem]; simp [k3, KClique.map]
    use a2
    constructor
    · apply Finset.mem_map_of_mem; exact a_mem_vs
    · apply SB0.auto_v₁
  case c1 =>
    rw [KClique.get_eq_iff_mem]; simp [k3, KClique.map]
    use b2
    constructor
    · apply Finset.mem_map_of_mem; exact b_mem_vs
    · apply SB0.auto_v₂
      intro j hj
      simp [a2, b2, KVertex.bv_reorder, KVertex.colors_reorder]
      constructor
      · rw [← (same_on _ _).1, not_iff_not, Fin.val_eq_val,
          SB0.reorder_eq_j1, ← Fin.val_eq_val]
        rfl
      · rw [← (same_on _ _).2, not_iff_not, Fin.val_eq_val,
          SB0.reorder_eq_j2 _ _ hne, ← Fin.val_eq_val]
        rfl
