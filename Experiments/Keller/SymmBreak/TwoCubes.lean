/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.SymmBreak.Autos

namespace Keller.SymmBreak

/-! ## First Two Cubes

Any Keller clique can be mapped to a Keller clique with `c_0` and `c_1` fixed.
The justification relies on the veracity of
the Keller conjecture for the previous dimension.
-/


def TwoCubes.c0_colors : Vector (Fin (s+2)) (n+2) :=
  Vector.replicate (n+2) 0

@[simp] theorem TwoCubes.c0_colors_j (j : Nat) (hj : j < (n+2)) : (c0_colors (s := s))[j] = 0 := by
  simp [c0_colors]

def TwoCubes.c1_colors : Vector (Fin (s+2)) (n+2) :=
  #v[0,1].append (Vector.replicate n 0)
  |>.cast (by omega)

@[simp] theorem TwoCubes.c1_colors_j (j : Nat) (hj : j < (n+2)) :
    (c1_colors (s := s))[j] = if j = 1 then 1 else 0 := by
  simp [c1_colors, Vector.append, Array.getElem_append]
  rcases j with ⟨(_|_|_),h⟩ <;> simp [Nat.succ_lt_succ_iff, Fin.ext_iff]

structure TwoCubes (n s) extends KColoring (n+2) (s+2) where
  c0 : data 0 = TwoCubes.c0_colors
  c1 : data 1 = TwoCubes.c1_colors

namespace TwoCubes

theorem pick_pair {n s} (K : KColoring (n+2) (s+1)) (h : IsEmpty (KColoring (n+1) (s+1)))
  : ∃ (i₁ i₂ : BitVec (n+2)), ∃ (j₁ j₂ : Fin (n+2)), j₁ ≠ j₂ ∧
      ∀ (j : ℕ) (h : j < n + 2),
        (j ≠ ↑j₁ ↔ i₁[j] = i₂[j]) ∧
        (j ≠ ↑j₂ ↔ (K.data i₁)[j] = (K.data i₂)[j])
  := by
  -- construct the data for a coloring, using vertices with last bit 0 in bigger domain
  let K_0 : BitVec (n+1) → Vector (Fin (s+1)) (n+1) := fun i =>
        let i' := i.cons false
        let v := K.data i'
        v.take (n+1) |>.cast (by omega)
  -- K_0 satisfies (Gap) requirement still, but K_0 must not be a coloring,
  -- so the (No-Faceshare) constraint must be broken
  have := fun a => show False from h.elim {
    data := K_0, diff := a, same := by
      intro i j ne; obtain ⟨⟨d,dlt⟩,is_ne,cs_eq⟩ := K.same (i.cons false) (j.cons false) (by simp [ne])
      have : d ≠ n+1 := by rintro rfl; simp [BitVec.cons, BitVec.getElem_append] at is_ne
      replace dlt : d < n+1 := by omega
      simp [BitVec.cons, BitVec.getElem_append, dlt] at is_ne
      use ⟨d,dlt⟩; simpa [is_ne, K_0] using cs_eq
    }
  rw [imp_false] at this; push_neg at this
  -- now we have adjacent indices i,j which are fully equal in K_0
  obtain ⟨i,j,ij_adj,K0_ij_eq⟩ := this

  -- the biggified indices satisfy NoFaceshare in K, thus have a diff
  obtain ⟨d2,colors_ne⟩ := K.diff (i.cons false) (j.cons false) (adjacent_cons _ ij_adj)

  -- but that diff must occur in the last dimension, b/c of K0_ij_eq
  have : d2 = n+1 := by
    if d2 < n+1 then
      specialize K0_ij_eq ⟨d2,‹_›⟩
      simp_all [K_0]
    else omega
  cases d2; subst this

  obtain ⟨d1,adj⟩ := ij_adj

  -- Ok! We have all the info we need to fill the goal!
  use (i.cons false), (j.cons false), d1.castSucc, Fin.last _
  constructor
  · simp [Fin.ext_iff]; omega
  intro d dlt
  constructor
  · if dlt : d < n+1 then
      simp [BitVec.cons, BitVec.getElem_append, dlt]
      if d = d1 then
        subst d; simpa using adj.1
      else
        have := adj.2 ⟨d,dlt⟩
        simp_all [Fin.ext_iff]
    else
      have : d = n+1 := by omega
      subst d; simp [BitVec.cons, BitVec.getElem_append]; omega
  · if dlt : d < n+1 then
      specialize K0_ij_eq ⟨d,dlt⟩
      simpa [Nat.ne_of_lt dlt, K_0] using K0_ij_eq
    else
      have : d = n+1 := by omega
      subst d; simpa using colors_ne

/-- The permutation that reorders any columns `j₁`, `j₂`
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
def auto {n s} (i₁ i₂ : BitVec (n+2)) (K : KColoring (n+2) (s+2)) : KAuto (n+2) (s+2) :=
  (KAuto.flip i₁)
  |>.trans (KAuto.permColors fun j =>
    if j = 1 then
      Equiv.Perm.setAll [((K.data i₁)[j], 0), ((K.data i₂)[j], 1)]
    else
      Equiv.Perm.setAll [((K.data i₁)[j], 0)]
  )

section auto
variable {i₁ i₂ : BitVec (n+2)} {K : KColoring (n+2) (s+2)}
      (h : ∀ j (h : j < n+2),
          (j ≠ 0 ↔ i₁[j] = i₂[j]) ∧
          (j ≠ 1 ↔ (K.data i₁)[j] = (K.data i₂)[j]))
include h

theorem auto_v₁ : ((auto i₁ i₂ K) K).data 0 = c0_colors := by
  ext1 d d_range
  specialize h d d_range
  simp [auto]
  rw (occs := .pos [1]) [Equiv.trans_apply, KAuto.apply_flip, KAuto.apply_permColors]
  simp [KColoring.permColors, KColoring.flip]
  split <;> apply Equiv.Perm.setAll_eq_of_mem <;> simp_all

theorem auto_v₂ : ((auto i₁ i₂ K) K).data 1 = c1_colors := by
  ext1 d d_range
  have : (1#(n + 2) ^^^ i₁) = i₂ := by
    apply BitVec.eq_of_getElem_eq
    intro d hd
    have := (h d hd).1
    by_cases d0 : d = 0 <;> simpa [d0, Bool.eq_not] using this

  rw (occs := .pos [1]) [auto, Equiv.trans_apply, KAuto.apply_flip, KAuto.apply_permColors]

  simp [KColoring.permColors, KColoring.flip, this]
  replace h := (h d d_range).2
  split <;> apply Equiv.Perm.setAll_eq_of_mem <;> simp_all

end auto

theorem ofClique (h : IsEmpty (KColoring (n+1) (s+2))) (k : KColoring (n+2) (s+2))
  : Nonempty (TwoCubes n s) := by
  have ⟨i, j, d1, d2, hne, same_on⟩ := pick_pair k h
  -- apply the permColumns automorphism to get vs2, k2, a2, b2
  let k2 := (KAuto.permDims <| permColumns_j1_j2 d1 d2) k

  let i2 := BitVec.ofFn (i[(permColumns_j1_j2 d1 d2) ·])
  let j2 := BitVec.ofFn (j[(permColumns_j1_j2 d1 d2) ·])

  -- apply the "move to all 0s" automorphism to get vs3, k3
  let k3 := (auto i2 j2 k2) k2

  -- k3 is the clique we want! just have to prove 0 ↦ 0*, 1 ↦ 0,1,0*
  refine ⟨{k3 with c0 := auto_v₁ ?hh, c1 := auto_v₂ ?hh}⟩
  intro d d_range
  specialize same_on (permColumns_j1_j2 d1 d2 ⟨d,d_range⟩) (by simp)
  constructor
  · replace same_on := same_on.1
    simp [i2,j2]
    by_cases d = 0 <;> simp_all [← Fin.ext_iff]
  · replace same_on := same_on.2
    simp [i2,j2,k2,KAuto.permDims,KColoring.permDims]
    by_cases d = 1 <;> simp_all [← Fin.ext_iff]

/-! ### Useful TwoCubes theorems -/

@[simp] theorem c0_j (tc : TwoCubes n s) {j : Nat} {hj : j < (n+2)}
    : (tc.data 0#(n+2))[j] = 0 := by
  simpa using congrArg (·[j]) tc.c0

@[simp] theorem c1_j (tc : TwoCubes n s) {j} {hj : j < (n+2)}
    : (tc.data 1#(n+2))[j] = if j = 1 then 1 else 0 := by
  simpa using congrArg (·[j]) tc.c1


/-- We can reorder columns without affecting the first two cubes,
so long as 0 and 1 aren't reordered. -/
def permDims (f : Equiv.Perm (Fin (n+2)))
      (fixed_0 : f 0 = 0) (fixed_1 : f 1 = 1)
      (tc : TwoCubes n s) : TwoCubes n s where
  toKColoring := (KAuto.permDims f) tc.toKColoring
  c0 := by
    -- this one is true for any reordering regardless of fixed_0/fixed_1
    ext1 j hj
    simp [KAuto.permDims]
    rw (occs := .pos [1]) [Equiv.coe_fn_mk]
    simp [KColoring.permDims]
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
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod]
    -- therefore...
    ext1 j hj
    simp only [KAuto.apply_permDims, KColoring.permDims, BitVec.ofNat_eq_ofNat, Fin.getElem_fin, Vector.getElem_ofFn,this]
    simp only [tc.c1_j, c1_colors_j]
    congr 1
    conv => lhs; rhs; rw [show 1 = Fin.val (n := n+2) (f 1) by simp [fixed_1]]
    rw [← Fin.ext_iff, Equiv.apply_eq_iff_eq]; simp [Fin.ext_iff]

/-- We can permute color without affecting the first two cubes,
so long as 0 is fixed on all columns and 1 is fixed on column 1. -/
def permColors (f : Fin (n+2) → Equiv.Perm (Fin (s+2)))
      (fixed_0 : ∀ j, (f j) 0 = 0) (fixed_1 : (f 1) 1 = 1)
      (tc : TwoCubes n s) : TwoCubes n s where
  toKColoring := (KAuto.permColors f) tc.toKColoring
  c0 := by
    ext1 j hj
    simp [KColoring.permColors]
    apply fixed_0
  c1 := by
    ext j hj
    simp [KColoring.permColors]
    if h : j = 1 then
      simp [h, fixed_1]
    else
      simp [h, fixed_0]

/-- We can swap two neighboring indices without affecting the first two cubes,
so long as the swap is in column ≥ 2 and the color is not 0. -/
def condFlip (j : Fin (n+2)) (k : Fin (s+2)) (j_ge : j.val ≥ 2) (k_ne_0 : k ≠ 0)
      (tc : TwoCubes n s) : TwoCubes n s where
  toKColoring := (KAuto.condFlip j k) tc.toKColoring
  c0 := by
    ext1 j' hj'
    simp [KColoring.condFlip, KColoring.condFlipB, k_ne_0.symm]
  c1 := by
    ext j' hj'
    simp [KColoring.condFlip, KColoring.condFlipB,
      show j.val ≠ 1 by omega, k_ne_0.symm]

/-- We can flip bits in column 0, though it requires swapping colors 0/1 in column 1. -/
def flip0 (tc : TwoCubes n s) : TwoCubes n s where
  toKColoring := (KAuto.flip 1#_ |>.trans (KAuto.permColors (if ·.val = 1 then .swap 0 1 else .refl _))
    ) tc.toKColoring
  c0 := by
    ext j hj
    simp [KAuto.permColors, KColoring.permColors, KAuto.flip, KColoring.flip]
    split <;> simp
  c1 := by
    ext j hj
    simp [KAuto.permColors, KColoring.permColors, KAuto.flip, KColoring.flip]
    split <;> simp

end TwoCubes
