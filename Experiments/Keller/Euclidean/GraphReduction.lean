import Experiments.Keller.Euclidean.PeriodicReduction
import Experiments.Keller.KColoring

import Experiments.Keller.Upstream

namespace Keller.Euclidean

namespace Graph

theorem corners_eq_of_periodic (T : Tiling n) (periodic : T.Periodic) :
      T.corners = (Hajos.corners' T) := by
  have : (Hajos.corners' T) ⊆ T.corners := by
    rintro _ ⟨t,t_core,off,rfl⟩
    apply periodic; apply Hajos.core_subset_corners _ t_core

  apply Set.eq_of_subset_of_subset ?_ this
  intro t t_corner

  obtain ⟨t',⟨t'_corner,t_mem_t'⟩,t'_uniq⟩ := Hajos.corners'_covers T t
  suffices t' = t by subst t'; exact t'_corner

  apply T.covers_unique t
  · exact ⟨this t'_corner, t_mem_t'⟩
  · exact ⟨t_corner, Cube.start_mem ..⟩

/-- BHMN Appendix A.4 Lemma 3 Step 1 -/
theorem fract_eq_of_mem_core {T : Tiling n} (Tper : T.Periodic)
      (h₁ : t₁ ∈ Hajos.core T) (h₂ : t₂ ∈ Hajos.core T) (ne : t₁ ≠ t₂) :
      ∃ j, Cube.index t₁ j ≠ Cube.index t₂ j ∧ Int.fract (t₁ j) = Int.fract (t₂ j) := by
  by_contra contra
  push_neg at contra
  replace contra : ∀ j, Cube.index t₁ j ≠ Cube.index t₂ j → Int.fract (t₁ j - t₂ j) ≠ 0 := by
    intro j hj h; specialize contra j hj
    rw [ne_eq, Int.fract_eq_fract] at contra
    rw [Int.fract_eq_iff] at h; simp at h
    contradiction

  have exists_offs : ∀ j, Cube.index t₁ j ≠ Cube.index t₂ j →
                      ∃ z : ℤ, |t₁ j - t₂ j + 2 * z| < 1 := by
    intro j hj; specialize contra j hj
    generalize t₁ j - t₂ j = x at contra ⊢
    use -⌊(x+1)/2⌋
    -- the contra fact means the floor must actually *do* something
    have : 2 * (⌊(x + 1) / 2⌋ : ℝ) ≠ x + 1 := by
      intro h; apply contra; clear contra
      rw [← sub_eq_iff_eq_add, eq_comm] at h
      calc Int.fract x
        _ = Int.fract (2 * (⌊_⌋ : ℝ)) := by rw [h, Int.fract_sub_one]
        _ = Int.fract ((2 * ⌊_⌋ : ℤ) : ℝ) := by simp; rfl
      apply Int.fract_intCast
    -- lower bound the integer term
    have lower_bound := Int.lt_floor_add_one ((x+1)/2)
    rw [div_lt_iff₀' (by simp), mul_add] at lower_bound
    simp at lower_bound
    -- upper bound the integer term
    have upper_bound := Int.floor_le ((x+1)/2)
    rw [le_div_iff₀' (by simp)] at upper_bound
    replace upper_bound := lt_of_le_of_ne upper_bound this
    rw [abs_lt]; simp
    constructor <;> linarith

  have offs : (j : Fin n) → Cube.index t₁ j ≠ Cube.index t₂ j → { z : ℤ // |t₁ j - t₂ j + 2 * z| < 1} := by
    apply Nonempty.some
    apply Classical.nonempty_pi.mpr; intro j
    apply Classical.nonempty_pi.mpr; intro hj
    specialize exists_offs j hj; simpa

  clear exists_offs contra

  let z : IntPoint n := fun j =>
    if h : Cube.index t₁ j ≠ Cube.index t₂ j then offs j h else 0

  obtain ⟨j,diff_ge_1⟩ := T.exists_gap (Tper t₁ h₁.1 z) h₂.1 (by
    intro h
    have : z = 0 := by
      ext j
      have := h₁.2 j
      have := h₂.2 j; rw [← h, ← IntPoint.toPoint_nsmul, Cube.index_add_intpoint] at this
      simp_all; omega
    simp [this] at h; contradiction)

  if hidx : Cube.index t₁ j = Cube.index t₂ j then
    simp [z, hidx] at diff_ge_1
    simp [Cube.index] at hidx
    rw [le_abs] at diff_ge_1
    cases diff_ge_1
    case inl =>
      have := hidx ▸ Int.le_ceil (t₁ j)
      have := Int.ceil_lt_add_one (t₂ j)
      linarith
    case inr =>
      have := hidx ▸ Int.le_ceil (t₂ j)
      have := Int.ceil_lt_add_one (t₁ j)
      linarith
  else
    simp [add_sub_right_comm, z, hidx] at diff_ge_1
    have := offs j hidx |>.2
    linarith

/-! ### Bound # of Offsets in Each Dimension

For a `n+1` dimensional periodic tiling, there are ≤ `2^n` offsets in each dimension. -/

def offsets (j : Fin n) (T : Tiling n) := { Int.fract (t j) | t ∈ T.corners }

/-- The offsets are just those offsets in the core -/
theorem offsets_eq_core_of_periodic {j : Fin n} {T} (h : T.Periodic) :
      offsets j T = { Int.fract (t j) | t ∈ Hajos.core T } := by
  unfold offsets
  rw [corners_eq_of_periodic _ h]
  simp [Hajos.corners']
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨_,⟨t,t_core,off,rfl⟩,rfl⟩
    use t, t_core
    dsimp
    calc  Int.fract (t j)
      _ = Int.fract (t j + ↑(2 * off j)) := by rw [Int.fract_add_intCast]
      _ = Int.fract (t j + 2 • ↑(off j)) := by simp
  · rintro _ ⟨t,t_core,rfl⟩
    use t; simp; use t, t_core, 0; simp

/-- In fact, they are just *half* the offsets in the core -/
theorem offsets_eq_half_core_of_periodic {j : Fin n} {T} (h : T.Periodic) :
      offsets j T = { Int.fract (t j) | (t ∈ Hajos.core T) (_ : Cube.index t j = 0) } := by
  rw [offsets_eq_core_of_periodic h]; clear h
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨t,t_core,rfl⟩
    if h : Cube.index t j = 0 then use t
    else
    replace h : Cube.index t j = 1 := by simpa [h] using t_core.2 j
    let t' := T.get (Cube.index t + Pi.single j (-1)).toPoint
    have t'_core : t' ∈ Hajos.core T := by
      constructor
      · apply T.get_mem
      · intro j'
        rw [T.index_get]
        by_cases j' = j <;> simp [t_core.2 j', *]
    have t'_idx_0 : Cube.index t' j = 0 := by rw [T.index_get]; simp [h]
    have t'_j : t' j + 1 = t j := by
      apply Tiling.cube_adj_of_adj_points _ t'_core.1 t_core.1
      · apply Cube.index_mem
      · rw [Tiling.index_get]
        simp [add_assoc, ← Pi.single_add]
        apply Cube.index_mem
    use t', t'_core, t'_idx_0
    simp [← t'_j]
  · aesop

noncomputable def offsets_map (j) (T : Tiling n) : {i // i ∈ CoreIndex n ∧ i j = 0} → offsets j T :=
  fun ⟨i,_⟩ =>
  ⟨Int.fract (T.get i j), by
  use T.get i
  simp [offsets, T.get_mem]⟩

theorem offsets_map_surj_of_periodic {j : Fin n} (T : Tiling n) (periodic : T.Periodic) :
    Function.Surjective (offsets_map j T) := by
  rintro ⟨x,x_off⟩
  rw [offsets_eq_half_core_of_periodic periodic] at x_off
  simp at x_off
  rcases x_off with ⟨t,t_core,t_idx_0,rfl⟩
  use ⟨_,t_core.2, t_idx_0⟩
  simp [offsets_map, T.get_index t_core.1]

def coreidx_half_stepdown : {i // i ∈ CoreIndex (n+1) ∧ i j = 0} ≃ {i // i ∈ CoreIndex n} where
  toFun := fun ⟨i,i_core,_⟩ =>
    ⟨ fun ⟨j',h'⟩ => if h : j' < j then i ⟨j',by omega⟩ else i ⟨j' + 1,by omega⟩
    , by intro j'; dsimp; split <;> apply i_core ⟩
  invFun := fun ⟨i,i_core⟩ =>
    ⟨ fun ⟨j',h'⟩ => if h : j' < j then i ⟨j',by omega⟩ else if h : j' = j then 0 else i ⟨j'-1,by omega⟩
    , by constructor
         · intro j'; dsimp; split <;> (try split) <;> (try apply i_core) ; simp
         · simp⟩
  left_inv := by
    rintro ⟨i,i_core,_⟩; ext ⟨j',h'⟩
    if j' < j then simp [*] else
    if j' = j then simp [*] else
    have : ¬ (j' - 1 < j) := by omega
    have : j' - 1 + 1 = j' := by omega
    simp [*]
  right_inv := by
    rintro ⟨i,i_core⟩; ext ⟨j',h'⟩
    if j' < j then simp [*] else
    have : ¬ (j' + 1 < j) := by omega
    have : ¬ (j' + 1 = j) := by omega
    simp [*]

def coreidx_eqv_bitvec : {i // i ∈ CoreIndex n} ≃ BitVec n where
  toFun i := BitVec.ofFn fun j => i.1 j = 1
  invFun i := ⟨fun j => i[j].toInt,by intro j; by_cases i[j] <;> simp [*]⟩
  left_inv := by
    intro i; ext j
    have := i.2 j; simp at this
    cases this <;> simp [*]
  right_inv := by
    intro i; ext j
    by_cases i[j] <;> simp [*]

noncomputable def exists_color_map (T : Tiling (n+1)) (h : T.Periodic) (j) : offsets j T ↪ Fin (2^n) := by
  have off_to_idx := offsets_map_surj_of_periodic T h (j := j)
  have idx_to_off := Function.Embedding.ofSurjective _ off_to_idx
  refine Function.Embedding.trans idx_to_off ?_
  apply Equiv.toEmbedding
  refine Equiv.trans coreidx_half_stepdown ?_
  refine Equiv.trans coreidx_eqv_bitvec ?_
  apply BitVec.equiv_fin


/-! ### Tiling to Coloring -/

noncomputable def corner_to_vec (T : Tiling n) (colors : ∀ j, offsets j T ↪ α)
    {t} (t_corner : t ∈ T.corners) : Vector α n :=
  Vector.ofFn fun j => colors j ⟨ Int.fract (t j), t, t_corner, rfl⟩


noncomputable def tiling_to_coloring (T : Tiling (n+1)) (periodic : T.Periodic) (ff_free : T.FaceshareFree) :
      KColoring (n+1) (2^n) := by
  have colors : (∀ j : Fin (n+1), Graph.offsets j T ↪ Fin (2^n)) :=
    Graph.exists_color_map _ periodic

  let data := fun i =>
    corner_to_vec T colors (T.get_mem (coreidx_eqv_bitvec.symm i).val.toPoint)

  suffices ∀ i j, i ≠ j →
    (∃ d : Fin (n+1), i[d] ≠ j[d] ∧ (data i)[d] = (data j)[d]) ∧
    (adjacent i j → ∃ d : Fin (n+1), (data i)[d] ≠ (data j)[d]) by
    refine {
      data,
      same := fun i j ne => (this i j ne).left,
      diff := fun i j adj => (this i j (ne_of_adjacent adj)).right adj}

  intro i₁ i₂ is_ne
  -- do a bunch of book-keeping
  simp [data, corner_to_vec]
  generalize ht₁ : T.get _ = t₁
  generalize ht₂ : T.get _ = t₂
  have ts_ne : t₁ ≠ t₂ := by
    intro h; subst ht₁ ht₂; replace h := T.get_inj h; simp [Subtype.val_inj] at h; contradiction
  have t₁_core : t₁ ∈ Hajos.core T := by simp [← ht₁, Hajos.core, T.get_mem, T.index_get]
  have t₂_core : t₂ ∈ Hajos.core T := by simp [← ht₂, Hajos.core, T.get_mem, T.index_get]
  -- OK! the s-gap comes from the following lemma:
  have := fract_eq_of_mem_core periodic (t₁ := t₁) (t₂ := t₂) t₁_core t₂_core ts_ne
  obtain ⟨j₁,idxs_ne,fracts_eq⟩ := this
  simp [← ht₁, ← ht₂, Tiling.index_get, coreidx_eqv_bitvec, Bool.toInt_inj] at idxs_ne
  constructor
  · use j₁, idxs_ne, fracts_eq
  · intro adj
    have idxs_eq : ∀ d, d ≠ j₁ → i₁[d] = i₂[d] := by
      obtain ⟨d,is_ne,is_eq⟩ := adj
      have : j₁ = d := by specialize is_eq j₁; simpa [idxs_ne] using is_eq
      subst d
      exact is_eq
    -- The second difference is because T is faceshare-free.
    by_contra contra
    push_neg at contra
    replace contra : ∀ (j2 : Fin (n + 1)), j2 ≠ j₁ → t₁ j2 = t₂ j2 := by
      intro j₂ j₂_ne
      specialize contra j₂
      replace idxs_eq : Cube.index t₁ j₂ = Cube.index t₂ j₂ := by
        simp [← ht₁, ← ht₂, T.index_get, coreidx_eqv_bitvec, Bool.toInt_inj]
        exact idxs_eq _ j₂_ne
      replace idxs_eq : ⌈t₁ j₂⌉ = ⌈t₂ j₂⌉ := by
        simpa [Cube.index] using idxs_eq
      -- TODO(JG): make this its own lemma about Int.ceil and Int.fract
      rw [eq_comm, Int.fract_eq_fract] at contra
      obtain ⟨z,h⟩ := contra
      have : z = 0 := by
        rw [sub_eq_iff_eq_add'] at h
        rw [h] at idxs_eq
        simpa [Int.ceil_add_intCast] using idxs_eq
      simp [this] at h; linarith
    apply ff_free (x := t₁) (y := t₂) (ht₁ ▸ T.get_mem ..) (ht₂ ▸ T.get_mem ..) ts_ne
    refine ⟨j₁,?_,contra⟩
    -- because the offsets are equal, the diff must be integral
    rw [Int.fract_eq_fract] at fracts_eq
    -- but also, because both are in the core, the diff is < 2
    have diff_lt_2 := Hajos.core_diff_lt_2 T t₁_core t₂_core j₁
    -- and the diff can't be 0, because that contradicts `t₁ ≠ t₂`!
    have diff_ne_0 : |t₁ j₁ - t₂ j₁| ≠ 0 := by
      simp [sub_eq_iff_eq_add]
      intro j₁_eq; apply ts_ne; ext j
      if j = j₁ then subst j; apply j₁_eq
      else apply contra; assumption
    obtain ⟨z,hz⟩ := fracts_eq
    rw [hz] at diff_lt_2 diff_ne_0 ⊢
    clear * - diff_lt_2 diff_ne_0
    -- TODO(JG): surely there is a better way to do this...
    simp_all [abs_lt, abs_eq]
    rw [show (2 : ℝ) = Int.cast 2 by simp, ← Int.cast_neg, Int.cast_lt, Int.cast_lt] at diff_lt_2
    rw [show (-1 : ℝ) = Int.cast (-1) by simp, Int.cast_inj]
    omega


/-! ### Coloring to Tiling -/

noncomputable def color_to_real (i : Bool) (c : Fin s) : ℝ :=
   -1 + i.toInt + ((c+1 : ℕ) : ℝ) / s

noncomputable def colorvec_to_point (idx : BitVec n) (color : Vector (Fin s) n) : Point n :=
  fun d => color_to_real idx[d] color[d]

theorem color_to_real.bounds (i : Bool) (c : Fin s) :
    -1 < color_to_real i c ∧ color_to_real i c ≤ 1 := by
  simp only [color_to_real]

  have idx_bounds : 0 ≤ (i.toInt: ℝ) ∧ (i.toInt: ℝ) ≤ 1 := by
    norm_cast
    cases i <;> simp

  have hs : 0 < (s : ℝ) := by
    simp [Nat.pos_iff_ne_zero]; rintro rfl; apply Fin.elim0 c
  have color_lb : 0 < ((c + 1 : ℕ) : ℝ) / s := by
    rw [lt_div_iff₀ hs]
    norm_cast; simp
  have : ((c + 1 : ℕ): ℝ) / s ≤ 1 := by
    rw [div_le_iff₀ hs]
    norm_cast; omega

  constructor <;> linarith

theorem color_to_real.ext (h : s > 0) {i₁ i₂ : Bool} {c₁ c₂ : Fin s} :
    color_to_real i₁ c₁ = color_to_real i₂ c₂ ↔ i₁ = i₂ ∧ c₁ = c₂ := by
  unfold color_to_real
  have : 0 < c₁.val + 1 ∧ c₁.val + 1 ≤ s := by
    constructor <;> omega
  have : 0 < c₂.val + 1 ∧ c₂.val + 1 ≤ s := by
    constructor <;> omega

  refine ⟨?_,by rintro ⟨rfl,rfl⟩; rfl⟩

  wlog i1_le : i₁ ≤ i₂ generalizing i₁ i₂ c₁ c₂
  · rw [not_le] at i1_le
    rw [eq_comm, eq_comm (a := i₁), eq_comm (a := c₁)]
    apply this
    · assumption
    · assumption
    · apply le_of_lt; assumption
  by_cases i₁ = i₂
  case pos =>
    subst i₂
    simp [div_eq_div_iff, Nat.ne_zero_of_lt h, Fin.val_eq_val]
  case neg i_eq =>
    have := lt_of_le_of_ne i1_le i_eq
    clear i1_le i_eq
    rw [Bool.lt_iff] at this
    rcases this with ⟨rfl,rfl⟩
    simp only [Bool.toInt_false, Int.cast_zero, add_zero, Bool.toInt_true, Int.cast_one,
      neg_add_cancel, zero_add, Bool.false_eq_true, false_and, imp_false, ne_eq]

    have hs : (s : ℝ) ≠ 0 := by norm_cast; omega
    rw [eq_comm, div_eq_iff hs, add_mul, div_mul_cancel₀ _ hs]
    norm_cast; omega

theorem colorvec_to_point.ext (h : s > 0) {i1 i2 : BitVec n} {c1 c2 : Vector (Fin s) n} (j) :
    colorvec_to_point i1 c1 j = colorvec_to_point i2 c2 j ↔ i1[j] = i2[j] ∧ c1[j] = c2[j] := by
  simp only [colorvec_to_point, Point.app_ofFn]
  apply color_to_real.ext h

theorem colorvec_to_point.inj (h : s > 0) {i1 i2 : BitVec n} {c1 c2 : Vector (Fin s) n} :
    colorvec_to_point i1 c1 = colorvec_to_point i2 c2 ↔ i1 = i2 ∧ c1 = c2 := by
  simp_rw [funext_iff, colorvec_to_point.ext h]
  rw [BitVec.eq_of_getElem_eq_iff, Vector.ext_iff]
  simp [forall_and, Fin.forall_iff]

theorem colorvec_to_point.cube_index_is_index (h : s > 0) (i : BitVec n) (c : Vector (Fin s) n) :
    Cube.index (colorvec_to_point i c) = coreidx_eqv_bitvec.symm i := by
  ext j
  simp only [Cube.index, colorvec_to_point, color_to_real, Point.app_ofFn,
    coreidx_eqv_bitvec, Equiv.coe_fn_symm_mk]

  have hs : 0 < (s : ℝ) := by norm_cast
  have : 0 < ((c[j].val + 1 : ℕ) : ℝ) / s := by
    rw [lt_div_iff₀ hs]; norm_cast; omega
  have : ((c[j].val + 1 : ℕ) : ℝ) / s ≤ 1 := by
    rw [div_le_iff₀ hs]; norm_cast; omega

  generalize ((c[j].val + 1 : ℕ) : ℝ) / s = x at *
  rw [Int.ceil_eq_iff]
  constructor <;> linarith

def coloring_to_corners (C : KColoring n s) : Set (Point n) :=
  periodify { colorvec_to_point i (C.data i) | i }

theorem coloring_to_corners_disjoint (C : KColoring n s) :
    (coloring_to_corners C).PairwiseDisjoint Cube := by
  intro t₁ ht₁ t₂ ht₂ ts_ne
  simp [coloring_to_corners] at ht₁ ht₂
  obtain ⟨_,⟨i₁,i₁_mem,rfl⟩,off₁,ht₁⟩ := ht₁
  obtain ⟨_,⟨i₂,i₂_mem,rfl⟩,off₂,ht₂⟩ := ht₂

  rw [Function.onFun, Set.disjoint_iff, Set.subset_empty_iff]
  apply Cube.inter_empty_of_exists_gap

  by_cases i₁ = i₂
  case pos =>
    subst i₂ t₁ t₂

    simp [funext_iff] at ts_ne
    rcases ts_ne with ⟨j,offs_ne⟩

    use j
    simp [← mul_sub_left_distrib, abs_mul]

    have : |off₁ j - off₂ j| ≥ 1 := by
      apply Int.one_le_abs
      omega

    rw [ge_iff_le, ← Int.cast_le (R := ℝ)] at this
    simp at this
    linarith

  case neg is_ne =>
  clear ts_ne

  obtain ⟨d,is_ne,cs_eq⟩ := C.same i₁ i₂ is_ne
  use d

  simp only [Fin.getElem_fin] at cs_eq

  subst t₁ t₂

  simp [colorvec_to_point, color_to_real, cs_eq]
  ring_nf

  generalize i₁[d] = b₁ at *
  generalize i₂[d] = b₂ at *
  generalize off₁ d = o₁
  generalize off₂ d = o₂
  clear! n s

  wlog h : b₁ = true
  · specialize this b₂ b₁ (Ne.symm is_ne) o₂ o₁ (by simp_all)
    rw [← abs_neg]
    convert this using 2
    ring

  subst b₁; simp at is_ne; subst b₂
  simp only [Bool.toInt_true, Int.cast_one, Bool.toInt_false, Int.cast_zero, neg_zero, zero_sub]

  rw [le_abs]
  simp only [le_add_neg_iff_add_le, add_le_add_iff_left, Nat.ofNat_pos, mul_le_mul_right,
    Int.cast_le, neg_add_rev, neg_neg, or_iff_not_imp_left, not_le]

  intro h
  rw [Int.lt_iff_add_one_le, ← Int.cast_le (R := ℝ)] at h
  simp at h
  linarith

theorem coloring_to_corners_covers.cube.ih (C : KColoring n s) (j₀ : Nat)
    (p : Point n) (p_range_1 : ∀ j, j₀ ≤ j.val → p j ∈ show Set ℝ from {0,1})
    (p_range_2 : ∀ j, j.val < j₀ → 0 ≤ p j ∧ p j < 2) :
    ∃ c, c ∈ coloring_to_corners C ∧ p ∈ Cube c := by
  match j₀ with
  | 0 =>
    simp at p_range_1 p_range_2
    let i : BitVec n := BitVec.ofFn fun j => p j = 1
    let v := colorvec_to_point i (C.data i)
    use v, ⟨v,⟨i,rfl⟩,0,by simp⟩
    have : p = Cube.index v := by
      ext j
      unfold v
      rw [colorvec_to_point.cube_index_is_index]
      · cases p_range_1 j <;>
        next h => simp [coreidx_eqv_bitvec, i, h]
      · have := (C.data 0)[0]'(j.pos); exact this.pos
    rw [this]
    apply Cube.index_mem
  | j+1 =>
  clear j₀
  by_cases j < n
  case neg =>
    apply ih C n
    · simp
    · rintro j -; apply p_range_2; omega
  case pos j₀h =>
    -- replace j with `j₀ : Fin n`
    have : j = (⟨j,j₀h⟩ : Fin n).val := rfl
    generalize (⟨j,j₀h⟩ : Fin n) = j₀ at this; subst j
    clear j₀h
    have p_range := p_range_2 j₀ (by simp)
    -- apply IH to two points in a line with `p`
    let p₀ := p.update j₀ 0
    let p₁ := p.update j₀ 1
    have p₀_covered := ih C j₀ p₀
      (by intro j j_range
          if hj : j = j₀ then subst j; simp [p₀]
          else simp [p₀,hj]; simp [Fin.ext_iff] at hj; apply p_range_1; omega)
      (by intro j j_range
          have : j ≠ j₀ := (by simp [Fin.ext_iff]; omega)
          simp [p₀, this]; apply p_range_2; omega)
    have p₁_covered := ih C j₀ p₁
      (by intro j j_range
          if hj : j = j₀ then subst j; simp [p₁]
          else simp [p₁,hj]; simp [Fin.ext_iff] at hj; apply p_range_1; omega)
      (by intro j j_range
          have : j ≠ j₀ := (by simp [Fin.ext_iff]; omega)
          simp [p₁, this]; apply p_range_2; omega)
    clear p_range_1 p_range_2

    obtain ⟨t₀,t₀_mem,p₀_mem⟩ := p₀_covered
    obtain ⟨t₁,t₁_mem,p₁_mem⟩ := p₁_covered

    -- t₀ and t₁ have ranges on their `j₀` coordinate
    have t₀_range := (Cube.mem_iff _ _).mp p₀_mem j₀
    simp [p₀] at t₀_range
    have t₁_range := (Cube.mem_iff _ _).mp p₁_mem j₀
    simp [p₁] at t₁_range

    -- define `t₂` as `t₀` but offset by 2e_{j₀}
    let t₂ := t₀ + Pi.single j₀ 2
    have t₂_mem : t₂ ∈ coloring_to_corners C := by
      obtain ⟨t₀,t₀_mem,off,rfl⟩ := t₀_mem
      use t₀, t₀_mem,(off + Pi.single j₀ 1)
      rw [IntPoint.toPoint_add, IntPoint.toPoint_single, nsmul_add,
        ← Pi.single_nsmul]
      simp [t₂,add_assoc]

    -- in fact, they are next to each other
    have : t₀ j₀ + 1 = t₁ j₀ := by
      have disjoint01 := coloring_to_corners_disjoint C t₀_mem t₁_mem
        (by intro h; have := congrFun h j₀; linarith)
      have disjoint12 := coloring_to_corners_disjoint C t₁_mem t₂_mem
        (by intro h; have := congrFun h j₀; simp [t₂] at this; linarith)
      rw [Function.onFun, Set.disjoint_right] at disjoint01 disjoint12
      specialize @disjoint01 (p₁.update j₀ (t₁ j₀)) (by
        apply Cube.update_mem_of_mem p₁_mem; simp)
      specialize @disjoint12 ((p₀+Pi.single j₀ 2).update j₀ (t₂ j₀)) (by
        apply Cube.update_mem_of_mem
        · simp [t₂, Cube.mem_add_iff]; exact p₀_mem
        · simp)
      rw [Cube.mem_iff] at disjoint01 disjoint12
      replace disjoint01 : ¬ (t₀ j₀ ≤ t₁ j₀ ∧ t₁ j₀ < t₀ j₀ + 1) := by
        intro h; apply disjoint01; intro j
        if hj : j = j₀ then
          subst hj; simpa using h
        else
          simpa [hj, p₀, p₁] using (Cube.mem_iff _ _).mp p₀_mem j
      replace disjoint12 : ¬ (t₁ j₀ ≤ t₂ j₀ ∧ t₂ j₀ < t₁ j₀ + 1) := by
        intro h; apply disjoint12; intro j
        if hj : j = j₀ then
          subst hj; simpa using h
        else
          simpa [hj, p₀, p₁] using (Cube.mem_iff _ _).mp p₁_mem j
      push_neg at disjoint01 disjoint12
      simp [t₂] at disjoint12
      specialize disjoint01 (by linarith)
      specialize disjoint12 (by linarith)
      linarith

    -- no matter where `p` is on the line between `p₀` and `p₁`,
    -- it is covered
    if p j₀ < t₁ j₀ then
      use t₀, t₀_mem
      have := Cube.update_mem_of_mem (j := j₀) (y := p j₀) p₀_mem
        (by constructor <;> linarith)
      simpa [p₀] using this
    else if p j₀ < t₁ j₀ + 1 then
      use t₁, t₁_mem
      have := Cube.update_mem_of_mem (j := j₀) (y := p j₀) p₁_mem
        (by constructor <;> linarith)
      simpa [p₁] using this
    else
      use t₂, t₂_mem
      rw [Cube.mem_add_iff, sub_eq_add_neg,
        ← Pi.single_neg, Point.add_single_eq_update]
      have := Cube.update_mem_of_mem (j := j₀) (y := p j₀ - 2) p₀_mem
        (by constructor <;> linarith)
      simpa [p₀] using this


theorem coloring_to_corners_covers.cube (K : KColoring n s) (p : Point n)
      (p_range : ∀ j, 0 ≤ p j ∧ p j < 2) :
    ∃ c, c ∈ coloring_to_corners K ∧ p ∈ Cube c := by
  apply coloring_to_corners_covers.cube.ih K n
  · simp
  · simp [p_range]

theorem coloring_to_corners_covers (K : KColoring n s) (p : Point n) :
    ∃ c, c ∈ coloring_to_corners K ∧ p ∈ Cube c := by
  let p_fract : Point n := Point.ofFn fun j => Int.fract (p j / 2) * 2
  let p_off : IntPoint n := fun j => ⌊p j / 2⌋
  have : p_fract + 2 • p_off = p := by
    ext j
    have : ⌊p j / 2⌋ + Int.fract (p j / 2) = p j / 2 := Int.floor_add_fract ..
    rw [eq_comm, add_comm, div_eq_iff (by simp), add_mul] at this
    simp [p_fract, p_off]; linarith

  obtain ⟨t,t_mem,p'_mem⟩ :=
    coloring_to_corners_covers.cube K p_fract (by
      simp [p_fract, Int.fract_lt_one])

  unfold coloring_to_corners at t_mem
  rcases t_mem with ⟨t,t_mem,off,rfl⟩
  use t + 2 • (off + p_off).toPoint
  constructor
  · use t, t_mem; simp [-IntPoint.toPoint_add]
  · rw [← this, IntPoint.toPoint_add, nsmul_add, ← add_assoc, Cube.mem_add_iff,
      add_sub_cancel_right]
    exact p'_mem

theorem coloring_to_corners_ff (h : s > 0) (C : KColoring n s) :
    ∀ c₁ ∈ coloring_to_corners C, ∀ c₂ ∈ coloring_to_corners C, ¬ Faceshare c₁ c₂ := by
  rintro _ ⟨_,⟨i₁,rfl⟩,off₁,rfl⟩ _ ⟨_,⟨i₂,rfl⟩,off₂,rfl⟩
  rintro ⟨j₁,gap,rest⟩

  replace rest : ∀ j2, j2 ≠ j₁ → colorvec_to_point i₁ (C.data i₁) j2 = colorvec_to_point i₂ (C.data i₂) j2 := by
    intro j2 j2_ne; specialize rest j2 j2_ne
    suffices (-1 : ℤ) < (off₂ j2 - off₁ j2 : ℝ) ∧ (off₂ j2 - off₁ j2 : ℝ) < (1 : ℤ) by
      simp only [← Int.cast_sub, Int.cast_lt] at this
      have : off₂ j2 = off₁ j2 := by omega
      simpa [this] using rest

    simp only [colorvec_to_point,
      nsmul_eq_mul, Nat.cast_ofNat, Pi.add_apply, Pi.mul_apply, Pi.ofNat_apply,
      IntPoint.apply_toPoint] at rest
    simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one]
    have := color_to_real.bounds i₁[j2] (C.data i₁)[j2]
    have := color_to_real.bounds i₂[j2] (C.data i₂)[j2]
    constructor <;> linarith

  simp_rw [colorvec_to_point.ext h] at rest

  have vs_ne : color_to_real i₁[j₁] (C.data i₁)[j₁] ≠ color_to_real i₂[j₁] (C.data i₂)[j₁] := by
    intro h
    simp only [nsmul_eq_mul, Nat.cast_ofNat, Pi.add_apply, Pi.mul_apply, Pi.ofNat_apply,
      IntPoint.apply_toPoint, colorvec_to_point, h] at gap
    suffices 2 * |off₁ j₁ - off₂ j₁| = 1 by omega
    rw [← Int.cast_inj (α := ℝ)]
    simpa [← mul_sub, abs_mul] using gap

  have is_ne : i₁ ≠ i₂ := by rintro rfl; simp at vs_ne

  obtain ⟨j,ij_ne,cs_eq⟩ := C.same i₁ i₂ is_ne

  have : j = j₁ := by
    specialize rest j; simpa [-Fin.getElem_fin, ij_ne] using rest
  subst j

  obtain ⟨j₂,diff⟩ := C.diff i₁ i₂ ⟨j₁,ij_ne,(rest · · |>.left)⟩

  specialize rest j₂
  aesop


def coloring_to_tiling (K : KColoring (n+1) (2^n)) :
          ∃ T : Tiling (n+1), T.Periodic ∧ T.FaceshareFree := by
  use {
    corners := coloring_to_corners K
    covers := by
      intro p
      apply existsUnique_of_exists_of_unique
      · apply coloring_to_corners_covers K
      · rintro c₁ c₂ ⟨c₁_mem,p_mem_c₁⟩ ⟨c₂_mem,p_mem_c₂⟩
        have := coloring_to_corners_disjoint K c₁_mem c₂_mem
        rw [not_imp_comm] at this
        apply this; clear this
        simp [Set.disjoint_iff, Set.ext_iff]
        use p
  }
  refine ⟨?periodic,?ff⟩
  case periodic =>
    apply periodify_periodic
  case ff =>
    rintro c₁ h₁ c₂ h₂ -
    apply coloring_to_corners_ff (by simp) K _ h₁ _ h₂


end Graph

open Graph in
theorem euclideanConjecture_iff_graphConjecture :
      Euclidean.conjectureIn (n+1) ↔ IsEmpty (KColoring (n+1) (2^n)) := by
  rw [conjecture_iff_periodic]
  constructor
  · intro h; constructor; intro K
    apply h
    exact coloring_to_tiling K
  · rintro h ⟨T,T_per,T_ff⟩
    apply h.false; clear h
    apply tiling_to_coloring T T_per T_ff


/--
info: 'Keller.Euclidean.euclideanConjecture_iff_graphConjecture' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms euclideanConjecture_iff_graphConjecture
