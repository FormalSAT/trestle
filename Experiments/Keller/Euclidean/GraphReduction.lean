import Experiments.Keller.Euclidean.PeriodicReduction
import Experiments.Keller.KellerGraph

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
      _ = Int.fract (t j + ↑(2 * off j)) := by rw [Int.fract_add_int]
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
    let t' := T.get (Cube.index t + .single j (-1)).toPoint
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
      · rw [Tiling.index_get]; simp [add_assoc]
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


/-! ### Tiling to Clique -/

noncomputable def corner_to_vec (T : Tiling n) (colors : ∀ j, offsets j T ↪ α)
    {t} (t_corner : t ∈ T.corners) : Vector α n :=
  Vector.ofFn fun j => colors j ⟨ Int.fract (t j), t, t_corner, rfl⟩


noncomputable def clique_of_tiling (T : Tiling (n+1)) (periodic : T.Periodic) (ff_free : T.FaceshareFree) :
      KClique (n+1) (2^n) := by
  have colors : (∀ j : Fin (n+1), Graph.offsets j T ↪ Fin (2^n)) :=
    Graph.exists_color_map _ periodic

  let K : Finset (KVertex (n+1) (2^n)) :=
    { ⟨i, corner_to_vec T colors (T.get_mem (coreidx_eqv_bitvec.symm i))⟩ | (i) }

  use K
  constructor
  · rintro ⟨i₁,c₁⟩ v₁_mem ⟨i₂,c₂⟩ v₂_mem vs_ne
    -- do a bunch of book-keeping
    simp [K] at v₁_mem v₂_mem; subst c₁ c₂
    clear K
    have is_ne : i₁ ≠ i₂ := by simpa +contextual using vs_ne
    clear vs_ne
    simp [KAdj, corner_to_vec]
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
    use j₁, idxs_ne, fracts_eq
    -- The second difference is because T is faceshare-free.
    by_contra contra
    push_neg at contra
    replace contra : ∀ (j2 : Fin (n + 1)), j2 ≠ j₁ → t₁ j2 = t₂ j2 := by
      clear fracts_eq idxs_ne ts_ne
      intro j₂ j₂_ne; specialize contra j₂ (Ne.symm j₂_ne)
      obtain ⟨idxs_eq,fracts_eq⟩ := contra
      replace idxs_eq : Cube.index t₁ j₂ = Cube.index t₂ j₂ := by
        simp [← ht₁, ← ht₂, T.index_get, coreidx_eqv_bitvec, Bool.toInt_inj]; exact idxs_eq
      replace idxs_eq : ⌈t₁ j₂⌉ = ⌈t₂ j₂⌉ := by
        simpa [Cube.index] using idxs_eq
      -- TODO(JG): make this its own lemma about Int.ceil and Int.fract
      rw [eq_comm, Int.fract_eq_fract] at fracts_eq
      obtain ⟨z,h⟩ := fracts_eq
      have : z = 0 := by
        rw [sub_eq_iff_eq_add'] at h
        rw [h] at idxs_eq
        simpa [Int.ceil_add_int] using idxs_eq
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
  · simp [K]
    rw [Finset.card_image_of_injective _ ?inj]
    · simp
    case inj =>
      intro i₁ i₂; simp +contextual


/-! ### Clique to Tiling -/


end Graph

open Graph

theorem graphConjecture_implies_euclideanConjecture (h : Keller.conjectureIn n) :
      Euclidean.conjectureIn n := by
  rw [conjecture_iff_periodic]
  rintro ⟨T,T_per,T_ff⟩
  apply h.false; clear h
  match n with
  | 0 => simp [KClique]; use {default}, default
  | n+1 =>
  apply Graph.clique_of_tiling T T_per T_ff


/--
info: 'Keller.Euclidean.graphConjecture_implies_euclideanConjecture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms graphConjecture_implies_euclideanConjecture
