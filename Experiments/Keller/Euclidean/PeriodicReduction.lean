import Experiments.Keller.Euclidean.Basic
import Experiments.Keller.Euclidean.TilingStructure

namespace Keller.Euclidean

def Periodic (corners : Set (Point d)) : Prop :=
  ∀ t ∈ corners, ∀ x : IntPoint d, t + 2 • x ∈ corners

def periodify (corners : Set (Point d)) : Set (Point d) :=
  { c + 2 • i | (c ∈ corners) (i : IntPoint d) }

theorem periodify_periodic (corners : Set (Point d)) :
  Periodic (periodify corners) := by
  rintro _ ⟨c,c_mem,i,rfl⟩ i₂
  use c, c_mem, i+i₂; simp; abel

nonrec def Tiling.Periodic (T : Tiling d) : Prop :=
  Periodic T.corners


/-- `{0,1}ᵈ` on paper -/
def CoreIndex (d : Nat) := { i : IntPoint d | ∀ j, i j ∈ ({0,1} : Set ℤ) }

/-- a cube's index is core if the cube's corner is in (-1,1] -/
theorem CoreIndex.index_mem_iff : Cube.index t ∈ CoreIndex d ↔ ∀ j, (-1 : ℝ) < t j ∧ t j ≤ (1 : ℝ) := by
  constructor
  · intro h j; specialize h j
    simp only [Cube.index, Set.mem_insert_iff, Set.mem_singleton_iff, Int.ceil_eq_iff,
                Int.cast_zero, zero_sub, Int.cast_one, sub_self] at h
    cases h <;> constructor <;> linarith
  · intro h j; specialize h j
    simp only [Cube.index, Set.mem_insert_iff, Set.mem_singleton_iff, Int.ceil_eq_iff,
                Int.cast_zero, zero_sub, Int.cast_one, sub_self]
    by_cases t j ≤ 0
    · left; constructor <;> linarith
    · right; constructor <;> linarith

def ClosedCube (t : Point d) := { x : Point d | ∀ j, t j ≤ x j ∧ x j ≤ t j + 1 }

/-- if a cube intersects with the origin unit cube `[0,1]ᵈ`,
    then its integer index must be in `{0,1}ᵈ` -/
theorem CoreIndex.of_inter_closed_cube_nonempty {t : Point d}(h : (ClosedCube 0 ∩ Cube t).Nonempty)
    : Cube.index t ∈ CoreIndex d := by
  rw [CoreIndex.index_mem_iff]
  intro j
  rcases h with ⟨x,x_mem_unit,x_mem_t⟩
  specialize x_mem_unit j
  replace x_mem_t := (Cube.mem_iff _ _).mp x_mem_t j
  simp [IntPoint.toPoint, abs_lt] at x_mem_t x_mem_unit
  constructor <;> linarith

theorem CoreIndex.decompose_intpoint (x : IntPoint d) :
      ∃ x' ∈ CoreIndex d, ∃ y : IntPoint d, x = x' + 2 • y := by

  -- can decompose component-wise with emod and ediv
  have : ∀ j : Fin d, Σ' x', Σ' y, x' ∈ ({0,1} : Set ℤ) ∧ x j = x' + 2 * y := by
    intro j
    have := Int.emod_add_ediv (x j) 2
    refine ⟨_, _, ?_, this.symm⟩
    generalize x j = z; clear! d

    simp; omega

  -- and then construct it from the component-wise decomposition
  -- this term is crazy
  exact ⟨
      fun j => (this j).1
    , fun j => (this j).2.2.1
    , fun j => (this j).2.1
    , funext fun j => (this j).2.2.2⟩


namespace Hajos

variable (T : Tiling d)

def core := { t ∈ T.corners | (Cube.index t ∈ CoreIndex d)}
def corners' := periodify (core T)

theorem core_subset_corners : core T ⊆ T.corners := by
  apply Set.sep_subset

theorem core_subset_corners' : core T ⊆ corners' T := by
  rintro t t_mem
  use t, t_mem, 0
  simp

theorem core_diff_lt_2 (ht1 : t1 ∈ core T) (ht2 : t2 ∈ core T) :
    ∀ j, |t1 j - t2 j| < 2 := by
  intro j
  obtain ⟨t1_corner,t1_idx_core⟩ := ht1
  obtain ⟨t2_corner,t2_idx_core⟩ := ht2
  rw [CoreIndex.index_mem_iff] at t1_idx_core t2_idx_core
  specialize t1_idx_core j; specialize t2_idx_core j
  rw [abs_lt]
  constructor <;> linarith

theorem corners'_closed_even_addition (t) (ht : t ∈ corners' T) (z : IntPoint d) :
    t + 2 • z ∈ corners' T := by
  obtain ⟨t,t_core,off,rfl⟩ := ht
  use t, t_core, off + z
  simp [add_assoc]

theorem corners'_uniquely_closed_even_addition (x : Point d) (h : ∃! t ∈ corners' T, x ∈ Cube t)
  : ∀ z : IntPoint d, ∃! t ∈ corners' T, x + 2 • z ∈ Cube t := by
  intro z
  obtain ⟨-,⟨⟨t,t_core,off,rfl⟩,x_mem_t⟩,uniq⟩ := h
  use t + (2 • (off + z).toPoint)
  refine ⟨⟨?corner,?mem⟩,?uniq⟩
  case corner =>
    use t, t_core
    refine ⟨_,rfl⟩
  case mem =>
    rw [Cube.mem_add_iff] at x_mem_t ⊢
    convert x_mem_t using 1
    simp
  case uniq =>
    -- TODO this is such an awful proof script
    rintro y ⟨L,R⟩
    specialize uniq (y - 2 • z) (by
      simp [sub_eq_add_neg,Cube.mem_add_iff,R]
      simpa using corners'_closed_even_addition T _ L (-z)
    )
    simp at uniq ⊢
    abel_nf at uniq ⊢
    rw [← uniq]; abel


/-- SUPER important lemma: if a set of cubes uniquely covers an interval,
then the cubes containing the endpoints of the interval must be adjacent. -/
theorem cubes_adjacent_of_uniquely_covers_interval (corners : Set (Point d)) (j : Fin d) (x : Point d) :
      (∀ α, 0 ≤ α ∧ α ≤ 1 → ∃! t ∈ corners, x + .single j α ∈ Cube t) →
      t1 ∈ corners → x ∈ Cube t1 → t2 ∈ corners → x + .single j 1 ∈ Cube t2 →
      t1 j + 1 = t2 j := by
  intro h t1_mem mem_t1 t2_mem mem_t2

  have t1j_bounds := (Cube.mem_iff _ _).mp mem_t1 j
  have t2j_bounds := (Cube.mem_iff _ _).mp mem_t2 j
  simp at t2j_bounds

  -- there is a cube where the interval intersects the end of `t1`
  obtain ⟨t,⟨t_mem,mem_t⟩,-⟩ := h (t1 j + 1 - x j) (by constructor <;> linarith)

  have tj_bounds := (Cube.mem_iff _ _).mp mem_t j
  simp at tj_bounds

  -- `t j` can't be less than `x j`, because then both `t1` and `t` would contain `x`
  have bound1 : ¬ t j < x j := by
    intro lt
    suffices t1 = t by subst t; linarith
    apply (h 0 (by simp)).unique
    · exact ⟨t1_mem,by simp [mem_t1]⟩
    · refine ⟨t_mem,?_⟩
      have := Cube.update_mem_of_mem mem_t (y := x j) (j := j)
        (by constructor <;> linarith)
      simpa [Point.add_single_eq_update] using this

  -- `t j` can't be less than `t1 j + 1` because both would contain `x.update j (t j)`
  have bound2 : ¬ t j < t1 j + 1 := by
    intro lt
    suffices t1 = t by subst t; linarith
    apply (h (t j - x j) ?in_int).unique
    case in_int =>
      constructor <;> linarith
    all_goals {
      simp [t1_mem, t_mem, Point.add_single_eq_update]
      apply Cube.update_mem_of_inter_line_nonempty
      · refine ⟨_,‹_›,?_⟩; simp [Point.add_single_eq_update, Line.update_mem_iff]
      · constructor <;> linarith
    }

  have tj : t j = t1 j + 1 := by linarith
  clear bound1 bound2 tj_bounds

  -- `t2 j` can't be less than `t1 j + 1` because both would contain `x.update j (t2 j)`
  have bound3 : ¬ t2 j < t1 j + 1 := by
    intro lt
    suffices t1 = t2 by subst t2; linarith
    apply (h (t2 j - x j) ?in_int).unique
    case in_int =>
      constructor <;> linarith
    all_goals {
      simp [t1_mem, t2_mem, Point.add_single_eq_update]
      apply Cube.update_mem_of_inter_line_nonempty
      · refine ⟨_,‹_›,?_⟩; simp [Point.add_single_eq_update, Line.update_mem_iff]
      · constructor <;> linarith
    }

  -- both t2 and t contain `x.update j (t2 j)`
  have : t2 = t := by
    apply (h (t2 j - x j) ?in_int).unique
    case in_int =>
      constructor <;> linarith
    · use t2_mem
      have := Cube.update_mem_of_mem mem_t2 (y := t2 j) (j := j) (by simp)
      simpa [Point.add_single_eq_update] using this
    · use t_mem
      have := Cube.update_mem_of_mem mem_t (y := t2 j) (j := j) (by constructor <;> linarith)
      simpa [Point.add_single_eq_update] using this

  cc

set_option maxHeartbeats 1000000 in
theorem corners'_step_closed_cube (c : Point d) (j : Fin d)
    (h : ∀ x ∈ ClosedCube c, ∃! t ∈ corners' T, x ∈ Cube t)
    : ∀ x ∈ ClosedCube c, ∃! t ∈ corners' T, x + .single j 1 ∈ Cube t := by
  intro x x_mem_c

  -- We have 3 points of interest
  -- note that `x` is between `x₀` and `x₁`, while `x + eⱼ` is between `x₁` and `x₂`
  let x₀ := x.update j (c j)
  let x₁ := x.update j (c j + 1)
  let x₂ := x.update j (c j + 2)

  have x₂_eq : x₂ = x₀ + 2 • (IntPoint.single j 1).toPoint := by simp [x₀, x₂]

  -- x₀ and x₁ are uniquely covered because they are in `c`
  have x₀_mem_c : x₀ ∈ ClosedCube c := by
    intro j'; by_cases hj : j' = j <;>
      ((try rw [hj]); simp [x₀, hj, x_mem_c j'])

  have x₁_mem_c : x₁ ∈ ClosedCube c := by
    intro j'; by_cases hj : j' = j <;>
      ((try rw [hj]); simp [x₁, hj, x_mem_c j'])

  have x₀_uniquely_covered := h x₀ x₀_mem_c
  have x₁_uniquely_covered := h x₁ x₁_mem_c

  -- x₂ is uniquely covered because it is even offset away from x₀
  have x₂_uniquely_covered := by
    have := corners'_uniquely_closed_even_addition T x₀ x₀_uniquely_covered (.single j 1)
    rw [← x₂_eq] at this
    exact this

  -- the cubes containing each point will be called `t₀`, `t₁`, `t₂`
  obtain ⟨t₀,⟨t₀_corner,x₀_mem_t₀⟩,t₀_uniq⟩ := x₀_uniquely_covered
  obtain ⟨t₁,⟨t₁_corner,x₁_mem_t₁⟩,t₁_uniq⟩ := x₁_uniquely_covered
  obtain ⟨t₂,⟨t₂_corner,x₂_mem_t₂⟩,t₂_uniq⟩ := x₂_uniquely_covered

  -- the interval between x₀ and x₁ is uniquely covered,
  -- so the cubes containing x₀ and x₁ must be adjacent
  have t₀_step_t₁ : t₀ j + 1 = t₁ j := by
    apply cubes_adjacent_of_uniquely_covers_interval (corners' T) j x₀ ?h
      t₀_corner x₀_mem_t₀ t₁_corner (by simpa [Point.add_single_eq_update, x₀])
    intro α α_range
    apply h
    simp [x₀]
    intro j'
    if j' = j then subst j'; simpa using α_range else
    simp [*, x_mem_c j']

  -- also `t₂` must be `t₀ + 2eⱼ`
  have t₂_eq : t₂ = t₀ + 2 • IntPoint.single j 1 := by
    rw [eq_comm];
    apply t₂_uniq _ ⟨?_, ?_⟩
    apply corners'_closed_even_addition T _ t₀_corner
    simp only [Cube.mem_add_iff, x₂_eq, add_sub_cancel_right]
    exact x₀_mem_t₀

  have t₁_step_t₂ : t₁ j + 1 = t₂ j := by
    subst t₂; simp [← t₀_step_t₁]; ring

  -- every cube containing `x + eⱼ` must also contain either `x₁` or `x₂`,
  have must_contain_x1_x2 : ∀ t, x + .single j 1 ∈ Cube t → x₁ ∈ Cube t ∨ x₂ ∈ Cube t := by
    intro t x_step_mem
    have := x_mem_c j
    have := (Cube.mem_iff _ _).mp x_step_mem j; simp at this
    if t j ≤ c j + 1 then
      left
      have := Cube.update_mem_of_mem x_step_mem (y := c j + 1) (j := j) (by
        constructor <;> linarith)
      simpa [Point.add_single_eq_update] using this
    else
      right
      have := Cube.update_mem_of_mem x_step_mem (y := c j + 2) (j := j) (by
        constructor <;> linarith)
      simpa [Point.add_single_eq_update] using this

  -- and, if `t` is a corner, it must equal either `t₁` or `t₂`
  have eq_t1_or_t2 : ∀ t ∈ corners' T, x + .single j 1 ∈ Cube t → t = t₁ ∨ t = t₂ := by
    intro t t_corner x_step_mem
    cases must_contain_x1_x2 t x_step_mem
    case inl =>
      left; apply t₁_uniq _ ⟨t_corner,‹_›⟩
    case inr =>
      right; apply t₂_uniq _ ⟨t_corner,‹_›⟩

  -- but `t₁` and `t₂` are disjoint...
  have t₁_t₂_disjoint : Disjoint (Cube t₁) (Cube t₂) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    apply Cube.inter_empty_of_exists_gap
    use j; simp [← t₁_step_t₂]

  -- OK: now we case on whether `x` is in `t₀` or `t₁`
  by_cases comparison : x j < t₀ j + 1
  case pos =>
    -- `x + eⱼ` is in `t₁`
    have x_step_mem : x + .single j 1 ∈ Cube t₁ := by
      have : t₀ j ≤ x₀ j := (Cube.mem_iff _ _).mp x₀_mem_t₀ j |>.1
      have : x₀ j = c j := by simp +zetaDelta
      have : c j ≤ x j := x_mem_c j |>.1
      have := Cube.update_mem_of_mem x₁_mem_t₁ (y := x j + 1) (j := j) (by
        constructor <;> linarith)
      simpa [x₁, Point.add_single_eq_update] using this

    refine ⟨t₁, ⟨t₁_corner, x_step_mem⟩, ?_⟩

    · rintro t ⟨t_corner,x_step_mem_t⟩
      cases eq_t1_or_t2 t t_corner x_step_mem_t
      case inl h => exact h
      case inr h =>
        exfalso; subst t
        apply t₁_t₂_disjoint.not_mem_of_mem_left x_step_mem x_step_mem_t

  case neg =>
    -- `x + eⱼ` is in `t₂`
    have x_step_mem : x + .single j 1 ∈ Cube t₂ := by
      have : x j ≤ c j + 1 := x_mem_c j |>.2
      have : x₁ j = c j + 1 := by simp +zetaDelta
      have : x₁ j < t₁ j + 1 := (Cube.mem_iff _ _).mp x₁_mem_t₁ j |>.2
      have := Cube.update_mem_of_mem x₂_mem_t₂ (y := x j + 1) (j := j) (by
        constructor <;> linarith)
      simpa [x₂, Point.add_single_eq_update] using this

    refine ⟨t₂, ⟨t₂_corner, x_step_mem⟩, ?_⟩

    · rintro t ⟨t_corner,x_step_mem_t⟩
      cases eq_t1_or_t2 t t_corner x_step_mem_t
      case inr h => exact h
      case inl h =>
        exfalso; subst t
        apply t₁_t₂_disjoint.not_mem_of_mem_right x_step_mem x_step_mem_t

/-- BHMN A.3 Fact 1 (roughly) -/
theorem core_covers_closedcube : ∀ x ∈ ClosedCube 0, ∃! t ∈ core T, x ∈ Cube t := by
  intro x x_mem

  -- x is in a cube in T
  obtain ⟨t,⟨t_corner,x_mem_t⟩,t_uniq⟩ := T.covers x

  -- this cube corner `t` must be in core because `x ∈ UnitCube d`
  have t_in_core : t ∈ core T := by
    simp [core]
    use t_corner
    exact CoreIndex.of_inter_closed_cube_nonempty ⟨x,x_mem,x_mem_t⟩

  use t, ⟨t_in_core,x_mem_t⟩
  -- but we must prove this is unique
  rintro t' ⟨t'_core,x_mem_t'⟩
  refine t_uniq _ ⟨core_subset_corners T t'_core,x_mem_t'⟩

theorem corners'_covers_closedcube : ∀ x ∈ ClosedCube 0, ∃! t ∈ corners' T, x ∈ Cube t := by
  intro x x_mem

  obtain ⟨t,⟨t_core,x_mem_t⟩,t_uniq⟩ := core_covers_closedcube T x x_mem

  use t, ⟨core_subset_corners' T t_core, x_mem_t⟩

  -- just need to prove uniqueness
  rintro t' ⟨t'_corner,x_mem_t'⟩

  -- the other `t'` should also have a periodic index
  have : Cube.index t' ∈ CoreIndex d :=
    CoreIndex.of_inter_closed_cube_nonempty ⟨x,x_mem,x_mem_t'⟩

  -- and therefore its membership in `corners'` is only possible with offset 0
  rcases t'_corner with ⟨t',⟨t'_corner,t'_pidx⟩,offset,rfl⟩
  have : offset = 0 := by
    ext j; specialize this j; specialize t'_pidx j
    rw [← IntPoint.toPoint_nsmul, Cube.index_add_intpoint] at this
    simp at t'_pidx this ⊢
    omega
  subst offset; simp [T.index_get] at this ⊢
  -- so `t'` is in `core`
  have : t' ∈ core T := ⟨t'_corner,t'_pidx⟩
  -- and therefore equal to t
  apply t_uniq _ ⟨this,by simpa using x_mem_t'⟩


/-- Inductive hypothesis for proving `corners'_covers` -/
def corners'_covers.UpTo (doneDims : Nat) :=
  ∀ (x : Point d) (_x_range : ∀ j : Fin d, j.val ≥ doneDims → 0 ≤ x j ∧ x j ≤ 1),
              ∃! t ∈ corners' T, x ∈ Cube t


theorem corners'_covers.zero : corners'_covers.UpTo T 0 := by
  intro x x_range
  have : x ∈ ClosedCube 0 := by intro j; simpa using x_range j
  apply corners'_covers_closedcube _ _ this

theorem split_real (x : ℝ) :
      ∃ x_int : Int, ∃ x_rem : ℝ, (0 ≤ x_rem ∧ x_rem < 1) ∧ x = x_int + x_rem := by
  let x_int : Int := ⌊x⌋
  use x_int, x - x_int
  refine ⟨⟨?_,?_⟩,?_⟩ <;> simp [x_int, Int.fract_lt_one]

theorem corners'_covers.step (doneDims : Nat) (doneDims_lt : doneDims < d) :
    UpTo T doneDims → UpTo T (doneDims + 1) := by
  intro ih x x_range

  obtain ⟨x_int,x_rem,x_rem_range,x_eq_sum⟩ := split_real (x ⟨doneDims,doneDims_lt⟩)

  -- first let's get a point that is in the IH range
  let x_prev := x.update ⟨doneDims,doneDims_lt⟩ x_rem

  -- and apply the IH
  have x_prev_uniq_covered := ih x_prev (by
    intro j hj
    if j.val = doneDims then
      subst doneDims
      simp [x_prev]; constructor <;> linarith [x_rem_range]
    else
      simp [x_prev, Fin.ext_iff, *]
      apply x_range; omega
  )

  -- now we case on whether the offset `x_int` is even or odd
  cases Int.even_or_odd x_int
  case inl x_int_even =>
    rcases x_int_even with ⟨x_int,rfl⟩
    convert corners'_uniquely_closed_even_addition T
        x_prev x_prev_uniq_covered (.single ⟨doneDims,doneDims_lt⟩ x_int)
    ext j
    by_cases hj : j.val = doneDims
    · subst hj; simp [x_prev, x_eq_sum]; ring
    · simp [hj, Fin.ext_iff, x_prev]

  case inr x_int_odd =>
    rcases x_int_odd with ⟨x_int,rfl⟩

    -- we can extend the IH to a cube containing `x_prev + .single doneDims 1`
    let corner : Point d := Point.ofFn fun j =>
      if j.val < doneDims then x j else 0

    have x_prev_mem_corner : x_prev ∈ ClosedCube corner := by
      intro j
      if j.val = doneDims then
        subst doneDims; simp [corner, x_prev]
        constructor <;> linarith
      else
        if j.val < doneDims then
          simp [corner, x_prev, Fin.ext_iff, *]
        else
          have := x_range j (by omega)
          simp [corner, x_prev, Fin.ext_iff, *]

    have := corners'_step_closed_cube T corner ⟨doneDims,doneDims_lt⟩ (by
      intro x' x'_range
      apply ih
      intro j hj
      if j.val = doneDims then
        subst doneDims
        have := x'_range j
        simpa [corner] using this
      else
        have : ¬ j.val < doneDims := by omega
        have := x_range j (by omega)
        have := x'_range j
        simp [corner, Fin.ext_iff, *] at this
        constructor <;> linarith
    )

    -- and then step by 2 • x_int to get back to x
    specialize this x_prev x_prev_mem_corner
    have := corners'_uniquely_closed_even_addition T _ this
      (.single ⟨doneDims, doneDims_lt⟩ x_int)
    convert this

    ext j
    if h : j.val = doneDims then
      subst doneDims
      simp at x_eq_sum
      simp [Fin.ext_iff, x_prev, x_eq_sum]; ring
    else
      simp [Fin.ext_iff, h, x_prev]

theorem corners'_covers : ∀ p : Point d, ∃! c, c ∈ corners' T ∧ p ∈ Cube c := by
  have : ∀ j (hj : j ≤ d), corners'_covers.UpTo T j := by
    intro j hj
    induction j with
    | zero => apply corners'_covers.zero
    | succ j ih =>
      specialize ih (Nat.le_of_lt hj)
      apply corners'_covers.step T _ hj ih

  intro p
  exact this d (Nat.le_refl _) p (by simp)

def T' : Tiling d where
  corners := corners' T
  covers := corners'_covers T

theorem T'_periodic : (T' T).Periodic := by
  intro t t_corner off
  simp [T'] at t_corner ⊢
  apply corners'_closed_even_addition _ _ t_corner

theorem T'_get_add_even_integer (x : Point d) (z : IntPoint d) :
    (T' T).get (x + 2 • z) = (T' T).get x + 2 • z := by
  rw [eq_comm]; apply Tiling.get_unique
  · apply corners'_closed_even_addition
    have := Tiling.get_mem (T' T) x
    simpa using this
  · rw [Cube.mem_add_iff]
    simpa using Tiling.mem_get (T' T) x

theorem T'_get_eq_T_get_of_core_idx (x : IntPoint d) (x_core : x ∈ CoreIndex d) :
    (T' T).get x = T.get x := by
  rw [eq_comm]; apply Tiling.get_unique
  · use T.get x
    constructor
    · use T.get_mem ..; rw [T.index_get]; exact x_core
    · use 0; simp
  · apply Tiling.mem_get

theorem T'_ff (T_ff : T.FaceshareFree) : (T' T).FaceshareFree := by
  let T' := T' T; refold_let T'

  -- per BHMN Prop 5, suppose there were facesharing neighbors
  apply Tiling.FaceshareFree.of_neighbors
  intro x j h

  -- split x into a core index and an even integer offset
  obtain ⟨x',x'_core,y,x_eq⟩ := CoreIndex.decompose_intpoint x

  have : T'.get x' + IntPoint.single j 1 = T'.get (x' + IntPoint.single j 1).toPoint := by
    calc
      _ = T'.get (x' + 2 • y + 2 • (-y).toPoint) + .single j 1 := by simp
      _ = T'.get (x' + 2 • y) + 2 • (-y).toPoint + .single j 1 := by rw [T'_get_add_even_integer, IntPoint.toPoint_neg]
      _ = T'.get x + 2 • (-y).toPoint + .single j 1            := by rw [x_eq]; simp
      _ = T'.get x + .single j 1 + 2 • (-y).toPoint            := by rw [add_right_comm]
      _ = T'.get (x + IntPoint.single j 1) + 2 • (-y).toPoint  := by rw [h, IntPoint.toPoint_add]
      _ = T'.get (x + IntPoint.single j 1 + 2 • (-y).toPoint)  := by rw [T'_get_add_even_integer]
      _ = T'.get (x + 2 • (-y).toPoint + IntPoint.single j 1)  := by rw [add_right_comm]
      _ = T'.get (x' + IntPoint.single j 1).toPoint := by rw [x_eq]; simp

  have := x'_core j; simp at this
  cases this
  next x'_j_zero =>
    apply T_ff (T.get_mem x') (T.get_mem (x' + .single j 1).toPoint)
      (by intro h; have := T.get_inj h |> congrArg (· j); simp at this)
    rw [T'_get_eq_T_get_of_core_idx _ _ x'_core,
        T'_get_eq_T_get_of_core_idx _ _ ?x'_step_core] at this
    case x'_step_core =>
      intro j'
      if j' = j then
        subst j'; simp [x'_j_zero]
      else
        simpa [*] using x'_core j'

    use j; rw [← this]; simp

  next x'_j_one =>
    replace this : T'.get x' + IntPoint.single j (-1) = T'.get (x' + IntPoint.single j (-1)).toPoint := by
      calc
        _ = T'.get x' + (IntPoint.single j 1 + (2 : ℕ) • IntPoint.single j (-1)).toPoint := by
          congr 1; apply congrArg; simp
        _ = T'.get x' + IntPoint.single j 1 + _ := by rw [IntPoint.toPoint_add, add_assoc]
        _ = T'.get (x' + IntPoint.single j 1).toPoint + _ := by rw [this]
        _ = T'.get (x' + IntPoint.single j 1).toPoint + 2 • IntPoint.single j (-1) := by simp
        _ = T'.get _ := by rw [← T'_get_add_even_integer, ← IntPoint.toPoint_nsmul, ← IntPoint.toPoint_add]
        _ = T'.get (x' + IntPoint.single j (-1)).toPoint := by
          rw [add_assoc]
          apply congrArg; apply congrArg; congr
          simp

    apply T_ff (T.get_mem x') (T.get_mem (x' + .single j (-1)).toPoint)
      (by intro h; have := T.get_inj h |> congrArg (· j); simp at this)
    rw [T'_get_eq_T_get_of_core_idx _ _ x'_core,
        T'_get_eq_T_get_of_core_idx _ _ ?x'_step_core] at this
    case x'_step_core =>
      intro j'
      if j' = j then
        subst j'; simp [x'_j_one]
      else
        simpa [*] using x'_core j'

    use j; rw [← this]; simp

end Hajos

open Hajos in
theorem Hajos (h : ¬ ∃ T : Tiling d, T.Periodic ∧ T.FaceshareFree) : conjectureIn d := by
  rintro ⟨T,T_ff⟩
  apply h ⟨T' T, T'_periodic T, T'_ff T T_ff⟩

/-- The periodic tiling reduction. Keller's conjecture is true if and only if
    it is true for periodic tilings. -/
theorem conjecture_iff_periodic : conjectureIn d ↔ (¬ ∃ T : Tiling d, T.Periodic ∧ T.FaceshareFree) := by
  constructor
  · rintro h ⟨T,-,ff⟩
    apply h ⟨T,ff⟩
  · apply Hajos

/--
info: 'Keller.Euclidean.conjecture_iff_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms conjecture_iff_periodic
