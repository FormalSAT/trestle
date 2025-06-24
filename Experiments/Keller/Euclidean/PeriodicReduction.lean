import Experiments.Keller.Euclidean.Basic
import Experiments.Keller.Euclidean.TilingStructure

namespace Keller.Euclidean

def Tiling.Periodic (T : Tiling d) : Prop :=
  ∀ t ∈ T.corners, ∀ x : IntPoint d, t + 2 • x ∈ T.corners

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
def corners' := {t + (2 • x).toPoint | (t ∈ core T) (x : IntPoint d)}

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
  use t + (2 • (off + z)).toPoint
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

  -- get the points where `Line j x` intersects the boundary of `ClosedCube c`
  let x₀ := x.update j (c j)
  let x₁ := x.update j (c j + 1)

  have x₀_mem_c : x₀ ∈ ClosedCube c := by
    intro j'
    if j' = j then subst j'; simp [x₀]
    else
      simp [x₀, x_mem_c j', *]

  -- those points must both be covered uniquely by corners'
  obtain ⟨t₀,⟨t₀_corners',x₀_mem_t₀⟩,t₀_uniq⟩ := h x₀ x₀_mem_c

  obtain ⟨t₁,⟨t₁_corners',x₁_mem_t₁⟩,t₁_uniq⟩ := h x₁ <| by
    intro j'
    if j' = j then subst j'; simp [x₁]
    else
      simp [x₁, x_mem_c j', *]

  -- the interval between x₀ and x₁ is uniquely covered,
  -- so the cubes containing x₀ and x₁ must be adjacent
  have : t₀ j + 1 = t₁ j := by
    apply cubes_adjacent_of_uniquely_covers_interval (corners' T) j x₀ ?h
      t₀_corners' x₀_mem_t₀ t₁_corners' (by simpa [Point.add_single_eq_update, x₀])
    intro α α_range
    apply h
    simp [x₀]
    intro j'
    if j' = j then subst j'; simpa using α_range else
    simp [*, x_mem_c j']

  -- either `x ∈ t₀`, which implies `x + eⱼ ∈ t₁`
  if x j < t₀ j + 1 then
    use t₁
    refine ⟨⟨t₁_corners',?step_mem⟩,?uniq⟩
    case step_mem =>
      rw [Cube.mem_iff]; intro j'
      if j' = j then
        have := (Cube.mem_iff _ _).mp x₀_mem_t₀ j
        have := x_mem_c j
        subst j'
        simp_all +zetaDelta; linarith
      else
        have := (Cube.mem_iff _ _).mp x₁_mem_t₁ j'
        simp_all +zetaDelta

    case uniq =>
      rintro t ⟨t_corner,x_step_mem_t⟩
      if t j ≤ c j + 1 then
        apply t₁_uniq
        use t_corner
        have := Cube.update_mem_of_mem x_step_mem_t (y := c j + 1) (j := j) (by
          have := (Cube.mem_iff _ _).mp x_step_mem_t j
          have := x_mem_c j
          simp_all; linarith)
        simpa [Point.add_single_eq_update] using this
      else
        exfalso
        have one := x_mem_c j
        have two := (Cube.mem_iff _ _).mp x_step_mem_t j
        simp at one two
        have := corners'_uniquely_closed_even_addition T x₀ (h x₀ x₀_mem_c) (.single j 1)
          |>.unique (y₁ := t) (y₂ := t₀ + (2 • IntPoint.single j 1).toPoint)
          ?first_goal ?second_goal
        case first_goal =>
          use t_corner; simp [x₀, Point.add_single_eq_update]
          have := Cube.update_mem_of_mem x_step_mem_t (y := c j + 2) (j := j) (by
            constructor <;> linarith)
          simpa [Point.add_single_eq_update] using this
        case second_goal =>
          have := corners'_closed_even_addition T _ t₀_corners' (.single j 1)
          use (by simpa using this)
          rw [Cube.mem_add_iff]; simpa using x₀_mem_t₀
        replace this := congrArg (· j) this; simp at this
        linarith

  -- or `x ∈ t₁`, which implies `x + eⱼ ∈ t₀ + 2eⱼ`
  else
    use t₀ + 2 • IntPoint.single j 1
    refine ⟨⟨?mem_corners',?step_mem⟩,?uniq⟩
    case mem_corners' =>
      apply corners'_closed_even_addition T _ t₀_corners'
    case step_mem =>
      rw [Cube.mem_iff]; intro j'
      if js_ne : j' = j then
        subst j'
        have := (Cube.mem_iff _ _).mp x₁_mem_t₁ j
        have := x_mem_c j
        simp [x₁] at *
        constructor <;> linarith
      else
        have := (Cube.mem_iff _ _).mp x₀_mem_t₀ j'
        unfold x₀ at this
        simp [js_ne] at this ⊢
        simpa using this

    case uniq =>
      rintro t ⟨t_corner,x_step_mem_t⟩
      have one := x_mem_c j
      have two := (Cube.mem_iff _ _).mp x_step_mem_t j
      simp at one two

      if t j ≤ c j + 1 then
        exfalso
        have := t₁_uniq _ ⟨t_corner,?mem⟩
        case mem =>
          have := Cube.update_mem_of_mem x_step_mem_t (y := c j + 1) (j := j) (by
            have := (Cube.mem_iff _ _).mp x_step_mem_t j
            have := x_mem_c j
            simp_all; linarith)
          simpa [Point.add_single_eq_update] using this
        replace this := congrArg (· j) this; simp at this
        linarith

      else
        have := corners'_uniquely_closed_even_addition T x₀ (h x₀ x₀_mem_c) (.single j 1)
          |>.unique (y₁ := t) (y₂ := t₀ + (2 • IntPoint.single j 1).toPoint)
          ?first_goal ?second_goal
        case first_goal =>
          use t_corner; simp [x₀, Point.add_single_eq_update]
          have := Cube.update_mem_of_mem x_step_mem_t (y := c j + 2) (j := j) (by
            constructor <;> linarith)
          simpa [Point.add_single_eq_update] using this
        case second_goal =>
          have := corners'_closed_even_addition T _ t₀_corners' (.single j 1)
          use (by simpa using this)
          rw [Cube.mem_add_iff]; simpa using x₀_mem_t₀
        simpa [Point.add_single_eq_update] using this

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

@[deprecated]
theorem corners'_covers_unitcube : ∀ x ∈ ClosedCube 0, ∃! t ∈ corners' T, x ∈ Cube t := by
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
    rw [Cube.index_add_intpoint] at this
    simp at t'_pidx this ⊢
    omega
  subst offset; simp [T.index_get] at this ⊢
  -- so `t'` is in `core`
  have : t' ∈ core T := ⟨t'_corner,t'_pidx⟩
  -- and therefore equal to t
  apply t_uniq _ ⟨this,by simpa using x_mem_t'⟩


/-- Inductive hypothesis for proving `corners'_covers` -/
structure corners'_covers.UpTo (doneDims : Nat) where
  covers : ∀ (x : Point d) (_x_range : ∀ j : Fin d, j.val ≥ doneDims → 0 ≤ x j ∧ x j < 1),
              ∃! t ∈ corners' T, x ∈ Cube t


theorem corners'_covers.zero : corners'_covers.UpTo T 0 := by
  intro x x_range
  have : x ∈ UnitCube d := by simpa using x_range
  apply corners'_covers_unitcube _ _ this

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
  let x_prev := Point.ofFn (d := d) fun j =>
    if j.val = doneDims then x_rem
    else x j

  -- and apply the IH
  specialize ih x_prev (by
    intro j hj
    if j.val = doneDims then
      subst doneDims
      simp [x_prev]; exact x_rem_range
    else
      simp [x_prev, *]
      apply x_range; omega
  )

  obtain ⟨t_prev,⟨t_prev_corner,x_prev_mem⟩,t_prev_uniq⟩ := ih

  -- now we note that
  sorry

theorem corners'_can_step (x : Point d) (j : Fin d) (z : ℤ) :
    (∃ t ∈ corners' T, x ∈ Cube t) → ∃ t ∈ corners' T, (x + .single j z) ∈ Cube t := by
  rintro ⟨t,t_corners',x_mem_t⟩
  -- per defn of corners', `t` is even offset from a core cube
  obtain ⟨t,t_core,offset,rfl⟩ := t_corners'

  by_cases Even z
  -- if `z` is even, we can directly reuse `t`
  case pos evenz =>
    rcases evenz with ⟨z,rfl⟩
    refine ⟨t + (2 • (offset + IntPoint.single j z)).toPoint
      , ?in_corners',?x_mem⟩
    case in_corners' =>
      use t, t_core, offset + IntPoint.single j z
    case x_mem =>
      rw [Cube.mem_add_iff] at x_mem_t ⊢
      convert x_mem_t using 1
      ext j'; by_cases j' = j <;> simp [*]
      ring
  -- if `z` is odd, we need to step either forward or backward within the core
  case neg oddz =>
    rw [Int.not_even_iff_odd] at oddz; rcases oddz with ⟨z,rfl⟩
    have := core_can_step_unitcube
    done

theorem split_point (x : Point d) :
      ∃ x_int : IntPoint d, ∃ x_rem ∈ UnitCube d, x = x_int + x_rem := by
  let x_int : IntPoint d := fun j => ⌊x j⌋
  use x_int, x - x_int
  constructor
  · intro j; simp [x_int, Int.fract_lt_one]
  · ext j; simp [x_int]

theorem corners'_covers (p : Point d) : ∃! c, c ∈ corners' T ∧ p ∈ Cube c := by
  obtain ⟨p_int,p_rem,p_rem_mem_unitcube,rfl⟩ := split_point p

  -- basically,
  sorry

def T' : Tiling d where
  corners := corners' T
  covers := corners'_covers T

theorem T'_periodic : (T' T).Periodic := by
  simp [T', Tiling.Periodic, corners', core]
  rintro t i hi x x'
  use i, hi, x+x'
  ext j; simp [mul_add]; abel

theorem T'_ff (T_ff : T.FaceshareFree) : (T' T).FaceshareFree := by
  let T' := T' T; refold_let T'

  -- use BHMN Prop 5
  apply Tiling.FaceshareFree.of_neighbors
  intro x j h

  obtain ⟨x',x'_pidx,y,x_eq⟩ := CoreIndex.decompose_intpoint x
  cases x'_pidx j
  next x'_j_zero =>
    have : T'.get x' + .single j 1 = T'.get (x' + .single j 1).toPoint := by
      calc
        _ = T'.get (x' + (2 : ℤ) • y + (-2) • y) + .single j 1 := by done
        _ = T'.get (x' + 2 • y) + (-2) • y + .single j 1 := by done
        _ = T'.get x + (-2) • y + .single j 1 := by
            rw [x_eq, IntPoint.toPoint_add, IntPoint.toPoint_smul]
    done
  next x'_j_one =>
    done

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
