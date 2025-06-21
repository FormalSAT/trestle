import Experiments.Keller.Euclidean.Basic
import Experiments.Keller.Euclidean.TilingStructure

namespace Keller.Euclidean

def Tiling.Periodic (T : Tiling d) : Prop :=
  ∀ t ∈ T.corners, ∀ x : IntPoint d, t + 2 • x ∈ T.corners

/-- `{0,1}ᵈ` on paper -/
def PeriodicIndex (d : Nat) := { i : IntPoint d | ∀ j, i j ∈ ({0,1} : Set ℤ) }

theorem PeriodicIndex.mem_iff_real_range : i ∈ PeriodicIndex d ↔ ∀ j, (-1 : ℝ) < i j ∧ i j < (2 : ℝ) := by
  constructor
  · intro h j; specialize h j
    aesop
  · intro h j
    suffices -1 < i j ∧ i j < 2 by
      simp; omega
    simpa [← Int.cast_lt (R := ℝ)] using h j

/-- if a cube intersects with the origin unit cube `[0,1]ᵈ`,
    then its integer index must be in `{0,1}ᵈ` -/
theorem PeriodicIndex.of_inter_unitcube_cube_nonempty (h : (UnitCube d ∩ Cube t).Nonempty)
    : Cube.index t ∈ PeriodicIndex d := by
  rw [PeriodicIndex.mem_iff_real_range]
  intro j
  rcases h with ⟨x,x_mem_unit,x_mem_t⟩
  specialize x_mem_unit j
  replace x_mem_t := Cube.close_of_mem_cube x_mem_t (Cube.index_mem _) j
  simp [IntPoint.toPoint, abs_lt] at x_mem_t
  constructor <;> linarith

theorem PeriodicIndex.decompose_intpoint (x : IntPoint d) :
      ∃ x' ∈ PeriodicIndex d, ∃ y : IntPoint d, x = x' + 2 • y := by

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

def core := { t ∈ T.corners | (Cube.index t ∈ PeriodicIndex d)}
def corners' := {t + (2 • x).toPoint | (t ∈ core T) (x : IntPoint d)}

theorem core_subset_corners : core T ⊆ T.corners := by
  apply Set.sep_subset

theorem core_subset_corners' : core T ⊆ corners' T := by
  rintro t t_mem
  use t, t_mem, 0
  simp

theorem core_covers_unitcube : ∀ x ∈ UnitCube d, ∃! t ∈ core T, x ∈ Cube t := by
  intro x x_mem

  -- x is in a cube in T
  obtain ⟨t,⟨t_corner,x_mem_t⟩,t_uniq⟩ := T.covers x

  -- this cube corner `t` must be in core because `x ∈ UnitCube d`
  have t_in_core : t ∈ core T := by
    simp [core]
    use t_corner
    exact PeriodicIndex.of_inter_unitcube_cube_nonempty ⟨x,x_mem,x_mem_t⟩

  use t, ⟨t_in_core,x_mem_t⟩
  -- but we must prove this is unique
  rintro t' ⟨t'_core,x_mem_t'⟩
  refine t_uniq _ ⟨core_subset_corners T t'_core,x_mem_t'⟩

/-- BHMN A.3 Fact 1 -/
theorem corners'_covers_unitcube : ∀ x ∈ UnitCube d, ∃! t ∈ corners' T, x ∈ Cube t := by
  intro x x_mem

  obtain ⟨t,⟨t_core,x_mem_t⟩,t_uniq⟩ := core_covers_unitcube T x x_mem

  use t, ⟨core_subset_corners' T t_core, x_mem_t⟩

  rintro t' ⟨t'_corner,x_mem_t'⟩

  -- the other `t'` should also have a periodic index
  have : Cube.index t' ∈ PeriodicIndex d :=
    PeriodicIndex.of_inter_unitcube_cube_nonempty ⟨x,x_mem,x_mem_t'⟩

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

/-- from the unitcube, we can always step either forward or backward by 1
    and remain in the core.

    this is heavily modified from BHMN, and is the key lemma
    used in `corners'_covers` -/
theorem core_can_step_unitcube : ∀ x ∈ UnitCube d, ∀ j : Fin d,
    (∃ t ∈ core T, x + .single j 1 ∈ Cube t) ∨
    (∃ t ∈ core T, x - .single j 1 ∈ Cube t) := by
  intro x x_mem_unit_cube j

  -- get the core cube containing `x`
  obtain ⟨t,⟨⟨t_corner,t_pidx⟩,x_mem_t⟩,-⟩ := core_covers_unitcube T x x_mem_unit_cube

  -- we'll need the integral spaced line through `x`
  have int_spaced_line := ILattice.fromTiling T j |>.inter_line_IntegralSpaced x
  -- and that `t` intersects the line
  have t_mem_inter : t ∈ ILattice.inter_line T.corners j x :=
    ⟨t_corner,x,x_mem_t,Line.start_mem ..⟩

  -- case on whether the index of `t` is 0 or 1 in dimension j
  cases t_pidx j
  case inl ti_j =>
    -- the step forward case
    left

    -- get the next cube in the line
    obtain ⟨t',⟨⟨t'_corner,t'_inter_ne⟩,t_j_step⟩,-⟩ := int_spaced_line.exists_unique_next t_mem_inter

    -- `x + eⱼ` is in the `t'` cube
    have x'_mem_t' : x + .single j 1 ∈ Cube t' := by
      rw [Point.add_single_eq_update]
      apply Cube.update_mem_of_inter_line_nonempty _ t'_inter_ne
      have := (Cube.mem_iff _ _).mp x_mem_t j
      constructor <;> linarith

    -- and its index is periodic
    have t'_pidx : Cube.index t' ∈ PeriodicIndex d := by
      rw [PeriodicIndex.mem_iff_real_range]
      intro j'

      -- unfold defn of Cube.index and bound the ceil operation
      simp only [Cube.index] at ti_j ⊢
      generalize t'i_j' : ⌈t' j'⌉ = t'i
      simp [Int.ceil_eq_iff] at ti_j t'i_j'

      -- if `j' = j`, we use `next_in_line` to justify the bounds
      if hj' : j' = j then
        subst j'
        constructor <;> linarith
      -- otherwise, can bound based on `x`
      else
        -- since `x ∈ UnitCube d`, we can bound `x j' ∈ [0,1)`
        specialize x_mem_unit_cube j'

        -- because `x' ∈ Cube t'`, we know `x j' ∈ [t' j', t' j'+1)`
        replace x'_mem_t' := (Cube.mem_iff _ _).mp x'_mem_t' j'

        simp [hj'] at x'_mem_t'
        constructor <;> linarith

    use t', ⟨t'_corner,t'_pidx⟩


  case inr ti_j =>
    -- the step backward case. this argument is very very similar to the forward case.
    right

    -- get the next cube in the line
    obtain ⟨t',⟨⟨t'_corner,t'_inter_ne⟩,t_j_step⟩,-⟩ := int_spaced_line.exists_unique_prev t_mem_inter

    -- `x - eⱼ` is in the `t'` cube
    have x'_mem_t' : x - .single j 1 ∈ Cube t' := by
      rw [sub_eq_add_neg, ← EuclideanSpace.single_neg, Point.add_single_eq_update]
      apply Cube.update_mem_of_inter_line_nonempty _ t'_inter_ne
      have := (Cube.mem_iff _ _).mp x_mem_t j
      constructor <;> linarith

    -- and its index is periodic
    have t'_pidx : Cube.index t' ∈ PeriodicIndex d := by
      rw [PeriodicIndex.mem_iff_real_range]
      intro j'

      -- unfold defn of Cube.index and bound the ceil operation
      simp only [Cube.index] at ti_j ⊢
      generalize t'i_j' : ⌈t' j'⌉ = t'i
      simp [Int.ceil_eq_iff] at ti_j t'i_j'

      -- if `j' = j`, we use `next_in_line` to justify the bounds
      if hj' : j' = j then
        subst j'
        constructor <;> linarith
      -- otherwise, can bound based on `x`
      else
        -- since `x ∈ UnitCube d`, we can bound `x j' ∈ [0,1)`
        specialize x_mem_unit_cube j'

        -- because `x' ∈ Cube t'`, we know `x j' ∈ [t' j', t' j'+1)`
        replace x'_mem_t' := (Cube.mem_iff _ _).mp x'_mem_t' j'

        simp [hj'] at x'_mem_t'
        constructor <;> linarith

    use t', ⟨t'_corner,t'_pidx⟩

theorem split_point (x : Point d) :
      ∃ x_int : IntPoint d, ∃ x_rem ∈ UnitCube d, x = x_int + x_rem := by
  let x_int : IntPoint d := fun j => ⌊x j⌋
  use x_int, x - x_int
  constructor
  · intro j; simp [x_int, Int.fract_lt_one]
  · ext j; simp [x_int]

theorem corners'_covers (p : Point d) : ∃! c, c ∈ corners' T ∧ p ∈ Cube c := by
  obtain ⟨p_int,p_rem,p_rem_mem_unitcube,rfl⟩ := split_point p

  -- for every dimension,
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

  obtain ⟨x',x'_pidx,y,x_eq⟩ := PeriodicIndex.decompose_intpoint x
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
