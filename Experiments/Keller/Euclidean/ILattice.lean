import Experiments.Keller.Euclidean.Defs

namespace Keller.Euclidean

def Line (j : Fin d) (x : Point d) : Set (Point d) :=
  { x.update j α | (α : ℝ) }

@[simp] theorem Line.mem (j : Fin d) (x) : x ∈ Line j x := by
  use x j; ext j'; simp [Point.update]

theorem Line.add_single_mem_iff {j : Fin d} {x y α} :
    y + EuclideanSpace.single j α ∈ Line j x ↔ y ∈ Line j x := by
  simp [Line, Point.add_single_eq_update]
  constructor
  · rintro ⟨β,h⟩
    use β + -α
    replace h := congrArg (· + EuclideanSpace.single j (-α)) h
    conv at h => lhs; simp
    rw [h]; simp
  · rintro ⟨β,rfl⟩
    simp

def UnitInterval (j : Fin d) (x : Point d) : Set (Point d) :=
  { x + EuclideanSpace.single j α | (α : ℝ) (_ : 0 ≤ α ∧ α < 1) }

@[simp] theorem UnitInterval.mem (j : Fin d) (x) : x ∈ UnitInterval j x := by
  use 0; simp

theorem Line.inter_cube (t : Point d) (j x) :
    Cube t ∩ Line j x ≠ ∅ →
    Cube t ∩ Line j x = UnitInterval j (x.update j (t j))
  := by
  intro inter_nonempty
  -- prove each direction of inclusion separately
  ext y
  constructor
  · -- if `y` is in the intersection, it is in the interval
    rintro ⟨mem_cube,mem_line⟩
    simp only [UnitInterval, Point.update_add_single, exists_prop, Set.mem_setOf_eq]
    -- `α` is just the diff between `y` and `t` in dim j
    use y j - t j
    constructor
    · -- `α` is in range [0,1) because `y` is in `Cube t`
      rw [Cube.mem_iff] at mem_cube
      specialize mem_cube j
      constructor <;> linarith
    · -- interval start + e_j * `α` = y
      ext j'
      if js_ne : j' = j then
        subst j'
        simp
      else
        rcases mem_line with ⟨y,rfl⟩
        simp [*]
  · -- if `y` is in the interval, it is in the intersection
    rintro ⟨α,α_range,rfl⟩
    constructor
    · simp [Cube.mem_iff]
      intro j'
      simp [Point.update]
      if js_ne : j' = j then
        subst j'
        simp [α_range]
      else
        simp [js_ne]
        -- in every direction other than `j`, we can bound `x j'`
        -- because of `inter_nonempty`
        rw [← Set.nonempty_iff_ne_empty] at inter_nonempty
        rcases inter_nonempty with ⟨z,z_mem_cube,z_mem_line⟩
        rw [Cube.mem_iff] at z_mem_cube; specialize z_mem_cube j'
        rcases z_mem_line with ⟨z,rfl⟩
        simpa [js_ne] using z_mem_cube
    · -- adding in the direction j is still in the Line
      simp [Line]

theorem Line.partition_is_Z_shifted {j x} (intervals : Set (Point d))
      (intervals_mem : ∀ i ∈ intervals, i ∈ Line j x)
      (intervals_partition : ∀ y ∈ Line j x, ∃! i ∈ intervals, y ∈ UnitInterval j i)
  : ∃ y : Point d, intervals = { y + EuclideanSpace.single j (z : ℝ) | z : ℤ } := by

  -- The gap between intervals must be at least 1
  have gap_at_least_one : ∀ a ∈ intervals, ∀ y : ℝ, |y| < 1 →
        let b := a + EuclideanSpace.single j y;
        b ∈ intervals → y = 0 := by
    intro a a_mem y y_range b b_mem
    wlog y_pos : 0 ≤ y generalizing y a b
    · specialize this b b_mem (-y) (by simp [y_range])
        (by convert a_mem using 1; simp [EuclideanSpace.single_neg, b])
        (by linarith)
      simpa using this
    suffices a = b by
      unfold b at this
      have := congrArg (· j) this
      simp at this; simp [this]
    -- b is in a unique interval
    apply intervals_partition _ (intervals_mem _ b_mem) |>.unique
    · simp [a_mem, b, UnitInterval]
      have : 0 ≤ y ∧ y < 1 := ⟨y_pos,lt_of_abs_lt y_range⟩
      use y
    · simp [b_mem, UnitInterval.mem]

  -- can step forward by 1
  have step_forward : ∀ a ∈ intervals, (a + EuclideanSpace.single j 1) ∈ intervals := by
    intro a a_mem
    have ⟨b,b_mem,h⟩ := intervals_partition (a + EuclideanSpace.single j 1)
        (by simp [Line.add_single_mem_iff]; apply intervals_mem; exact a_mem)
      |>.exists

    simp [UnitInterval] at h
    rcases h with ⟨α,α_range,h⟩
    have := gap_at_least_one a a_mem (b j - a j)
    convert b_mem
    done
  -- Starting from any interval, any integer offset must also be an interval
  have : ∀ y ∈ intervals, ∀ z : ℤ, (y + EuclideanSpace.single j (z : ℝ)) ∈ intervals := by
    done

  -- Any intervals that are < 1 dist away
  -- First let's get an arbitrary interval to use as the starting point `y`
  rcases intervals_partition x (Line.mem _ _) with ⟨y,⟨y_mem,-⟩,-⟩
  use y
  sorry

structure ILattice (d : ℕ) where
  corners : Set (Point d)
  j : Fin d
  condition : ∀ (x : Point d), ∃ (a : ℝ),
    { t j   | (t : Point d) (_ : t ∈ corners) (_ : Cube t ∩ Line j x ≠ ∅) } =
    { a + z | (z : ℤ) }

def ILattice.fromTiling (T : Tiling d) (j : Fin d) : ILattice d where
  corners := T.corners
  j := j
  condition := by
    intro x
    use (T.get x) j; simp
    ext y; simp
    constructor
    · rintro ⟨t,inter_nonempty,t_mem,rfl⟩
      rw [← ne_eq, ← Set.nonempty_iff_ne_empty] at inter_nonempty
      rcases inter_nonempty with ⟨z,z_mem_cube,z_mem_line⟩
      done
    · done
