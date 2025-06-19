import Experiments.Keller.Euclidean.Defs

import Mathlib.Order.Partition.Basic

namespace Keller.Euclidean

def Line (j : Fin d) (x : Point d) : Set (Point d) :=
  { x.update j α | (α : ℝ) }

namespace Line

theorem mem_iff_all_eq (j : Fin d) (x y) :
      x ∈ Line j y ↔ ∀ j', j' ≠ j → x j' = y j' := by
  constructor
  · rintro ⟨α,rfl⟩ j' j'_ne
    simp [j'_ne]
  · intro h
    use x j
    ext j'
    if j' = j then
      subst j'; simp
    else
      simp [*]

@[simp] theorem start_mem (j : Fin d) (x) : x ∈ Line j x := by
  use x j; ext j'; simp [Point.update]

theorem mem_comm (j : Fin d) {x y : Point d} :
      x ∈ Line j y ↔ y ∈ Line j x := by
  rw [Line.mem_iff_all_eq, Line.mem_iff_all_eq]
  apply forall_congr'; intro j'
  simp [eq_comm]

theorem mem_trans (j : Fin d) {x y z : Point d} :
      x ∈ Line j y → y ∈ Line j z → x ∈ Line j z := by
  intro h1 h2
  rw [Line.mem_iff_all_eq] at h1 h2 ⊢
  intro j' j'_ne
  rw [h1 j' j'_ne, h2 j' j'_ne]

theorem update_mem_iff {j : Fin d} {x y z} :
    y.update j z ∈ Line j x ↔ y ∈ Line j x := by
  simp [Line]
  constructor
  · rintro ⟨z',h⟩
    replace h := congrArg (·.update j (y j)) h; simp at h
    use y j, h
  · rintro ⟨z',rfl⟩
    simp

theorem add_single_mem_iff {j : Fin d} {x y α} :
    y + EuclideanSpace.single j α ∈ Line j x ↔ y ∈ Line j x := by
  simp [Point.add_single_eq_update, update_mem_iff]

end Line

def UnitInterval (j : Fin d) (x : Point d) : Set (Point d) :=
  { x + EuclideanSpace.single j α | (α : ℝ) (_ : 0 ≤ α ∧ α < 1) }

namespace UnitInterval

theorem range_of_mem (a_mem : a ∈ UnitInterval j x) :
      x j ≤ a j ∧ a j < x j + 1 := by
  simp [UnitInterval] at a_mem
  rcases a_mem with ⟨α,α_range,rfl⟩
  simpa

@[simp] theorem start_mem (j : Fin d) (x) : x ∈ UnitInterval j x := by
  use 0; simp

theorem end_not_mem (j : Fin d) (x) :
      x + unitVec j ∉ UnitInterval j x := by
  simp [unitVec, UnitInterval]

@[simp] theorem Nonempty (j : Fin d) (x) : (UnitInterval j x).Nonempty := by
  use x; apply start_mem

@[simp] theorem ne_empty (j : Fin d) (x) : (UnitInterval j x) = ∅ ↔ False := by
  simp; apply Set.Nonempty.ne_empty; simp

@[simp] theorem inj_iff {j : Fin d} (x y : Point d) :
    UnitInterval j x = UnitInterval j y ↔ x = y := by
  constructor
  · intro h
    have mem1 : x ∈ UnitInterval j y := h ▸ UnitInterval.start_mem j x
    have mem2 : y ∈ UnitInterval j x := h.symm ▸ UnitInterval.start_mem j y
    simp [UnitInterval] at mem1 mem2
    rcases mem1 with ⟨α,α_range,rfl⟩
    rcases mem2 with ⟨β,β_range,h⟩
    replace h := congrFun h j
    simp at h ⊢; rw [← EuclideanSpace.single_zero j, EuclideanSpace.single_inj_iff]
    linarith
  · rintro rfl; rfl

theorem app_eq_of_ne_of_mem {j j' : Fin d} (js_ne : j' ≠ j)
    {x y} (y_mem : y ∈ UnitInterval j x) : y j' = x j' := by
  rcases y_mem with ⟨α,α_range,rfl⟩
  simp [js_ne]

theorem inter_nonempty_implies_mem_line (j : Fin d) (x₁ x₂ : Point d) :
    (UnitInterval j x₁ ∩ UnitInterval j x₂).Nonempty → x₁ ∈ Line j x₂ := by
  intro h
  use x₁ j
  ext j'
  if js_ne : j' = j then
    subst j'; simp
  else
  rw [Point.app_update_ne js_ne]
  rcases h with ⟨x,h₁,h₂⟩
  trans x j'
  · rw [eq_comm]; exact app_eq_of_ne_of_mem js_ne h₂
  · exact app_eq_of_ne_of_mem js_ne h₁

theorem inter_nonempty_implies_diff_lt_one (j : Fin d) (x₁ x₂ : Point d) :
    (UnitInterval j x₁ ∩ UnitInterval j x₂).Nonempty → |x₁ j - x₂ j| < 1 := by
  rintro ⟨x,h₁,h₂⟩
  have g₁ := range_of_mem h₁
  have g₂ := range_of_mem h₂
  rw [abs_sub_lt_iff]
  constructor <;> linarith

theorem inter_nonempty_of_mem_line {j : Fin d} {x y : Point d}
    (in_line : x ∈ Line j y) (close : |x j - y j| < 1)
  : (UnitInterval j x ∩ UnitInterval j y).Nonempty := by
  wlog h_le : x j ≤ y j generalizing x y
  · rw [Line.mem_comm] at in_line
    rw [abs_sub_comm] at close
    rw [Set.inter_comm]
    apply this ‹_› ‹_›; linarith
  rcases in_line with ⟨x,rfl⟩
  rw [abs_of_nonpos (by linarith)] at close
  simp at close h_le
  use y; constructor
  · simp [UnitInterval]
    use y j - x
    simp [h_le, close]
  · apply UnitInterval.start_mem

end UnitInterval

namespace Cube

theorem inter_line_eq_inter_interval {t : Point d} {j x} :
    Cube t ∩ Line j x = Cube t ∩ UnitInterval j (x.update j (t j))
  := by
  ext y; simp only [Set.mem_inter_iff, and_congr_right_iff]
  intro y_mem
  simp [UnitInterval]
  constructor
  · rintro ⟨y,rfl⟩
    use y - t j
    constructor
    · have := (Cube.mem_iff _ _).mp y_mem j
      simp at this
      constructor <;> linarith
    · ext j'
      by_cases j' = j <;> simp [*]
  · rw [Line.mem_iff_all_eq]
    rintro ⟨α,α_range,rfl⟩ j' j'_ne
    simp [j'_ne]

theorem inter_interval_empty_of_not_mem {t : Point d} {j} {x : Point d}
        (not_mem : ¬ x.update j (t j) ∈ Cube t)
      : Cube t ∩ UnitInterval j (x.update j (t j)) = ∅ := by
  -- the hypothesis says there's some j' where x is out of range
  rw [Cube.mem_iff] at not_mem
  set_option push_neg.use_distrib true in
  push_neg at not_mem
  rcases not_mem with ⟨j',t_j'_range⟩
  -- this j' cannot be j because it is in range on j
  have j'_ne : j' ≠ j := by rintro rfl; simp at t_j'_range; linarith
  -- thus we're really talking about x being out of range
  simp [j'_ne] at t_j'_range
  -- if something is in both the cube and interval, x must be in range! contradiction
  ext y; simp; intro y_mem_cube y_mem_interval
  replace y_mem_cube := (Cube.mem_iff _ _).mp y_mem_cube j'
  replace y_mem_interval := UnitInterval.app_eq_of_ne_of_mem j'_ne y_mem_interval
  simp [j'_ne] at y_mem_interval
  cases t_j'_range <;> linarith

theorem inter_interval_eq_self_of_mem {t : Point d} {j} {x : Point d} :
    x.update j (t j) ∈ Cube t → Cube t ∩ UnitInterval j (x.update j (t j)) = UnitInterval j (x.update j (t j)) := by
  intro mem
  -- proving the interval subsets the cube
  rw [Set.inter_eq_right]
  rintro y ⟨α,α_range,rfl⟩
  -- which means proving in range for every dimension j'
  rw [Point.update_add_single]
  rw [Cube.mem_iff] at mem ⊢
  intro j'; specialize mem j'
  if j'_ne : j' = j then
    subst j'; simp [α_range]
  else
  simpa [j'_ne] using mem

theorem inter_line_eq_interval {t : Point d} {j x} :
    (Cube t ∩ Line j x).Nonempty →
    Cube t ∩ Line j x = UnitInterval j (x.update j (t j))
  := by
  intro inter_nonempty
  rw [inter_line_eq_inter_interval] at inter_nonempty ⊢
  apply inter_interval_eq_self_of_mem
  rcases inter_nonempty with ⟨y,y_mem_cube,⟨α,α_range,rfl⟩⟩
  simp at y_mem_cube
  rw [Cube.mem_iff] at y_mem_cube ⊢
  intro j'; specialize y_mem_cube j'
  if j' = j then
    subst j'; simp
  else
    simp_all

theorem inter_line_nonempty_iff_start_mem (t : Point d) (j x) :
    (Cube t ∩ Line j x).Nonempty ↔ (x.update j (t j)) ∈ Cube t
  := by
  constructor
  · intro h
    have := inter_line_eq_interval h
    have := congrArg (x.update j (t j) ∈ ·) this
    simp at this
    exact this.1
  · intro h
    refine ⟨_, h, ?_⟩
    use t j

theorem update_mem_of_inter_line_nonempty {t : Point d} {j x} (z : ℝ)
    (inter_ne : (Cube t ∩ Line j x).Nonempty) (h : t j ≤ z ∧ z < t j + 1)
    : x.update j z ∈ Cube t := by
  rw [inter_line_nonempty_iff_start_mem] at inter_ne
  rw [mem_iff] at inter_ne ⊢
  intro j'; specialize inter_ne j'
  if js_ne : j' = j then
    subst j'; simp [h]
  else
    simpa [js_ne] using inter_ne

end Cube


structure Line.UnitPartition (j : Fin d) (x) where
  partition : Partition (Line j x)
  unit_intervals : ∀ i ∈ partition.parts, ∃ a, i = UnitInterval j a

namespace Line.UnitPartition

variable {j : Fin d} (P : Line.UnitPartition j x)

def starts := { start | UnitInterval j start ∈ P.partition.parts }
def start_coords : Set ℝ := { a j | a ∈ P.starts }

theorem exists_start_coord (a_mem : a ∈ P.partition.parts) :
      ∃ start, a = UnitInterval j (x.update j start) := by
  rcases P.unit_intervals a a_mem with ⟨start,rfl⟩
  use start j
  have start_mem := P.partition.le_of_mem a_mem (UnitInterval.start_mem ..)
  rcases start_mem with ⟨start,rfl⟩
  rw [UnitInterval.inj_iff]
  ext j'
  if j'_ne : j' = j then subst j'; simp else
  simp [start_mem, j'_ne]

theorem mem_start_coords :
      a ∈ P.start_coords ↔ UnitInterval j (x.update j a) ∈ P.partition.parts := by
  constructor
  · rintro ⟨a,ha,rfl⟩
    have ⟨start,h⟩ := P.exists_start_coord ha
    rw [UnitInterval.inj_iff] at h; subst a
    simpa using ha
  · intro h
    refine ⟨_, h, ?_⟩
    simp

theorem covers (a : Point d) (a_mem : a ∈ Line j x) :
    ∃ b, b ∈ P.start_coords ∧ a ∈ UnitInterval j (x.update j b) := by
  rw [← P.partition.sSup_eq, Set.sSup_eq_sUnion] at a_mem
  simp at a_mem
  rcases a_mem with ⟨interval,mem_part,a_mem⟩
  rcases P.unit_intervals _ mem_part with ⟨b,rfl⟩
  have ⟨start, h⟩ := P.exists_start_coord mem_part
  rw [UnitInterval.inj_iff] at h; subst b
  use start
  constructor <;> simpa [mem_start_coords]

theorem starts_gap {a b} (a_mem : a ∈ P.start_coords) (b_mem : b ∈ P.start_coords) (ne : a ≠ b) :
    |a - b| ≥ 1 := by
  wlog a_ge_b : a ≤ b generalizing a b
  · rw [abs_sub_comm]
    exact this b_mem a_mem ne.symm (by linarith)
  rw [abs_of_nonpos (by linarith)]
  by_contra h; simp [sub_lt_iff_lt_add, add_comm] at h
  simp [mem_start_coords] at a_mem b_mem
  have disjoint := P.partition.disjoint a_mem b_mem (by
    simp [UnitInterval.inj_iff, Point.update_inj]; exact ne)
  apply disjoint.not_mem_of_mem_right (UnitInterval.start_mem ..)
  simp [UnitInterval, Point.update_inj]
  use b - a
  refine ⟨⟨?_,?_⟩,?_⟩ <;> linarith

theorem step_forward (a_mem : a ∈ P.start_coords) : a + 1 ∈ P.start_coords := by
  -- a+1 must be in some interval starting at b
  have ⟨b,b_mem,mem_b⟩ := P.covers (x.update j (a+1)) (by simp [Line])
  -- we will show a+1 *is* b
  suffices a+1 = b by rw [this]; exact b_mem
  -- since a+1 is in the interval at b, b ≤ a+1 < b + 1
  simp [UnitInterval, Point.update_inj] at mem_b
  rcases mem_b with ⟨α, α_range, h⟩
  -- simultaneously, |b-a| ≥ 1
  have gap := P.starts_gap a_mem b_mem
  clear a_mem b_mem
  specialize gap (by linarith)
  -- this is enough to conclude a+1 = b
  rw [abs_of_neg (by linarith)] at gap
  linarith

theorem step_backward (a_mem : a ∈ P.start_coords) : a - 1 ∈ P.start_coords := by
  -- a-1 must be in some interval starting at b
  have ⟨b,b_mem,mem_b⟩ := P.covers (x.update j (a-1)) (by simp [Line])
  -- and therefore b+1 is the start of an interval
  have := P.step_forward b_mem
  -- we can prove a=b+1
  suffices a = b+1 by subst a; simpa using b_mem
  -- because either a, b+1 are either equal or they have a gap.
  have gap := P.starts_gap a_mem this
  clear a_mem b_mem
  -- ... and they don't have a gap.
  by_contra hne
  specialize gap hne

  -- since a-1 is in the b interval, we can bound it:
  have : b ≤ a-1 ∧ a-1 < b+1 := by
    simpa using UnitInterval.range_of_mem mem_b

  -- contradiction!
  rw [abs_of_nonneg (by linarith)] at gap
  linarith

theorem start_coords_eq_Z ⦃a : ℝ⦄ (a_mem : a ∈ P.start_coords) :
    P.start_coords = { a + ↑z | z : ℤ } := by

  -- the RHS is a subset of the LHS
  have subset1 : { a + ↑z | z:ℤ } ⊆ P.start_coords := by
    rintro _ ⟨z,rfl⟩
    induction z using Int.induction_on with
    | hz => simpa using a_mem
    | hp i h => simp; convert P.step_forward h using 1; simp; ring
    | hn i h => convert P.step_backward h using 1; simp; ring

  -- so let's prove by double inclusion
  apply subset1.antisymm'
  intro p p_mem
  -- there is a point in the RHS just below p
  let b : ℝ := a + Int.floor (p - a)
  have b_mem_RHS : b ∈ {a + ↑z | z:ℤ} := by simp [b]
  -- in fact, p = b
  suffices p = b by rw [this]; exact b_mem_RHS
  -- from the other direction's subset, we know b ∈ LHS
  have b_mem_LHS : b ∈ P.start_coords := subset1 b_mem_RHS
  -- therefore either p = b or there's a gap
  have := P.starts_gap p_mem b_mem_LHS
  -- but there can't be such a gap
  by_contra p_ne_b; specialize this p_ne_b
  have b_le_p : b ≤ p := by unfold b; have := Int.floor_le (p-a); linarith
  have p_lt_b1 : p < b+1 := by unfold b; have := Int.lt_floor_add_one (p-a); linarith
  rw [abs_of_nonneg (by linarith)] at this
  linarith

end Line.UnitPartition


/-- The `T_i(x)` operation in Brakensiek. -/
def ILattice.inter_line (corners : Set (Point d)) (j : Fin d) (x : Point d) :=
  { corner ∈ corners | (Cube corner ∩ Line j x).Nonempty }

/-- i-lattice defn from Brakensiek (approximately) -/
-- TODO(JG): `structure` automatically generates projections, can I just turn that off?
inductive ILattice.integral_spaced (corners : Set (Point d)) (j : Fin d) : Prop
| intro
    (offset : ℝ)
    (corner_to_Z : ∀ c ∈ corners, ∃ z:ℤ, c j = offset + z)
    (Z_to_corner : ∀ z:ℤ, ∃! c ∈ corners, c j = offset + z)

theorem ILattice.integral_spaced.exists_unique_range {j : Fin d} (is : ILattice.integral_spaced corners j) :
    ∀ a : ℝ, ∃! c ∈ corners, c j ≤ a ∧ a < c j + 1 := by
  rcases is with ⟨off,c2Z,Z2c⟩
  intro a
  -- ⌊a-off⌋ has a corresponding cube corner
  specialize Z2c ⌊a - off⌋
  rcases Z2c with ⟨c,⟨c_is_corner,c_j⟩,corner_unique⟩
  -- this cube corner fulfills the condition
  use c; constructor
  · simp [c_is_corner,c_j]
    constructor
    · rw [add_comm, ← le_sub_iff_add_le]; apply Int.floor_le
    · rw [add_assoc,add_comm,← sub_lt_iff_lt_add]; apply Int.lt_floor_add_one
  -- and it is unique
  · rintro c' ⟨c'_corner,c'_j_range⟩
    apply corner_unique; clear corner_unique
    refine ⟨c'_corner,?_⟩
    specialize c2Z c' c'_corner
    rcases c2Z with ⟨z,c'_j⟩
    rw [c'_j] at c'_j_range ⊢; clear c'_j
    simp
    rw [eq_comm, Int.floor_eq_iff]
    constructor <;> linarith

structure ILattice (d : ℕ) (j : Fin d) where
  corners : Set (Point d)
  inter_line_integral_spaced : ∀ (x : Point d),
    ILattice.integral_spaced (ILattice.inter_line corners j x) j

def ILattice.line_partition_of_tiling (j : Fin d) (x : Point d) (T : Tiling d) : Line.UnitPartition j x where
  partition := {
    parts := T.corners.image (Cube · ∩ Line j x) \ { ∅ }
    sSupIndep' := by
      rw [sSupIndep_iff_pairwiseDisjoint]
      intro a a_mem b b_mem ne
      simp at a_mem b_mem
      rcases a_mem with ⟨⟨a,a_mem,rfl⟩,a_not_empty⟩
      rcases b_mem with ⟨⟨b,b_mem,rfl⟩,b_not_empty⟩
      simp [Function.onFun]
      apply Disjoint.inter_left; apply Disjoint.inter_right
      rw [Set.disjoint_iff]; rintro c ⟨c_mem_a,c_mem_b⟩
      have := (T.covers c).unique ⟨a_mem,c_mem_a⟩ ⟨b_mem,c_mem_b⟩
      subst this; simp at ne
    bot_not_mem' := by simp
    sSup_eq' := by
      simp
      apply Set.Subset.antisymm
      · intro y; simp
      · intro y y_mem_line
        simp
        have ⟨i,i_mem_corners,mem_i⟩ := (T.covers y).exists
        use i
  }
  unit_intervals := by
    intro i i_mem
    simp at i_mem
    rcases i_mem with ⟨⟨corner,corner_mem,rfl⟩,not_empty⟩
    have := Cube.inter_line_eq_interval <| Set.nonempty_iff_ne_empty.mpr not_empty
    refine ⟨_,this⟩


theorem ILattice.line_partition_start_coords (j : Fin d) (x T) :
        (line_partition_of_tiling j x T).start_coords =
        { t j | t ∈ (ILattice.inter_line T.corners j x)} := by
  simp only [line_partition_of_tiling, Line.UnitPartition.start_coords, Line.UnitPartition.starts,
    Set.mem_setOf_eq, Set.mem_diff, Set.mem_image]
  simp only [Set.mem_singleton_iff, UnitInterval.Nonempty, Set.Nonempty.ne_empty, not_false_eq_true,
    and_true]
  simp only [inter_line, Set.mem_setOf_eq]
  rw [Set.setOf_inj]; funext a; simp
  constructor
  · rintro ⟨y,⟨z,z_corner,h⟩,rfl⟩
    have := Cube.inter_line_eq_interval (by rw [h]; apply UnitInterval.Nonempty j y)
    use z
    simp [z_corner, h, (UnitInterval.Nonempty j y).ne_empty ]
    rw [this, UnitInterval.inj_iff] at h
    have := congrFun h j
    simpa using this
  · rintro ⟨y,⟨y_corner,inter_nonempty⟩,rfl⟩
    have := Cube.inter_line_eq_interval inter_nonempty
    refine ⟨_,⟨y,y_corner,this⟩,?_⟩
    simp


def ILattice.fromTiling (T : Tiling d) (j : Fin d) : ILattice d j where
  corners := T.corners
  inter_line_integral_spaced := by
    intro x
    -- get the line partition `T_i(x)`
    let line_part := line_partition_of_tiling j x T

    -- The cube `T.get x` must contain x, so it is a natural choice of starting point

    -- we're gonna need to know the start coords are integer spaced
    have start_coords_eq := line_part.start_coords_eq_Z
    specialize @start_coords_eq (T.get x j) (by
      use x.update j (T.get x j)
      simp [line_part, line_partition_of_tiling,
        Line.UnitPartition.starts, Line.UnitPartition.partition,
        -SetLike.mem_coe, -Partition.coe_parts]
      use T.get x
      constructor
      · apply T.get_mem
      · rw [Cube.inter_line_eq_interval]
        use x; simp [T.mem_get]
    )

    use T.get x j
    -- first gotta prove each line cube is at an integer offset
    · intro c c_mem
      have : c j ∈ line_part.start_coords := by
        use x.update j (c j)
        simp [line_part, line_partition_of_tiling,
          Line.UnitPartition.starts, Line.UnitPartition.partition,
          -SetLike.mem_coe, -Partition.coe_parts]
        use c
        simp [inter_line] at c_mem
        refine ⟨c_mem.1, ?_⟩
        rw [Cube.inter_line_eq_interval]
        exact c_mem.2
      rw [start_coords_eq] at this
      rcases this with ⟨z,h⟩
      use z, h.symm

    -- then that each integer offset is a unique cube
    · intro z
      have : T.get x j + z ∈ line_part.start_coords := by
        rw [start_coords_eq]; simp
      rcases this with ⟨w,w_mem_starts,w_j⟩
      simp [line_part, line_partition_of_tiling,
          Line.UnitPartition.starts, Line.UnitPartition.partition,
          -SetLike.mem_coe, -Partition.coe_parts] at w_mem_starts
      rcases w_mem_starts with ⟨c,c_is_corner,c_inter⟩
      have w_mem_c : w ∈ Cube c := by
        have := UnitInterval.start_mem j w; rw [← c_inter] at this
        exact this.1
      have : w = x.update j (c j) := by
        rw [Cube.inter_line_eq_interval ?ne, UnitInterval.inj_iff] at c_inter
        rw [c_inter]
        case ne => rw [c_inter]; simp
      subst w
      simp at w_j
      use c; constructor
      · simp [inter_line, c_is_corner, c_inter, w_j]
      · clear c_inter
        rintro c' ⟨⟨c'_corner,c'_inter_ne⟩,c'_j⟩
        refine T.covers_unique _ ⟨c'_corner, ?_⟩ ⟨c_is_corner,w_mem_c⟩
        rw [w_j, ← c'_j]
        rw [Cube.inter_line_nonempty_iff_start_mem] at c'_inter_ne
        exact c'_inter_ne


/-- Get the corners whose cube contains `x` -/
noncomputable def ILattice.covers (L : ILattice d j) (x : Point d) :
    ∃! t ∈ L.corners, x ∈ Cube t := by
  have ⟨off,corner_to_Z,Z_to_corner⟩ := L.inter_line_integral_spaced x
  let a := Int.floor (x j - off)
  specialize Z_to_corner a
  simp [inter_line] at Z_to_corner
  convert Z_to_corner using 1
  ext t; simp [and_assoc]; intro t_mem
  constructor
  · intro x_mem
    have inter_ne : (Cube t ∩ Line j x).Nonempty := ⟨x,x_mem,Line.start_mem _ _⟩
    refine ⟨inter_ne,?_⟩
    specialize corner_to_Z t ⟨t_mem,inter_ne⟩
    rcases corner_to_Z with ⟨a₀,h⟩
    rw [h]; simp
    have : a ≤ x j - off := Int.floor_le _
    have : x j - off < (a + 1 : ℤ) := Int.lt_succ_floor _
    have := (Cube.mem_iff x t).mp x_mem j
    rw [h] at this
    linarith
    done
  · rintro ⟨inter_ne,t_j⟩
    have := Cube.update_mem_of_inter_line_nonempty
    rw [Cube.inter_line_eq_inter_interval] at h
    have := (not_imp_not.mpr Cube.inter_interval_empty_of_not_mem) h.1.ne_empty
    rw [h.2] at this
    simp [a] at this
    done

def ILattice.toTiling (L : ILattice d j) : Tiling d where
  corners := L.corners
  covers := L.covers

def ILattice.replace (a b : ℝ) (L : ILattice d j) : ILattice d j where
  corners :=
    { (t + EuclideanSpace.single j b) | (t ∈ L.corners) (_ : ∃ z, t j = a + z) }
    ∪ { (t) | (t ∈ L.corners) (_ : ∀ z, t j ≠ a + z)}
  inter_line_integral_spaced := by
    intro x
    sorry

def Tiling.replace (j : Fin d) (a b : ℝ) (T : Tiling d) : Tiling d :=
  ILattice.fromTiling T j |>.replace a b |>.toTiling

theorem Tiling.corners_replace {j : Fin d} {a b : ℝ} (T : Tiling d) :
    T.replace j a b |>.corners =
