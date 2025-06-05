import Experiments.Keller.Euclidean.Defs

import Mathlib.Order.Partition.Basic

namespace Keller.Euclidean

def Line (j : Fin d) (x : Point d) : Set (Point d) :=
  { x.update j α | (α : ℝ) }

theorem Line.mem_iff (j : Fin d) (x y) :
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

@[simp] theorem Line.start_mem (j : Fin d) (x) : x ∈ Line j x := by
  use x j; ext j'; simp [Point.update]

theorem Line.mem_comm (j : Fin d) {x y : Point d} :
      x ∈ Line j y ↔ y ∈ Line j x := by
  rw [Line.mem_iff, Line.mem_iff]
  apply forall_congr'; intro j'
  simp [eq_comm]

theorem Line.mem_trans (j : Fin d) {x y z : Point d} :
      x ∈ Line j y → y ∈ Line j z → x ∈ Line j z := by
  intro h1 h2
  rw [Line.mem_iff] at h1 h2 ⊢
  intro j' j'_ne
  rw [h1 j' j'_ne, h2 j' j'_ne]


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

theorem UnitInterval.range_of_mem (a_mem : a ∈ UnitInterval j x) :
      x j ≤ a j ∧ a j < x j + 1 := by
  simp [UnitInterval] at a_mem
  rcases a_mem with ⟨α,α_range,rfl⟩
  simpa

@[simp] theorem UnitInterval.start_mem (j : Fin d) (x) : x ∈ UnitInterval j x := by
  use 0; simp

theorem UnitInterval.end_not_mem (j : Fin d) (x) :
      x + unitVec j ∉ UnitInterval j x := by
  simp [unitVec, UnitInterval]

@[simp] theorem UnitInterval.Nonempty (j : Fin d) (x) : (UnitInterval j x).Nonempty := by
  use x; apply start_mem

theorem UnitInterval.inj_iff {j : Fin d} (x y : Point d) :
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

theorem UnitInterval.app_eq_of_ne_of_mem {j j' : Fin d} (js_ne : j' ≠ j)
    {x y} (y_mem : y ∈ UnitInterval j x) : y j' = x j' := by
  rcases y_mem with ⟨α,α_range,rfl⟩
  simp [js_ne]

theorem UnitInterval.inter_nonempty_implies_mem_line (j : Fin d) (x₁ x₂ : Point d) :
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

theorem UnitInterval.inter_nonempty_implies_diff_lt_one (j : Fin d) (x₁ x₂ : Point d) :
    (UnitInterval j x₁ ∩ UnitInterval j x₂).Nonempty → |x₁ j - x₂ j| < 1 := by
  rintro ⟨x,h₁,h₂⟩
  have g₁ := range_of_mem h₁
  have g₂ := range_of_mem h₂
  rw [abs_sub_lt_iff]
  constructor <;> linarith

theorem UnitInterval.inter_nonempty_of_mem_line {j : Fin d} {x y : Point d}
    (in_line : x ∈ Line j y) (close : |x j - y j| < 1)
  : (UnitInterval j x ∩ UnitInterval j y).Nonempty := by
  wlog h_le : x j ≤ y j generalizing x y
  · rw [Line.mem_comm] at in_line
    rw [abs_sub_comm] at close
    rw [Set.inter_comm]
    apply this ‹_› ‹_›; linarith
  rw [Line.mem_iff] at in_line
  rw [abs_of_nonpos (by linarith)] at close
  simp at close
  use y; constructor
  · simp [UnitInterval]
    use y j - x j
    simp [h_le, close]; clear h_le close
    ext j'
    if j' = j then
      subst j'; simp
    else
      simp [*]
  · apply UnitInterval.start_mem

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
  rw [Line.mem_iff] at start_mem
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
  { corner ∈ corners | Cube corner ∩ Line j x ≠ ∅}

/-- i-lattice defn from Brakensiek (approximately) -/
def ILattice.integral_spaced (corners : Set (Point d)) (j : Fin d) :=
  ∃ a : ℝ, ∀ z:ℤ, ∃! c ∈ corners, c j = a + z

theorem ILattice.integral_spaced.exists_unique_range (is : ILattice.integral_spaced corners j) :
    ∀ a : ℝ, ∃! c ∈ corners, c j ≤ a ∧ a < c j + 1 := by
  rcases is with ⟨off,h⟩
  intro a
  -- off + ⌊a-off⌋ is in the RHS set, so there must be a corresponding cube corner
  have mem_corner := congrArg (off + ⌊a - off⌋ ∈ ·) h; simp at mem_corner
  rcases mem_corner with ⟨c,corner,c_j⟩
  -- this cube corner fulfills the condition
  use c; constructor
  · simp [corner, c_j]
    constructor
    · rw [add_comm, ← le_sub_iff_add_le]; apply Int.floor_le
    · rw [add_assoc,add_comm,← sub_lt_iff_lt_add]; apply Int.lt_floor_add_one
  -- and it is unique
  · rintro c' ⟨c'_corner,c'_j⟩
    -- .. because any other corner must also be in the RHS set
    have c'_int := congrArg (c' j ∈ ·) h; simp at c'_int
    replace c'_int := c'_int.mp ⟨c',c'_corner,rfl⟩
    rcases c'_int with ⟨z,h2⟩
    done

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
    have := Line.inter_cube corner j x not_empty
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
    have := Line.inter_cube z j x (by rw [h]; apply (UnitInterval.Nonempty j y).ne_empty)
    use z
    simp [z_corner, h, (UnitInterval.Nonempty j y).ne_empty ]
    rw [this, UnitInterval.inj_iff] at h
    have := congrFun h j
    simpa using this
  · rintro ⟨y,⟨y_corner,inter_nonempty⟩,rfl⟩
    have := Line.inter_cube y j x inter_nonempty
    refine ⟨_,⟨y,y_corner,this⟩,?_⟩
    simp


def ILattice.fromTiling (T : Tiling d) (j : Fin d) : ILattice d j where
  corners := T.corners
  inter_line_integral_spaced := by
    intro x
    -- get the line partition `T_i(x)`
    let line_part := line_partition_of_tiling j x T
    -- The cube `T.get x` must contain x, so it is a natural choice of starting point
    use T.get x j
    intro z
    -- we need to prove there's a unique cube corresponding to `T.get x j + z`
    -- the line partition starting coords are integral-spaced
    have := line_partition_start_coords j x T ▸ line_part.start_coords_eq_Z
    specialize @this z; simp at this
    apply this; clear this starts_eq line_part
    simp [inter_line]
    refine ⟨_,⟨T.get_mem x,?_⟩,rfl⟩
    apply Set.Nonempty.ne_empty; use x
    simp [T.mem_get]

/-- Get the corners whose cube contains `x` -/
noncomputable def ILattice.getSet (x : Point d) (L : ILattice d j) : Set (Point d) :=
  { t ∈ L.corners | x ∈ Cube t }

theorem ILattice.getSet_singleton (x : Point d) (L : ILattice d j) :
    ∃ t, L.getSet x = {t} := by
  have ⟨off,h⟩ := L.inter_line_integral_spaced x
  let a := off + Int.floor (x j - off)
  have h2 := congrArg (a ∈ ·) h
  simp [a] at h2
  rcases h2 with ⟨t,⟨t_corner,nonempty⟩,t_j⟩

def ILattice.toTiling (L : ILattice d j) : Tiling d where
  corners := L.corners
  covers := by
    intro p
    have := L.inter_line_integral_spaced p
    simp [integral_spaced,inter_line] at this
    rcases this with ⟨off,h⟩
    let a := off + Int.floor (p j - off)
    have a_mem : a ∈ {off + ↑z|z:ℤ} := by simp [a]
    rw [← h] at a_mem; simp at a_mem
    rcases a_mem with ⟨c,⟨c_corner,inter_nonempty⟩,eq⟩
    sorry

def ILattice.replace (a b : ℝ) (L : ILattice d j) : ILattice d j where
  corners :=
    { corner | ∃ t ∈ L.corners, t L.j ≡ a [PMOD 1] ∧ corner = t + EuclideanSpace.single L.j b }
    ∪ { t | t ∈ L.corners ∧ ¬ (t L.j ≡ a [PMOD 1])}
  j := L.j
  condition := by
    sorry

def Tiling.replace (j : Fin d) (a b : ℝ) (T : Tiling d) : Tiling d :=
  ILattice.fromTiling T j |>.replace a b |>.toTiling

theorem Tiling.replace
