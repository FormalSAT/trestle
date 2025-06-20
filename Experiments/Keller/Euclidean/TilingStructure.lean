import Experiments.Keller.Euclidean.Basic
import Experiments.Keller.Euclidean.Upstream

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

theorem nonempty : (Line j x).Nonempty := ⟨x,start_mem ..⟩

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

/-! ### Integral Spaced -/

structure IntegralSpaced (S : Set ℝ) where
  nonempty : S.Nonempty
  spaced : ∀ x ∈ S, S = {x + ↑z | z : ℤ}

namespace IntegralSpaced
variable (h : IntegralSpaced S)
include h

theorem eq_add_of_mem_of_mem (hx : x ∈ S) (hy : y ∈ S) :
    ∃ z : ℤ, x + z = y := by
  rw [h.spaced x hx] at hy
  simpa using hy

theorem add_mem (hx : x ∈ S) (z : ℤ) : (x + z) ∈ S := by
  rw [h.spaced x hx]; simp

theorem exists_offset : ∃ x ∈ S, S = {x + ↑z | z : ℤ} := by
  rcases h.nonempty with ⟨x,x_mem⟩
  use x, x_mem, h.spaced x x_mem

theorem unique_range (x : ℝ) :
      ∃! s ∈ S, s ≤ x ∧ x < s + 1 := by
  rcases h.exists_offset with ⟨off, -, rfl⟩; clear h
  use off + ⌊x - off⌋
  simp
  have := Int.floor_le (x - off)
  have := Int.lt_floor_add_one (x - off)
  constructor
  · constructor <;> linarith
  · intro z h₁ h₂
    rw [eq_comm, Int.floor_eq_iff]
    constructor <;> linarith

theorem image (hf : ∀ x z, f (x + z) = f x + z) : IntegralSpaced (f '' S) := by
  constructor
  · apply h.nonempty.image
  · rintro _ ⟨x,x_mem,rfl⟩
    have := h.spaced x x_mem; clear h x_mem; subst S
    ext y
    simp [hf]

end IntegralSpaced

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

def start_coords_IntegralSpaced : IntegralSpaced P.start_coords where
  nonempty := by
    have ⟨w,hw,_⟩ := P.covers x (Line.start_mem ..)
    use w
  spaced := by
    intro a a_mem

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


namespace ILattice

/-- The `T_i(x)` operation in Brakensiek. -/
def inter_line (corners : Set (Point d)) (j : Fin d) (x : Point d) :=
  { corner ∈ corners | (Cube corner ∩ Line j x).Nonempty }

theorem mem_inter_line (t : Point d) :
  t ∈ inter_line corners j x ↔ t ∈ corners ∧ (Cube t ∩ Line j x).Nonempty
  := by simp [inter_line]

theorem inter_line.union {c1 c2 : Set (Point d)} {j x} :
    inter_line (c1 ∪ c2) j x = inter_line c1 j x ∪ inter_line c2 j x := by
  simp [inter_line]

theorem inter_line.filter {cs : Set (Point d)} {j x} (P : Point d → Prop) :
    inter_line {c ∈ cs | P c} j x = {c ∈ inter_line cs j x | P c} := by
  simp [inter_line]; aesop

theorem inter_line.image {cs : Set (Point d)} {j x}
    (h : ∀ t, (Cube (f t) ∩ Line j x).Nonempty ↔ (Cube t ∩ Line j x).Nonempty):
    inter_line (f '' cs) j x = f '' inter_line cs j x := by
  ext t; simp [inter_line]
  aesop

/-- i-lattice defn from Brakensiek (approximately) -/
structure IntegralSpaced (corners : Set (Point d)) (j : Fin d) where
  starts_inj : ∀ t₁ ∈ corners, ∀ t₂ ∈ corners, t₁ j = t₂ j → t₁ = t₂
  integral_spaced : Euclidean.IntegralSpaced ((· j) '' corners)

namespace IntegralSpaced

theorem exists_unique_range {j : Fin d}
    (is : ILattice.IntegralSpaced corners j) :
    ∀ a : ℝ, ∃! c ∈ corners, c j ≤ a ∧ a < c j + 1 := by
  intro a
  have := is.integral_spaced.unique_range a
  simp at this
  rcases this with ⟨_,⟨⟨c,c_corner,rfl⟩,range⟩,uniq⟩
  refine ⟨c,⟨c_corner,range⟩,?_⟩
  rintro c' ⟨c'_corner,range'⟩
  apply is.starts_inj _ c'_corner _ c_corner
  apply uniq
  exact ⟨⟨c',c'_corner,rfl⟩,range'⟩

theorem image_linear {j : Fin d} (is : ILattice.IntegralSpaced corners j) :
      ILattice.IntegralSpaced ((· + v) '' corners) j := by
  constructor
  case starts_inj =>
    simp; intro t₁ t₁_mem t₂ t₂_mem starts_eq
    have := is.starts_inj _ t₁_mem _ t₂_mem
    simpa [starts_eq] using this
  case integral_spaced =>
    have := is.integral_spaced.image (f := (· + v j))
              (by intros; simp; ring)
    rw [Set.image_image] at this ⊢
    simpa using this

end IntegralSpaced

end ILattice

structure ILattice (d : ℕ) (j : Fin d) where
  corners : Set (Point d)
  inter_line_IntegralSpaced : ∀ (x : Point d),
    ILattice.IntegralSpaced (ILattice.inter_line corners j x) j

namespace ILattice

def line_partition_of_tiling (j : Fin d) (x : Point d) (T : Tiling d) : Line.UnitPartition j x where
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


theorem line_partition_start_coords (j : Fin d) (x T) :
        (line_partition_of_tiling j x T).start_coords =
        { t j | t ∈ (ILattice.inter_line T.corners j x)} := by
  simp only [line_partition_of_tiling, Line.UnitPartition.start_coords, Line.UnitPartition.starts,
    Set.mem_setOf_eq, Set.mem_diff, Set.mem_image]
  simp only [Set.mem_singleton_iff, UnitInterval.Nonempty, Set.Nonempty.ne_empty, not_false_eq_true,
    and_true]
  simp only [mem_inter_line]
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


def fromTiling (T : Tiling d) (j : Fin d) : ILattice d j where
  corners := T.corners
  inter_line_IntegralSpaced := by
    intro x

    -- get the line partition `T_i(x)`
    let line_part := line_partition_of_tiling j x T

    -- we're gonna need to know the start coords are integer spaced
    have start_coords_spaced := line_part.start_coords_IntegralSpaced

    constructor
    case starts_inj =>
      clear start_coords_spaced
      rintro t₁ ⟨t₁_corner,t₁_line⟩ t₂ ⟨t₂_corner,t₂_line⟩ starts_eq
      apply T.covers_unique (x.update j (t₁ j))
      · use t₁_corner
        apply Cube.update_mem_of_inter_line_nonempty _ t₁_line
        simp
      · use t₂_corner
        rw [starts_eq]
        apply Cube.update_mem_of_inter_line_nonempty _ t₂_line
        simp

    case integral_spaced =>
      convert start_coords_spaced
      rw [line_partition_start_coords]
      ext t
      simp


/-- Every `x` is contained by a unique cube -/
theorem covers (L : ILattice d j) (x : Point d) :
    ∃! t ∈ L.corners, x ∈ Cube t := by
  -- The `j`-line through `x` is integral spaced
  have := L.inter_line_IntegralSpaced x
  -- so there is a unique corner where x is in range.
  replace this := this.exists_unique_range (x j)
  simp [mem_inter_line, and_assoc] at this
  -- this condition is the same as our desired condition
  convert this using 3; clear this; next t =>
  constructor
  · intro h
    refine ⟨⟨x,h,Line.start_mem ..⟩,?_⟩
    exact (Cube.mem_iff _ _).mp h j
  · rintro ⟨inter_ne,x_j_range⟩
    have := Cube.update_mem_of_inter_line_nonempty (x j) inter_ne x_j_range
    simpa using this

def toTiling (L : ILattice d j) : Tiling d where
  corners := L.corners
  covers := L.covers

def replace (a b : ℝ) (L : ILattice d j) : ILattice d j where
  /- for corners that are integer offset from a, we shift by b.
    other corners stay in place -/
  corners :=
    { t ∈ L.corners | ∃ z : ℤ, a + z = t j }.image (· + EuclideanSpace.single j b)
    ∪ { t ∈ L.corners | ¬ ∃ z : ℤ, a + z = t j }
  inter_line_IntegralSpaced := by
    intro x

    rw [inter_line.union, inter_line.image ?h, inter_line.filter, inter_line.filter]
    case h =>
      intro t
      simp [Cube.inter_line_nonempty_iff_start_mem]
      rw [Cube.mem_add_iff,
          sub_eq_add_neg,
          ← EuclideanSpace.single_neg]
      simp

    generalize ucdef : setOf _ = updated_corners
    generalize scdef : setOf _ = same_corners

    -- the line through x is integral spaced
    have line_IS := L.inter_line_IntegralSpaced x

    -- either all are equal to `a` modulo 1 or none are
    by_cases h : ∃ t ∈ inter_line L.corners j x, a = t j
    · suffices ∀ t ∈ inter_line L.corners j x, ∃ z : ℤ, a + z = t j by
        have sub1 : same_corners = ∅ := by
          ext t; subst same_corners; simp; exact this t
        have sub2 : updated_corners = inter_line L.corners j x := by
          ext t; subst updated_corners; simp; exact this t
        subst sub1 sub2; rw [Set.union_empty]
        apply line_IS.image_linear
      clear! updated_corners same_corners
      rcases h with ⟨t,h,rfl⟩
      intro t' t'_mem
      apply line_IS.integral_spaced.eq_add_of_mem_of_mem
        <;> aesop

    · suffices ∀ t ∈ inter_line L.corners j x, ¬∃ z : ℤ, a + z = t j by
        have sub1 : same_corners = inter_line L.corners j x := by
          ext t; specialize this t; subst same_corners; simpa using this
        have sub2 : updated_corners = ∅ := by
          ext t; specialize this t; subst updated_corners; simpa using this
        subst sub1 sub2; rw [Set.image_empty, Set.empty_union]
        exact line_IS
      clear! updated_corners same_corners

      push_neg at h ⊢
      intro t t_mem z t_j

      have := line_IS.integral_spaced.add_mem (x := t j) (by aesop) (-z)
      simp [← t_j] at this
      obtain ⟨w, w_mem, rfl⟩ := this
      apply h _ w_mem rfl

end ILattice

/-- The replacement lemma! -/
def Tiling.replace (j : Fin d) (a b : ℝ) (T : Tiling d) : Tiling d :=
  ILattice.fromTiling T j |>.replace a b |>.toTiling

theorem Tiling.corners_replace {j : Fin d} {a b : ℝ} (T : Tiling d) :
    (T.replace j a b).corners =
    { t ∈ T.corners | ∃ z : ℤ, a + z = t j }.image (· + EuclideanSpace.single j b)
    ∪ { t ∈ T.corners | ¬ ∃ z : ℤ, a + z = t j }
:= by rfl
