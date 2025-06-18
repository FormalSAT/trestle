import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic

import Experiments.Keller.Euclidean.Upstream

namespace Keller.Euclidean

/-- This is the equivalent to `ℝᵈ` in math -/
abbrev Point (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- The unit cube, `[0,1)ᵈ` -/
def UnitCube (d : ℕ) : Set (Point d) :=
  fun point =>
    ∀ j : Fin d, 0 ≤ point j ∧ point j < 1

/-- The unit cube transposed to `corner`: `[0, 1)ᵈ + corner` -/
def Cube {d : ℕ} (corner : Point d) : Set (Point d) :=
  (corner + ·) '' (UnitCube d)

/-- Two cubes faceshare if their corners are 1 apart in one dimension and equal in every other. -/
def Faceshare (c1 c2 : Point d) : Prop :=
  ∃ j, |c1 j - c2 j| = 1 ∧ ∀ j2 ≠ j, c1 j2 = c2 j2

/-- A tiling is a set of cubes such that all points in `ℝᵈ`
    are covered by exactly one cube.
    We represent the set of cubes as a set of their corners. -/
structure Tiling (d : ℕ) where
  corners : Set (Point d)
  covers : ∀ p : Point d, ∃! c ∈ corners, p ∈ Cube c

/-- A tiling is faceshare-free when every pair of cubes does not faceshare. -/
def Tiling.FaceshareFree (T : Tiling d) : Prop :=
  T.corners.Pairwise (¬ Faceshare · ·)

/-- Keller's conjecture in `d` dimensions: there is no faceshare-free tiling. -/
def conjectureIn (d : ℕ) : Prop := ¬ ∃ T : Tiling d, T.FaceshareFree




/-! #### Helper Defs/Lemmas -/

abbrev unitVec [DecidableEq ι] [RCLike 𝕜] (i : ι) := EuclideanSpace.single (𝕜 := 𝕜) i 1


noncomputable def Point.ofFn (f : Fin d → ℝ) : Point d := (EuclideanSpace.equiv _ _).symm f
@[simp] theorem Point.app_ofFn (x) (f : Fin d → ℝ) : (Point.ofFn f) x = f x := rfl
@[simp] theorem Point.ofFn_point (x : Point d) : Point.ofFn x = x := rfl

noncomputable def Point.update (x : Point d) (j : Fin d) (y : ℝ) :=
  Point.ofFn <| Function.update x j y
@[simp] theorem Point.app_update_eq : Point.update x j y j = y := by
  simp [Point.update]
@[simp] theorem Point.app_update_ne (h : j' ≠ j) : Point.update x j y j' = x j' := by
  simp [Point.update, h]

@[simp] theorem Point.update_app {x : Point d} {j} : Point.update x j (x j) = x := by
  simp [Point.update]

theorem Point.update_inj {x} {j : Fin d} {a b} :
    Point.update x j a = Point.update x j b ↔ a = b := by
  constructor
  · intro h
    replace h := congrFun h j
    simpa using h
  · rintro rfl; rfl

theorem Point.add_single_eq_update {x : Point d} {j α} :
      x + EuclideanSpace.single j α = x.update j (x j + α) := by
  ext j'
  if j' = j then
    subst j'; simp
  else
    simp [*]

@[simp] theorem Point.update_update {x : Point d} {j α α'} :
      (x.update j α).update j α' = x.update j α' := by
  simp [Point.update]

@[simp] theorem Point.update_add_single {x : Point d} {j y α} :
      x.update j y + EuclideanSpace.single j α = x.update j (y + α) := by
  rw [add_single_eq_update]; simp


abbrev IntPoint (d : ℕ) : Type := Fin d → ℤ
noncomputable def IntPoint.toPoint {d : ℕ} (p : IntPoint d) : Point d :=
  Point.ofFn fun j => p j

noncomputable instance : Coe (IntPoint d) (Point d) where
  coe := IntPoint.toPoint

theorem Cube.mem_iff (x : Point d) (c : Point d) :
    x ∈ Cube c ↔ ∀ j, c j ≤ x j ∧ x j < c j + 1 := by
  unfold Cube UnitCube; simp; simp [Set.mem_def]

lemma Cube.exists_gap_of_inter_empty (c1 c2 : Point d) :
      (Cube c1 ∩ Cube c2 = ∅) → (∃ j : Fin d, |c1 j - c2 j| ≥ 1) := by
  intro inter_empty
  by_contra no_gaps
  push_neg at no_gaps
  -- we can construct a point that is in both
  let x : Point d := Point.ofFn fun j => max (c1 j) (c2 j)
  have mem_c1 : x ∈ Cube c1 := by
    rw [Cube.mem_iff]
    intro j
    specialize no_gaps j; rw [abs_lt] at no_gaps
    simp [x]; linarith
  have mem_c2 : x ∈ Cube c2 := by
    rw [Cube.mem_iff]
    intro j
    specialize no_gaps j; rw [abs_lt] at no_gaps
    simp [x]; linarith
  clear no_gaps; clear_value x
  apply Set.not_mem_empty x; rw [← inter_empty]
  simp [mem_c1, mem_c2]

lemma Cube.inter_empty_of_exists_gap (c1 c2 : Point d) :
      (∃ j : Fin d, |c1 j - c2 j| ≥ 1) → (Cube c1 ∩ Cube c2 = ∅) := by
  rintro ⟨j,gap_at_j⟩
  ext x; simp
  intro mem_c1
  replace mem_c1 : c1 j ≤ x j ∧ x j < c1 j + 1 := by
    rw [Cube.mem_iff] at mem_c1
    exact mem_c1 j

  set_option push_neg.use_distrib true in
  rw [Cube.mem_iff]; push_neg; use j

  if h : c1 j ≤ c2 j then
    replace gap_at_j : c1 j + 1 ≤ c2 j := by
      rw [abs_of_nonpos (by linarith)] at gap_at_j
      linarith
    left
    calc
      _ < c1 j + 1  := mem_c1.2
      _ ≤ c2 j      := gap_at_j
  else
    replace gap_at_j : c2 j + 1 ≤ c1 j := by
      rw [abs_of_nonneg (by linarith)] at gap_at_j
      linarith
    right
    calc
      _ ≤ c1 j  := gap_at_j
      _ ≤ x j   := mem_c1.1

theorem Cube.inter_empty_iff_exists_gap (c1 c2 : Point d) :
    (Cube c1 ∩ Cube c2 = ∅) ↔ (∃ j, |c1 j - c2 j| ≥ 1) := by
  constructor
  · apply Cube.exists_gap_of_inter_empty
  · apply Cube.inter_empty_of_exists_gap

noncomputable def Cube.index (c : Point d) : IntPoint d :=
  fun j => Int.ceil (c j)

theorem Cube.index_mem (c : Point d) : (Cube.index c).toPoint ∈ Cube c := by
  simp [index, IntPoint.toPoint, Cube.mem_iff]
  intro j; constructor
  · apply Int.le_ceil
  · apply Int.ceil_lt_add_one

theorem Cube.index_unique {c : Point d} {x : IntPoint d} :
    x.toPoint ∈ Cube c → x = Cube.index c := by
  intro h; ext j
  rw [Cube.mem_iff] at h; specialize h j
  simp [IntPoint.toPoint] at h
  unfold index; rw [eq_comm, Int.ceil_eq_iff]
  constructor <;> linarith


theorem Faceshare.symm {c1 c2 : Point d} (h : Faceshare c1 c2) :
    Faceshare c2 c1 := by
  unfold Faceshare at h ⊢
  simp_rw [abs_sub_comm (c2 _), eq_comm (a := c2 _)]
  exact h


/-
Takes a point p and a tiling T and returns the unique corner in T such that p
is in the cube defined by that corner. This function, for integer points,
is denoted t(x) ∈ T in Brakensiek et al.'s paper
-/
noncomputable def Tiling.get (T : Tiling d) (p : Point d) : Point d :=
  Exists.choose <| T.covers p

theorem Tiling.get_mem (T : Tiling d) (p : Point d) : T.get p ∈ T.corners := by
  unfold Tiling.get
  apply Exists.choose_spec (T.covers p) |>.1.1

theorem Tiling.mem_get (T : Tiling d) (p : Point d) : p ∈ Cube (T.get p) := by
  unfold Tiling.get
  apply Exists.choose_spec (T.covers p) |>.1.2

theorem Tiling.get_unique (T : Tiling d) (p : Point d) (c : Point d) :
    c ∈ T.corners → p ∈ Cube c → c = T.get p := by
  intro c_mem p_mem
  unfold Tiling.get
  apply Exists.choose_spec (T.covers p) |>.2
  simp [*]

theorem Tiling.index_get (i : IntPoint d) (T : Tiling d) :
    Cube.index (T.get i) = i := by
  have : i.toPoint ∈ Cube (T.get i) := Tiling.mem_get ..
  rw [eq_comm]; apply Cube.index_unique this

def Tiling.covers_unique (T : Tiling d) (x) :=
  @(T.covers x).unique
