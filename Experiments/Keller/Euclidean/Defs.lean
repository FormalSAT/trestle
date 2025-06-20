import Mathlib.Analysis.InnerProductSpace.PiL2

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
