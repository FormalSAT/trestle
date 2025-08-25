import Mathlib.Data.Real.Basic

namespace Keller.Euclidean

/-- Equivalent to ℝ^n on paper -/
abbrev Point (n) := Fin n → ℝ

/-- The unit cube [0,1)^n -/
def UnitCube (n) : Set (Point n) := { p | ∀ d, 0 ≤ p d ∧ p d < 1 }

/-- A transposed unit cube, corner + [0, 1)^n -/
def Cube (corner : Point n) := (corner + ·) '' (UnitCube n)

/-- A tiling is a set of corners such that all points
    are covered by exactly one cube. -/
structure Tiling (n : ℕ) where
  corners : Set (Point n)
  covers : ∀ p : Point n, ∃! c ∈ corners, p ∈ Cube c

/-- Cubes faceshare when the corners differ by 1 in some dimension,
    and are equal in all other dimensions. -/
def Faceshare (c₁ c₂ : Point n) :=
  ∃ d, |c₁ d - c₂ d| = 1 ∧ ∀ d' ≠ d, c₁ d' = c₂ d'

/-- A tiling is faceshare-free when every pair of cubes does not faceshare. -/
def Tiling.FaceshareFree (T : Tiling n) :=
  T.corners.Pairwise (¬ Faceshare · ·)

/-- Keller's conjecture in `n` dimensions. -/
def conjectureIn (n) := ¬ ∃ T : Tiling n, T.FaceshareFree
