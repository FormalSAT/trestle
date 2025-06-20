import Experiments.Keller.Euclidean.Basic

namespace Keller.Euclidean

def Tiling.Periodic (T : Tiling d) : Prop :=
  ∀ t ∈ T.corners, ∀ x : IntPoint d, t + 2 • x ∈ T.corners

/-- `{0,1}ᵈ` on paper -/
def PeriodicIndex (d : Nat) := { i : IntPoint d | ∀ j, i j ∈ ({0,1} : Set ℤ) }

/-- if a cube intersects with the origin unit cube `[0,1]ᵈ`,
    then its integer index must be in `{0,1}ᵈ` -/
theorem PeriodicIndex.of_inter_unitcube_cube_nonempty (h : (UnitCube d ∩ Cube t).Nonempty)
    : Cube.index t ∈ PeriodicIndex d := by
  intro j
  suffices -1 < Cube.index t j ∧ Cube.index t j < 2 by
    simp; omega
  simp [← Int.cast_lt (R := ℝ)]
  rcases h with ⟨x,x_mem_unit,x_mem_t⟩
  specialize x_mem_unit j
  replace x_mem_t := Cube.close_of_mem_cube x_mem_t (Cube.index_mem _) j
  simp [IntPoint.toPoint, abs_lt] at x_mem_t
  constructor <;> linarith


theorem Hajos (h : ¬ ∃ T : Tiling d, T.Periodic ∧ T.FaceshareFree) : conjectureIn d := by
  rintro ⟨T,T_ff⟩
  let core := { T.get i | (i ∈ PeriodicIndex d)}
  let T'_corners := {t + (2 • x).toPoint | (t ∈ core) (x : IntPoint d)}

  have covers_unitcube : ∀ x ∈ UnitCube d, ∃! t ∈ T'_corners, x ∈ Cube t := by
    intro x x_mem

    -- x is in a cube in T
    obtain ⟨t,⟨t_corner,x_mem_t⟩,t_uniq⟩ := T.covers x

    -- this cube corner `t` must be in core because `x ∈ UnitCube d`
    have t_in_core : t ∈ core := by
      simp [core]
      obtain i_mem_t :=
        PeriodicIndex.of_inter_unitcube_cube_nonempty ⟨x,x_mem,x_mem_t⟩
      use Cube.index t, i_mem_t
      rw [T.get_index t_corner]

    -- and core cubes are in `T'_corners`
    have t_corner' : t ∈ T'_corners := by
      use t, t_in_core, 0
      ext; simp [IntPoint.toPoint]

    use t, ⟨t_corner',x_mem_t⟩
    -- but we must prove this is unique
    rintro t' ⟨t'_corner,x_mem_t'⟩
    refine t_uniq _ ⟨?_,x_mem_t'⟩

    -- the other `t'` should also have a periodic index
    have : Cube.index t' ∈ PeriodicIndex d :=
      PeriodicIndex.of_inter_unitcube_cube_nonempty ⟨x,x_mem,x_mem_t'⟩
    clear! x

    -- and therefore its membership in `T'_corners` is only possible with offset 0
    rcases t'_corner with ⟨t',⟨i,i_pidx,rfl⟩,offset,rfl⟩
    have : offset = 0 := by
      ext j; specialize this j; specialize i_pidx j
      rw [Cube.index_add_intpoint, Tiling.index_get] at this
      simp at i_pidx this ⊢
      omega

    -- which means `t'` was actually in `T` the whole time
    subst offset
    simp [T.get_mem]

  let T' : Tiling d := {
    corners := T'_corners
    covers := by
      done
  }

  have T'_periodic : T'.Periodic := by
    simp [T', Tiling.Periodic, T'_corners, core]
    rintro t i hi x rfl x'
    use i, hi, x+x'
    simp; abel

  have T'_ff : T'.FaceshareFree := by
    done

  apply h ⟨T', T'_periodic, T'_ff⟩

/-- The periodic tiling reduction. Keller's conjecture is true if and only if
    it is true for periodic tilings. -/
theorem conjecture_iff_periodic : conjectureIn d ↔ (¬ ∃ T : Tiling d, T.Periodic ∧ T.FaceshareFree) := by
  constructor
  · rintro h ⟨T,-,ff⟩
    apply h ⟨T,ff⟩
  · apply Hajos
