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

def core := { T.get i | (i ∈ PeriodicIndex d)}
def corners' := {t + (2 • x).toPoint | (t ∈ core T) (x : IntPoint d)}

/-- BHMN A.3 Fact 1 -/
theorem corners'_covers_unitcube : ∀ x ∈ UnitCube d, ∃! t ∈ corners' T, x ∈ Cube t := by
  intro x x_mem

  -- x is in a cube in T
  obtain ⟨t,⟨t_corner,x_mem_t⟩,t_uniq⟩ := T.covers x

  -- this cube corner `t` must be in core because `x ∈ UnitCube d`
  have t_in_core : t ∈ core T := by
    simp [core]
    obtain i_mem_t :=
      PeriodicIndex.of_inter_unitcube_cube_nonempty ⟨x,x_mem,x_mem_t⟩
    use Cube.index t, i_mem_t
    rw [T.get_index t_corner]

  -- and core cubes are in `corners'`
  have t_corner' : t ∈ corners' T := by
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

  -- and therefore its membership in `corners'` is only possible with offset 0
  rcases t'_corner with ⟨t',⟨i,i_pidx,rfl⟩,offset,rfl⟩
  have : offset = 0 := by
    ext j; specialize this j; specialize i_pidx j
    rw [Cube.index_add_intpoint, Tiling.index_get] at this
    simp at i_pidx this ⊢
    omega

  -- which means `t'` was actually in `T` the whole time
  subst offset
  simp [T.get_mem]



def T' : Tiling d where
  corners := corners' T
  covers := by
    done

theorem T'_periodic : (T' T).Periodic := by
  simp [T', Tiling.Periodic, corners', core]
  rintro t i hi x rfl x'
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
