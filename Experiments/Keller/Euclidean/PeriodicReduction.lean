import Experiments.Keller.Euclidean.Basic

namespace Keller.Euclidean

def Tiling.Periodic (T : Tiling d) : Prop :=
  ∀ t ∈ T.corners, ∀ x : IntPoint d, t + 2 • x ∈ T.corners

/-- `{0,1}ᵈ` on paper -/
def PeriodicIndex (d : Nat) := { i : IntPoint d | ∀ j, i j ∈ ({0,1} : Set ℤ) }

theorem Hajos (h : ¬ ∃ T : Tiling d, T.Periodic ∧ T.FaceshareFree) : conjectureIn d := by
  rintro ⟨T,T_ff⟩
  let core := { T.get i | (i ∈ PeriodicIndex d)}
  let T'_corners := {t + 2 • x | (t ∈ core) (x : IntPoint d)}

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

theorem conjecture_iff_periodic : conjectureIn d ↔ (¬ ∃ T : Tiling d, T.Periodic ∧ T.FaceshareFree) := by
  constructor
  · rintro h ⟨T,-,ff⟩
    apply h ⟨T,ff⟩
  · apply Hajos
