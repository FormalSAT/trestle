/- Copyright (c) the LeanSAT contributors

Authors: James Gallicchio
-/

import LeanSAT.Model.Subst

namespace LeanSAT.Model

namespace PropFun

variable [DecidableEq ν]

/-- evaluates a propfun which is closed, i.e. has no semantic variables. -/
def closedEval (φ : PropFun ν) (h : φ.semVars = ∅) : Bool :=
  φ.eval (fun _ => false)

@[simp]
theorem closedEval_true (φ : PropFun ν) (h)
  : φ.closedEval h = true ↔ ∀ τ : PropAssignment ν, τ ⊨ φ := by
  simp [closedEval]
  constructor
  · intro heval τ
    rw [agreeOn_semVars]
    · apply heval
    · intro v hv; rw [h] at hv; contradiction
  · intro hi; apply hi

@[simp]
theorem closedEval_false (φ : PropFun ν) (h)
  : φ.closedEval h = false ↔ ¬ ∀ τ : PropAssignment ν, τ ⊨ φ := by
  rw [← closedEval_true]
  · simp
  · assumption


/-
/-! ### `toFinset` -/

def toFinset.aux (φ : PropFun ν) (vars : List ν) (h : φ.semVars ⊆ vars.toFinset)
  : Finset (PropAssignment ν) :=
  match vars with
  | [] =>
    if φ.closedEval (by simp_all [Finset.subset_empty])
    then {fun _ => false} else {}
  | v::vs =>
    ( toFinset.aux (φ.substOne v ⊤) vs (by
      simp [semVars_substOne])
    ).disjUnion
    ( toFinset.aux (φ.substOne v ⊥) vs sorry
    )
    (by
      sorry)

/-- Any propfun `φ` can be broken down into a finset of assignments
such that any satisfying assignment `τ ⊨ φ` has
a representative in the set `σ ∈ φ.toFinset` such that
`τ.agreeOn φ.semVars σ` -/
noncomputable def toFinset (φ : PropFun ν) : Finset (PropAssignment ν) :=
  φ.semVars.elim
    (fun set h =>
      toFinset.aux φ set (by unfold List.toFinset; rw [h]; simp))
    (by
      intro a b ha hb
      sorry)

theorem satisfies_iff_mem_toFinset (τ : PropAssignment ν) (φ : PropFun ν)
  : τ ⊨ φ ↔ ∃ σ, σ ∈ φ.toFinset ∧ τ.agreeOn φ.semVars σ := by
  sorry
-/
