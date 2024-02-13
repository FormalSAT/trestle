/- Copyright (c) the LeanSAT contributors

Authors: James Gallicchio
-/

import LeanSAT.Model.OfFun

namespace LeanSAT.Model

/-! ## Quantification

This file characterizes existential and universal quantification
of variables in a `PropFun`.
-/

namespace PropFun

variable [Fintype ν']

open Classical in
/-- Most general form of existential quantification.
True at `τ` iff there exists a model of `φ` whose image under `f` is `τ`.
-/
noncomputable def existsAssn (f : PropAssignment ν → PropAssignment ν') (φ : PropFun ν) : PropFun ν' :=
  ofSet { τ | ∃ σ, σ ⊨ φ ∧ τ = f σ }

open Classical in
@[simp]
theorem satisfies_exists (f : PropAssignment ν → PropAssignment ν') (τ)
  : τ ⊨ existsAssn f φ ↔ ∃ σ, σ ⊨ φ ∧ τ = f σ := by
  simp [existsAssn]

noncomputable def existsInv (f : ν' → ν) (φ : PropFun ν): PropFun ν' :=
  φ.existsAssn (fun σ => σ.map f)

@[simp]
theorem satisfies_existsInv (f : ν' → ν) (φ) (τ)
  : τ ⊨ existsInv f φ ↔ ∃ σ : PropAssignment ν, σ ⊨ φ ∧ τ = σ.map f := by
  simp [existsInv]

@[simp]
theorem existsInv_existsInv [Fintype ν'']
      (f : ν'' → ν') (g : ν' → ν) (φ : PropFun ν)
  : (φ.existsInv g).existsInv f = φ.existsInv (g ∘ f) := by
  ext τ; simp
  constructor
  · rintro ⟨_, ⟨σ,h,rfl⟩, rfl⟩
    use σ
    simp [*, PropAssignment.map]
    rfl
  · rintro ⟨σ,h,rfl⟩
    use σ.map g
    simp [*, PropAssignment.map, Function.comp]
    use σ


open Classical in
/-- Most general form of universal quantification.
True at `τ` iff for all models of `φ`, their image under `f` is `τ`.
-/
noncomputable def forallAssn (f : PropAssignment ν → PropAssignment ν') (φ : PropFun ν) : PropFun ν' :=
  ofSet { σ | ∀ τ, τ ⊨ φ → σ = f τ }

open Classical in
@[simp]
theorem satisfies_forallAssn (f : PropAssignment ν → PropAssignment ν') (τ)
  : τ ⊨ forallAssn f φ ↔ ∀ σ, σ ⊨ φ → τ = f σ := by
  simp [forallAssn]

noncomputable def forallInv (f : ν' → ν) (φ : PropFun ν): PropFun ν' :=
  φ.forallAssn (fun σ => σ.map f)

@[simp]
theorem satisfies_forallInv (f : ν' → ν) (φ) (τ)
  : τ ⊨ forallInv f φ ↔ ∀ σ : PropAssignment ν, σ ⊨ φ → τ = σ.map f := by
  simp [forallInv]

end PropFun
