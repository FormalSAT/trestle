/- Copyright (c) the LeanSAT contributors

Authors: James Gallicchio
-/

import LeanSAT.Model.OfFun

namespace LeanSAT.Model

/-! ## Quantification

The main result of this file is a characterization of
existential quantification over [PropFun].

Quantifying over a single variable is straightforward
(see [PropFun.satisfies_existQuant]).
Quantifying over a *set* of variables is less straightforward.
-/

namespace PropFun

variable [Fintype ν']

open Classical in
/-- Most general form of existential quantification.
True at `τ` iff there exists a model of `φ` whose image under `f` is `τ`.
-/
noncomputable def «exists» (f : PropAssignment ν → PropAssignment ν') (φ : PropFun ν) : PropFun ν' :=
  ofSet { τ | ∃ σ, σ ⊨ φ ∧ τ = f σ }

open Classical in
@[simp]
theorem satisfies_exists (f : PropAssignment ν → PropAssignment ν') (τ)
  : τ ⊨ «exists» f φ ↔ ∃ σ, σ ⊨ φ ∧ τ = f σ := by
  simp [«exists»]

noncomputable def existsInv (f : ν' → ν) (φ : PropFun ν): PropFun ν' :=
  φ.exists (fun σ => σ.map f)

@[simp]
theorem satisfies_existsInv (f : ν' → ν) (φ) (τ)
  : τ ⊨ «existsInv» f φ ↔ ∃ σ : PropAssignment ν, σ ⊨ φ ∧ τ = σ.map f := by
  simp [«existsInv»]

@[simp]
theorem existsInv_existsInv [DecidableEq ν''] [Fintype ν'']
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
noncomputable def «forall» (f : PropAssignment ν → PropAssignment ν') (φ : PropFun ν) : PropFun ν' :=
  ofSet { σ | ∀ τ, τ ⊨ φ → σ = f τ }

open Classical in
@[simp]
theorem satisfies_forall (f : PropAssignment ν → PropAssignment ν') (τ)
  : τ ⊨ «forall» f φ ↔ ∀ σ, σ ⊨ φ → τ = f σ := by
  simp [«forall»]

noncomputable def forallInv (f : ν' → ν) (φ : PropFun ν): PropFun ν' :=
  φ.forall (fun σ => σ.map f)

@[simp]
theorem satisfies_forallInv (f : ν' → ν) (φ) (τ)
  : τ ⊨ «forallInv» f φ ↔ ∀ σ : PropAssignment ν, σ ⊨ φ → τ = σ.map f := by
  simp [«forallInv»]


end PropFun
