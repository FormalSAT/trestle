/-
Copyright (c) 2026 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: Wojciech Nawrocki, James Gallicchio
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Pi

namespace Trestle.Model

/-! ### Propositional assignments -/

/-- A (total) assignment of truth values to propositional variables. -/
def PropAssignment (ν : Type u) := ν → Bool

namespace PropAssignment

instance : Inhabited (PropAssignment ν) :=
  inferInstanceAs (Inhabited (_ → _))

instance [DecidableEq V] [Fintype V] : DecidableEq (PropAssignment V) :=
  inferInstanceAs (DecidableEq (_ → _))

instance [DecidableEq V] [Fintype V] : Fintype (PropAssignment V) :=
  inferInstanceAs (Fintype (_ → _))

/-- Due to Lean's new `def` transparency (around v4.30), `PropAssignment ν` is
now semireducible for `ν → Bool`, so instance resolution cannot see that
the inequality of two assignments is decidable. -/
instance (σ₁ σ₂ : PropAssignment ν) : DecidablePred (fun x => σ₁ x ≠ σ₂ x) :=
  fun x => inferInstanceAs (Decidable (σ₁ x ≠ σ₂ x))

@[ext] theorem ext (v1 v2 : PropAssignment ν) (h : ∀ x, v1 x = v2 x) : v1 = v2 := funext h

section set

variable {ν : Type u} [DecidableEq ν] (τ : PropAssignment ν)

/-- Modifies the assignment `τ` by setting `τ (x) = v`. -/
def set (x : ν) (v : Bool) : PropAssignment ν :=
  fun y => if y = x then v else τ y

@[simp]
theorem get_set_self (x : ν) (v : Bool) : τ.set x v x = v := by
  simp [set]

theorem get_set_of_ne {x y : ν} (h_ne : x ≠ y) (τ : PropAssignment ν) (v : Bool)
    : τ.set x v y = τ y := by
  simp [set, h_ne.symm]

theorem get_set (x y : ν) (v : Bool) : τ.set x v y = if y = x then v else τ y := by
  simp [set]

@[simp]
theorem set_set (x : ν) (v v' : Bool) : (τ.set x v).set x v' = τ.set x v' := by
  ext x'
  dsimp [set]; split <;> simp_all

@[simp]
theorem set_get (x : ν) : τ.set x (τ x) = τ := by
  ext x'
  dsimp [set]; split <;> simp_all

theorem set_comm {x₁ x₂ : ν} (h_ne : x₁ ≠ x₂) (τ : PropAssignment ν) (b₁ b₂ : Bool)
    : (τ.set x₂ b₂).set x₁ b₁ = (τ.set x₁ b₁).set x₂ b₂ := by
  ext v
  simp [set]; split <;> split <;> (subst_vars; simp at *)

/-- Assignment which agrees with `τ'` on `vs` but `τ` everywhere else. -/
def setMany (xs : Finset ν) (τ' : PropAssignment ν) : PropAssignment ν :=
  fun v => if v ∈ xs then τ' v else τ v

theorem setMany_mem {v : ν} {xs} (h : v ∈ xs) (τ τ') : (setMany τ xs τ') v = τ' v := by
  simp only [setMany, h, ↓reduceIte]

theorem setMany_not_mem {v : ν} {xs} (h : ¬ v ∈ xs) (τ τ') : (setMany τ xs τ') v = τ v := by
  simp only [setMany, h, ↓reduceIte]

@[simp]
theorem setMany_same (xs) : setMany τ xs τ = τ := by
  ext v; simp only [setMany, ite_self]

@[simp]
theorem setMany_setMany (xs₁ τ₁ xs₂ τ₂)
    : (τ.setMany xs₁ τ₁).setMany xs₂ τ₂ = τ.setMany (xs₁ ∪ xs₂) (τ₁.setMany xs₂ τ₂) := by
  ext v
  simp only [setMany, Finset.mem_union]
  split_ifs <;> try rfl
  · rename_i hv hvs
    simp only [not_or] at hvs
    exact absurd hv hvs.2
  · rename_i hv hvs
    simp only [not_or] at hvs
    exact absurd hv hvs.1
  · rename_i hv₂ hv₁ hvs
    rcases hvs with (hv | hv)
    · exact absurd hv hv₁
    · exact absurd hv hv₂

theorem setMany_union (xs₁ xs₂ τ')
    : τ.setMany (xs₁ ∪ xs₂) τ' = (τ.setMany xs₁ τ').setMany xs₂ τ' := by
  ext v
  simp only [setMany, Finset.mem_union]
  split_ifs <;> try rfl
  · rename_i hvs hv₂ hv₁
    rcases hvs with (hv | hv)
    · exact absurd hv hv₁
    · exact absurd hv hv₂
  · rename_i hvs hv
    simp only [not_or] at hvs
    exact absurd hv hvs.2
  · rename_i hvs _ hv
    simp only [not_or] at hvs
    exact absurd hv hvs.1

@[simp]
theorem setMany_singleton (v : ν) (τ') : τ.setMany {v} τ' = τ.set v (τ' v) := by
  ext v
  simp [setMany, set]
  split_ifs <;> try rfl
  rename_i h
  subst h
  rfl

theorem setMany_set_comm (xs) (τ') (v : ν)
    : (τ.setMany xs τ').set v (τ' v) = (τ.set v (τ' v)).setMany xs τ' := by
  simp_rw [← setMany_singleton, ← setMany_union]
  rw [Finset.union_comm]

theorem setMany_set_comm_of_not_mem {xs} {v : ν} (h : ¬ v ∈ xs) (τ') (b : Bool)
    : (τ.setMany xs τ').set v b = (τ.set v b).setMany xs τ' := by
  ext v'
  by_cases h_mem' : v' ∈ xs
  · have : v ≠ v' := by
      rintro rfl
      exact h h_mem'
    simp [setMany_mem h_mem', get_set_of_ne this]
  · simp [setMany_not_mem h_mem', get_set]

theorem setMany_insert (v : ν) (vs) (τ')
    : τ.setMany (insert v vs) τ' = (τ.setMany vs τ').set v (τ' v) := by
  rw [Finset.insert_eq, setMany_set_comm, ← setMany_singleton, ← setMany_union]

end set /- section -/

section agreeOn

variable {ν : Type u} (τ : PropAssignment ν)

-- TODO: is this defined in mathlib for functions in general?
def agreeOn (X : Set ν) (σ₁ σ₂ : PropAssignment ν) : Prop :=
  ∀ x ∈ X, σ₁ x = σ₂ x

theorem agreeOn_refl (X : Set ν) (σ : PropAssignment ν) : agreeOn X σ σ :=
  fun _ _ => rfl
@[symm] theorem agreeOn.symm : agreeOn X σ₁ σ₂ → agreeOn X σ₂ σ₁ :=
  fun h x hX => Eq.symm (h x hX)
@[trans] theorem agreeOn.trans : agreeOn X σ₁ σ₂ → agreeOn X σ₂ σ₃ → agreeOn X σ₁ σ₃ :=
  fun h₁ h₂ x hX => Eq.trans (h₁ x hX) (h₂ x hX)

theorem agreeOn.subset : X ⊆ Y → agreeOn Y σ₁ σ₂ → agreeOn X σ₁ σ₂ :=
  fun hSub h x hX => h x (hSub hX)

theorem agreeOn_empty (σ₁ σ₂ : PropAssignment ν) : agreeOn ∅ σ₁ σ₂ :=
  fun _ h => False.elim (Set.notMem_empty _ h)

theorem agreeOn_set_of_not_mem [DecidableEq ν] {x : ν} {X : Set ν} (σ : PropAssignment ν) (v : Bool)
    : x ∉ X → agreeOn X (σ.set x v) σ := by
  -- I ❤ A️esop
  aesop (add norm unfold agreeOn, norm unfold set)

theorem agreeOn_setMany [DecidableEq ν] (xs : Finset ν) (τ')
    : agreeOn xs (τ.setMany xs τ') τ' := by
  intro v hv
  simp at hv
  simp [setMany, hv]

theorem agreeOn_setMany_of_disjoint [DecidableEq ν]
    (xs : Set ν) (xs' : Finset ν) (τ') (h : Disjoint xs xs')
    : agreeOn xs (τ.setMany xs' τ') τ := by
  intro v hv
  simp [setMany]
  intro hv'; exfalso
  apply h.ne_of_mem hv hv' rfl

theorem agreeOn_setMany_compl [DecidableEq ν] (xs : Finset ν) (τ')
    : agreeOn xsᶜ (τ.setMany xs τ') τ := by
  apply agreeOn_setMany_of_disjoint
  exact disjoint_compl_left

end agreeOn /- section -/

/-- Maps a truth assignment on variable type `ν₁` to variable type `ν₂` via `f`. -/
abbrev map (f : ν₂ → ν₁) (τ : PropAssignment ν₁) : PropAssignment ν₂ :=
  τ ∘ f

@[simp] theorem get_map : map f τ v = τ (f v) := rfl

@[simp] theorem map_set [DecidableEq ν₁] [DecidableEq ν₂] (f : ν₂ → ν₁) (τ) (finj : f.Injective) :
    map f (set τ (f v) b) = set (map f τ) v b := by
  unfold map; unfold set; ext; simp [finj.eq_iff]

theorem map_eq_map (f : ν → ν₁) (τ) (f' : ν → ν₂) (τ')
  : map f τ = map f' τ' ↔ ∀ v : ν, τ (f v) = τ' (f' v) := by
  simp [map]
  constructor <;> intro h
  · intro v; have := congrFun h v; simp_all
  · ext v; simp [*]

def pmap {vs : Set ν₂} [DecidablePred (· ∈ vs)] [DecidableEq ν₂]
    (f : vs → ν₁) (τ : PropAssignment ν₁) : PropAssignment ν₂ :=
  fun v =>
    if h : v ∈ vs then τ (f ⟨v,h⟩) else false

theorem exists_preimage [DecidableEq ν₂] (f : ν₁ ↪ ν₂) (τ : PropAssignment ν₁)
    : ∃ σ : PropAssignment ν₂, τ = σ.map f := by
  have : ∀ v2 : Set.range f, ∃ v1, f v1 = v2 := by
    rintro ⟨v2,h⟩
    have := f.injective.existsUnique_of_mem_range h
    simp; exact this.exists
  replace this := Classical.axiomOfChoice this
  rcases this with ⟨f',h⟩
  open Classical in
  use τ.pmap f'
  ext v1
  specialize h ⟨f v1, by simp⟩
  simp at h
  simp [pmap, h]
