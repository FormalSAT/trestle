import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.Partition.Basic

/-! ### EuclideanSpace -/

namespace EuclideanSpace

@[simp] theorem single_zero [DecidableEq ι] [RCLike 𝕜] (i : ι) :
  EuclideanSpace.single (𝕜 := 𝕜) i 0 = 0 := by ext; simp

theorem single_neg [DecidableEq ι] [RCLike 𝕜] (i : ι) (k : 𝕜):
    EuclideanSpace.single i (-k) = -EuclideanSpace.single i k := by
  ext i'; by_cases i' = i <;> simp_all

theorem single_inj [DecidableEq ι] [RCLike 𝕜] (i : ι) (k₁ k₂ : 𝕜)
    : EuclideanSpace.single i k₁ = EuclideanSpace.single i k₂ → k₁ = k₂ := by
  intro h
  replace h := congrFun h i
  simpa using h

@[simp] theorem single_inj_iff [DecidableEq ι] [RCLike 𝕜] (i : ι) (k₁ k₂ : 𝕜) :
    EuclideanSpace.single i k₁ = EuclideanSpace.single i k₂ ↔ k₁ = k₂ := by
  constructor
  · apply single_inj
  · rintro rfl; rfl

end EuclideanSpace


/-! ### Partition -/

nonrec abbrev Set.Partition (s : Set α) := Partition s

namespace Set.Partition
variable {s : Set α} (p : Set.Partition s)

def exists_unique : ∀ x ∈ s, ∃! t ∈ p, x ∈ t := by
  unfold Partition at p
  intro x x_mem_s
  rw [← p.iSup_eq] at x_mem_s
  simp at x_mem_s
  rcases x_mem_s with ⟨t,t_mem_p,x_mem_t⟩
  use t; constructor
  · simp [t_mem_p, x_mem_t]
  · rintro t' ⟨t'_mem_p,x_mem_t'⟩
    by_contra t'_ne
    have := p.disjoint t'_mem_p t_mem_p t'_ne
    apply this.notMem_of_mem_left x_mem_t' x_mem_t

def of_exists_unique (s : Set α) (p : Set (Set α)) (subsets : ∀ t ∈ p, t ⊆ s)
        (h : ∀ x ∈ s, ∃! t ∈ p, x ∈ t) : Partition s where
  parts := p \ { ∅ }
  bot_notMem' := by simp
  sSup_eq' := by
    ext x; constructor
    · rintro ⟨t,⟨t_mem,-⟩,x_mem⟩
      apply subsets _ t_mem x_mem
    · rintro x_mem
      specialize h x x_mem
      rcases h with ⟨t,⟨t_mem,x_mem⟩,-⟩
      simp; use t
  sSupIndep' := by
    apply PairwiseDisjoint.sSupIndep
    rintro a ⟨a_mem,-⟩ b ⟨b_mem,-⟩ ne
    apply disjoint_iff.mpr
    ext x; simp
    intro x_mem_a x_mem_b
    -- we'll prove a = b
    apply ne; clear ne
    specialize h x (subsets a a_mem x_mem_a)
    exact h.unique ⟨a_mem,x_mem_a⟩ ⟨b_mem,x_mem_b⟩

@[simp] theorem of_exists_unique.parts (s : Set α) (p subsets h) :
    (of_exists_unique s p subsets h).parts = p \ {∅} := rfl

end Set.Partition

theorem Bool.toInt_inj : Bool.toInt b₁ = Bool.toInt b₂ ↔ b₁ = b₂ := by
  cases b₁ <;> cases b₂ <;> simp
