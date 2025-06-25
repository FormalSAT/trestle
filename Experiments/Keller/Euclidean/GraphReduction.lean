import Experiments.Keller.Euclidean.PeriodicReduction
import Experiments.Keller.KellerGraph

namespace Keller.Euclidean

namespace Graph

theorem corners_eq_of_periodic (T : Tiling n) (periodic : T.Periodic) :
      T.corners = (Hajos.corners' T) := by
  have : (Hajos.corners' T) ⊆ T.corners := by
    rintro _ ⟨t,t_core,off,rfl⟩
    apply periodic; apply Hajos.core_subset_corners _ t_core

  apply Set.eq_of_subset_of_subset ?_ this
  intro t t_corner

  obtain ⟨t',⟨t'_corner,t_mem_t'⟩,t'_uniq⟩ := Hajos.corners'_covers T t
  suffices t' = t by subst t'; exact t'_corner

  apply T.covers_unique t
  · exact ⟨this t'_corner, t_mem_t'⟩
  · exact ⟨t_corner, Cube.start_mem ..⟩

theorem fract_eq_of_mem_core {T : Tiling n} (h₁ : t₁ ∈ Hajos.core T) (h₂ : t₂ ∈ Hajos.core T)
    (ne : t₁ ≠ t₂) : ∃ j, Int.fract (t₁ j) = Int.fract (t₂ j) := by
  by_contra contra
  push_neg at contra
  have := Cube.exists_gap_of_inter_empty
  sorry

def offsets (j : Fin n) (T : Tiling n) := { Int.fract (t j) | t ∈ T.corners }

/-- The offsets are just those offsets in the core -/
theorem offsets_eq_core_of_periodic {j : Fin n} {T} (h : T.Periodic) :
      offsets j T = { Int.fract (t j) | t ∈ Hajos.core T } := by
  unfold offsets
  rw [corners_eq_of_periodic _ h]
  simp [Hajos.corners']
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨_,⟨t,t_core,off,rfl⟩,rfl⟩
    use t, t_core
    dsimp
    calc  Int.fract (t j)
      _ = Int.fract (t j + ↑(2 * off j)) := by rw [Int.fract_add_int]
      _ = Int.fract (t j + 2 • ↑(off j)) := by simp
  · rintro _ ⟨t,t_core,rfl⟩
    use t; simp; use t, t_core, 0; simp

/-- In fact, they are just *half* the offsets in the core -/
theorem offsets_eq_half_core_of_periodic {j : Fin n} {T} (h : T.Periodic) :
      offsets j T = { Int.fract (t j) | (t ∈ Hajos.core T) (_ : Cube.index t j = 0) } := by
  rw [offsets_eq_core_of_periodic h]; clear h
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨t,t_core,rfl⟩
    if h : Cube.index t j = 0 then use t
    else
    replace h : Cube.index t j = 1 := by simpa [h] using t_core.2 j
    let t' := T.get (Cube.index t + .single j (-1)).toPoint
    have t'_core : t' ∈ Hajos.core T := by
      constructor
      · apply T.get_mem
      · intro j'
        rw [T.index_get]
        by_cases j' = j <;> simp [t_core.2 j', *]
    have t'_idx_0 : Cube.index t' j = 0 := by rw [T.index_get]; simp [h]
    have t'_j : t' j + 1 = t j := by
      apply Tiling.cube_adj_of_adj_points _ t'_core.1 t_core.1
      · apply Cube.index_mem
      · rw [Tiling.index_get]; simp [add_assoc]
        apply Cube.index_mem
    use t', t'_core, t'_idx_0
    simp [← t'_j]
  · aesop

noncomputable def offsets_map (j) (T : Tiling n) : {i // i ∈ CoreIndex n ∧ i j = 0} → offsets j T :=
  fun ⟨i,_⟩ =>
  ⟨Int.fract (T.get i j), by
  use T.get i
  simp [offsets, T.get_mem]⟩

theorem offsets_map_surj_of_periodic {j : Fin n} (T : Tiling n) (periodic : T.Periodic) :
    Function.Surjective (offsets_map j T) := by
  rintro ⟨x,x_off⟩
  rw [offsets_eq_half_core_of_periodic periodic] at x_off
  simp at x_off
  rcases x_off with ⟨t,t_core,t_idx_0,rfl⟩
  use ⟨_,t_core.2, t_idx_0⟩
  simp [offsets_map, T.get_index t_core.1]

def bitvec_eqv_coreidx : BitVec n ≃ {i // i ∈ CoreIndex n} where
  toFun i := ⟨fun j => i[j].toInt,by intro j; by_cases i[j] <;> simp [*]⟩
  invFun i := BitVec.ofFn fun j => i.1 j = 1
  left_inv := by
    intro i; ext j
    by_cases i[j] <;> simp [*]
  right_inv := by
    intro i; ext j
    have := i.2 j; simp at this
    cases this <;> simp [*]

theorem exists_color_map (T : Tiling (n+1)) (h : T.Periodic) (j) : Nonempty (offsets j T ↪ Fin (2^n)) := by
  have off_to_idx := offsets_map_surj_of_periodic T h (j := j) |>.preimage_injective |> Function.Embedding.mk _
  --have bv_to_idx := bitvec_to_coreidx (n := n) (j := j)
  sorry


noncomputable def corner_to_vec (T : Tiling n) (colors : ∀ j, offsets j T ↪ α)
    {t} (t_corner : t ∈ T.corners) : Vector α n :=
  Vector.ofFn fun j => colors j ⟨ Int.fract (t j), t, t_corner, rfl⟩

end Graph

open Graph

theorem clique_of_tiling (T : Tiling (n+1)) (periodic : T.Periodic) (ff_free : T.FaceshareFree) :
      Nonempty <| KClique (n+1) (2^n) := by
  have colors : (∀ j : Fin (n+1), Graph.offsets j T ↪ Fin (2^n)) := by
    apply Nonempty.some
    rw [Classical.nonempty_pi]
    intro j; apply Graph.exists_color_map _ periodic

  let K : Finset (KVertex (n+1) (2^n)) :=
    {⟨i, corner_to_vec T colors (T.get_mem (bitvec_eqv_coreidx i))⟩ | (i) }

  apply Nonempty.intro
  use K
  constructor
  · rintro ⟨i₁,c₁⟩ v₁_mem ⟨i₂,c₂⟩ v₂_mem vs_ne
    simp [K] at v₁_mem v₂_mem; subst c₁ c₂
    clear K
    have is_ne : i₁ ≠ i₂ := by simpa +contextual using vs_ne
    clear vs_ne
    simp [KAdj]
    done
  · done
