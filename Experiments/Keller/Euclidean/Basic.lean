import Experiments.Keller.Euclidean.Upstream
import Experiments.Keller.Euclidean.Defs

namespace Keller.Euclidean

/-! #### Helper Defs/Lemmas -/


namespace Point

noncomputable def ofFn (f : Fin d → ℝ) : Point d := (EuclideanSpace.equiv _ _).symm f
@[simp] theorem app_ofFn (x) (f : Fin d → ℝ) : (Point.ofFn f) x = f x := rfl
@[simp] theorem ofFn_point (x : Point d) : Point.ofFn x = x := rfl

noncomputable def update (x : Point d) (j : Fin d) (y : ℝ) :=
  Point.ofFn <| Function.update x j y
@[simp] theorem app_update_eq : Point.update x j y j = y := by
  simp [Point.update]
@[simp] theorem app_update_ne (h : j' ≠ j) : Point.update x j y j' = x j' := by
  simp [Point.update, h]

@[simp] theorem update_app {x : Point d} {j} : Point.update x j (x j) = x := by
  simp [Point.update]

theorem update_inj {x} {j : Fin d} {a b} :
    Point.update x j a = Point.update x j b ↔ a = b := by
  constructor
  · intro h
    replace h := congrFun h j
    simpa using h
  · rintro rfl; rfl

theorem add_single_eq_update {x : Point d} {j α} :
      x + Pi.single j α = x.update j (x j + α) := by
  ext j'
  if j' = j then
    subst j'; simp
  else
    simp [*]

@[simp] theorem update_update {x : Point d} {j α α'} :
      (x.update j α).update j α' = x.update j α' := by
  simp [Point.update]

@[simp] theorem update_add_single {x : Point d} {j y α} :
      x.update j y + Pi.single j α = x.update j (y + α) := by
  rw [add_single_eq_update]; simp

@[simp] theorem nsmul_single (n : ℕ) (j : Fin d) (x : ℝ) :
    n • EuclideanSpace.single j x = EuclideanSpace.single j (n * x) := by
  ext j'; by_cases j' = j <;> simp_all

@[simp] theorem single_add (j : Fin d) (a b : ℝ) : EuclideanSpace.single j a + .single j b = .single j (a + b) := by
  ext j'; aesop

end Point


abbrev IntPoint (d : ℕ) : Type := Fin d → ℤ

namespace IntPoint

instance : AddCommGroup (IntPoint d) := inferInstanceAs (AddCommGroup (Fin d → ℤ))

@[simp] theorem app_add (a b : IntPoint d) (j : Fin d) : (a + b) j = a j + b j := rfl
@[simp] theorem app_zsmul (s : ℤ) (a : IntPoint d) (j : Fin d) : (s • a) j = s * a j := rfl
@[simp] theorem app_nsmul (s : ℕ) (a : IntPoint d) (j : Fin d) : (s • a) j = s * a j := rfl
@[simp] theorem app_zero (j : Fin d) : (0 : IntPoint d) j = 0 := rfl

@[ext] theorem ext (a b : IntPoint d) : (∀ j, a j = b j) → a = b := funext

noncomputable def toPoint {d : ℕ} (p : IntPoint d) : Point d :=
  Point.ofFn fun j => p j

noncomputable instance : Coe (IntPoint d) (Point d) where
  coe := IntPoint.toPoint

@[simp] theorem apply_toPoint (j : Fin d) (p : IntPoint d) :
      p.toPoint j = p j := rfl

@[simp] theorem toPoint_add (p1 p2 : IntPoint d) :
    (p1 + p2).toPoint = p1.toPoint + p2.toPoint := by
  ext j; simp [toPoint]

@[simp] theorem toPoint_neg (p : IntPoint d) :
    (-p).toPoint = -p.toPoint := by
  ext j; simp [toPoint]

@[simp] theorem toPoint_nsmul (n : ℕ) (b : IntPoint d) :
    (n • b).toPoint = n • b.toPoint := by
  ext j; simp [toPoint]

@[simp] theorem toPoint_zsmul (z : ℤ) (b : IntPoint d) :
    (z • b).toPoint = z • b.toPoint := by
  ext j; simp [toPoint]

@[simp] theorem toPoint_zero : IntPoint.toPoint (d := d) 0 = 0 := by
  ext j; simp [toPoint]

@[simp] theorem toPoint_single : IntPoint.toPoint (Pi.single j z) = Pi.single j z := by
  ext j'
  by_cases h : j' = j
  · subst j'; simp
  · simp [h]


end IntPoint

theorem Cube.mem_iff (x : Point d) (c : Point d) :
    x ∈ Cube c ↔ ∀ j, c j ≤ x j ∧ x j < c j + 1 := by
  unfold Cube UnitCube; simp

theorem Cube.start_mem (c : Point d) : c ∈ Cube c := by
  simp [mem_iff]

theorem Cube.update_mem_of_mem (x_mem : x ∈ Cube t) (range : t j ≤ y ∧ y < t j + 1) :
    x.update j y ∈ Cube t := by
  rw [Cube.mem_iff] at x_mem ⊢
  intro j'
  if j' = j then
    subst j'; simpa using range
  else
    simp [*]

lemma Cube.exists_gap_of_inter_empty (c1 c2 : Point d) :
      (Cube c1 ∩ Cube c2 = ∅) → (∃ j : Fin d, |c1 j - c2 j| ≥ 1) := by
  intro inter_empty
  by_contra no_gaps
  push_neg at no_gaps
  -- we can construct a point that is in both
  let x : Point d := Point.ofFn fun j => max (c1 j) (c2 j)
  have mem_c1 : x ∈ Cube c1 := by
    rw [Cube.mem_iff]
    intro j
    specialize no_gaps j; rw [abs_lt] at no_gaps
    simp [x]; linarith
  have mem_c2 : x ∈ Cube c2 := by
    rw [Cube.mem_iff]
    intro j
    specialize no_gaps j; rw [abs_lt] at no_gaps
    simp [x]; linarith
  clear no_gaps; clear_value x
  apply Set.notMem_empty x; rw [← inter_empty]
  simp [mem_c1, mem_c2]

theorem Cube.mem_add_iff (c : Point d) (x y) :
    x ∈ Cube (c + y) ↔ x - y ∈ Cube c := by
  simp [Cube, sub_eq_add_neg]; apply iff_of_eq; congr 1; abel

lemma Cube.inter_empty_of_exists_gap (c1 c2 : Point d) :
      (∃ j : Fin d, |c1 j - c2 j| ≥ 1) → (Cube c1 ∩ Cube c2 = ∅) := by
  rintro ⟨j,gap_at_j⟩
  ext x; simp
  intro mem_c1
  replace mem_c1 : c1 j ≤ x j ∧ x j < c1 j + 1 := by
    rw [Cube.mem_iff] at mem_c1
    exact mem_c1 j

  set_option push_neg.use_distrib true in
  rw [Cube.mem_iff]; push_neg; use j

  if h : c1 j ≤ c2 j then
    replace gap_at_j : c1 j + 1 ≤ c2 j := by
      rw [abs_of_nonpos (by linarith)] at gap_at_j
      linarith
    left
    calc
      _ < c1 j + 1  := mem_c1.2
      _ ≤ c2 j      := gap_at_j
  else
    replace gap_at_j : c2 j + 1 ≤ c1 j := by
      rw [abs_of_nonneg (by linarith)] at gap_at_j
      linarith
    right
    calc
      _ ≤ c1 j  := gap_at_j
      _ ≤ x j   := mem_c1.1

theorem Cube.inter_empty_iff_exists_gap (c1 c2 : Point d) :
    (Cube c1 ∩ Cube c2 = ∅) ↔ (∃ j, |c1 j - c2 j| ≥ 1) := by
  constructor
  · apply Cube.exists_gap_of_inter_empty
  · apply Cube.inter_empty_of_exists_gap

noncomputable def Cube.index (c : Point d) : IntPoint d :=
  fun j => Int.ceil (c j)

theorem Cube.index_mem (c : Point d) : (Cube.index c).toPoint ∈ Cube c := by
  simp [index, IntPoint.toPoint, Cube.mem_iff]
  intro j; constructor
  · apply Int.le_ceil
  · apply Int.ceil_lt_add_one

theorem Cube.index_unique {c : Point d} {x : IntPoint d} :
    x.toPoint ∈ Cube c → x = Cube.index c := by
  intro h; ext j
  rw [Cube.mem_iff] at h; specialize h j
  simp [IntPoint.toPoint] at h
  unfold index; rw [eq_comm, Int.ceil_eq_iff]
  constructor <;> linarith

theorem Cube.index_add_intpoint (c : Point d) (x : IntPoint d) :
    Cube.index (c + x.toPoint) = Cube.index c + x := by
  unfold index; ext j; simp [IntPoint.toPoint]

theorem Cube.close_of_mem_cube {t x y : Point d} (hx : x ∈ Cube t) (hy : y ∈ Cube t)
      : ∀ j, |x j - y j| < 1 := by
  rw [Cube.mem_iff] at hx hy
  intro j
  specialize hx j; specialize hy j
  rw [abs_lt]
  constructor <;> linarith

theorem Faceshare.symm {c1 c2 : Point d} (h : Faceshare c1 c2) :
    Faceshare c2 c1 := by
  unfold Faceshare at h ⊢
  simp_rw [abs_sub_comm (c2 _), eq_comm (a := c2 _)]
  exact h


/-
Takes a point p and a tiling T and returns the unique corner in T such that p
is in the cube defined by that corner. This function, for integer points,
is denoted t(x) ∈ T in Brakensiek et al.'s paper
-/
noncomputable def Tiling.get (T : Tiling d) (p : Point d) : Point d :=
  Exists.choose <| T.covers p

theorem Tiling.get_mem (T : Tiling d) (p : Point d) : T.get p ∈ T.corners := by
  unfold Tiling.get
  apply Exists.choose_spec (T.covers p) |>.1.1

theorem Tiling.mem_get (T : Tiling d) (p : Point d) : p ∈ Cube (T.get p) := by
  unfold Tiling.get
  apply Exists.choose_spec (T.covers p) |>.1.2

theorem Tiling.get_unique {T : Tiling d} {p c} :
    c ∈ T.corners → p ∈ Cube c → c = T.get p := by
  intro c_mem p_mem
  unfold Tiling.get
  apply Exists.choose_spec (T.covers p) |>.2
  simp [*]

theorem Tiling.get_eq_of_mem_corners (T : Tiling d) {t} (h : t ∈ T.corners) : T.get t = t := by
  rw [eq_comm]; apply T.get_unique h (Cube.start_mem _)

theorem Tiling.index_get (i : IntPoint d) (T : Tiling d) :
    Cube.index (T.get i) = i := by
  have : i.toPoint ∈ Cube (T.get i) := Tiling.mem_get ..
  rw [eq_comm]; apply Cube.index_unique this

theorem Tiling.get_index (T : Tiling d) (ht : t ∈ T.corners) :
    T.get (Cube.index t) = t := by
  have : (Cube.index t).toPoint ∈ Cube t := Cube.index_mem ..
  rw [eq_comm]; apply T.get_unique ht this

theorem Tiling.get_inj (T : Tiling d) {x y : IntPoint d} : T.get x = T.get y → x = y := by
  intro h
  have := congrArg Cube.index h
  simpa [T.index_get] using this

def Tiling.covers_unique (T : Tiling d) (x) :=
  @(T.covers x).unique

theorem Tiling.exists_gap (T : Tiling d) (h₁ : t₁ ∈ T.corners) (h₂ : t₂ ∈ T.corners) (h : t₁ ≠ t₂) :
    ∃ j, |t₁ j - t₂ j| ≥ 1 := by
  apply Cube.exists_gap_of_inter_empty
  contrapose h; push_neg at h ⊢
  rcases h with ⟨x,mem1,mem2⟩
  apply T.covers_unique x ⟨h₁,mem1⟩ ⟨h₂,mem2⟩

/-- Proposition 5 in BHMN -/
theorem Tiling.FaceshareFree.of_neighbors {T : Tiling d}
    (h : ∀ (x : IntPoint d) (j : Fin d),
      ¬ (T.get x) + Pi.single j 1 = (T.get (x + Pi.single j 1).toPoint))
    : T.FaceshareFree := by
  rintro t₁ t₁_corner t₂ t₂_corner - ts_faceshare
  obtain ⟨j,diff_one,others_eq⟩ := ts_faceshare
  wlog t₁_smaller : t₁ j ≤ t₂ j generalizing t₁ t₂
  · apply this t₂_corner t₁_corner
    case diff_one => rw [abs_sub_comm]; exact diff_one
    case others_eq => simp_rw [eq_comm]; exact others_eq
    linarith
  -- rewrite the abs
  rw [← sub_nonpos] at t₁_smaller
  rw [abs_of_nonpos t₁_smaller] at diff_one
  clear t₁_smaller
  -- now we know the relation between t₁ and t₂
  have : t₁ + Pi.single j 1 = t₂ := by
    ext j'
    if hj : j' = j then subst j'; simp; linarith
    else simp [hj,others_eq]
  -- and can apply the hypothesis `h`
  apply h (Cube.index t₁) j
  convert this
  · rw [T.get_index]; assumption
  · rw [← Cube.index_add_intpoint]
    simp [this]
    apply T.get_index t₂_corner
