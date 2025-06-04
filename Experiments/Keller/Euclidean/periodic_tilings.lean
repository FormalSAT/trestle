import tilings_structure

def is_periodic {d : ℕ} {T : set (point d)} (T_is_tiling : is_tiling T) : Prop :=
  ∀ x : int_point d, ∀ y : int_point d,
  (int_point_to_corner T_is_tiling (add_int_vectors x (double_int_vector y))).val =
  add_vectors (int_point_to_corner T_is_tiling x).val (int_point_to_point (double_int_vector y))

def core_points (d : ℕ) : set (point d) := {x : point d | ∀ i : fin d, x.nth i = 0 ∨ x.nth i = 1}
def is_core_point {d : ℕ} (p : point d) : Prop := ∀ i : fin d, vector.nth p i = 0 ∨ vector.nth p i = 1

lemma is_core_point_of_in_core_points {d : ℕ} {p : point d}: p ∈ core_points d → is_core_point p :=
begin
  intro p_in_core_points,
  rw core_points at p_in_core_points,
  simp only [set.mem_set_of_eq] at p_in_core_points,
  exact p_in_core_points,
end

lemma le_one_of_is_core_point {d : ℕ} {p : point d} (i : fin d) : is_core_point p → p.nth i ≤ 1 :=
begin
  intro p_is_core_point,
  cases p_is_core_point i with p_eq_zero p_eq_one,
  { rw p_eq_zero,
    linarith,
  },
  rw p_eq_one,
end

lemma ge_zero_of_is_core_point {d : ℕ} {p : point d} (i : fin d) : is_core_point p → p.nth i ≥ 0 :=
begin
  intro p_is_core_point,
  cases p_is_core_point i with p_eq_zero p_eq_one,
  { rw p_eq_zero,
    linarith,
  },
  rw p_eq_one,
  linarith,
end

def has_periodic_core {d : ℕ} {T : set (point d)} (T_is_tiling : is_tiling T) : Prop :=
  ∀ t ∈ T, ∃ p ∈ core_points d, ∃ t_core ∈ T, ∃ t_offset : int_point d,
  in_cube t_core p ∧ t = add_vectors t_core (int_point_to_point (double_int_vector t_offset))

theorem has_periodic_core_of_is_periodic :
  ∀ d : ℕ, ∀ T : set (point d), ∀ T_is_tiling : is_tiling T, is_periodic T_is_tiling → has_periodic_core T_is_tiling :=
begin
  intros d T T_is_tiling T_is_periodic t t_in_T,
  let p : int_point d := vector.of_fn(λ i : fin d, int.ceil(t.nth i)),
  let int_p_core_point : int_point d := vector.of_fn(λ i : fin d, p.nth i % 2),
  let p_core_point : point d := vector.of_fn(λ i : fin d, ↑(int_p_core_point.nth i)),
  have p_core_point_in_core_points : p_core_point ∈ core_points d :=
    begin
      rw core_points,
      dsimp[p_core_point, p],
      simp only [vector.nth_of_fn, euclidean_domain.mod_eq_zero],
      intro i,
      cases int.even_or_odd (int.ceil(t.nth i)) with p_even p_odd,
      { left,
        rw int.even_iff at p_even,
        exact_mod_cast p_even,
      },
      right,
      rw int.odd_iff at p_odd,
      exact_mod_cast p_odd,
    end,
  let p_core_point_corner := (point_to_corner T_is_tiling p_core_point).val,
  have p_core_point_corner_def : p_core_point_corner = (point_to_corner T_is_tiling p_core_point).val := by refl,
  have p_core_point_corner_property := (point_to_corner T_is_tiling p_core_point).property,
  rw ← p_core_point_corner_def at p_core_point_corner_property,
  rcases p_core_point_corner_property with 
    ⟨p_core_point_corner_in_T, p_core_point_in_p_core_point_corner, p_core_point_corner_unique⟩,
  use [p_core_point, p_core_point_in_core_points, p_core_point_corner],
  split, exact p_core_point_corner_in_T,
  let p_offset : int_point d := vector.of_fn (λ i : fin d, (p.nth i) - (int_p_core_point.nth i)),
  let p_offset_div_two : int_point d := vector.of_fn (λ i : fin d, (p_offset.nth i) / 2),
  use p_offset_div_two,
  rw cube at p_core_point_in_p_core_point_corner,
  simp only [set.mem_set_of_eq] at p_core_point_in_p_core_point_corner,
  split, exact p_core_point_in_p_core_point_corner,
  rw is_periodic at T_is_periodic,
  replace T_is_periodic := T_is_periodic int_p_core_point p_offset_div_two,
  have p_eq_p_core_point_plus_offset : p = add_int_vectors int_p_core_point (double_int_vector p_offset_div_two) :=
    begin
      dsimp[p_offset_div_two, int_p_core_point],
      rw [add_int_vectors, double_int_vector],
      apply vector.ext,
      intro i,
      simp only [vector.nth_of_fn],
      have p_sub_p_mod_2_is_even : even (⌈t.nth i⌉ - ⌈t.nth i⌉ % 2) :=
        begin
          have even_or_odd := int.even_or_odd (⌈t.nth i⌉),
          cases even_or_odd,
          { have even_h := even_or_odd,
            rw int.even_iff at even_or_odd,
            rw [even_or_odd, sub_zero],
            exact even_h,
          },
          have odd_h := even_or_odd,
          rw int.odd_iff at even_or_odd,
          have one_odd := int.not_even_one,
          rw ← int.odd_iff_not_even at one_odd,
          rw ← even_or_odd at one_odd,
          exact int.odd.sub_odd odd_h one_odd,
        end,
      have rhs_rw := mul_div_two_of_even p_sub_p_mod_2_is_even,
      rw rhs_rw,
      norm_num,
    end,
  rw ← p_eq_p_core_point_plus_offset at T_is_periodic,
  have p_core_point_corner_eq_int_p_core_point_corner : 
    p_core_point_corner = (int_point_to_corner T_is_tiling int_p_core_point).val :=
    begin
      rcases (int_point_to_corner T_is_tiling int_p_core_point).property with
        ⟨int_p_core_point_corner_in_T, int_p_core_point_in_int_p_core_point_corner, int_p_core_point_corner_unique⟩,
      have p_core_point_eq_int_p_core_point_to_point : p_core_point = int_point_to_point int_p_core_point :=
        by {dsimp[p_core_point], rw int_point_to_point},
      conv at int_p_core_point_in_int_p_core_point_corner
      begin
        find (int_point_to_point int_p_core_point) {rw ← p_core_point_eq_int_p_core_point_to_point},
      end,
      symmetry,
      exact p_core_point_corner_unique (int_point_to_corner T_is_tiling int_p_core_point).val int_p_core_point_corner_in_T
        int_p_core_point_in_int_p_core_point_corner,
    end,
  rw ← p_core_point_corner_eq_int_p_core_point_corner at T_is_periodic,
  have t_eq_p_corner : t = (int_point_to_corner T_is_tiling p).val :=
    begin
      rcases (int_point_to_corner T_is_tiling p).property with ⟨p_corner_in_T, p_in_p_corner, p_corner_unique⟩,
      have p_in_t : int_point_to_point p ∈ cube t :=
        begin
          dsimp[p],
          rw [int_point_to_point, cube],
          simp only [set.mem_set_of_eq],
          rw in_cube,
          intro i,
          simp only [not_lt, not_le, vector.nth_of_fn],
          exact ⟨int.le_ceil (t.nth i), int.ceil_lt_add_one (t.nth i)⟩,
        end,
      exact p_corner_unique t t_in_T p_in_t,
    end,
  rw ← t_eq_p_corner at T_is_periodic,
  exact T_is_periodic,
end

lemma is_periodic_of_has_periodic_core_x_offset_def (d : ℕ) (T : set (point d)) (T_is_tiling : is_tiling T) (T_has_periodic_core : has_periodic_core T_is_tiling)
  (x y : int_point d) (x_core : point d) (x_core_in_core_points : x_core ∈ core_points d) (x_corner_core : point d) (x_corner_core_in_T : x_corner_core ∈ T)
  (x_offset : int_point d) (x_core_in_x_corner_core : in_cube x_corner_core x_core) (x_core' : point d) (x_core'_in_core_points : x_core' ∈ core_points d)
  (x_corner_core' : point d) (x_corner_core'_in_T : x_corner_core' ∈ T) (x_add_2y_offset : int_point d)
  (x_core'_in_x_corner_core' : in_cube x_corner_core' x_core') :
  let x_corner : point d := (int_point_to_corner T_is_tiling x).val,
      x_add_2y : vector ℤ d := add_int_vectors x (double_int_vector y),
      x_add_2y_corner : point d :=
        (int_point_to_corner T_is_tiling
           (add_int_vectors x (double_int_vector y))).val
  in x_corner = (int_point_to_corner T_is_tiling x).val →
     x_corner ∈ T →
     int_point_to_point x ∈ cube x_corner →
     (∀ (alt_corner : point d),
        alt_corner ∈ T →
        int_point_to_point x ∈ cube alt_corner → alt_corner = x_corner) →
     x_add_2y_corner =
       (int_point_to_corner T_is_tiling
          (add_int_vectors x (double_int_vector y))).val →
     x_add_2y_corner ∈ T →
     int_point_to_point (add_int_vectors x (double_int_vector y)) ∈
       cube x_add_2y_corner →
     (∀ (alt_corner : point d),
        alt_corner ∈ T →
        int_point_to_point (add_int_vectors x (double_int_vector y)) ∈
          cube alt_corner →
        alt_corner = x_add_2y_corner) →
     x_corner =
       add_vectors x_corner_core
         (int_point_to_point (double_int_vector x_offset)) →
     x_add_2y_corner =
       add_vectors x_corner_core'
         (int_point_to_point (double_int_vector x_add_2y_offset)) →
     ∀ (i : fin d), vector.nth x_offset i = vector.nth x i / 2 :=
begin
  intros x_corner x_add_2y x_add_2y_corner x_corner_def x_corner_in_T x_in_x_corner x_corner_unique x_add_2y_corner_def x_add_2y_corner_in_T x_add_2y_in_x_add_2y_corner 
    x_add_2y_corner_unique x_corner_eq_x_corner_core_add_double_x_offset x_add_2y_corner_eq_x_corner_core'_add_double_x_add_2y_offset i,
  replace x_corner_eq_x_corner_core_add_double_x_offset : 
    x_corner.nth i = (add_vectors x_corner_core (int_point_to_point (double_int_vector x_offset))).nth i :=
    by rw x_corner_eq_x_corner_core_add_double_x_offset,
  rw [add_vectors, int_point_to_point, double_int_vector] at x_corner_eq_x_corner_core_add_double_x_offset,
  simp only [vector.nth_of_fn, int.cast_mul, int.cast_bit0, int.cast_one] at x_corner_eq_x_corner_core_add_double_x_offset,
  have x_core_le_one := le_one_of_is_core_point i (is_core_point_of_in_core_points x_core_in_core_points),
  have x_core_ge_zero := ge_zero_of_is_core_point i (is_core_point_of_in_core_points x_core_in_core_points),
  rw [int_point_to_point, cube] at x_in_x_corner,
  simp only [set.mem_set_of_eq] at x_in_x_corner,
  rw in_cube at x_in_x_corner,
  replace x_in_x_corner := x_in_x_corner i,
  simp only [vector.nth_of_fn] at x_in_x_corner,
  cases x_in_x_corner with x_corner_le_x x_lt_x_corner_add_one,
  rw in_cube at x_core_in_x_corner_core,
  replace x_core_in_x_corner_core := x_core_in_x_corner_core i,
  cases x_core_in_x_corner_core with x_corner_core_le_x_core x_core_lt_x_corner_core_add_one,
  rcases eq_or_lt_or_gt (vector.nth x_offset i) (vector.nth x i / 2) with x_offset_eq_x_div_2 | x_offset_lt_x_div_2 | x_offset_gt_x_div_2,
  exact x_offset_eq_x_div_2,
  { exfalso,
    have x_offset_le_x_div_2_sub_1 : x_offset.nth i ≤ (x.nth i) / 2 - 1 := by linarith,
    have x_offset_eq_x_corner_sub_x_corner_core_div_2 : ↑(x_offset.nth i) = (x_corner.nth i - x_corner_core.nth i) / 2 := by linarith,
    have cast_x_offset_le_x_div_2_sub_1 : (↑(x_offset.nth i) : ℝ) ≤ ↑((x.nth i) / 2) - 1 := by exact_mod_cast x_offset_le_x_div_2_sub_1,
    rw x_offset_eq_x_corner_sub_x_corner_core_div_2 at cast_x_offset_le_x_div_2_sub_1,
    by_cases x_even : even (x.nth i),
    { have cast_x_div_2 : ↑(vector.nth x i / 2) = (↑(x.nth i)) / (2 : ℝ) :=
        begin
          have h := int.two_mul_div_two_of_even x_even,
          have cast_h : (2 : ℝ) * ↑(vector.nth x i / 2) = ↑(vector.nth x i) := by exact_mod_cast h,
          linarith,
        end,
      have x_core_eq_zero : x_core.nth i = 0 :=
        begin
          rw core_points at x_core_in_core_points,
          simp only [set.mem_set_of_eq] at x_core_in_core_points,
          cases x_core_in_core_points i with x_core_eq_zero x_core_eq_one,
          exact x_core_eq_zero,
          exfalso,
          rw x_core_eq_one at x_corner_core_le_x_core x_core_lt_x_corner_core_add_one,
          cases x_even with x_half x_eq_double_x_half,
          have cast_x_eq_double_x_half : ↑(x.nth i) = (2 : ℝ) * ↑x_half := by exact_mod_cast x_eq_double_x_half,
          have x_half_eq_x_offset : x_half = x_offset.nth i :=
            begin
              rcases eq_or_lt_or_gt x_half (x_offset.nth i) with x_half_eq_x_offset | x_half_lt_x_offset | x_half_gt_x_offset,
              exact x_half_eq_x_offset,
              { exfalso,
                have x_half_le_x_offset_sub_one : x_half ≤ x_offset.nth i - 1 := by linarith,
                linarith,
              },
              exfalso,
              have x_half_ge_x_offset_add_one : x_half ≥ x_offset.nth i + 1 := by linarith,
              linarith,
            end,
          rw [← x_half_eq_x_offset, ← cast_x_eq_double_x_half] at x_corner_eq_x_corner_core_add_double_x_offset,
          linarith,
        end,
      rw cast_x_div_2 at cast_x_offset_le_x_div_2_sub_1,
      linarith,
    },
    rename x_even x_not_even,
    have x_odd : odd (x.nth i) := by {rw ← int.odd_iff_not_even at x_not_even, exact x_not_even},
    have cast_x_div_2 : ↑(vector.nth x i / 2) = (↑(x.nth i) - 1) / (2 : ℝ) :=
      begin
        have h := int.two_mul_div_two_of_odd x_odd,
        have cast_h : (2 : ℝ) * ↑(vector.nth x i / 2) = ↑(vector.nth x i) - 1 := by exact_mod_cast h,
        linarith,
      end,
    have x_core_eq_one : x_core.nth i = 1 :=
      begin
        rw core_points at x_core_in_core_points,
        simp only [set.mem_set_of_eq] at x_core_in_core_points,
        cases x_core_in_core_points i with x_core_eq_zero x_core_eq_one,
        { exfalso,
          rw x_core_eq_zero at x_corner_core_le_x_core x_core_lt_x_corner_core_add_one,
          cases x_odd with x_half x_eq_double_x_half_add_one,
          have cast_x_eq_double_x_half_add_one : ↑(vector.nth x i) = (2 : ℝ) * ↑x_half + 1 := by exact_mod_cast x_eq_double_x_half_add_one,
          have x_half_eq_x_offset : x_half = x_offset.nth i :=
            begin
              rcases eq_or_lt_or_gt x_half (x_offset.nth i) with x_half_eq_x_offset | x_half_lt_x_offset | x_half_gt_x_offset,
              exact x_half_eq_x_offset,
              { exfalso,
                have x_half_le_x_offset_sub_one : x_half ≤ x_offset.nth i - 1 := by linarith,
                linarith,
              },
              exfalso,
              have x_half_ge_x_offset_add_one : x_half ≥ x_offset.nth i + 1 := by linarith,
              linarith,
            end,
          rw ← x_half_eq_x_offset at x_corner_eq_x_corner_core_add_double_x_offset,
          linarith,
        },
        exact x_core_eq_one,
      end,
    rw cast_x_div_2 at cast_x_offset_le_x_div_2_sub_1,
    linarith,
  },
  exfalso,
  have x_offset_ge_x_div_2_add_1 : x_offset.nth i ≥ (x.nth i) / 2 + 1 := by linarith,
  have x_offset_eq_x_corner_sub_x_corner_core_div_2 : ↑(x_offset.nth i) = (x_corner.nth i - x_corner_core.nth i) / 2 := by linarith,
  have cast_x_offset_ge_x_div_2_add_1 : (↑(x_offset.nth i) : ℝ) ≥ ↑((x.nth i) / 2) + 1 := by exact_mod_cast x_offset_ge_x_div_2_add_1,
  rw x_offset_eq_x_corner_sub_x_corner_core_div_2 at cast_x_offset_ge_x_div_2_add_1,
  by_cases x_even : even (x.nth i),
  { have cast_x_div_2 : ↑(vector.nth x i / 2) = (↑(x.nth i)) / (2 : ℝ) :=
      begin
        have h := int.two_mul_div_two_of_even x_even,
        have cast_h : (2 : ℝ) * ↑(vector.nth x i / 2) = ↑(vector.nth x i) := by exact_mod_cast h,
        linarith,
      end,
    have x_core_eq_zero : x_core.nth i = 0 :=
      begin
        rw core_points at x_core_in_core_points,
        simp only [set.mem_set_of_eq] at x_core_in_core_points,
        cases x_core_in_core_points i with x_core_eq_zero x_core_eq_one,
        exact x_core_eq_zero,
        exfalso,
        rw x_core_eq_one at x_corner_core_le_x_core x_core_lt_x_corner_core_add_one,
        cases x_even with x_half x_eq_double_x_half,
        have cast_x_eq_double_x_half : ↑(x.nth i) = (2 : ℝ) * ↑x_half := by exact_mod_cast x_eq_double_x_half,
        have x_half_eq_x_offset : x_half = x_offset.nth i :=
          begin
            rcases eq_or_lt_or_gt x_half (x_offset.nth i) with x_half_eq_x_offset | x_half_lt_x_offset | x_half_gt_x_offset,
            exact x_half_eq_x_offset,
            { exfalso,
              have x_half_le_x_offset_sub_one : x_half ≤ x_offset.nth i - 1 := by linarith,
              linarith,
            },
            exfalso,
            have x_half_ge_x_offset_add_one : x_half ≥ x_offset.nth i + 1 := by linarith,
            linarith,
          end,
        rw [← x_half_eq_x_offset, ← cast_x_eq_double_x_half] at x_corner_eq_x_corner_core_add_double_x_offset,
        linarith,
      end,
    rw cast_x_div_2 at cast_x_offset_ge_x_div_2_add_1,
    linarith,
  },
  rename x_even x_not_even,
  have x_odd : odd (x.nth i) := by {rw ← int.odd_iff_not_even at x_not_even, exact x_not_even},
  have cast_x_div_2 : ↑(vector.nth x i / 2) = (↑(x.nth i) - 1) / (2 : ℝ) :=
    begin
      have h := int.two_mul_div_two_of_odd x_odd,
      have cast_h : (2 : ℝ) * ↑(vector.nth x i / 2) = ↑(vector.nth x i) - 1 := by exact_mod_cast h,
      linarith,
    end,
  have x_core_eq_one : x_core.nth i = 1 :=
    begin
      rw core_points at x_core_in_core_points,
      simp only [set.mem_set_of_eq] at x_core_in_core_points,
      cases x_core_in_core_points i with x_core_eq_zero x_core_eq_one,
      { exfalso,
        rw x_core_eq_zero at x_corner_core_le_x_core x_core_lt_x_corner_core_add_one,
        cases x_odd with x_half x_eq_double_x_half_add_one,
        have cast_x_eq_double_x_half_add_one : ↑(vector.nth x i) = (2 : ℝ) * ↑x_half + 1 := by exact_mod_cast x_eq_double_x_half_add_one,
        have x_half_eq_x_offset : x_half = x_offset.nth i :=
          begin
            rcases eq_or_lt_or_gt x_half (x_offset.nth i) with x_half_eq_x_offset | x_half_lt_x_offset | x_half_gt_x_offset,
            exact x_half_eq_x_offset,
            { exfalso,
              have x_half_le_x_offset_sub_one : x_half ≤ x_offset.nth i - 1 := by linarith,
              linarith,
            },
            exfalso,
            have x_half_ge_x_offset_add_one : x_half ≥ x_offset.nth i + 1 := by linarith,
            linarith,
          end,
        rw ← x_half_eq_x_offset at x_corner_eq_x_corner_core_add_double_x_offset,
        linarith,
      },
      exact x_core_eq_one,
    end,
  rw cast_x_div_2 at cast_x_offset_ge_x_div_2_add_1,
  linarith,
end

lemma is_periodic_of_has_periodic_core : 
  ∀ d : ℕ, ∀ T : set (point d), ∀ T_is_tiling : is_tiling T, has_periodic_core T_is_tiling → is_periodic T_is_tiling :=
begin
  intros d T T_is_tiling T_has_periodic_core x y,
  let x_corner := (int_point_to_corner T_is_tiling x).val,
  have x_corner_def : x_corner = (int_point_to_corner T_is_tiling x).val := by refl,
  have x_corner_property := (int_point_to_corner T_is_tiling x).property,
  rw ← x_corner_def at x_corner_property,
  rcases x_corner_property with ⟨x_corner_in_T, x_in_x_corner, x_corner_unique⟩,
  let x_add_2y := add_int_vectors x (double_int_vector y),
  let x_add_2y_corner := (int_point_to_corner T_is_tiling (add_int_vectors x (double_int_vector y))).val,
  have x_add_2y_corner_def : x_add_2y_corner = (int_point_to_corner T_is_tiling (add_int_vectors x (double_int_vector y))).val := by refl,
  have x_add_2y_corner_property := (int_point_to_corner T_is_tiling (add_int_vectors x (double_int_vector y))).property,
  rw ← x_add_2y_corner_def at x_add_2y_corner_property,
  rcases x_add_2y_corner_property with ⟨x_add_2y_corner_in_T, x_add_2y_in_x_add_2y_corner, x_add_2y_corner_unique⟩,
  rw [← x_corner_def, ← x_add_2y_corner_def],
  rcases T_has_periodic_core x_corner x_corner_in_T with 
    ⟨x_core, x_core_in_core_points, x_corner_core, x_corner_core_in_T, x_offset, x_core_in_x_corner_core, x_corner_eq_x_corner_core_add_double_x_offset⟩,
  rcases T_has_periodic_core x_add_2y_corner x_add_2y_corner_in_T with
    ⟨x_core', x_core'_in_core_points, x_corner_core', x_corner_core'_in_T, x_add_2y_offset, x_core'_in_x_corner_core', 
    x_add_2y_corner_eq_x_corner_core'_add_double_x_add_2y_offset⟩,
  have x_offset_def : ∀ i : fin d, x_offset.nth i = x.nth i / 2 :=
    is_periodic_of_has_periodic_core_x_offset_def d T T_is_tiling T_has_periodic_core x y x_core x_core_in_core_points x_corner_core x_corner_core_in_T
      x_offset x_core_in_x_corner_core x_core' x_core'_in_core_points x_corner_core' x_corner_core'_in_T x_add_2y_offset x_core'_in_x_corner_core'
      x_corner_def x_corner_in_T x_in_x_corner x_corner_unique x_add_2y_corner_def x_add_2y_corner_in_T x_add_2y_in_x_add_2y_corner 
      x_add_2y_corner_unique x_corner_eq_x_corner_core_add_double_x_offset x_add_2y_corner_eq_x_corner_core'_add_double_x_add_2y_offset,
  have x_add_2y_offset_def : ∀ i : fin d, x_add_2y_offset.nth i = x_add_2y.nth i / 2 :=
    begin
      intro i,
      replace x_add_2y_corner_eq_x_corner_core'_add_double_x_add_2y_offset :
        x_add_2y_corner.nth i = (add_vectors x_corner_core' (int_point_to_point (double_int_vector x_add_2y_offset))).nth i :=
        by rw x_add_2y_corner_eq_x_corner_core'_add_double_x_add_2y_offset,
      rw [add_vectors, int_point_to_point, double_int_vector] at x_add_2y_corner_eq_x_corner_core'_add_double_x_add_2y_offset,
      simp only [vector.nth_of_fn, int.cast_mul, int.cast_bit0, int.cast_one] at x_add_2y_corner_eq_x_corner_core'_add_double_x_add_2y_offset,
      have x_core'_le_one := le_one_of_is_core_point i (is_core_point_of_in_core_points x_core'_in_core_points),
      have x_core'_ge_zero := ge_zero_of_is_core_point i (is_core_point_of_in_core_points x_core'_in_core_points),
      rw [int_point_to_point, cube] at x_add_2y_in_x_add_2y_corner,
      simp only [set.mem_set_of_eq] at x_add_2y_in_x_add_2y_corner,
      rw in_cube at x_add_2y_in_x_add_2y_corner,
      replace x_add_2y_in_x_add_2y_corner := x_add_2y_in_x_add_2y_corner i,
      simp only [vector.nth_of_fn] at x_add_2y_in_x_add_2y_corner,
      cases x_add_2y_in_x_add_2y_corner with x_add_2y_corner_le_x_add_2y x_add_2y_lt_x_add_2y_corner_add_one,
      rw in_cube at x_core'_in_x_corner_core',
      replace x_core'_in_x_corner_core' := x_core'_in_x_corner_core' i,
      cases x_core'_in_x_corner_core' with x_corner_core'_le_x_core' x_core'_lt_x_corner_core'_add_one,
      rcases eq_or_lt_or_gt (x_add_2y_offset.nth i) (x_add_2y.nth i / 2) with 
        x_add_2y_offset_eq_x_add_2y_div_2 | x_add_2y_offset_lt_x_add_2y_div_2 | x_add_2y_offset_gt_x_add_2y_div_2,
      exact x_add_2y_offset_eq_x_add_2y_div_2,
      { exfalso,
        have x_add_2y_offset_le_x_add_2y_div_2_sub_1 : x_add_2y_offset.nth i ≤ (x_add_2y.nth i) / 2 - 1 := by linarith,
        have x_add_2y_offset_eq_x_add_2y_corner_sub_x_corner_core'_div_2 : 
          ↑(x_add_2y_offset.nth i ) = (x_add_2y_corner.nth i - x_corner_core'.nth i) / 2 := by linarith,
        have cast_x_add_2y_offset_le_x_add_2y_div_2_sub_1 : (↑(x_add_2y_offset.nth i) : ℝ) ≤ ↑((x_add_2y.nth i) / 2) - 1 := 
          by exact_mod_cast x_add_2y_offset_le_x_add_2y_div_2_sub_1,
        rw x_add_2y_offset_eq_x_add_2y_corner_sub_x_corner_core'_div_2 at cast_x_add_2y_offset_le_x_add_2y_div_2_sub_1,
        by_cases x_add_2y_even : even (x_add_2y.nth i),
        { have cast_x_add_2y_div_2 : ↑(x_add_2y.nth i / 2) = ↑(x_add_2y.nth i)/ (2 : ℝ) :=
            begin
              have h := int.two_mul_div_two_of_even x_add_2y_even,
              have cast_h : (2 : ℝ) * ↑(x_add_2y.nth i / 2) = ↑(x_add_2y.nth i) := by exact_mod_cast h,
              linarith,
            end,
          have x_core'_eq_zero : x_core'.nth i = 0 :=
            begin
              rw core_points at x_core'_in_core_points,
              simp only [set.mem_set_of_eq] at x_core'_in_core_points,
              cases x_core'_in_core_points i with x_core'_eq_zero x_core'_eq_one,
              exact x_core'_eq_zero,
              exfalso,
              rw x_core'_eq_one at x_corner_core'_le_x_core' x_core'_lt_x_corner_core'_add_one,
              cases x_add_2y_even with x_add_2y_half x_add_2y_eq_double_x_add_2y_half,
              have cast_x_add_2y_eq_double_x_add_2y_half : ↑(x_add_2y.nth i) = (2 : ℝ) * ↑x_add_2y_half := 
                by exact_mod_cast x_add_2y_eq_double_x_add_2y_half,
              have x_add_2y_half_eq_x_add_2y_offset : x_add_2y_half = x_add_2y_offset.nth i := by linarith,
              rw [← x_add_2y_half_eq_x_add_2y_offset, ← cast_x_add_2y_eq_double_x_add_2y_half] at x_add_2y_corner_eq_x_corner_core'_add_double_x_add_2y_offset,
              linarith,
            end,
          rw cast_x_add_2y_div_2 at cast_x_add_2y_offset_le_x_add_2y_div_2_sub_1,
          linarith,
        },
        rename x_add_2y_even x_add_2y_not_even,
        have x_add_2y_odd : odd (x_add_2y.nth i) := by {rw ← int.odd_iff_not_even at x_add_2y_not_even, exact x_add_2y_not_even},
        have cast_x_add_2y_div_2 : ↑(x_add_2y.nth i / 2) = (↑(x_add_2y.nth i) - 1) / (2 : ℝ) :=
          begin
            have h := int.two_mul_div_two_of_odd x_add_2y_odd,
            have cast_h : (2 : ℝ) * ↑(x_add_2y.nth i / 2) = ↑(x_add_2y.nth i) - 1 := by exact_mod_cast h,
            linarith,
          end,
        have x_core'_eq_zero : x_core'.nth i = 1 :=
          begin
            rw core_points at x_core'_in_core_points,
            simp only [set.mem_set_of_eq] at x_core'_in_core_points,
            cases x_core'_in_core_points i with x_core'_eq_zero x_core'_eq_one,
            { exfalso,
              rw x_core'_eq_zero at x_corner_core'_le_x_core' x_core'_lt_x_corner_core'_add_one,
              cases x_add_2y_odd with x_add_2y_half x_add_2y_eq_double_x_add_2y_half_add_one,
              have cast_x_add_2y_eq_double_x_add_2y_half_add_one : ↑(vector.nth x_add_2y i) = (2 : ℝ) * ↑x_add_2y_half + 1 := 
                by exact_mod_cast x_add_2y_eq_double_x_add_2y_half_add_one,
              have x_add_2y_half_eq_x_add_2y_offset : x_add_2y_half = x_add_2y_offset.nth i :=
                begin
                  rcases eq_or_lt_or_gt x_add_2y_half (x_add_2y_offset.nth i) with 
                    x_add_2y_half_eq_x_add_2y_offset | x_add_2y_half_lt_x_add_2y_offset | x_add_2y_half_gt_x_add_2y_offset,
                  exact x_add_2y_half_eq_x_add_2y_offset,
                  linarith,
                  linarith,
                end,
              rw ← x_add_2y_half_eq_x_add_2y_offset at x_add_2y_corner_eq_x_corner_core'_add_double_x_add_2y_offset,
              linarith,
            },
            exact x_core'_eq_one,
          end,
        rw cast_x_add_2y_div_2 at cast_x_add_2y_offset_le_x_add_2y_div_2_sub_1,
        linarith,
      },
      exfalso,
      have x_add_2y_offset_ge_x_add_2y_div_2_add_1 : x_add_2y_offset.nth i ≥ (x_add_2y.nth i) / 2 + 1 := by linarith,
      have x_add_2y_offset_eq_x_add_2y_corner_sub_x_corner_core'_div_2 : 
        ↑(x_add_2y_offset.nth i) = (x_add_2y_corner.nth i - x_corner_core'.nth i) / 2 := by linarith,
      have cast_x_add_2y_offset_ge_x_add_2y_div_2_add_1 : (↑(x_add_2y_offset.nth i) : ℝ) ≥ ↑((x_add_2y.nth i) / 2) + 1 := 
        by exact_mod_cast x_add_2y_offset_ge_x_add_2y_div_2_add_1,
      rw x_add_2y_offset_eq_x_add_2y_corner_sub_x_corner_core'_div_2 at cast_x_add_2y_offset_ge_x_add_2y_div_2_add_1,
      by_cases x_add_2y_even : even (x_add_2y.nth i),
      { have cast_x_add_2y_div_2 : ↑(x_add_2y.nth i / 2) = ↑(x_add_2y.nth i)/ (2 : ℝ) :=
          begin
            have h := int.two_mul_div_two_of_even x_add_2y_even,
            have cast_h : (2 : ℝ) * ↑(x_add_2y.nth i / 2) = ↑(x_add_2y.nth i) := by exact_mod_cast h,
            linarith,
          end,
        have x_core'_eq_zero : x_core'.nth i = 0 :=
          begin
            rw core_points at x_core'_in_core_points,
            simp only [set.mem_set_of_eq] at x_core'_in_core_points,
            cases x_core'_in_core_points i with x_core'_eq_zero x_core'_eq_one,
            exact x_core'_eq_zero,
            exfalso,
            rw x_core'_eq_one at x_corner_core'_le_x_core' x_core'_lt_x_corner_core'_add_one,
            cases x_add_2y_even with x_add_2y_half x_add_2y_eq_double_x_add_2y_half,
            have cast_x_add_2y_eq_double_x_add_2y_half : ↑(x_add_2y.nth i) = (2 : ℝ) * ↑x_add_2y_half := 
              by exact_mod_cast x_add_2y_eq_double_x_add_2y_half,
            have x_add_2y_half_eq_x_add_2y_offset : x_add_2y_half = x_add_2y_offset.nth i := by linarith,
            rw [← x_add_2y_half_eq_x_add_2y_offset, ← cast_x_add_2y_eq_double_x_add_2y_half] at x_add_2y_corner_eq_x_corner_core'_add_double_x_add_2y_offset,
            linarith,
          end,
        rw cast_x_add_2y_div_2 at cast_x_add_2y_offset_ge_x_add_2y_div_2_add_1,
        linarith,
      },
      rename x_add_2y_even x_add_2y_not_even,
      have x_add_2y_odd : odd (x_add_2y.nth i) := by {rw ← int.odd_iff_not_even at x_add_2y_not_even, exact x_add_2y_not_even},
      have cast_x_add_2y_div_2 : ↑(x_add_2y.nth i / 2) = (↑(x_add_2y.nth i) - 1) / (2 : ℝ) :=
        begin
          have h := int.two_mul_div_two_of_odd x_add_2y_odd,
          have cast_h : (2 : ℝ) * ↑(x_add_2y.nth i / 2) = ↑(x_add_2y.nth i) - 1 := by exact_mod_cast h,
          linarith,
        end,
      have x_core'_eq_one : x_core'.nth i = 1 :=
        begin
          rw core_points at x_core'_in_core_points,
          simp only [set.mem_set_of_eq] at x_core'_in_core_points,
          cases x_core'_in_core_points i with x_core'_eq_zero x_core'_eq_one,
          { exfalso,
            rw x_core'_eq_zero at x_corner_core'_le_x_core' x_core'_lt_x_corner_core'_add_one,
            cases x_add_2y_odd with x_add_2y_half x_add_2y_eq_double_x_add_2y_half_add_one,
            have cast_x_add_2y_eq_double_x_add_2y_half_add_one : ↑(vector.nth x_add_2y i) = (2 : ℝ) * ↑x_add_2y_half + 1 := 
              by exact_mod_cast x_add_2y_eq_double_x_add_2y_half_add_one,
            have x_add_2y_half_eq_x_add_2y_offset : x_add_2y_half = x_add_2y_offset.nth i :=
              begin
                rcases eq_or_lt_or_gt x_add_2y_half (x_add_2y_offset.nth i) with 
                  x_add_2y_half_eq_x_add_2y_offset | x_add_2y_half_lt_x_add_2y_offset | x_add_2y_half_gt_x_add_2y_offset,
                exact x_add_2y_half_eq_x_add_2y_offset,
                linarith,
                linarith,
              end,
            rw ← x_add_2y_half_eq_x_add_2y_offset at x_add_2y_corner_eq_x_corner_core'_add_double_x_add_2y_offset,
            linarith,
          },
          exact x_core'_eq_one,
        end,
      rw cast_x_add_2y_div_2 at cast_x_add_2y_offset_ge_x_add_2y_div_2_add_1,
      linarith,
    end,
  have x_add_2y_offset_eq_x_offset_add_y : ∀ i : fin d, vector.nth x_add_2y_offset i = vector.nth x_offset i + vector.nth y i :=
    begin
      intro i,
      rw [x_offset_def, x_add_2y_offset_def],
      dsimp only[x_add_2y],
      rw[add_int_vectors, double_int_vector],
      simp only [vector.nth_of_fn],
      have two_divides_double_y : 2 ∣ (2 * vector.nth y i) := dvd_mul_right 2 (vector.nth y i),
      rw int.add_div_of_dvd_right two_divides_double_y,
      simp only [int.mul_div_cancel_left, ne.def, bit0_eq_zero, one_ne_zero, not_false_iff],
    end,
  have x_core_eq_x_core' : x_core = x_core' :=
    begin
      apply vector.ext,
      intro i,
      replace x_offset_def := x_offset_def i,
      replace x_add_2y_offset_def := x_add_2y_offset_def i,
      replace x_corner_eq_x_corner_core_add_double_x_offset : 
        x_corner.nth i = (add_vectors x_corner_core (int_point_to_point (double_int_vector x_offset))).nth i :=
        by rw x_corner_eq_x_corner_core_add_double_x_offset,
      replace x_add_2y_offset_eq_x_offset_add_y := x_add_2y_offset_eq_x_offset_add_y i,
      rw [add_vectors, int_point_to_point, double_int_vector] at x_corner_eq_x_corner_core_add_double_x_offset,
      simp only [vector.nth_of_fn, int.cast_mul, int.cast_bit0, int.cast_one] at x_corner_eq_x_corner_core_add_double_x_offset,
      rw [int_point_to_point, cube] at x_in_x_corner,
      simp only [set.mem_set_of_eq] at x_in_x_corner,
      rw in_cube at x_in_x_corner,
      replace x_in_x_corner := x_in_x_corner i,
      simp only [vector.nth_of_fn] at x_in_x_corner,
      cases x_in_x_corner with x_corner_le_x x_lt_x_corner_add_one,
      rw in_cube at x_core_in_x_corner_core,
      replace x_core_in_x_corner_core := x_core_in_x_corner_core i,
      cases x_core_in_x_corner_core with x_corner_core_le_x_core x_core_lt_x_corner_core_add_one,
      replace x_add_2y_corner_eq_x_corner_core'_add_double_x_add_2y_offset :
        x_add_2y_corner.nth i = (add_vectors x_corner_core' (int_point_to_point (double_int_vector x_add_2y_offset))).nth i :=
        by rw x_add_2y_corner_eq_x_corner_core'_add_double_x_add_2y_offset,
      rw [add_vectors, int_point_to_point, double_int_vector] at x_add_2y_corner_eq_x_corner_core'_add_double_x_add_2y_offset,
      simp only [vector.nth_of_fn, int.cast_mul, int.cast_bit0, int.cast_one] at x_add_2y_corner_eq_x_corner_core'_add_double_x_add_2y_offset,
      rw [int_point_to_point, cube] at x_add_2y_in_x_add_2y_corner,
      simp only [set.mem_set_of_eq] at x_add_2y_in_x_add_2y_corner,
      rw in_cube at x_add_2y_in_x_add_2y_corner,
      replace x_add_2y_in_x_add_2y_corner := x_add_2y_in_x_add_2y_corner i,
      simp only [vector.nth_of_fn] at x_add_2y_in_x_add_2y_corner,
      cases x_add_2y_in_x_add_2y_corner with x_add_2y_corner_le_x_add_2y x_add_2y_lt_x_add_2y_corner_add_one,
      rw in_cube at x_core'_in_x_corner_core',
      replace x_core'_in_x_corner_core' := x_core'_in_x_corner_core' i,
      cases x_core'_in_x_corner_core' with x_corner_core'_le_x_core' x_core'_lt_x_corner_core'_add_one,
      by_cases x_even : even (x.nth i),
      { have cast_x_div_2 : ↑(vector.nth x i / 2) = (↑(x.nth i)) / (2 : ℝ) :=
          begin
            have h := int.two_mul_div_two_of_even x_even,
            have cast_h : (2 : ℝ) * ↑(vector.nth x i / 2) = ↑(vector.nth x i) := by exact_mod_cast h,
            linarith,
          end,
        have x_core_eq_zero : x_core.nth i = 0 :=
          begin
            rw core_points at x_core_in_core_points,
            simp only [set.mem_set_of_eq] at x_core_in_core_points,
            cases x_core_in_core_points i with x_core_eq_zero x_core_eq_one,
            exact x_core_eq_zero,
            exfalso,
            rw x_core_eq_one at x_corner_core_le_x_core x_core_lt_x_corner_core_add_one,
            cases x_even with x_half x_eq_double_x_half,
            have cast_x_eq_double_x_half : ↑(x.nth i) = (2 : ℝ) * ↑x_half := by exact_mod_cast x_eq_double_x_half,
            have x_half_eq_x_offset : x_half = x_offset.nth i :=
              begin
                rcases eq_or_lt_or_gt x_half (x_offset.nth i) with x_half_eq_x_offset | x_half_lt_x_offset | x_half_gt_x_offset,
                exact x_half_eq_x_offset,
                { exfalso,
                  have x_half_le_x_offset_sub_one : x_half ≤ x_offset.nth i - 1 := by linarith,
                  have cast_x_half_le_x_offset_sub_one : (↑x_half : ℝ) ≤ ↑(x_offset.nth i) - 1 := by exact_mod_cast x_half_le_x_offset_sub_one,
                  linarith,
                },
                exfalso,
                have x_half_ge_x_offset_add_one : x_half ≥ x_offset.nth i + 1 := by linarith,
                have cast_x_half_ge_x_offset_add_one : (↑(x_half) : ℝ) ≥ ↑(x_offset.nth i) + 1 := by exact_mod_cast x_half_ge_x_offset_add_one,
                linarith,
              end,
            rw [← x_half_eq_x_offset, ← cast_x_eq_double_x_half] at x_corner_eq_x_corner_core_add_double_x_offset,
            linarith,
          end,
        have x_add_2y_even : even (x_add_2y.nth i) :=
          begin
            dsimp only[x_add_2y],
            rw[add_int_vectors, double_int_vector],
            simp only [vector.nth_of_fn],
            rw ← iff_true (even (vector.nth x i)) at x_even,
            rw [int.even_add, x_even, true_iff, even_iff_two_dvd],
            exact dvd_mul_right 2 (vector.nth y i),
          end,
        have cast_x_add_2y_div_2 : ↑(x_add_2y.nth i / 2) = ↑(x_add_2y.nth i)/ (2 : ℝ) :=
          begin
            have h := int.two_mul_div_two_of_even x_add_2y_even,
            have cast_h : (2 : ℝ) * ↑(x_add_2y.nth i / 2) = ↑(x_add_2y.nth i) := by exact_mod_cast h,
            linarith,
          end,
        have x_core'_eq_zero : x_core'.nth i = 0 :=
          begin
            rw core_points at x_core'_in_core_points,
            simp only [set.mem_set_of_eq] at x_core'_in_core_points,
            cases x_core'_in_core_points i with x_core'_eq_zero x_core'_eq_one,
            exact x_core'_eq_zero,
            exfalso,
            rw x_core'_eq_one at x_corner_core'_le_x_core' x_core'_lt_x_corner_core'_add_one,
            cases x_add_2y_even with x_add_2y_half x_add_2y_eq_double_x_add_2y_half,
            have cast_x_add_2y_eq_double_x_add_2y_half : ↑(x_add_2y.nth i) = (2 : ℝ) * ↑x_add_2y_half := 
              by exact_mod_cast x_add_2y_eq_double_x_add_2y_half,
            have x_add_2y_half_eq_x_add_2y_offset : x_add_2y_half = x_add_2y_offset.nth i :=
              begin
                rcases eq_or_lt_or_gt x_add_2y_half (x_add_2y_offset.nth i) with 
                  x_add_2y_half_eq_x_add_2y_offset | x_add_2y_half_lt_x_add_2y_offset | x_add_2y_half_gt_x_add_2y_offset,
                exact x_add_2y_half_eq_x_add_2y_offset,
                { exfalso,
                  have x_add_2y_half_le_x_add_2y_offset_sub_one : x_add_2y_half ≤ x_add_2y_offset.nth i - 1 := by linarith,
                  have cast_x_add_2y_half_le_x_add_2y_offset_sub_one : ↑x_add_2y_half ≤ ↑(x_add_2y_offset.nth i) - (1 : ℝ) :=
                    by exact_mod_cast x_add_2y_half_le_x_add_2y_offset_sub_one,
                  linarith,
                },
                exfalso,
                have x_add_2y_half_ge_x_add_2y_offset_add_one : x_add_2y_half ≥ x_add_2y_offset.nth i + 1 := by linarith,
                have cast_x_add_2y_half_ge_x_add_2y_offset_add_one : ↑x_add_2y_half ≥ ↑(x_add_2y_offset.nth i) + (1 : ℝ) :=
                  by exact_mod_cast x_add_2y_half_ge_x_add_2y_offset_add_one,
                linarith,
              end,
            rw [← x_add_2y_half_eq_x_add_2y_offset, ← cast_x_add_2y_eq_double_x_add_2y_half] at x_add_2y_corner_eq_x_corner_core'_add_double_x_add_2y_offset,
            linarith,
          end,
        rw [x_core_eq_zero, x_core'_eq_zero],
      },
      rename x_even x_not_even,
      have x_odd : odd (x.nth i) := by {rw ← int.odd_iff_not_even at x_not_even, exact x_not_even},
      have cast_x_div_2 : ↑(vector.nth x i / 2) = (↑(x.nth i) - 1) / (2 : ℝ) :=
        begin
          have h := int.two_mul_div_two_of_odd x_odd,
          have cast_h : (2 : ℝ) * ↑(vector.nth x i / 2) = ↑(vector.nth x i) - 1 := by exact_mod_cast h,
          linarith,
        end,
      have x_core_eq_one : x_core.nth i = 1 :=
        begin
          rw core_points at x_core_in_core_points,
          simp only [set.mem_set_of_eq] at x_core_in_core_points,
          cases x_core_in_core_points i with x_core_eq_zero x_core_eq_one,
          { exfalso,
            rw x_core_eq_zero at x_corner_core_le_x_core x_core_lt_x_corner_core_add_one,
            cases x_odd with x_half x_eq_double_x_half_add_one,
            have cast_x_eq_double_x_half_add_one : ↑(vector.nth x i) = (2 : ℝ) * ↑x_half + 1 := by exact_mod_cast x_eq_double_x_half_add_one,
            have x_half_eq_x_offset : x_half = x_offset.nth i :=
              begin
                rcases eq_or_lt_or_gt x_half (x_offset.nth i) with x_half_eq_x_offset | x_half_lt_x_offset | x_half_gt_x_offset,
                exact x_half_eq_x_offset,
                { exfalso,
                  have x_half_le_x_offset_sub_one : x_half ≤ x_offset.nth i - 1 := by linarith,
                  have cast_x_half_le_x_offset_sub_one : ↑x_half ≤ ↑(x_offset.nth i) - (1 : ℝ) := by exact_mod_cast x_half_le_x_offset_sub_one,
                  linarith,
                },
                exfalso,
                have x_half_ge_x_offset_add_one : x_half ≥ x_offset.nth i + 1 := by linarith,
                have cast_x_half_ge_x_offset_add_one : ↑(x_half) ≥ ↑(x_offset.nth i) + (1 : ℝ) := by exact_mod_cast x_half_ge_x_offset_add_one,
                linarith,
              end,
            rw ← x_half_eq_x_offset at x_corner_eq_x_corner_core_add_double_x_offset,
            linarith,
          },
          exact x_core_eq_one,
        end,
      have x_add_2y_odd : odd (x_add_2y.nth i) :=
        begin
          dsimp only[x_add_2y],
          rw [add_int_vectors, double_int_vector],
          simp only [vector.nth_of_fn],
          rw ← iff_true (odd (vector.nth x i)) at x_odd,
          rw [int.odd_add, x_odd, true_iff, even_iff_two_dvd],
          exact dvd_mul_right 2 (vector.nth y i),
        end,
      have cast_x_add_2y_div_2 : ↑(x_add_2y.nth i / 2) = (↑(x_add_2y.nth i) - 1) / (2 : ℝ) :=
        begin
          have h := int.two_mul_div_two_of_odd x_add_2y_odd,
          have cast_h : (2 : ℝ) * ↑(x_add_2y.nth i / 2) = ↑(x_add_2y.nth i) - 1 := by exact_mod_cast h,
          linarith,
        end,
      have x_core'_eq_one : x_core'.nth i = 1 :=
        begin
          rw core_points at x_core'_in_core_points,
          simp only [set.mem_set_of_eq] at x_core'_in_core_points,
          cases x_core'_in_core_points i with x_core'_eq_zero x_core'_eq_one,
          { exfalso,
            rw x_core'_eq_zero at x_corner_core'_le_x_core' x_core'_lt_x_corner_core'_add_one,
            cases x_add_2y_odd with x_add_2y_half x_add_2y_eq_double_x_add_2y_half_add_one,
            have cast_x_add_2y_eq_double_x_add_2y_half_add_one : ↑(vector.nth x_add_2y i) = (2 : ℝ) * ↑x_add_2y_half + 1 := 
              by exact_mod_cast x_add_2y_eq_double_x_add_2y_half_add_one,
            have x_add_2y_half_eq_x_add_2y_offset : x_add_2y_half = x_add_2y_offset.nth i :=
              begin
                rcases eq_or_lt_or_gt x_add_2y_half (x_add_2y_offset.nth i) with 
                  x_add_2y_half_eq_x_add_2y_offset | x_add_2y_half_lt_x_add_2y_offset | x_add_2y_half_gt_x_add_2y_offset,
                exact x_add_2y_half_eq_x_add_2y_offset,
                { exfalso,
                  have x_add_2y_half_le_x_add_2y_offset_sub_one : x_add_2y_half ≤ (x_add_2y_offset.nth i) - 1 := by linarith,
                  have cast_x_add_2y_half_le_x_add_2y_offset_sub_one : ↑(x_add_2y_half) ≤ ↑(x_add_2y_offset.nth i) - (1 : ℝ) :=
                    by exact_mod_cast x_add_2y_half_le_x_add_2y_offset_sub_one,
                  linarith,
                },
                exfalso,
                have x_add_2y_half_ge_x_add_2y_offset_add_one : x_add_2y_half ≥ (x_add_2y_offset.nth i) + 1 := by linarith,
                have cast_x_add_2y_half_ge_x_add_2y_offset_add_one : ↑(x_add_2y_half) ≥ ↑(x_add_2y_offset.nth i) + (1 : ℝ) :=
                  by exact_mod_cast x_add_2y_half_ge_x_add_2y_offset_add_one,
                linarith,
              end,
            rw ← x_add_2y_half_eq_x_add_2y_offset at x_add_2y_corner_eq_x_corner_core'_add_double_x_add_2y_offset,
            linarith,
          },
          exact x_core'_eq_one,
        end,
      rw [x_core_eq_one, x_core'_eq_one],
    end,
  have x_corner_core_eq_x_corner_core' : x_corner_core = x_corner_core' :=
    begin
      rcases T_is_tiling x_core with ⟨unique_corner, unique_corner_in_T, x_core_in_unique_corner, unique_corner_unique⟩,
      conv at unique_corner_unique
      begin
        find (x_core ∈ cube _) {rw cube},
      end,
      simp only [set.mem_set_of_eq] at unique_corner_unique,
      have x_corner_core_eq_unique_corner := unique_corner_unique x_corner_core x_corner_core_in_T x_core_in_x_corner_core,
      rw ← x_core_eq_x_core' at x_core'_in_x_corner_core',
      have x_corner_core'_eq_unique_corner := unique_corner_unique x_corner_core' x_corner_core'_in_T x_core'_in_x_corner_core',
      rw [x_corner_core_eq_unique_corner, x_corner_core'_eq_unique_corner],
    end,
  apply vector.ext,
  intro i,
  rw [x_corner_eq_x_corner_core_add_double_x_offset, x_add_2y_corner_eq_x_corner_core'_add_double_x_add_2y_offset, add_vectors, add_vectors, add_vectors,
    int_point_to_point, double_int_vector, int_point_to_point, double_int_vector, int_point_to_point, double_int_vector],
  simp only [vector.nth_of_fn, int.cast_mul, int.cast_bit0, int.cast_one],
  rw [x_corner_core_eq_x_corner_core', x_add_2y_offset_eq_x_offset_add_y],
  simp only [int.cast_add],
  rw [mul_add, ← add_assoc],
end

lemma shifted_periodic_tiling_still_periodic_b_floor_even_case {d : ℕ} (a b : ℝ) {T : set (point d)} (T_is_tiling : is_tiling T)
  (T_is_periodic : is_periodic T_is_tiling) (i : fin d) (T_shifted_is_tiling : is_tiling (shift_tiling T i a b)) 
  (T_has_periodic_core : has_periodic_core T_is_tiling) (t : vector ℝ d) (t' : point d) (t'_in_T : t' ∈ T) 
  (t_eq_t'_add_b : t = add_vectors t' (scaled_basis_vector b i)) (t'_eq_a_mod_one : eq_mod_one (vector.nth t' i) a)
  (cp : point d) (cp_in_core_points : cp ∈ core_points d) (t'_core : point d) (t'_core_in_T : t'_core ∈ T)
  (t'_offset : int_point d) (cp_in_t'_core : in_cube t'_core cp)
  (t'_eq_t'_core_add_double_t'_offset : t' = add_vectors t'_core (int_point_to_point (double_int_vector t'_offset))) :
  let b_floor : ℤ := ⌊b⌋
  in even b_floor →
     (∃ (p : point d) (H : p ∈ core_points d) (t_core : point d)
        (H : t_core ∈ shift_tiling T i a b) (t_offset : int_point d),
        in_cube t_core p ∧
          t =
            add_vectors t_core
              (int_point_to_point (double_int_vector t_offset))) :=
begin
  intros b_floor b_floor_even,
  let b_floor_div_2 := b_floor / 2,
  have double_b_floor_div_2 : 2 * b_floor_div_2 = b_floor :=
    begin
      dsimp[b_floor_div_2],
      exact int.two_mul_div_two_of_even b_floor_even,
    end,
  by_cases t'_core_add_b_sub_b_floor_le_one : t'_core.nth i + b - b_floor ≤ 1,
  { let t_core := vector.of_fn (λ j, if(i = j) then t'_core.nth j + b - b_floor else t'_core.nth j),
    have t_core_in_T_shifted : t_core ∈ shift_tiling T i a b :=
      begin
        rw shift_tiling,
        simp only [exists_prop, set.mem_union_eq],
        right,
        let t_core_preshift := vector.of_fn (λ j, if(i = j) then t'_core.nth j - b_floor else t'_core.nth j),
        have t_core_preshift_in_T : t_core_preshift ∈ T :=
          begin
            rw is_periodic at T_is_periodic,
            let int_cp : int_point d := vector.of_fn(λ j, if(cp.nth j = 0) then 0 else 1),
            replace T_is_periodic := T_is_periodic int_cp (int_scaled_basis_vector (-b_floor_div_2) i),
            have t'_core_rw : t'_core = (int_point_to_corner T_is_tiling int_cp).val :=
              begin
                rcases (int_point_to_corner T_is_tiling int_cp).property with
                  ⟨int_cp_corner_in_T, int_cp_in_int_cp_corner, int_cp_corner_unique⟩,
                have int_point_to_point_int_cp_eq_cp : int_point_to_point int_cp = cp :=
                  begin
                    apply vector.ext,
                    intro j,
                    rw int_point_to_point,
                    dsimp only[int_cp],
                    simp only [vector.nth_of_fn],
                    rw core_points at cp_in_core_points,
                    simp only [set.mem_set_of_eq] at cp_in_core_points,
                    cases cp_in_core_points j with cp_eq_zero cp_eq_one,
                    { rw [if_pos cp_eq_zero, cp_eq_zero],
                      refl,
                    },
                    have cp_ne_zero : vector.nth cp j ≠ 0 := by {rw cp_eq_one, exact one_ne_zero},
                    rw [if_neg cp_ne_zero, cp_eq_one],
                    have one_eq_one : 1 = 1 := by refl,
                    exact_mod_cast one_eq_one,
                  end,
                conv at int_cp_corner_unique
                begin
                  find (int_point_to_point int_cp) {rw int_point_to_point_int_cp_eq_cp},
                  find (cp ∈ cube _) {rw cube, simp},
                end,
                exact int_cp_corner_unique t'_core t'_core_in_T cp_in_t'_core,
              end,
            have t_core_preshift_rw : add_vectors t'_core (int_point_to_point (double_int_vector (int_scaled_basis_vector (-b_floor_div_2) i))) = t_core_preshift :=
              begin
                apply vector.ext,
                intro j,
                rw [int_point_to_point, double_int_vector, add_vectors, int_scaled_basis_vector],
                dsimp only[t_core_preshift],
                simp only [vector.nth_of_fn, mul_ite, mul_neg, mul_zero],
                by_cases i_eq_j : i = j,
                { rw [if_pos i_eq_j, if_pos i_eq_j, double_b_floor_div_2],
                  simp only [int.cast_neg],
                  refl,
                },
                rename i_eq_j i_ne_j,
                rw [if_neg i_ne_j, if_neg i_ne_j, int.cast_zero, add_zero],
              end,
            rw [← t'_core_rw, t_core_preshift_rw, int_point_to_corner] at T_is_periodic,
            have h := 
              (point_to_corner T_is_tiling (int_point_to_point (add_int_vectors int_cp (double_int_vector (int_scaled_basis_vector (-b_floor_div_2) i))))).property,
            rcases h with ⟨goal, _, _⟩,
            rw ← T_is_periodic,
            exact goal,
          end,
        use [t_core_preshift, t_core_preshift_in_T],
        split,
        { apply vector.ext,
          intro j,
          dsimp[t_core_preshift, t_core],
          rw [add_vectors, scaled_basis_vector],
          simp only [vector.nth_of_fn],
          by_cases i_eq_j : i = j,
          { rw [if_pos i_eq_j, if_pos i_eq_j, if_pos i_eq_j],
            linarith,
          },
          rename i_eq_j i_ne_j,
          rw [if_neg i_ne_j, if_neg i_ne_j, if_neg i_ne_j, add_zero],
        },
        dsimp[t_core_preshift],
        simp only [if_true, eq_self_iff_true, vector.nth_of_fn],
        have t'_core_eq_a_mod_one : eq_mod_one (t'_core.nth i) a :=
          begin
            have h : t'.nth i = (add_vectors t'_core (int_point_to_point (double_int_vector t'_offset))).nth i := by rw t'_eq_t'_core_add_double_t'_offset,
            rw [add_vectors, int_point_to_point, double_int_vector] at h,
            simp only [int.cast_bit0, int.cast_mul, int.cast_one, vector.nth_of_fn] at h,
            replace h : vector.nth t' i - 2 * ↑(vector.nth t'_offset i) = vector.nth t'_core i := by linarith,
            have t'_offset_id : (2 : ℝ) * ↑(vector.nth t'_offset i) = ↑(2 * (vector.nth t'_offset i)) := by finish,
            rw [← h, t'_offset_id],
            exact eq_mod_one_int_sub t'_eq_a_mod_one,
          end,
        exact eq_mod_one_int_sub t'_core_eq_a_mod_one,
      end,
    let t_offset := vector.of_fn (λ j, if(i = j) then t'_offset.nth i + b_floor_div_2 else t'_offset.nth j),
    by_cases t'_core_add_b_sub_b_floor_le_zero : t'_core.nth i + b - b_floor ≤ 0,
    { let new_cp : point d := vector.of_fn (λ j, if(i = j) then 0 else cp.nth j),
      have new_cp_in_core_points : new_cp ∈ core_points d :=
        begin
          rw core_points,
          simp only [vector.nth_of_fn, set.mem_set_of_eq, ite_eq_left_iff],
          intro j,
          by_cases i_eq_j : i = j,
          { left,
            intro i_ne_j,
            exfalso,
            exact i_ne_j i_eq_j,
          },
          rename i_eq_j i_ne_j,
          rw core_points at cp_in_core_points,
          simp only [set.mem_set_of_eq] at cp_in_core_points,
          replace cp_in_core_points := cp_in_core_points j,
          cases cp_in_core_points with cp_eq_zero cp_eq_one,
          { left,
            intro i_ne_j,
            exact cp_eq_zero,
          },
          right,
          rw if_neg i_ne_j,
          exact cp_eq_one,
        end,
      use [new_cp, new_cp_in_core_points, t_core, t_core_in_T_shifted, t_offset],
      split,
      { dsimp[new_cp, t_core],
        rw in_cube,
        simp only [not_exists, ge_iff_le, vector.nth_of_fn],
        intro j,
        by_cases i_eq_j : i = j,
        { rw [if_pos i_eq_j, if_pos i_eq_j],
          split, {rw ← i_eq_j, exact t'_core_add_b_sub_b_floor_le_zero},
          have zero_le_b_sub_b_floor : 0 ≤ b - ↑b_floor :=
            begin
              dsimp only[b_floor],
              have h := int.floor_le b,
              clear_except h,
              linarith,
            end,
          have neg_one_lt_t'_core: -1 < t'_core.nth j :=
            begin
              rw in_cube at cp_in_t'_core,
              replace cp_in_t'_core := cp_in_t'_core j,
              rcases cp_in_t'_core with ⟨t'_core_le_cp, cp_lt_t'_core_add_one⟩,
              have cp_eq_zero : cp.nth j = 0 :=
                begin
                  rw i_eq_j at t'_core_add_b_sub_b_floor_le_zero,
                  rw core_points at cp_in_core_points,
                  simp only [set.mem_set_of_eq] at cp_in_core_points,
                  cases cp_in_core_points j with cp_eq_zero cp_eq_one,
                  exact cp_eq_zero,
                  rw cp_eq_one at cp_lt_t'_core_add_one,
                  linarith,
                end,
              rw cp_eq_zero at cp_lt_t'_core_add_one,
              linarith,
            end,
          clear_except zero_le_b_sub_b_floor neg_one_lt_t'_core,
          linarith,
        },
        rename i_eq_j i_ne_j,
        rw [if_neg i_ne_j, if_neg i_ne_j],
        rw in_cube at cp_in_t'_core,
        replace cp_in_t'_core := cp_in_t'_core j,
        exact cp_in_t'_core,
      },
      apply vector.ext,
      intro j,
      dsimp[t_core, t_offset],
      rw [t_eq_t'_add_b, add_vectors, add_vectors, scaled_basis_vector, int_point_to_point, double_int_vector],
      simp only [vector.nth_of_fn, mul_ite],
      by_cases i_eq_j : i = j,
      { rw [if_pos i_eq_j, if_pos i_eq_j, if_pos i_eq_j, mul_add, double_b_floor_div_2],
        simp only [int.cast_add, int.cast_mul, int.cast_bit0, int.cast_one, sub_add_add_cancel],
        rw [add_assoc, add_comm b (2 * ↑(vector.nth t'_offset i)), ← add_assoc, add_left_inj, t'_eq_t'_core_add_double_t'_offset, 
          int_point_to_point, double_int_vector, add_vectors, i_eq_j],
        simp only [vector.nth_of_fn, int.cast_mul, int.cast_bit0, int.cast_one, add_right_inj, mul_eq_mul_left_iff, int.cast_inj,
          bit0_eq_zero, one_ne_zero, or_false],
      },
      rename i_eq_j i_ne_j,
      rw [t'_eq_t'_core_add_double_t'_offset, add_vectors, int_point_to_point, double_int_vector, if_neg i_ne_j, if_neg i_ne_j, if_neg i_ne_j, add_zero],
      simp only [vector.nth_of_fn],
    },
    rename t'_core_add_b_sub_b_floor_le_zero t'_core_add_b_sub_b_floor_gt_zero,
    let new_cp : point d := vector.of_fn (λ j, if(i = j) then 1 else cp.nth j),
    have new_cp_in_core_points : new_cp ∈ core_points d :=
      begin
        rw core_points,
        simp only [vector.nth_of_fn, set.mem_set_of_eq, ite_eq_left_iff],
        intro j,
        by_cases i_eq_j : i = j,
        { right,
          intro i_ne_j,
          exfalso,
          exact i_ne_j i_eq_j,
        },
        rename i_eq_j i_ne_j,
        rw core_points at cp_in_core_points,
        simp only [set.mem_set_of_eq] at cp_in_core_points,
        replace cp_in_core_points := cp_in_core_points j,
        cases cp_in_core_points with cp_eq_zero cp_eq_one,
        { left,
          rw if_neg i_ne_j,
          exact cp_eq_zero,
        },
        right,
        intro _,
        exact cp_eq_one,
      end,
    use [new_cp, new_cp_in_core_points, t_core, t_core_in_T_shifted, t_offset],
    split,
    { dsimp[new_cp, t_core],
      rw in_cube,
      simp only [not_exists, ge_iff_le, vector.nth_of_fn],
      intro j,
      by_cases i_eq_j : i = j,
      { rw [if_pos i_eq_j, if_pos i_eq_j, ← i_eq_j],
        split, exact t'_core_add_b_sub_b_floor_le_one,
        simp only [sub_nonpos, not_le] at t'_core_add_b_sub_b_floor_gt_zero,
        linarith,
      },
      rename i_eq_j i_ne_j,
      rw [if_neg i_ne_j, if_neg i_ne_j],
      rw in_cube at cp_in_t'_core,
      replace cp_in_t'_core := cp_in_t'_core j,
      exact cp_in_t'_core,
    },
    apply vector.ext,
    intro j,
    dsimp[t_core, t_offset],
    rw [t_eq_t'_add_b, add_vectors, add_vectors, scaled_basis_vector, int_point_to_point, double_int_vector],
    simp only [vector.nth_of_fn, mul_ite],
    by_cases i_eq_j : i = j,
    { rw [if_pos i_eq_j, if_pos i_eq_j, if_pos i_eq_j, mul_add, double_b_floor_div_2],
      simp only [int.cast_add, int.cast_mul, int.cast_bit0, int.cast_one, sub_add_add_cancel],
      rw [add_assoc, add_comm b (2 * ↑(vector.nth t'_offset i)), ← add_assoc, add_left_inj, t'_eq_t'_core_add_double_t'_offset, 
        int_point_to_point, double_int_vector, add_vectors, i_eq_j],
      simp only [vector.nth_of_fn, int.cast_mul, int.cast_bit0, int.cast_one, add_right_inj, mul_eq_mul_left_iff, int.cast_inj,
        bit0_eq_zero, one_ne_zero, or_false],
    },
    rename i_eq_j i_ne_j,
    rw [t'_eq_t'_core_add_double_t'_offset, add_vectors, int_point_to_point, double_int_vector, if_neg i_ne_j, if_neg i_ne_j, if_neg i_ne_j, add_zero],
    simp only [vector.nth_of_fn],
  },
  rename t'_core_add_b_sub_b_floor_le_one one_lt_t'_core_add_b_sub_b_floor,
  simp only [not_le] at one_lt_t'_core_add_b_sub_b_floor,
  let t_core := vector.of_fn (λ j, if(i = j) then t'_core.nth j + b - b_floor - 2 else t'_core.nth j),
  have t_core_in_T_shifted : t_core ∈ shift_tiling T i a b :=
    begin
      rw shift_tiling,
      simp only [exists_prop, set.mem_union_eq],
      right,
      let t_core_preshift := vector.of_fn (λ j, if(i = j) then t'_core.nth j - b_floor - 2 else t'_core.nth j),
      have t_core_preshift_in_T : t_core_preshift ∈ T :=
        begin
          rw is_periodic at T_is_periodic,
          let int_cp : int_point d := vector.of_fn (λ j, if(cp.nth j = 0) then 0 else 1),
          replace T_is_periodic := T_is_periodic int_cp (int_scaled_basis_vector (-b_floor_div_2 - 1) i),
          have t'_core_rw : t'_core = (int_point_to_corner T_is_tiling int_cp).val :=
            begin
              rcases (int_point_to_corner T_is_tiling int_cp).property with
                ⟨int_cp_corner_in_T, int_cp_in_int_cp_corner, int_cp_corner_unique⟩,
              have int_point_to_point_int_cp_eq_cp : int_point_to_point int_cp = cp :=
                begin
                  apply vector.ext,
                  intro j,
                  rw int_point_to_point,
                  dsimp only[int_cp],
                  simp only [vector.nth_of_fn],
                  rw core_points at cp_in_core_points,
                  simp only [set.mem_set_of_eq] at cp_in_core_points,
                  cases cp_in_core_points j with cp_eq_zero cp_eq_one,
                  { rw [if_pos cp_eq_zero, cp_eq_zero],
                    refl,
                  },
                  have cp_ne_zero : vector.nth cp j ≠ 0 := by {rw cp_eq_one, exact one_ne_zero},
                  rw [if_neg cp_ne_zero, cp_eq_one],
                  have one_eq_one : 1 = 1 := by refl,
                  exact_mod_cast one_eq_one,
                end,
              conv at int_cp_corner_unique
              begin
                find (int_point_to_point int_cp) {rw int_point_to_point_int_cp_eq_cp},
                find (cp ∈ cube _) {rw cube, simp},
              end,
              exact int_cp_corner_unique t'_core t'_core_in_T cp_in_t'_core,
            end,
          have t_core_preshift_rw : 
            add_vectors t'_core (int_point_to_point (double_int_vector (int_scaled_basis_vector (-b_floor_div_2 - 1) i))) = t_core_preshift :=
            begin
              apply vector.ext,
              intro j,
              rw [int_point_to_point, double_int_vector, add_vectors, int_scaled_basis_vector],
              dsimp only[t_core_preshift],
              simp only [vector.nth_of_fn, mul_ite, mul_neg, mul_zero],
              by_cases i_eq_j : i = j,
              { rw [if_pos i_eq_j, if_pos i_eq_j, mul_sub],
                simp only [mul_neg, mul_one, int.cast_sub, int.cast_neg, int.cast_mul, int.cast_bit0, int.cast_one],
                have cast_double_b_floor_div_2 : (2 : ℝ) * ↑b_floor_div_2 = ↑b_floor := by exact_mod_cast double_b_floor_div_2,
                rw [cast_double_b_floor_div_2, add_sub, sub_left_inj, add_comm, neg_add_eq_sub],
              },
              rename i_eq_j i_ne_j,
              rw [if_neg i_ne_j, if_neg i_ne_j, int.cast_zero, add_zero],
            end,
          rw [← t'_core_rw, t_core_preshift_rw, int_point_to_corner] at T_is_periodic,
          have h := 
            (point_to_corner T_is_tiling (int_point_to_point (add_int_vectors int_cp (double_int_vector (int_scaled_basis_vector (-b_floor_div_2 - 1) i))))).property,
          rcases h with ⟨goal, _, _⟩,
          rw ← T_is_periodic,
          exact goal,
        end,
      use [t_core_preshift, t_core_preshift_in_T],
      split,
      { apply vector.ext,
        intro j,
        dsimp[t_core_preshift, t_core],
        rw [add_vectors, scaled_basis_vector],
        simp only [vector.nth_of_fn],
        by_cases i_eq_j : i = j,
        { rw [if_pos i_eq_j, if_pos i_eq_j, if_pos i_eq_j],
          linarith,
        },
        rename i_eq_j i_ne_j,
        rw [if_neg i_ne_j, if_neg i_ne_j, if_neg i_ne_j, add_zero],
      },
      dsimp[t_core_preshift],
      simp only [if_true, eq_self_iff_true, vector.nth_of_fn],
      have t'_core_eq_a_mod_one : eq_mod_one (t'_core.nth i) a :=
        begin
          have h : t'.nth i = (add_vectors t'_core (int_point_to_point (double_int_vector t'_offset))).nth i := by rw t'_eq_t'_core_add_double_t'_offset,
          rw [add_vectors, int_point_to_point, double_int_vector] at h,
          simp only [int.cast_bit0, int.cast_mul, int.cast_one, vector.nth_of_fn] at h,
          replace h : vector.nth t' i - 2 * ↑(vector.nth t'_offset i) = vector.nth t'_core i := by linarith,
          have t'_offset_id : (2 : ℝ) * ↑(vector.nth t'_offset i) = ↑(2 * (vector.nth t'_offset i)) := by finish,
          rw [← h, t'_offset_id],
          exact eq_mod_one_int_sub t'_eq_a_mod_one,
        end,
      have h : eq_mod_one (vector.nth t'_core i - ↑b_floor) a := eq_mod_one_int_sub t'_core_eq_a_mod_one,
      have two_rw : (2 : ℝ) = ↑(2 : ℤ) := by norm_num,
      rw two_rw,
      exact eq_mod_one_int_sub h,
    end,
  let t_offset := vector.of_fn (λ j, if(i = j) then t'_offset.nth i + b_floor_div_2 + 1 else t'_offset.nth j),
  let new_cp : point d := vector.of_fn (λ j, if(i = j) then 0 else cp.nth j),
  have new_cp_in_core_points : new_cp ∈ core_points d :=
    begin
      rw core_points,
      simp only [vector.nth_of_fn, set.mem_set_of_eq, ite_eq_left_iff],
      intro j,
      by_cases i_eq_j : i = j,
      { left,
        intro i_ne_j,
        exfalso,
        exact i_ne_j i_eq_j,
      },
      rename i_eq_j i_ne_j,
      rw core_points at cp_in_core_points,
      simp only [set.mem_set_of_eq] at cp_in_core_points,
      replace cp_in_core_points := cp_in_core_points j,
      cases cp_in_core_points with cp_eq_zero cp_eq_one,
      { left,
        intro i_ne_j,
        exact cp_eq_zero,
      },
      right,
      rw if_neg i_ne_j,
      exact cp_eq_one,
    end,
  use [new_cp, new_cp_in_core_points, t_core, t_core_in_T_shifted, t_offset],
  split,
  { dsimp only[new_cp, t_core],
    rw in_cube,
    simp only [vector.nth_of_fn, ge_iff_le, not_exists],
    intro j,
    by_cases i_eq_j : i = j,
    { rw [if_pos i_eq_j, if_pos i_eq_j, ← i_eq_j],
      split,
      { have cp_le_1 : cp.nth i ≤ 1 :=
          begin
            rw core_points at cp_in_core_points,
            simp only [set.mem_set_of_eq] at cp_in_core_points,
            cases cp_in_core_points i with cp_eq_zero cp_eq_one,
            { rw cp_eq_zero,
              linarith,
            },
            rw cp_eq_one,
          end,
        have t'_core_le_1 : t'_core.nth i ≤ 1 :=
          begin
            rw in_cube at cp_in_t'_core,
            replace cp_in_t'_core := cp_in_t'_core i,
            cases cp_in_t'_core,
            linarith,
          end,
        have b_sub_b_floor_le_1 : b - ↑b_floor ≤ 1 :=
          begin
            have h := int.sub_one_lt_floor b,
            dsimp only[b_floor],
            linarith,
          end,
        linarith,
      },
      linarith,
    },
    rename i_eq_j i_ne_j,
    rw [if_neg i_ne_j, if_neg i_ne_j],
    rw in_cube at cp_in_t'_core,
    replace cp_in_t'_core := cp_in_t'_core j,
    exact cp_in_t'_core,
  },
  apply vector.ext,
  intro j,
  dsimp[t_core, t_offset],
  rw [t_eq_t'_add_b, add_vectors, add_vectors, scaled_basis_vector, int_point_to_point, double_int_vector],
  simp only [vector.nth_of_fn, mul_ite],
  by_cases i_eq_j : i = j,
  { rw [if_pos i_eq_j, if_pos i_eq_j, if_pos i_eq_j, mul_add, mul_add, mul_one, double_b_floor_div_2],
    simp only [int.cast_add, int.cast_mul, int.cast_bit0, int.cast_one, sub_add_add_cancel],
    rw [add_assoc, add_comm b (2 * ↑(vector.nth t'_offset i)), ← add_assoc, add_left_inj, t'_eq_t'_core_add_double_t'_offset, 
      int_point_to_point, double_int_vector, add_vectors, i_eq_j],
    simp only [vector.nth_of_fn, int.cast_mul, int.cast_bit0, int.cast_one, add_right_inj, mul_eq_mul_left_iff, int.cast_inj,
      bit0_eq_zero, one_ne_zero, or_false],
  },
  rename i_eq_j i_ne_j,
  rw [t'_eq_t'_core_add_double_t'_offset, add_vectors, int_point_to_point, double_int_vector, if_neg i_ne_j, if_neg i_ne_j, if_neg i_ne_j, add_zero],
  simp only [vector.nth_of_fn],
end

lemma shifted_periodic_tiling_still_periodic_b_floor_odd_case_helper {d : ℕ} (a b : ℝ) {T : set (point d)} (T_is_tiling : is_tiling T) 
  (T_is_periodic : is_periodic T_is_tiling) (i : fin d) (T_shifted_is_tiling : is_tiling (shift_tiling T i a b)) 
  (T_has_periodic_core : has_periodic_core T_is_tiling) (t : vector ℝ d) (t' : point d) (t'_in_T : t' ∈ T)
  (t_eq_t'_add_b : t = add_vectors t' (scaled_basis_vector b i)) (t'_eq_a_mod_one : eq_mod_one (vector.nth t' i) a) (cp : point d)
  (cp_in_core_points : cp ∈ core_points d) (t'_core : point d) (t'_core_in_T : t'_core ∈ T) (t'_offset : int_point d) (cp_in_t'_core : in_cube t'_core cp)
  (t'_eq_t'_core_add_double_t'_offset : t' = add_vectors t'_core (int_point_to_point (double_int_vector t'_offset))) :
  let b_floor : ℤ := ⌊b⌋
  in ¬even b_floor →
     ¬vector.nth t'_core i + b - ↑b_floor + 1 ≤ 1 →
     (∃ (p : point d) (H : p ∈ core_points d) (t_core : point d)
        (H : t_core ∈ shift_tiling T i a b) (t_offset : int_point d),
        in_cube t_core p ∧
          t =
            add_vectors t_core
              (int_point_to_point (double_int_vector t_offset))) :=
begin
  intros b_floor b_floor_odd t'_core_add_b_sub_b_floor_add_one_gt_one,
  let b_floor_add_one_div_2 := (b_floor + 1) / 2,
  have b_floor_add_one_even : even (b_floor + 1) :=
    begin
      rw int.even_add,
      split,
      { intro b_floor_even,
        exfalso,
        exact b_floor_odd b_floor_even,
      },
      intro even_one,
      exfalso,
      exact int.not_even_one even_one,
    end,
  have double_b_floor_add_one_div_2 : 2 * b_floor_add_one_div_2 = b_floor + 1 :=
    begin
      dsimp[b_floor_add_one_div_2],
      exact int.two_mul_div_two_of_even b_floor_add_one_even,
    end,
  let t_core := vector.of_fn (λ j, if(i = j) then t'_core.nth j + b - b_floor - 1 else t'_core.nth j),
  have t_core_in_T_shifted : t_core ∈ shift_tiling T i a b :=
    begin
      rw shift_tiling,
      simp only [exists_prop, set.mem_union_eq],
      right,
      let t_core_preshift := vector.of_fn (λ j, if(i = j) then t'_core.nth j - b_floor - 1 else t'_core.nth j),
        have t_core_preshift_in_T : t_core_preshift ∈ T :=
        begin
          rw is_periodic at T_is_periodic,
          let int_cp : int_point d := vector.of_fn(λ j, if(cp.nth j = 0) then 0 else 1),
          replace T_is_periodic := T_is_periodic int_cp (int_scaled_basis_vector (-b_floor_add_one_div_2) i),
          have t'_core_rw : t'_core = (int_point_to_corner T_is_tiling int_cp).val :=
            begin
              rcases (int_point_to_corner T_is_tiling int_cp).property with
                ⟨int_cp_corner_in_T, int_cp_in_int_cp_corner, int_cp_corner_unique⟩,
              have int_point_to_point_int_cp_eq_cp : int_point_to_point int_cp = cp :=
                begin
                  apply vector.ext,
                  intro j,
                  rw int_point_to_point,
                  dsimp only[int_cp],
                  simp only [vector.nth_of_fn],
                  rw core_points at cp_in_core_points,
                  simp only [set.mem_set_of_eq] at cp_in_core_points,
                  cases cp_in_core_points j with cp_eq_zero cp_eq_one,
                  { rw [if_pos cp_eq_zero, cp_eq_zero],
                    refl,
                  },
                  have cp_ne_zero : vector.nth cp j ≠ 0 := by {rw cp_eq_one, exact one_ne_zero},
                  rw [if_neg cp_ne_zero, cp_eq_one],
                  have one_eq_one : 1 = 1 := by refl,
                  exact_mod_cast one_eq_one,
                end,
              conv at int_cp_corner_unique
              begin
                find (int_point_to_point int_cp) {rw int_point_to_point_int_cp_eq_cp},
                find (cp ∈ cube _) {rw cube, simp},
              end,
              exact int_cp_corner_unique t'_core t'_core_in_T cp_in_t'_core,
            end,
          have t_core_preshift_rw : add_vectors t'_core (int_point_to_point (double_int_vector (int_scaled_basis_vector (-b_floor_add_one_div_2) i))) = t_core_preshift :=
            begin
              apply vector.ext,
              intro j,
              rw [int_point_to_point, double_int_vector, add_vectors, int_scaled_basis_vector],
              dsimp only[t_core_preshift],
              simp only [vector.nth_of_fn, mul_ite, mul_neg, mul_zero],
              by_cases i_eq_j : i = j,
              { rw [if_pos i_eq_j, if_pos i_eq_j, double_b_floor_add_one_div_2],
                simp only [neg_add_rev, int.cast_add, int.cast_neg, int.cast_one],
                rw [add_comm (-1) (-(↑b_floor : ℝ)), ← add_assoc, sub_eq_add_neg, sub_eq_add_neg],
              },
              rename i_eq_j i_ne_j,
              rw [if_neg i_ne_j, if_neg i_ne_j, int.cast_zero, add_zero],
            end,
          rw [← t'_core_rw, t_core_preshift_rw, int_point_to_corner] at T_is_periodic,
          have h := 
            (point_to_corner T_is_tiling (int_point_to_point (add_int_vectors int_cp (double_int_vector (int_scaled_basis_vector (-b_floor_add_one_div_2) i))))).property,
          rcases h with ⟨goal, _, _⟩,
          rw ← T_is_periodic,
          exact goal,
        end,
      use [t_core_preshift, t_core_preshift_in_T],
      split,
      { apply vector.ext,
        intro j,
        dsimp[t_core_preshift, t_core],
        rw [add_vectors, scaled_basis_vector],
        simp only [vector.nth_of_fn],
        by_cases i_eq_j : i = j,
        { rw [if_pos i_eq_j, if_pos i_eq_j, if_pos i_eq_j],
          linarith,
        },
        rename i_eq_j i_ne_j,
        rw [if_neg i_ne_j, if_neg i_ne_j, if_neg i_ne_j, add_zero],
      },
      dsimp[t_core_preshift],
      simp only [if_true, eq_self_iff_true, vector.nth_of_fn],
      have t'_core_eq_a_mod_one : eq_mod_one (t'_core.nth i) a :=
        begin
          have h : t'.nth i = (add_vectors t'_core (int_point_to_point (double_int_vector t'_offset))).nth i := by rw t'_eq_t'_core_add_double_t'_offset,
          rw [add_vectors, int_point_to_point, double_int_vector] at h,
          simp only [int.cast_bit0, int.cast_mul, int.cast_one, vector.nth_of_fn] at h,
          replace h : vector.nth t' i - 2 * ↑(vector.nth t'_offset i) = vector.nth t'_core i := by linarith,
          have t'_offset_id : (2 : ℝ) * ↑(vector.nth t'_offset i) = ↑(2 * (vector.nth t'_offset i)) := by finish,
          rw [← h, t'_offset_id],
          exact eq_mod_one_int_sub t'_eq_a_mod_one,
        end,
      have t'_core_sub_b_floor_eq_a_mod_one : eq_mod_one (t'_core.nth i - ↑b_floor) a := eq_mod_one_int_sub t'_core_eq_a_mod_one,
      have one_eq_cast_one : (1 : ℝ) = ↑(1 : ℤ) := by finish,
      rw one_eq_cast_one,
      exact eq_mod_one_int_sub t'_core_sub_b_floor_eq_a_mod_one,
    end,
  let t_offset := vector.of_fn (λ j, if(i = j) then t'_offset.nth i + b_floor_add_one_div_2 else t'_offset.nth j),
  by_cases t'_core_add_b_sub_b_floor_sub_one_le_zero : vector.nth t'_core i + b - ↑b_floor - 1 ≤ 0,
  { let new_cp : point d := vector.of_fn (λ j, if(i = j) then 0 else cp.nth j),
    have new_cp_in_core_points : new_cp ∈ core_points d :=
      begin
        rw core_points,
        simp only [vector.nth_of_fn, set.mem_set_of_eq, ite_eq_left_iff],
        intro j,
        by_cases i_eq_j : i = j,
        { left,
          intro i_ne_j,
          exfalso,
          exact i_ne_j i_eq_j,
        },
        rename i_eq_j i_ne_j,
        rw core_points at cp_in_core_points,
        simp only [set.mem_set_of_eq] at cp_in_core_points,
        replace cp_in_core_points := cp_in_core_points j,
        cases cp_in_core_points with cp_eq_zero cp_eq_one,
        { left,
          intro _,
          exact cp_eq_zero,
        },
        right,
        rw if_neg i_ne_j,
        exact cp_eq_one,
      end,
    use [new_cp, new_cp_in_core_points, t_core, t_core_in_T_shifted, t_offset],
    split,
    { dsimp[new_cp, t_core],
      rw in_cube,
      simp only [not_exists, ge_iff_le, vector.nth_of_fn],
      intro j,
      by_cases i_eq_j : i = j,
      { rw [if_pos i_eq_j, if_pos i_eq_j],
        split, {rw ← i_eq_j, exact t'_core_add_b_sub_b_floor_sub_one_le_zero},
        have zero_le_b_sub_b_floor : 0 ≤ b - ↑b_floor :=
          begin
            dsimp only[b_floor],
            have h := int.floor_le b,
            clear_except h,
            linarith,
          end,
        have neg_one_lt_t'_core: -1 < t'_core.nth j :=
          begin
            rw in_cube at cp_in_t'_core,
            replace cp_in_t'_core := cp_in_t'_core j,
            rcases cp_in_t'_core with ⟨t'_core_le_cp, cp_lt_t'_core_add_one⟩,
            have cp_ge_zero : cp.nth j ≥ 0 :=
              begin
                rw core_points at cp_in_core_points,
                simp only [set.mem_set_of_eq] at cp_in_core_points,
                cases cp_in_core_points j with cp_eq_zero cp_eq_one,
                { rw cp_eq_zero,
                  exact rfl.ge,
                },
                rw cp_eq_one,
                linarith,
              end,
            linarith,
          end,
        simp only [add_le_iff_nonpos_left, sub_nonpos, not_le] at t'_core_add_b_sub_b_floor_add_one_gt_one,
        norm_num,
        rw ← i_eq_j,
        exact t'_core_add_b_sub_b_floor_add_one_gt_one,
      },
      rename i_eq_j i_ne_j,
      rw [if_neg i_ne_j, if_neg i_ne_j],
      rw in_cube at cp_in_t'_core,
      replace cp_in_t'_core := cp_in_t'_core j,
      exact cp_in_t'_core,
    },
    apply vector.ext,
    intro j,
    dsimp[t_core, t_offset],
    rw [t_eq_t'_add_b, add_vectors, add_vectors, scaled_basis_vector, int_point_to_point, double_int_vector],
    simp only [vector.nth_of_fn, mul_ite],
    by_cases i_eq_j : i = j,
    { rw [if_pos i_eq_j, if_pos i_eq_j, if_pos i_eq_j, mul_add, double_b_floor_add_one_div_2],
      simp only [int.cast_add, int.cast_mul, int.cast_bit0, int.cast_one, int.cast_sub],
      rw [add_comm ((2 : ℝ) * ↑(vector.nth t'_offset i)) ((↑b_floor : ℝ) + 1), ← add_assoc],
      simp only [sub_add_add_cancel, sub_add_cancel],
      rw [add_assoc, add_comm b ((2 : ℝ) * ↑(vector.nth t'_offset i)), ← add_assoc, t'_eq_t'_core_add_double_t'_offset, add_vectors,
        int_point_to_point, double_int_vector, i_eq_j],
      simp only [vector.nth_of_fn, int.cast_mul, int.cast_bit0, int.cast_one, add_left_inj, add_right_inj, mul_eq_mul_left_iff,
        int.cast_inj, bit0_eq_zero, one_ne_zero, or_false],
    },
    rename i_eq_j i_ne_j,
    rw [t'_eq_t'_core_add_double_t'_offset, add_vectors, int_point_to_point, double_int_vector, if_neg i_ne_j, if_neg i_ne_j, if_neg i_ne_j, add_zero],
    simp only [vector.nth_of_fn],
  },
  rename t'_core_add_b_sub_b_floor_sub_one_le_zero t'_core_add_b_sub_b_floor_sub_one_gt_zero,
  let new_cp : point d := vector.of_fn (λ j, if(i = j) then 1 else cp.nth j),
  have new_cp_in_core_points : new_cp ∈ core_points d :=
    begin
      rw core_points,
      simp only [vector.nth_of_fn, set.mem_set_of_eq, ite_eq_left_iff],
      intro j,
      by_cases i_eq_j : i = j,
      { right,
        intro i_ne_j,
        exfalso,
        exact i_ne_j i_eq_j,
      },
      rename i_eq_j i_ne_j,
      rw core_points at cp_in_core_points,
      simp only [set.mem_set_of_eq] at cp_in_core_points,
      replace cp_in_core_points := cp_in_core_points j,
      cases cp_in_core_points with cp_eq_zero cp_eq_one,
      { left,
        rw if_neg i_ne_j,
        exact cp_eq_zero,
      },
      right,
      intro _,
      exact cp_eq_one,
    end,
  use [new_cp, new_cp_in_core_points, t_core, t_core_in_T_shifted, t_offset],
  split,
  { dsimp[new_cp, t_core],
    rw in_cube,
    simp only [not_exists, ge_iff_le, vector.nth_of_fn],
    intro j,
    by_cases i_eq_j : i = j,
    { rw [if_pos i_eq_j, if_pos i_eq_j],
      split,
      { have b_sub_b_floor_le_1 : b - ↑b_floor ≤ 1 :=
          begin
            simp only [int.self_sub_floor],
            have h := int.fract_lt_one b,
            linarith,
          end,
        have cp_le_1 : vector.nth cp j ≤ 1 :=
          begin
            rw core_points at cp_in_core_points,
            simp only [set.mem_set_of_eq] at cp_in_core_points,
            cases cp_in_core_points j with cp_eq_zero cp_eq_one,
            { rw cp_eq_zero,
              exact zero_le_one,
            },
            rw cp_eq_one,
          end,
        have t'_core_le_1 : t'_core.nth j ≤ 1 :=
          begin
            rw in_cube at cp_in_t'_core,
            replace cp_in_t'_core := cp_in_t'_core j,
            cases cp_in_t'_core with t'_core_le_cp _,
            linarith,
          end,
        linarith,
      },
      simp only [add_le_iff_nonpos_left, sub_nonpos, not_le] at t'_core_add_b_sub_b_floor_add_one_gt_one,
      rw ← i_eq_j,
      linarith,
    },
    rename i_eq_j i_ne_j,
    rw [if_neg i_ne_j, if_neg i_ne_j],
    rw in_cube at cp_in_t'_core,
    replace cp_in_t'_core := cp_in_t'_core j,
    exact cp_in_t'_core,
  },
  apply vector.ext,
  intro j,
  dsimp[t_core, t_offset],
  rw [t_eq_t'_add_b, add_vectors, add_vectors, scaled_basis_vector, int_point_to_point, double_int_vector],
  simp only [vector.nth_of_fn, mul_ite],
  by_cases i_eq_j : i = j,
  { rw [if_pos i_eq_j, if_pos i_eq_j, if_pos i_eq_j, mul_add, double_b_floor_add_one_div_2],
    simp only [int.cast_add, int.cast_mul, int.cast_bit0, int.cast_one, int.cast_sub],
    rw [add_comm ((2 : ℝ) * ↑(vector.nth t'_offset i)) ((↑b_floor : ℝ) + 1), ← add_assoc],
    simp only [sub_add_add_cancel, sub_add_cancel],
    rw [add_assoc, add_comm b ((2 : ℝ) * ↑(vector.nth t'_offset i)), ← add_assoc, t'_eq_t'_core_add_double_t'_offset, add_vectors,
      int_point_to_point, double_int_vector, i_eq_j],
    simp only [vector.nth_of_fn, int.cast_mul, int.cast_bit0, int.cast_one, add_left_inj, add_right_inj, mul_eq_mul_left_iff,
      int.cast_inj, bit0_eq_zero, one_ne_zero, or_false],
  },
  rename i_eq_j i_ne_j,
  rw [t'_eq_t'_core_add_double_t'_offset, add_vectors, int_point_to_point, double_int_vector, if_neg i_ne_j, if_neg i_ne_j, if_neg i_ne_j, add_zero],
  simp only [vector.nth_of_fn],
end

lemma shifted_periodic_tiling_still_periodic_b_floor_odd_case {d : ℕ} (a b : ℝ) {T : set (point d)} (T_is_tiling : is_tiling T) 
  (T_is_periodic : is_periodic T_is_tiling) (i : fin d) (T_shifted_is_tiling : is_tiling (shift_tiling T i a b))
  (T_has_periodic_core : has_periodic_core T_is_tiling) (t : vector ℝ d) (t' : point d) (t'_in_T : t' ∈ T) 
  (t_eq_t'_add_b : t = add_vectors t' (scaled_basis_vector b i)) (t'_eq_a_mod_one : eq_mod_one (vector.nth t' i) a)
  (cp : point d) (cp_in_core_points : cp ∈ core_points d) (t'_core : point d) (t'_core_in_T : t'_core ∈ T) (t'_offset : int_point d)
  (cp_in_t'_core : in_cube t'_core cp) (t'_eq_t'_core_add_double_t'_offset : t' = add_vectors t'_core (int_point_to_point (double_int_vector t'_offset))) :
  let b_floor : ℤ := ⌊b⌋
  in ¬even b_floor →
     (∃ (p : point d) (H : p ∈ core_points d) (t_core : point d)
        (H : t_core ∈ shift_tiling T i a b) (t_offset : int_point d),
        in_cube t_core p ∧
          t =
            add_vectors t_core
              (int_point_to_point (double_int_vector t_offset))) :=
begin
  intros b_floor b_floor_odd,
  by_cases t'_core_add_b_sub_b_floor_add_one_le_one : t'_core.nth i + b - b_floor + 1 ≤ 1,
  { let b_floor_sub_one_div_2 := (b_floor - 1) / 2,
    have b_floor_sub_one_even : even (b_floor - 1) :=
      begin
        rw int.even_sub,
        split,
        { intro b_floor_even,
          exfalso,
          exact b_floor_odd b_floor_even,
        },
        intro even_one,
        exfalso,
        exact int.not_even_one even_one,
      end,
    have double_b_floor_sub_one_div_2 : 2 * b_floor_sub_one_div_2 = b_floor - 1 :=
      begin
        dsimp[b_floor_sub_one_div_2],
        exact int.two_mul_div_two_of_even b_floor_sub_one_even,
      end,
    let t_core := vector.of_fn (λ j, if(i = j) then t'_core.nth j + b - b_floor + 1 else t'_core.nth j),
    have t_core_in_T_shifted : t_core ∈ shift_tiling T i a b :=
      begin
        rw shift_tiling,
        simp only [exists_prop, set.mem_union_eq],
        right,
        let t_core_preshift := vector.of_fn (λ j, if(i = j) then t'_core.nth j - b_floor + 1 else t'_core.nth j),
         have t_core_preshift_in_T : t_core_preshift ∈ T :=
          begin
            rw is_periodic at T_is_periodic,
            let int_cp : int_point d := vector.of_fn(λ j, if(cp.nth j = 0) then 0 else 1),
            replace T_is_periodic := T_is_periodic int_cp (int_scaled_basis_vector (-b_floor_sub_one_div_2) i),
            have t'_core_rw : t'_core = (int_point_to_corner T_is_tiling int_cp).val :=
              begin
                rcases (int_point_to_corner T_is_tiling int_cp).property with
                  ⟨int_cp_corner_in_T, int_cp_in_int_cp_corner, int_cp_corner_unique⟩,
                have int_point_to_point_int_cp_eq_cp : int_point_to_point int_cp = cp :=
                  begin
                    apply vector.ext,
                    intro j,
                    rw int_point_to_point,
                    dsimp only[int_cp],
                    simp only [vector.nth_of_fn],
                    rw core_points at cp_in_core_points,
                    simp only [set.mem_set_of_eq] at cp_in_core_points,
                    cases cp_in_core_points j with cp_eq_zero cp_eq_one,
                    { rw [if_pos cp_eq_zero, cp_eq_zero],
                      refl,
                    },
                    have cp_ne_zero : vector.nth cp j ≠ 0 := by {rw cp_eq_one, exact one_ne_zero},
                    rw [if_neg cp_ne_zero, cp_eq_one],
                    have one_eq_one : 1 = 1 := by refl,
                    exact_mod_cast one_eq_one,
                  end,
                conv at int_cp_corner_unique
                begin
                  find (int_point_to_point int_cp) {rw int_point_to_point_int_cp_eq_cp},
                  find (cp ∈ cube _) {rw cube, simp},
                end,
                exact int_cp_corner_unique t'_core t'_core_in_T cp_in_t'_core,
              end,
            have t_core_preshift_rw : add_vectors t'_core (int_point_to_point (double_int_vector (int_scaled_basis_vector (-b_floor_sub_one_div_2) i))) = t_core_preshift :=
              begin
                apply vector.ext,
                intro j,
                rw [int_point_to_point, double_int_vector, add_vectors, int_scaled_basis_vector],
                dsimp only[t_core_preshift],
                simp only [vector.nth_of_fn, mul_ite, mul_neg, mul_zero],
                by_cases i_eq_j : i = j,
                { rw [if_pos i_eq_j, if_pos i_eq_j, double_b_floor_sub_one_div_2],
                  simp only [neg_sub, int.cast_sub, int.cast_one],
                  rw [sub_eq_add_neg, add_comm 1 (-(↑b_floor : ℝ)), ← add_assoc, ← sub_eq_add_neg],
                },
                rename i_eq_j i_ne_j,
                rw [if_neg i_ne_j, if_neg i_ne_j, int.cast_zero, add_zero],
              end,
            rw [← t'_core_rw, t_core_preshift_rw, int_point_to_corner] at T_is_periodic,
            have h := 
              (point_to_corner T_is_tiling (int_point_to_point (add_int_vectors int_cp (double_int_vector (int_scaled_basis_vector (-b_floor_sub_one_div_2) i))))).property,
            rcases h with ⟨goal, _, _⟩,
            rw ← T_is_periodic,
            exact goal,
          end,
        use [t_core_preshift, t_core_preshift_in_T],
        split,
        { apply vector.ext,
          intro j,
          dsimp[t_core_preshift, t_core],
          rw [add_vectors, scaled_basis_vector],
          simp only [vector.nth_of_fn],
          by_cases i_eq_j : i = j,
          { rw [if_pos i_eq_j, if_pos i_eq_j, if_pos i_eq_j],
            linarith,
          },
          rename i_eq_j i_ne_j,
          rw [if_neg i_ne_j, if_neg i_ne_j, if_neg i_ne_j, add_zero],
        },
        dsimp[t_core_preshift],
        simp only [if_true, eq_self_iff_true, vector.nth_of_fn],
        have t'_core_eq_a_mod_one : eq_mod_one (t'_core.nth i) a :=
          begin
            have h : t'.nth i = (add_vectors t'_core (int_point_to_point (double_int_vector t'_offset))).nth i := by rw t'_eq_t'_core_add_double_t'_offset,
            rw [add_vectors, int_point_to_point, double_int_vector] at h,
            simp only [int.cast_bit0, int.cast_mul, int.cast_one, vector.nth_of_fn] at h,
            replace h : vector.nth t' i - 2 * ↑(vector.nth t'_offset i) = vector.nth t'_core i := by linarith,
            have t'_offset_id : (2 : ℝ) * ↑(vector.nth t'_offset i) = ↑(2 * (vector.nth t'_offset i)) := by finish,
            rw [← h, t'_offset_id],
            exact eq_mod_one_int_sub t'_eq_a_mod_one,
          end,
        have t'_core_sub_b_floor_eq_a_mod_one : eq_mod_one (t'_core.nth i - ↑b_floor) a := eq_mod_one_int_sub t'_core_eq_a_mod_one,
        have one_eq_cast_one : (1 : ℝ) = ↑(1 : ℤ) := by finish,
        rw one_eq_cast_one,
        exact eq_mod_one_int_add t'_core_sub_b_floor_eq_a_mod_one,
      end,
    let t_offset := vector.of_fn (λ j, if(i = j) then t'_offset.nth i + b_floor_sub_one_div_2 else t'_offset.nth j),
    let new_cp : point d := vector.of_fn (λ j, if(i = j) then 1 else cp.nth j),
    have new_cp_in_core_points : new_cp ∈ core_points d :=
      begin
        rw core_points,
        simp only [vector.nth_of_fn, set.mem_set_of_eq, ite_eq_left_iff],
        intro j,
        by_cases i_eq_j : i = j,
        { right,
          intro i_ne_j,
          exfalso,
          exact i_ne_j i_eq_j,
        },
        rename i_eq_j i_ne_j,
        rw core_points at cp_in_core_points,
        simp only [set.mem_set_of_eq] at cp_in_core_points,
        replace cp_in_core_points := cp_in_core_points j,
        cases cp_in_core_points with cp_eq_zero cp_eq_one,
        { left,
          rw if_neg i_ne_j,
          exact cp_eq_zero,
        },
        right,
        intro i_ne_j,
        exact cp_eq_one,
      end,
    use [new_cp, new_cp_in_core_points, t_core, t_core_in_T_shifted, t_offset],
    split,
    { dsimp[new_cp, t_core],
      rw in_cube,
      simp only [not_exists, ge_iff_le, vector.nth_of_fn],
      intro j,
      by_cases i_eq_j : i = j,
      { rw [if_pos i_eq_j, if_pos i_eq_j],
        split, {rw ← i_eq_j, exact t'_core_add_b_sub_b_floor_add_one_le_one},
        have zero_le_b_sub_b_floor : 0 ≤ b - ↑b_floor :=
          begin
            dsimp only[b_floor],
            have h := int.floor_le b,
            clear_except h,
            linarith,
          end,
        have neg_one_lt_t'_core: -1 < t'_core.nth j :=
          begin
            rw in_cube at cp_in_t'_core,
            replace cp_in_t'_core := cp_in_t'_core j,
            rcases cp_in_t'_core with ⟨t'_core_le_cp, cp_lt_t'_core_add_one⟩,
            have cp_eq_zero : cp.nth j = 0 :=
              begin
                rw i_eq_j at t'_core_add_b_sub_b_floor_add_one_le_one,
                rw core_points at cp_in_core_points,
                simp only [set.mem_set_of_eq] at cp_in_core_points,
                cases cp_in_core_points j with cp_eq_zero cp_eq_one,
                exact cp_eq_zero,
                rw cp_eq_one at cp_lt_t'_core_add_one,
                linarith,
              end,
            rw cp_eq_zero at cp_lt_t'_core_add_one,
            linarith,
          end,
        clear_except zero_le_b_sub_b_floor neg_one_lt_t'_core,
        linarith,
      },
      rename i_eq_j i_ne_j,
      rw [if_neg i_ne_j, if_neg i_ne_j],
      rw in_cube at cp_in_t'_core,
      replace cp_in_t'_core := cp_in_t'_core j,
      exact cp_in_t'_core,
    },
    apply vector.ext,
    intro j,
    dsimp[t_core, t_offset],
    rw [t_eq_t'_add_b, add_vectors, add_vectors, scaled_basis_vector, int_point_to_point, double_int_vector],
    simp only [vector.nth_of_fn, mul_ite],
    by_cases i_eq_j : i = j,
    { rw [if_pos i_eq_j, if_pos i_eq_j, if_pos i_eq_j, mul_add, double_b_floor_sub_one_div_2],
      simp only [int.cast_add, int.cast_mul, int.cast_bit0, int.cast_one, int.cast_sub],
      rw [add_comm ((2 : ℝ) * ↑(vector.nth t'_offset i)) ((↑b_floor : ℝ) - 1), ← add_assoc],
      simp only [add_add_sub_cancel, sub_add_cancel],
      rw [add_assoc, add_comm b ((2 : ℝ) * ↑(vector.nth t'_offset i)), ← add_assoc, t'_eq_t'_core_add_double_t'_offset, add_vectors,
        int_point_to_point, double_int_vector, i_eq_j],
      simp only [vector.nth_of_fn, int.cast_mul, int.cast_bit0, int.cast_one, add_left_inj, add_right_inj, mul_eq_mul_left_iff,
        int.cast_inj, bit0_eq_zero, one_ne_zero, or_false],
    },
    rename i_eq_j i_ne_j,
    rw [t'_eq_t'_core_add_double_t'_offset, add_vectors, int_point_to_point, double_int_vector, if_neg i_ne_j, if_neg i_ne_j, if_neg i_ne_j, add_zero],
    simp only [vector.nth_of_fn],
  },
  rename t'_core_add_b_sub_b_floor_add_one_le_one t'_core_add_b_sub_b_floor_add_one_gt_one,
  exact shifted_periodic_tiling_still_periodic_b_floor_odd_case_helper a b T_is_tiling T_is_periodic i T_shifted_is_tiling T_has_periodic_core t t'
    t'_in_T t_eq_t'_add_b t'_eq_a_mod_one cp cp_in_core_points t'_core t'_core_in_T t'_offset cp_in_t'_core t'_eq_t'_core_add_double_t'_offset
    b_floor_odd t'_core_add_b_sub_b_floor_add_one_gt_one,
end

lemma shifted_periodic_tiling_still_periodic
  {d : ℕ} {T : set (point d)} (T_is_tiling : is_tiling T) (T_is_periodic : is_periodic T_is_tiling) (i : fin d) (a : ℝ) (b : ℝ)
  (T_shifted_is_tiling : is_tiling (shift_tiling T i a b)) : is_periodic T_shifted_is_tiling :=
begin
  have T_has_periodic_core := has_periodic_core_of_is_periodic d T T_is_tiling T_is_periodic,
  apply is_periodic_of_has_periodic_core,
  rw has_periodic_core,
  intros t t_in_T_shifted,
  rw shift_tiling at t_in_T_shifted,
  simp only [exists_prop, set.mem_union_eq] at t_in_T_shifted,
  rcases t_in_T_shifted with ⟨t_in_T, t_ne_a_mod_one⟩ | ⟨t', t'_in_T, t_eq_t'_add_b, t'_eq_a_mod_one⟩,
  { rcases T_has_periodic_core t t_in_T with ⟨cp, cp_in_core_points, t_core, t_core_in_T, t_offset, cp_in_t_core, t_eq_t_core_add_double_t_offset⟩,
    have t_core_in_T_shifted : t_core ∈ shift_tiling T i a b :=
      begin
        rw shift_tiling,
        simp only [exists_prop, set.mem_union_eq, set.mem_set_of_eq],
        left,
        split, exact t_core_in_T,
        intro t_core_eq_a_mod_one,
        rw t_eq_t_core_add_double_t_offset at t_ne_a_mod_one,
        rw [int_point_to_point, double_int_vector, add_vectors] at t_ne_a_mod_one,
        simp only [int.cast_bit0, int.cast_mul, int.cast_one, vector.nth_of_fn] at t_ne_a_mod_one,
        rcases t_core_eq_a_mod_one with ⟨t_core_floor, a_floor, y, zero_le_y, y_lt_one, t_core_eq_t_core_floor_add_y, a_eq_a_floor_add_y⟩,
        rw [ne_mod_one, eq_mod_one] at t_ne_a_mod_one,
        simp only [not_exists, not_and] at t_ne_a_mod_one,
        have h : vector.nth t_core i + 2 * ↑(vector.nth t_offset i) = ↑(t_core_floor + 2 * vector.nth t_offset i) + y :=
          begin
            rw t_core_eq_t_core_floor_add_y,
            simp only [int.cast_add, int.cast_bit0, int.cast_mul, int.cast_one],
            rw [add_assoc, add_comm y (2 * ↑(vector.nth t_offset i)), ← add_assoc],
          end,
        exact t_ne_a_mod_one (t_core_floor + 2 * (t_offset.nth i)) a_floor y zero_le_y y_lt_one h a_eq_a_floor_add_y,
      end,
    use [cp, cp_in_core_points, t_core, t_core_in_T_shifted, t_offset], 
    exact ⟨cp_in_t_core, t_eq_t_core_add_double_t_offset⟩,
  },
  rcases T_has_periodic_core t' t'_in_T with ⟨cp, cp_in_core_points, t'_core, t'_core_in_T, t'_offset, cp_in_t'_core, t'_eq_t'_core_add_double_t'_offset⟩,
  let b_floor := int.floor(b),
  by_cases b_floor_even : even b_floor,
  exact shifted_periodic_tiling_still_periodic_b_floor_even_case a b T_is_tiling T_is_periodic i T_shifted_is_tiling T_has_periodic_core t t' t'_in_T 
    t_eq_t'_add_b t'_eq_a_mod_one cp cp_in_core_points t'_core t'_core_in_T t'_offset cp_in_t'_core t'_eq_t'_core_add_double_t'_offset b_floor_even,
  rename b_floor_even b_floor_odd,
  exact shifted_periodic_tiling_still_periodic_b_floor_odd_case a b T_is_tiling T_is_periodic i T_shifted_is_tiling T_has_periodic_core t t' t'_in_T 
    t_eq_t'_add_b t'_eq_a_mod_one cp cp_in_core_points t'_core t'_core_in_T t'_offset cp_in_t'_core t'_eq_t'_core_add_double_t'_offset b_floor_odd,
end