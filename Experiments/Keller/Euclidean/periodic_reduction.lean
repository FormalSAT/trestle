import periodic_tilings

def periodic_Keller_conjecture (d : ℕ) (d_gt_zero : d > 0) : Prop :=
  ∀ T : set (point d), ∀ H : is_tiling T, is_periodic H → ¬tiling_faceshare_free T

lemma T'_covers_core (d : ℕ) (T : set (point d)) (T_is_tiling : is_tiling T) (T_faceshare_free : tiling_faceshare_free T) :
  let core_points : set (point d) :=
        {x :
           point d | ∀ (i : fin d),
           vector.nth x i = 0 ∨ vector.nth x i = 1},
      T_core : set (point d) :=
        {t ∈ T | ∃ (p : point d) (H : p ∈ core_points), in_cube t p},
      T' : set (point d) :=
        {t' :
           point d | ∃ (t : point d) (H : t ∈ T_core) (x : int_point d),
           t' = add_vectors t (int_point_to_point (double_int_vector x))}
  in ∀ (x : point d),
       (∀ (i : fin d), vector.nth x i ≥ 0 ∧ vector.nth x i ≤ 1) →
       (∃ (t' : point d) (H : t' ∈ T'),
          in_cube t' x ∧
            ∀ (alt_t' : point d),
              alt_t' ∈ T' → in_cube alt_t' x → t' = alt_t') :=
begin
  intros core_points T_core T' x x_in_core_space,
  have x_corner := point_to_corner T_is_tiling x,
  rcases x_corner with ⟨x_corner, ⟨x_corner_in_T, x_in_x_corner, x_corner_unique⟩⟩,
  have x_corner_in_T_core : x_corner ∈ T_core :=
    begin
      change x_corner ∈ T ∧ ∃ p : point d, ∃ H : p ∈ core_points, in_cube x_corner p,
      split, exact x_corner_in_T,
      let x_core_point : point d := vector.of_fn (λ j : fin d, int.ceil(x_corner.nth j)),
      have x_core_point_in_core_points : x_core_point ∈ core_points :=
        begin
          change ∀ i : fin d, x_core_point.nth i = 0 ∨ x_core_point.nth i = 1,
          intro i,
          rw cube at x_in_x_corner,
          simp at x_in_x_corner,
          rw in_cube at x_in_x_corner,
          replace x_in_x_corner := x_in_x_corner i,
          replace x_in_core_space := x_in_core_space i,
          cases x_in_x_corner with x_corner_le x x_lt_x_corner_add_one,
          cases x_in_core_space with x_ge_zero x_le_1,
          dsimp[x_core_point],
          simp,
          have neg_one_lt_x_corner : -1 < x_corner.nth i := by linarith,
          have x_corner_le_1 : x_corner.nth i ≤ 1 := by linarith,
          have x_corner_le_ceil := int.le_ceil (x_corner.nth i),
          have ceil_lt_x_corner_add_one := int.ceil_lt_add_one (x_corner.nth i),
          have neg_one_lt_ceil_x_corner : (-1 : ℝ) < ↑(int.ceil(x_corner.nth i)) := by linarith,
          have ceil_x_corner_lt_two : ↑(int.ceil(x_corner.nth i)) < (2 : ℝ) := by linarith,
          have coe_neg_one_lt_ceil_x_corner : -1 < int.ceil(x_corner.nth i) := by assumption_mod_cast,
          have coe_ceil_x_corner_lt_two : int.ceil(x_corner.nth i) < 2 := by assumption_mod_cast,
          have zero_le_ceil_x_corner : 0 ≤ int.ceil(x_corner.nth i) := by omega,
          have ceil_x_corner_le_one : int.ceil(x_corner.nth i) ≤ 1 := by omega,
          by_cases ceil_x_corner_eq_zero : int.ceil(x_corner.nth i) = 0, {left, exact ceil_x_corner_eq_zero,},
          rename ceil_x_corner_eq_zero ceil_x_corner_ne_zero,
          right,
          have coe_goal : ⌈vector.nth x_corner i⌉ = 1 := by omega,
          assumption_mod_cast,
        end,
      use [x_core_point, x_core_point_in_core_points],
      rw in_cube,
      simp,
      intro coord,
      exact ⟨int.le_ceil (x_corner.nth coord), int.ceil_lt_add_one (x_corner.nth coord)⟩,
    end,
  have x_corner_in_T' : x_corner ∈ T' :=
    begin
      change ∃ t ∈ T_core, ∃ y : int_point d, x_corner = add_vectors t (int_point_to_point (double_int_vector y)),
      use [x_corner, x_corner_in_T_core, vector.of_fn (λ j : fin d, 0)],
      rw [double_int_vector, int_point_to_point, add_vectors],
      simp,
    end,
  use [x_corner, x_corner_in_T'],
  rw cube at x_in_x_corner,
  simp at x_in_x_corner,
  split, exact x_in_x_corner,
  intros alt_t' alt_t'_in_T' x_in_alt_t',
  have alt_t'_in_T : alt_t' ∈ T :=
    begin
      rcases alt_t'_in_T' with ⟨t, t_in_T_core, y,  alt_t'_def⟩,
      rw [double_int_vector, int_point_to_point, add_vectors] at alt_t'_def,
      simp at alt_t'_def,
      by_cases y_ne_zero_vector : ∃ i : fin d, y.nth i ≠ 0,
      { exfalso, --Derive contradiction with x_in_alt_t'
        cases y_ne_zero_vector with i y_ne_zero_at_i,
        rw in_cube at x_in_alt_t',
        replace x_in_alt_t' := x_in_alt_t' i,
        rw alt_t'_def at x_in_alt_t',
        simp at x_in_alt_t',
        rcases t_in_T_core with ⟨t_in_T, p, p_in_core_points, p_in_cube_t⟩,
        replace p_in_core_points := p_in_core_points i,
        rw in_cube at p_in_cube_t,
        replace p_in_cube_t := p_in_cube_t i,
        cases p_in_cube_t with t_le_p p_lt_t_add_one,
        cases x_in_alt_t' with t_add_2y_le_x x_lt_t_add_2y_add_one,
        replace x_in_core_space := x_in_core_space i,
        cases x_in_core_space with x_ge_zero x_le_1,
        have y_le_neg_one_or_y_ge_one : y.nth i ≤ -1 ∨ y.nth i ≥ 1 :=
          begin
            by_cases y_le_zero : y.nth i ≤ 0, {left, omega,},
            right, omega,
          end,
        have coe_y_le_neg_one_or_y_ge_one : ↑(y.nth i) ≤ (-1 : ℝ) ∨ ↑(y.nth i) ≥ (1 : ℝ) := by assumption_mod_cast,
        cases coe_y_le_neg_one_or_y_ge_one,
        { cases p_in_core_points, linarith,
          linarith,
        },
        cases p_in_core_points, linarith,
        linarith,
      },
      rename y_ne_zero_vector y_eq_zero_vector,
      simp at y_eq_zero_vector,
      have alt_t'_eq_t : ∀ i : fin d, alt_t'.nth i = t.nth i :=
        begin
          intro i,
          rw alt_t'_def,
          simp,
          exact y_eq_zero_vector i,
        end,
      replace alt_t'_eq_t := vector.ext alt_t'_eq_t,
      rw alt_t'_eq_t,
      dsimp[T_core] at t_in_T_core,
      simp at t_in_T_core,
      cases t_in_T_core with t_in_T _,
      exact t_in_T,
    end,
  replace x_corner_unique := x_corner_unique alt_t' alt_t'_in_T,
  rw cube at x_corner_unique,
  simp at x_corner_unique,
  symmetry,
  exact x_corner_unique x_in_alt_t',
end

lemma line2_uniquely_covered_cube_induction_step_pos_helper (d : ℕ) (d_gt_zero : d > 0) (T : set (point d)) (T_is_tiling : is_tiling T)
  (T_faceshare_free : tiling_faceshare_free T) (j : fin d) (y : int_point d) (x : point d)
  (x_in_y_add_ej : ∀ (i : fin d), vector.nth x i ≥ ↑((add_int_vectors y (int_unit_basis_vector j)).nth i) ∧
                                  vector.nth x i ≤ ↑((add_int_vectors y (int_unit_basis_vector j)).nth i) + 1)
  (corner0 corner0_core : point d) (corner0_offset : int_point d)
  (corner0_def : corner0 = add_vectors corner0_core (int_point_to_point (double_int_vector corner0_offset)))
  (corner1 corner1_core : point d) (corner1_offset : int_point d)
  (corner1_def : corner1 = add_vectors corner1_core (int_point_to_point (double_int_vector corner1_offset)))
  (corner0_add_one_eq_corner1_at_j : vector.nth corner0 j + 1 = vector.nth corner1 j) :
  let core_points : set (point d) :=
        {x :
           point d | ∀ (i : fin d),
           vector.nth x i = 0 ∨ vector.nth x i = 1},
      T_core : set (point d) :=
        {t ∈ T | ∃ (p : point d) (H : p ∈ core_points), in_cube t p},
      T' : set (point d) :=
        {t' :
           point d | ∃ (t : point d) (H : t ∈ T_core) (x : int_point d),
           t' = add_vectors t (int_point_to_point (double_int_vector x))},
      x_j_set_to_y : point d :=
        vector.of_fn
          (λ (i : fin d), ite (i = j) ↑(vector.nth y j) (vector.nth x i)),
      x_j_set_to_y_add_one : point d :=
        vector.of_fn
          (λ (i : fin d),
             ite (i = j) (↑(vector.nth y j) + 1) (vector.nth x i)),
      x_j_set_to_y_add_two : point d :=
        vector.of_fn
          (λ (i : fin d),
             ite (i = j) (↑(vector.nth y j) + 2) (vector.nth x i)),
      line1 : set (point d) :=
        {p :
           point d | ∀ (i : fin d),
           (i = j →
              vector.nth p j ≥ ↑(vector.nth y j) ∧
                vector.nth p j ≤ ↑(vector.nth y j) + 1) ∧
             (i ≠ j → vector.nth p i = vector.nth x i)},
      line2 : set (point d) :=
        {p :
           point d | ∀ (i : fin d),
           (i = j →
              vector.nth p j ≥ ↑(vector.nth y j) + 1 ∧
                vector.nth p j ≤ ↑(vector.nth y j) + 2) ∧
             (i ≠ j → vector.nth p i = vector.nth x i)},
      corner2 : vector ℝ d :=
        add_vectors corner0_core
          (int_point_to_point
             (double_int_vector
                (add_int_vectors corner0_offset (int_unit_basis_vector j))))
  in (∀ (x : point d),
        (∀ (i : fin d),
           vector.nth x i ≥ ↑(vector.nth y i) ∧
             vector.nth x i ≤ ↑(vector.nth y i) + 1) →
        (∃ (t : point d) (H : t ∈ T'),
           in_cube t x ∧
             ∀ (alt_t : point d),
               alt_t ∈ T' → in_cube alt_t x → t = alt_t)) →
     (∀ (i : fin d),
        vector.nth x_j_set_to_y i ≥ ↑(vector.nth y i) ∧
          vector.nth x_j_set_to_y i ≤ ↑(vector.nth y i) + 1) →
     (∀ (i : fin d),
        vector.nth x_j_set_to_y_add_one i ≥ ↑(vector.nth y i) ∧
          vector.nth x_j_set_to_y_add_one i ≤ ↑(vector.nth y i) + 1) →
     corner0_core ∈ T_core →
     in_cube corner0 x_j_set_to_y →
     (∀ (alt_t : point d),
        alt_t ∈ T' → in_cube alt_t x_j_set_to_y → corner0 = alt_t) →
     corner1 ∈ T' →
     in_cube corner1 x_j_set_to_y_add_one →
     (∀ (alt_t : point d),
        alt_t ∈ T' →
        in_cube alt_t x_j_set_to_y_add_one → corner1 = alt_t) →
     corner1_core ∈ T_core →
     (∀ (p : point d),
        p ∈ line1 →
        ((in_cube corner0 p ∧
              ∀ (alt_corner : point d),
                alt_corner ∈ T' →
                in_cube alt_corner p → alt_corner = corner0) ∨
           in_cube corner1 p ∧
             ∀ (alt_corner : point d),
               alt_corner ∈ T' →
               in_cube alt_corner p → alt_corner = corner1)) →
     corner2 ∈ T' →
     ∀ (p : point d),
       p ∈ line2 →
       ((in_cube corner1 p ∧
             ∀ (alt_corner : point d),
               alt_corner ∈ T' →
               in_cube alt_corner p → corner1 = alt_corner) ∨
          in_cube corner2 p ∧
            ∀ (alt_corner : point d),
              alt_corner ∈ T' →
              in_cube alt_corner p → corner2 = alt_corner) :=
begin
  intros core_points T_core T' x_j_set_to_y x_j_set_to_y_add_one x_j_set_to_y_add_two line1 line2 corner2 T'_covers_y_uniquely
    x_j_set_to_y_in_y x_j_set_to_y_add_one_in_y corner0_core_in_T_core x_j_set_to_y_in_corner0 corner0_unique corner1_in_T'
    x_j_set_to_y_add_one_in_corner1 corner1_unique corner1_core_in_T_core line1_uniquely_covered corner2_in_T' p p_in_line2,
  let p_sub_ej := vector.of_fn (λ i : fin d, if(i = j) then p.nth i - 1 else p.nth i),
  have p_sub_ej_in_line1 : p_sub_ej ∈ line1 :=
    begin
      intro i,
      replace p_in_line2 := p_in_line2 i,
      cases p_in_line2,
      dsimp only[p_sub_ej],
      simp only [if_true, ge_iff_le, eq_self_iff_true, vector.nth_of_fn, ne.def],
      split,
      { intro i_eq_j,
        replace p_in_line2_left := p_in_line2_left i_eq_j,
        clear_except p_in_line2_left,
        exact ⟨by linarith, by linarith⟩,
      },
      intro i_ne_j,
      rw if_neg i_ne_j,
      exact p_in_line2_right i_ne_j,
    end,
  replace line1_uniquely_covered := line1_uniquely_covered p_sub_ej p_sub_ej_in_line1,
  rcases line1_uniquely_covered with
    ⟨p_sub_ej_in_corner0, p_sub_ej_only_in_corner0⟩ | ⟨p_sub_ej_in_corner1, p_sub_ej_only_in_corner1⟩,
  { left, --p should uniquely be in corner1 because p_sub_ej is uniquely in corner0
    have p_in_corner1 : in_cube corner1 p :=
      begin
        rw in_cube,
        intro i,
        rw in_cube at p_sub_ej_in_corner0,
        simp only [not_exists, ge_iff_le, vector.nth_of_fn] at p_sub_ej_in_corner0,
        replace p_sub_ej_in_corner0 := p_sub_ej_in_corner0 i,
        by_cases i_eq_j : i = j,
        { rw if_pos i_eq_j at p_sub_ej_in_corner0,
          rw ← i_eq_j at corner0_add_one_eq_corner1_at_j,
          rw ← corner0_add_one_eq_corner1_at_j,
          clear_except p_sub_ej_in_corner0,
          cases p_sub_ej_in_corner0,
          exact ⟨by linarith, by linarith⟩,
        },
        rename i_eq_j i_ne_j,
        rw in_cube at x_j_set_to_y_add_one_in_corner1,
        simp only [not_exists, ge_iff_le, vector.nth_of_fn] at x_j_set_to_y_add_one_in_corner1,
        replace x_j_set_to_y_add_one_in_corner1 := x_j_set_to_y_add_one_in_corner1 i,
        rw [if_neg i_ne_j] at x_j_set_to_y_add_one_in_corner1,
        have p_eq_x_at_i : p.nth i = x.nth i :=
          begin
            replace p_in_line2 := p_in_line2 i,
            cases p_in_line2,
            exact p_in_line2_right i_ne_j,
          end,
        rw p_eq_x_at_i,
        exact x_j_set_to_y_add_one_in_corner1,
      end,
    split, exact p_in_corner1,
    intros alt_corner alt_corner_in_T' p_in_alt_corner,
    have alt_corner_covers_x_j_set_to_y_add_one_or_two :
      in_cube alt_corner x_j_set_to_y_add_one ∨ in_cube alt_corner x_j_set_to_y_add_two :=
      begin
        rw in_cube at p_in_alt_corner,
        by_cases alt_corner_le_y_add_one : alt_corner.nth j ≤ y.nth j + 1,
        { left,
          rw in_cube,
          simp only [not_exists, ge_iff_le, vector.nth_of_fn],
          intro i,
          replace p_in_alt_corner := p_in_alt_corner i,
          by_cases i_eq_j : i = j,
          { rw [if_pos i_eq_j, i_eq_j],
            split, exact alt_corner_le_y_add_one,
            replace p_in_line2 := p_in_line2 j,
            cases p_in_line2,
            replace p_in_line2_left := p_in_line2_left (by refl),
            cases p_in_line2_left,
            simp only [ge_iff_le] at p_in_line2_left_left,
            rw i_eq_j at p_in_alt_corner,
            cases p_in_alt_corner,
            exact le_lt_trans p_in_line2_left_left p_in_alt_corner_right,
          },
          rename i_eq_j i_ne_j,
          rw if_neg i_ne_j,
          replace p_in_line2 := p_in_line2 i,
          cases p_in_line2,
          replace p_in_line2_right := p_in_line2_right i_ne_j,
          rw ← p_in_line2_right,
          exact p_in_alt_corner,
        },
        right,
        rw in_cube,
        simp only [not_exists, ge_iff_le, vector.nth_of_fn],
        intro i,
        replace p_in_alt_corner := p_in_alt_corner i,
        by_cases i_eq_j : i = j,
        { rw [if_pos i_eq_j, i_eq_j],
          split,
          { replace p_in_line2 := p_in_line2 j,
            cases p_in_line2,
            replace p_in_line2_left := p_in_line2_left (by refl),
            cases p_in_line2_left,
            rw i_eq_j at p_in_alt_corner,
            cases p_in_alt_corner,
            exact le_trans p_in_alt_corner_left p_in_line2_left_right,
          },
          clear_except alt_corner_le_y_add_one,
          linarith,
        },
        rename i_eq_j i_ne_j,
        rw if_neg i_ne_j,
        replace p_in_line2 := p_in_line2 i,
        cases p_in_line2,
        replace p_in_line2_right := p_in_line2_right i_ne_j,
        rw ← p_in_line2_right,
        exact p_in_alt_corner,
      end,
    cases alt_corner_covers_x_j_set_to_y_add_one_or_two with x_j_set_to_y_add_one_in_alt_corner x_j_set_to_y_add_two_in_alt_corner,
    { exact corner1_unique alt_corner alt_corner_in_T' x_j_set_to_y_add_one_in_alt_corner,
    },
    exfalso,
    rcases alt_corner_in_T' with ⟨alt_corner_core, alt_corner_core_in_T_core, alt_corner_offset, alt_corner_def⟩,
    let alt_corner_sub_2ej :=
      add_vectors alt_corner_core
      (int_point_to_point (double_int_vector (add_int_vectors alt_corner_offset (int_neg_unit_basis_vector j)))),
    have alt_corner_sub_2ej_in_T' : alt_corner_sub_2ej ∈ T' :=
      by use [alt_corner_core, alt_corner_core_in_T_core, add_int_vectors alt_corner_offset (int_neg_unit_basis_vector j)],
    have x_j_set_to_y_in_alt_corner_sub_2ej : in_cube alt_corner_sub_2ej x_j_set_to_y :=
      begin
        rw in_cube,
        simp only [not_exists, ge_iff_le, vector.nth_of_fn],
        intro i,
        dsimp only[alt_corner_sub_2ej],
        rw [int_neg_unit_basis_vector, add_int_vectors, double_int_vector, int_point_to_point, add_vectors],
        simp only [int.cast_add, int.cast_bit0, int.cast_mul, int.cast_one, vector.nth_of_fn],
        have alt_corner_def_at_i :
          alt_corner.nth i = (add_vectors alt_corner_core (int_point_to_point (double_int_vector alt_corner_offset))).nth i :=
          by rw alt_corner_def,
        rw [double_int_vector, int_point_to_point, add_vectors] at alt_corner_def_at_i,
        simp only [int.cast_bit0, int.cast_mul, int.cast_one, vector.nth_of_fn] at alt_corner_def_at_i,
        rw [mul_add, ← add_assoc, ← alt_corner_def_at_i],
        by_cases i_eq_j : i = j,
        { have j_eq_i : j = i := by {symmetry, exact i_eq_j},
          rw [if_pos i_eq_j, if_pos j_eq_i],
          simp only [int.cast_neg, int.cast_one, mul_neg, mul_one, add_neg_le_iff_le_add'],
          rw in_cube at x_j_set_to_y_add_two_in_alt_corner,
          simp only [not_exists, ge_iff_le, vector.nth_of_fn] at x_j_set_to_y_add_two_in_alt_corner,
          replace x_j_set_to_y_add_two_in_alt_corner := x_j_set_to_y_add_two_in_alt_corner i,
          rw [if_pos i_eq_j] at x_j_set_to_y_add_two_in_alt_corner,
          clear_except x_j_set_to_y_add_two_in_alt_corner,
          exact ⟨by linarith, by linarith⟩,
        },
        rename i_eq_j i_ne_j,
        have j_ne_i : j ≠ i := by {intro j_eq_i, symmetry' at j_eq_i, exact i_ne_j j_eq_i},
        rw [if_neg i_ne_j, if_neg j_ne_i],
        simp only [add_zero, int.cast_zero, mul_zero],
        rw in_cube at p_in_alt_corner,
        replace p_in_alt_corner := p_in_alt_corner i,
        replace p_in_line2 := p_in_line2 i,
        cases p_in_line2,
        replace p_in_line2_right := p_in_line2_right i_ne_j,
        rw ← p_in_line2_right,
        exact p_in_alt_corner,
      end,
    have corner0_eq_alt_corner_sub_2ej := corner0_unique alt_corner_sub_2ej alt_corner_sub_2ej_in_T' x_j_set_to_y_in_alt_corner_sub_2ej,
    rw corner0_eq_alt_corner_sub_2ej at corner0_add_one_eq_corner1_at_j,
    dsimp only[alt_corner_sub_2ej] at corner0_add_one_eq_corner1_at_j,
    rw [int_neg_unit_basis_vector, add_int_vectors, double_int_vector, int_point_to_point, add_vectors]
      at corner0_add_one_eq_corner1_at_j,
    simp only [int.cast_add, int.cast_bit0, if_true, int.cast_mul, eq_self_iff_true, int.cast_one, vector.nth_of_fn, int.cast_neg]
      at corner0_add_one_eq_corner1_at_j,
    rw [mul_add, ← add_assoc] at corner0_add_one_eq_corner1_at_j,
    have alt_corner_def_at_j :
      alt_corner.nth j = (add_vectors alt_corner_core (int_point_to_point (double_int_vector alt_corner_offset))).nth j :=
      by rw alt_corner_def,
    rw [double_int_vector, int_point_to_point, add_vectors] at alt_corner_def_at_j,
    simp only [int.cast_bit0, int.cast_mul, int.cast_one, vector.nth_of_fn] at alt_corner_def_at_j,
    rw ← alt_corner_def_at_j at corner0_add_one_eq_corner1_at_j,
    rw in_cube at p_in_corner1,
    replace p_in_corner1 := p_in_corner1 j,
    rw in_cube at p_in_alt_corner,
    replace p_in_alt_corner := p_in_alt_corner j,
    clear_except corner0_add_one_eq_corner1_at_j p_in_corner1 p_in_alt_corner,
    linarith,
  },
  right, --p should uniquely be in corner2 because p_sub_ej is uniquely in corner1
  have p_in_corner2 : in_cube corner2 p :=
    begin
      rw in_cube,
      intro i,
      rw in_cube at p_sub_ej_in_corner1,
      simp only [not_exists, ge_iff_le, vector.nth_of_fn] at p_sub_ej_in_corner1,
      replace p_sub_ej_in_corner1 := p_sub_ej_in_corner1 i,
      by_cases i_eq_j : i = j,
      { rw ← i_eq_j at corner0_add_one_eq_corner1_at_j,
        rw [if_pos i_eq_j, ← corner0_add_one_eq_corner1_at_j] at p_sub_ej_in_corner1,
        dsimp only[corner2],
        rw [int_unit_basis_vector, add_int_vectors, double_int_vector, int_point_to_point, add_vectors],
        simp only [int.cast_add, int.cast_bit0, int.cast_mul, int.cast_one, vector.nth_of_fn],
        have j_eq_i : j = i := by {symmetry, exact i_eq_j,},
        rw [if_pos j_eq_i, mul_add, ← add_assoc],
        simp only [mul_one, int.cast_one],
        have corner0_def_at_i :
          corner0.nth i = (add_vectors corner0_core (int_point_to_point (double_int_vector corner0_offset))).nth i :=
          by rw corner0_def,
        rw [double_int_vector, int_point_to_point, add_vectors] at corner0_def_at_i,
        simp only [int.cast_bit0, int.cast_mul, int.cast_one, vector.nth_of_fn] at corner0_def_at_i,
        rw ← corner0_def_at_i,
        clear_except p_sub_ej_in_corner1,
        exact ⟨by linarith, by linarith⟩,
      },
      rename i_eq_j i_ne_j,
      rw in_cube at x_j_set_to_y_in_corner0,
      simp only [not_exists, ge_iff_le, vector.nth_of_fn] at x_j_set_to_y_in_corner0,
      replace x_j_set_to_y_in_corner0 := x_j_set_to_y_in_corner0 i,
      have p_eq_x_at_i : p.nth i = x.nth i :=
        begin
          replace p_in_line2 := p_in_line2 i,
          cases p_in_line2,
          exact p_in_line2_right i_ne_j,
        end,
      have corner2_eq_corner0_at_i : corner2.nth i = corner0.nth i :=
        begin
          dsimp only[corner2],
          rw [corner0_def, int_unit_basis_vector, add_int_vectors, double_int_vector, double_int_vector, int_point_to_point,
            int_point_to_point, add_vectors, add_vectors],
          simp only [int.cast_add, int.cast_bit0, int.cast_mul, int.cast_one, vector.nth_of_fn],
          have j_ne_i : ¬(j = i) := by {intro j_eq_i, symmetry' at j_eq_i, exact i_ne_j j_eq_i},
          rw [if_neg j_ne_i, int.cast_zero, add_zero],
        end,
      rw [p_eq_x_at_i, corner2_eq_corner0_at_i],
      rw if_neg i_ne_j at x_j_set_to_y_in_corner0,
      exact x_j_set_to_y_in_corner0,
    end,
  split, exact p_in_corner2,
  intros alt_corner alt_corner_in_T' p_in_alt_corner,
  have alt_corner_covers_x_j_set_to_y_add_one_or_two :
    in_cube alt_corner x_j_set_to_y_add_one ∨ in_cube alt_corner x_j_set_to_y_add_two :=
    begin
      rw in_cube at p_in_alt_corner,
      by_cases alt_corner_le_y_add_one : alt_corner.nth j ≤ y.nth j + 1,
      { left,
        rw in_cube,
        simp only [not_exists, ge_iff_le, vector.nth_of_fn],
        intro i,
        replace p_in_alt_corner := p_in_alt_corner i,
        by_cases i_eq_j : i = j,
        { rw [if_pos i_eq_j, i_eq_j],
          split, exact alt_corner_le_y_add_one,
          replace p_in_line2 := p_in_line2 j,
          cases p_in_line2,
          replace p_in_line2_left := p_in_line2_left (by refl),
          cases p_in_line2_left,
          simp only [ge_iff_le] at p_in_line2_left_left,
          rw i_eq_j at p_in_alt_corner,
          cases p_in_alt_corner,
          exact le_lt_trans p_in_line2_left_left p_in_alt_corner_right,
        },
        rename i_eq_j i_ne_j,
        rw if_neg i_ne_j,
        replace p_in_line2 := p_in_line2 i,
        cases p_in_line2,
        replace p_in_line2_right := p_in_line2_right i_ne_j,
        rw ← p_in_line2_right,
        exact p_in_alt_corner,
      },
      right,
      rw in_cube,
      simp only [not_exists, ge_iff_le, vector.nth_of_fn],
      intro i,
      replace p_in_alt_corner := p_in_alt_corner i,
      by_cases i_eq_j : i = j,
      { rw [if_pos i_eq_j, i_eq_j],
        split,
        { replace p_in_line2 := p_in_line2 j,
          cases p_in_line2,
          replace p_in_line2_left := p_in_line2_left (by refl),
          cases p_in_line2_left,
          rw i_eq_j at p_in_alt_corner,
          cases p_in_alt_corner,
          exact le_trans p_in_alt_corner_left p_in_line2_left_right,
        },
        clear_except alt_corner_le_y_add_one,
        linarith,
      },
      rename i_eq_j i_ne_j,
      rw if_neg i_ne_j,
      replace p_in_line2 := p_in_line2 i,
      cases p_in_line2,
      replace p_in_line2_right := p_in_line2_right i_ne_j,
      rw ← p_in_line2_right,
      exact p_in_alt_corner,
    end,
  cases alt_corner_covers_x_j_set_to_y_add_one_or_two with x_j_set_to_y_add_one_in_alt_corner x_j_set_to_y_add_two_in_alt_corner,
  { exfalso,
    have corner1_eq_alt_corner := corner1_unique alt_corner alt_corner_in_T' x_j_set_to_y_add_one_in_alt_corner,
    rw in_cube at p_sub_ej_in_corner1 p_in_alt_corner,
    simp only [not_exists, ge_iff_le, vector.nth_of_fn] at p_sub_ej_in_corner1 p_in_alt_corner,
    replace p_sub_ej_in_corner1 := p_sub_ej_in_corner1 j,
    replace p_in_alt_corner := p_in_alt_corner j,
    rw [← corner1_eq_alt_corner] at p_in_alt_corner,
    rw [if_pos ((by refl) : j=j)] at p_sub_ej_in_corner1,
    clear_except p_in_alt_corner p_sub_ej_in_corner1,
    linarith,
  },
  rcases alt_corner_in_T' with ⟨alt_corner_core, alt_corner_core_in_T_core, alt_corner_offset, alt_corner_def⟩,
  let alt_corner_sub_2ej :=
    add_vectors alt_corner_core (int_point_to_point (double_int_vector (add_int_vectors alt_corner_offset (int_neg_unit_basis_vector j)))),
  have alt_corner_sub_2ej_in_T' : alt_corner_sub_2ej ∈ T' :=
    by use [alt_corner_core, alt_corner_core_in_T_core, add_int_vectors alt_corner_offset (int_neg_unit_basis_vector j)],
  have x_j_set_to_y_in_alt_corner_sub_2ej : in_cube alt_corner_sub_2ej x_j_set_to_y :=
    begin
      rw in_cube,
      simp only [not_exists, ge_iff_le, vector.nth_of_fn],
      intro i,
      dsimp only[alt_corner_sub_2ej],
      rw [int_neg_unit_basis_vector, add_int_vectors, double_int_vector, int_point_to_point, add_vectors],
      simp only [int.cast_add, int.cast_bit0, int.cast_mul, int.cast_one, vector.nth_of_fn],
      have alt_corner_def_at_i :
        alt_corner.nth i = (add_vectors alt_corner_core (int_point_to_point (double_int_vector alt_corner_offset))).nth i :=
        by rw alt_corner_def,
      rw [double_int_vector, int_point_to_point, add_vectors] at alt_corner_def_at_i,
      simp only [int.cast_bit0, int.cast_mul, int.cast_one, vector.nth_of_fn] at alt_corner_def_at_i,
      rw [mul_add, ← add_assoc, ← alt_corner_def_at_i],
      by_cases i_eq_j : i = j,
      { have j_eq_i : j = i := by {symmetry, exact i_eq_j},
        rw [if_pos i_eq_j, if_pos j_eq_i],
        simp only [int.cast_neg, int.cast_one, mul_neg, mul_one, add_neg_le_iff_le_add'],
        rw in_cube at x_j_set_to_y_add_two_in_alt_corner,
        simp only [not_exists, ge_iff_le, vector.nth_of_fn] at x_j_set_to_y_add_two_in_alt_corner,
        replace x_j_set_to_y_add_two_in_alt_corner := x_j_set_to_y_add_two_in_alt_corner i,
        rw [if_pos i_eq_j] at x_j_set_to_y_add_two_in_alt_corner,
        clear_except x_j_set_to_y_add_two_in_alt_corner,
        exact ⟨by linarith, by linarith⟩,
      },
      rename i_eq_j i_ne_j,
      have j_ne_i : j ≠ i := by {intro j_eq_i, symmetry' at j_eq_i, exact i_ne_j j_eq_i},
      rw [if_neg i_ne_j, if_neg j_ne_i],
      simp only [add_zero, int.cast_zero, mul_zero],
      rw in_cube at p_in_alt_corner,
      replace p_in_alt_corner := p_in_alt_corner i,
      replace p_in_line2 := p_in_line2 i,
      cases p_in_line2,
      replace p_in_line2_right := p_in_line2_right i_ne_j,
      rw ← p_in_line2_right,
      exact p_in_alt_corner,
    end,
  have corner0_eq_alt_corner_sub_2ej := corner0_unique alt_corner_sub_2ej alt_corner_sub_2ej_in_T' x_j_set_to_y_in_alt_corner_sub_2ej,
  apply vector.ext,
  intro i,
  dsimp only[corner2],
  rw [int_unit_basis_vector, add_int_vectors, double_int_vector, int_point_to_point, add_vectors],
  simp only [int.cast_add, int.cast_bit0, int.cast_mul, int.cast_one, vector.nth_of_fn],
  have corner0_def_at_i : corner0.nth i = (add_vectors corner0_core (int_point_to_point (double_int_vector corner0_offset))).nth i :=
    by rw corner0_def,
  rw [double_int_vector, int_point_to_point, add_vectors] at corner0_def_at_i,
  simp only [int.cast_add, int.cast_bit0, int.cast_mul, int.cast_one, vector.nth_of_fn] at corner0_def_at_i,
  rw [mul_add, ← add_assoc, ← corner0_def_at_i, corner0_eq_alt_corner_sub_2ej],
  dsimp only[alt_corner_sub_2ej],
  rw [alt_corner_def, int_neg_unit_basis_vector, add_int_vectors, double_int_vector, double_int_vector, int_point_to_point,
      int_point_to_point, add_vectors, add_vectors],
  simp only [int.cast_add, int.cast_bit0, int.cast_mul, int.cast_one, vector.nth_of_fn],
  by_cases j_eq_i : j = i,
  { rw [if_pos j_eq_i, if_pos j_eq_i, mul_add],
    simp only [int.cast_neg, int.cast_one, mul_neg, mul_one],
    clear_except,
    linarith,
  },
  rename j_eq_i j_ne_i,
  rw [if_neg j_ne_i, if_neg j_ne_i],
  simp only [add_zero, int.cast_zero, mul_zero],
end

lemma T'_is_tiling_cube_induction_step_pos (d : ℕ) (d_gt_zero : d > 0) (T : set (point d)) (T_is_tiling : is_tiling T)
  (T_faceshare_free : tiling_faceshare_free T) :
  let core_points : set (point d) :=
        {x :
           point d | ∀ (i : fin d),
           vector.nth x i = 0 ∨ vector.nth x i = 1},
      T_core : set (point d) :=
        {t ∈ T | ∃ (p : point d) (H : p ∈ core_points), in_cube t p},
      T' : set (point d) :=
        {t' :
           point d | ∃ (t : point d) (H : t ∈ T_core) (x : int_point d),
           t' = add_vectors t (int_point_to_point (double_int_vector x))}
  in ∀ (j : fin d) (y : int_point d),
       (∀ (x : point d),
          (∀ (i : fin d),
             vector.nth x i ≥ ↑(vector.nth y i) ∧
               vector.nth x i ≤ ↑(vector.nth y i) + 1) →
          (∃ (t : point d) (H : t ∈ T'),
             in_cube t x ∧
               ∀ (alt_t : point d),
                 alt_t ∈ T' → in_cube alt_t x → t = alt_t)) →
       ∀ (x : point d),
         (∀ (i : fin d),
            vector.nth x i ≥
                ↑((add_int_vectors y (int_unit_basis_vector j)).nth i) ∧
              vector.nth x i ≤
                ↑((add_int_vectors y (int_unit_basis_vector j)).nth i) +
                  1) →
         (∃ (t : point d) (H : t ∈ T'),
            in_cube t x ∧
              ∀ (alt_t : point d),
                alt_t ∈ T' → in_cube alt_t x → t = alt_t) :=
begin
  intros core_points T_core T' j y T'_covers_y_uniquely x x_in_y_add_ej, --ej is shorthand for int_unit_basis_vector j
  let x_j_set_to_y : point d := vector.of_fn (λ i : fin d, if(i = j) then y.nth j else x.nth i),
  let x_j_set_to_y_add_one : point d := vector.of_fn (λ i : fin d, if (i = j) then y.nth j + 1 else x.nth i),
  let x_j_set_to_y_add_two : point d := vector.of_fn (λ i : fin d, if (i = j) then y.nth j + 2 else x.nth i),
  let line1 : set (point d) :=
    {p : point d | ∀ i : fin d, (i = j → (p.nth j ≥ y.nth j ∧ p.nth j ≤ y.nth j + 1)) ∧ (i ≠ j → p.nth i = x.nth i)},
  let line2 : set (point d) :=
    {p : point d | ∀ i : fin d, (i = j → (p.nth j ≥ y.nth j + 1 ∧ p.nth j ≤ y.nth j + 2)) ∧ (i ≠ j → p.nth i = x.nth i)},
  have x_j_set_to_y_in_y : ∀ i : fin d, x_j_set_to_y.nth i ≥ ↑(y.nth i) ∧ x_j_set_to_y.nth i ≤ ↑(y.nth i) + 1 :=
    begin
      intro i,
      dsimp only[x_j_set_to_y],
      simp only [ge_iff_le, vector.nth_of_fn],
      replace x_in_y_add_ej := x_in_y_add_ej i,
      rw [int_unit_basis_vector, add_int_vectors] at x_in_y_add_ej,
      simp only [int.cast_add, ge_iff_le, vector.nth_of_fn] at x_in_y_add_ej,
      by_cases i_eq_j : i = j,
      { rw [if_pos i_eq_j, i_eq_j],
        split, exact_mod_cast le_refl (y.nth j),
        exact_mod_cast le_of_lt (lt_add_one (y.nth j)),
      },
      rename i_eq_j i_ne_j,
      rw if_neg i_ne_j,
      have j_ne_i : ¬(j = i) := by {intro j_eq_i, symmetry' at j_eq_i, exact i_ne_j j_eq_i},
      rw if_neg j_ne_i at x_in_y_add_ej,
      simp only [add_zero, int.cast_zero] at x_in_y_add_ej,
      exact x_in_y_add_ej,
    end,
  have x_j_set_to_y_uniquely_covered := T'_covers_y_uniquely x_j_set_to_y x_j_set_to_y_in_y,
  have x_j_set_to_y_add_one_in_y : ∀ i : fin d, x_j_set_to_y_add_one.nth i ≥ ↑(y.nth i) ∧ x_j_set_to_y_add_one.nth i ≤ ↑(y.nth i) + 1 :=
    begin
      intro i,
      dsimp only[x_j_set_to_y_add_one],
      simp only [ge_iff_le, vector.nth_of_fn],
      replace x_in_y_add_ej := x_in_y_add_ej i,
      rw [int_unit_basis_vector, add_int_vectors] at x_in_y_add_ej,
      simp only [int.cast_add, ge_iff_le, vector.nth_of_fn] at x_in_y_add_ej,
      by_cases i_eq_j : i = j,
      { rw [if_pos i_eq_j, i_eq_j],
        split, exact_mod_cast le_of_lt (lt_add_one (y.nth j)),
        exact_mod_cast le_refl (y.nth j + 1),
      },
      rename i_eq_j i_ne_j,
      rw if_neg i_ne_j,
      have j_ne_i : ¬(j = i) := by {intro j_eq_i, symmetry' at j_eq_i, exact i_ne_j j_eq_i},
      rw if_neg j_ne_i at x_in_y_add_ej,
      simp only [add_zero, int.cast_zero] at x_in_y_add_ej,
      exact x_in_y_add_ej,
    end,
  have x_j_set_to_y_add_one_uniquely_covered := T'_covers_y_uniquely x_j_set_to_y_add_one x_j_set_to_y_add_one_in_y,
  --corner0 and corner1 are the corners of x_j_set_to_y(_add_zero) and x_j_set_to_y_add_one respectively
  rcases x_j_set_to_y_uniquely_covered with ⟨corner0, corner0_in_T', x_j_set_to_y_in_corner0, corner0_unique⟩,
  have corner0_in_T'_copy := corner0_in_T',
  rcases corner0_in_T'_copy with ⟨corner0_core, corner0_core_in_T_core, corner0_offset, corner0_def⟩,
  rcases x_j_set_to_y_add_one_uniquely_covered with ⟨corner1, corner1_in_T', x_j_set_to_y_add_one_in_corner1, corner1_unique⟩,
  have corner1_in_T'_copy := corner1_in_T',
  rcases corner1_in_T'_copy with ⟨corner1_core, corner1_core_in_T_core, corner1_offset, corner1_def⟩,
  --Show relationship between corner0 and corner1's j values
  have corner0_add_one_eq_corner1_at_j : corner0.nth j + 1 = corner1.nth j :=
    begin
      rw in_cube at x_j_set_to_y_in_corner0 x_j_set_to_y_add_one_in_corner1,
      simp only [not_exists, ge_iff_le, vector.nth_of_fn] at x_j_set_to_y_in_corner0 x_j_set_to_y_add_one_in_corner1,
      have x_j_set_to_y_in_corner0_at_j := x_j_set_to_y_in_corner0 j,
      have x_j_set_to_y_add_one_in_corner1_at_j := x_j_set_to_y_add_one_in_corner1 j,
      rw [if_pos ((by refl) : j = j)] at x_j_set_to_y_in_corner0_at_j x_j_set_to_y_add_one_in_corner1_at_j,
      have h := real_eq_or_lt_or_gt (corner0.nth j + 1) (corner1.nth j),
      rcases h with corner0_add_one_eq_corner1 | corner0_add_one_lt_corner1 | corner0_add_one_gt_corner1, exact corner0_add_one_eq_corner1,
      { exfalso, --In this case, contradiction point is in neither corner0 nor corner1
        let contradiction_point := vector.of_fn (λ i : fin d, if(i = j) then corner0.nth j + 1 else x.nth i),
        have contradiction_point_in_y :
          ∀ i : fin d, contradiction_point.nth i ≥ ↑(vector.nth y i) ∧ contradiction_point.nth i ≤ ↑(vector.nth y i) + 1 :=
          begin
            intro i,
            dsimp only[contradiction_point],
            simp only [ge_iff_le, vector.nth_of_fn],
            replace x_in_y_add_ej := x_in_y_add_ej i,
            rw [int_unit_basis_vector, add_int_vectors] at x_in_y_add_ej,
            simp only [int.cast_add, ge_iff_le, vector.nth_of_fn] at x_in_y_add_ej,
            by_cases i_eq_j : i = j,
            { rw [if_pos i_eq_j, i_eq_j],
              have j_eq_i : j = i := by {symmetry, exact i_eq_j},
              rw [if_pos j_eq_i, i_eq_j, int.cast_one] at x_in_y_add_ej,
              clear_except x_in_y_add_ej x_j_set_to_y_in_corner0_at_j,
              exact ⟨by linarith, by linarith⟩,
            },
            rename i_eq_j i_ne_j,
            rw if_neg i_ne_j,
            have j_ne_i : ¬(j = i) := by {intro j_eq_i, symmetry' at j_eq_i, exact i_ne_j j_eq_i},
            rw [if_neg j_ne_i, int.cast_zero, add_zero] at x_in_y_add_ej,
            exact x_in_y_add_ej,
          end,
        have T'_covers_y_uniquely_copy := T'_covers_y_uniquely contradiction_point contradiction_point_in_y,
        rcases T'_covers_y_uniquely_copy with
          ⟨contradiction_corner, contradiction_corner_in_T', contradiction_point_in_contradiction_corner, contradiction_corner_unique⟩,
        have h := real_eq_or_lt_or_gt (contradiction_corner.nth j) (contradiction_point.nth j),
        rcases h with
          contradiction_corner_eq_contradiction_point_at_j | contradiction_corner_lt_contradiction_point_at_j |
          contradiction_corner_gt_contradiction_point_at_j,
        { have x_j_set_to_y_add_one_in_contradiction_corner : in_cube contradiction_corner x_j_set_to_y_add_one :=
            begin
              rw in_cube,
              simp only [not_exists, ge_iff_le, vector.nth_of_fn],
              intro i,
              by_cases i_eq_j : i = j,
              { rw [if_pos i_eq_j, i_eq_j, contradiction_corner_eq_contradiction_point_at_j],
                dsimp only[contradiction_point],
                simp only [if_true, eq_self_iff_true, vector.nth_of_fn, add_le_add_iff_right, add_lt_add_iff_right],
                clear_except x_j_set_to_y_in_corner0_at_j,
                exact ⟨by linarith, by linarith⟩,
              },
              rename i_eq_j i_ne_j,
              rw if_neg i_ne_j,
              rw in_cube at contradiction_point_in_contradiction_corner,
              simp only [not_exists, ge_iff_le, vector.nth_of_fn] at contradiction_point_in_contradiction_corner,
              replace contradiction_point_in_contradiction_corner := contradiction_point_in_contradiction_corner i,
              rw if_neg i_ne_j at contradiction_point_in_contradiction_corner,
              exact contradiction_point_in_contradiction_corner,
            end,
          have corner1_eq_contradiction_corner :=
            corner1_unique contradiction_corner contradiction_corner_in_T' x_j_set_to_y_add_one_in_contradiction_corner,
          rw [← corner1_eq_contradiction_corner, in_cube] at contradiction_point_in_contradiction_corner,
          simp only [not_exists, ge_iff_le, vector.nth_of_fn] at contradiction_point_in_contradiction_corner,
          replace contradiction_point_in_contradiction_corner := contradiction_point_in_contradiction_corner j,
          simp only [eq_self_iff_true, if_true, add_lt_add_iff_right] at contradiction_point_in_contradiction_corner,
          clear_except contradiction_point_in_contradiction_corner corner0_add_one_lt_corner1,
          linarith,
        },
        { by_cases contradiction_corner_lt_y_at_j : contradiction_corner.nth j < y.nth j,
          { have x_j_set_to_y_in_contradiction_corner : in_cube contradiction_corner x_j_set_to_y :=
              begin
                rw in_cube,
                simp only [not_exists, ge_iff_le, vector.nth_of_fn],
                intro i,
                by_cases i_eq_j : i = j,
                { rw [if_pos i_eq_j, i_eq_j],
                  rw in_cube at contradiction_point_in_contradiction_corner,
                  simp only [not_exists, ge_iff_le, vector.nth_of_fn] at contradiction_point_in_contradiction_corner,
                  replace contradiction_point_in_contradiction_corner := contradiction_point_in_contradiction_corner i,
                  rw [if_pos i_eq_j, i_eq_j] at contradiction_point_in_contradiction_corner,
                  clear_except x_j_set_to_y_in_corner0_at_j contradiction_point_in_contradiction_corner contradiction_corner_lt_y_at_j,
                  exact ⟨le_of_lt contradiction_corner_lt_y_at_j, by linarith⟩,
                },
                rename i_eq_j i_ne_j,
                rw [if_neg i_ne_j],
                rw in_cube at contradiction_point_in_contradiction_corner,
                simp only [not_exists, ge_iff_le, vector.nth_of_fn] at contradiction_point_in_contradiction_corner,
                replace contradiction_point_in_contradiction_corner := contradiction_point_in_contradiction_corner i,
                rw [if_neg i_ne_j] at contradiction_point_in_contradiction_corner,
                exact contradiction_point_in_contradiction_corner,
              end,
            have corner0_eq_contradiction_corner :=
              corner0_unique contradiction_corner contradiction_corner_in_T' x_j_set_to_y_in_contradiction_corner,
            rw [← corner0_eq_contradiction_corner, in_cube] at contradiction_point_in_contradiction_corner,
            simp only [not_exists, ge_iff_le, vector.nth_of_fn] at contradiction_point_in_contradiction_corner,
            replace contradiction_point_in_contradiction_corner := contradiction_point_in_contradiction_corner j,
            rw [if_pos ((by refl) : j = j)] at contradiction_point_in_contradiction_corner,
            cases contradiction_point_in_contradiction_corner,
            clear_except contradiction_point_in_contradiction_corner_right,
            linarith,
          },
          rename contradiction_corner_lt_y_at_j contradiction_corner_ge_y_at_j,
          let contradiction_corner_at_line1 := vector.of_fn (λ i : fin d, if (i = j) then contradiction_corner.nth j else x.nth i),
          have contradiction_corner_at_line1_in_y :
            ∀ i : fin d, contradiction_corner_at_line1.nth i ≥ ↑(y.nth i) ∧ contradiction_corner_at_line1.nth i ≤ ↑(y.nth i) + 1 :=
            begin
              intro i,
              dsimp only[contradiction_corner_at_line1],
              simp only [ge_iff_le, vector.nth_of_fn],
              by_cases i_eq_j : i = j,
              { rw [if_pos i_eq_j, i_eq_j],
                split,
                { simp only [not_lt] at contradiction_corner_ge_y_at_j,
                  exact contradiction_corner_ge_y_at_j,
                },
                dsimp only[contradiction_point] at contradiction_corner_lt_contradiction_point_at_j,
                simp only [if_true, eq_self_iff_true, vector.nth_of_fn] at contradiction_corner_lt_contradiction_point_at_j,
                clear_except contradiction_corner_lt_contradiction_point_at_j x_j_set_to_y_in_corner0_at_j,
                linarith,
              },
              rename i_eq_j i_ne_j,
              rw if_neg i_ne_j,
              replace x_in_y_add_ej := x_in_y_add_ej i,
              rw [int_unit_basis_vector, add_int_vectors] at x_in_y_add_ej,
              simp only [int.cast_add, ge_iff_le, vector.nth_of_fn] at x_in_y_add_ej,
              have j_ne_i : ¬(j = i) := by {intro j_eq_i, symmetry' at j_eq_i, exact i_ne_j j_eq_i},
              rw [if_neg j_ne_i, int.cast_zero, add_zero] at x_in_y_add_ej,
              exact x_in_y_add_ej,
            end,
          replace T'_covers_y_uniquely := T'_covers_y_uniquely contradiction_corner_at_line1 contradiction_corner_at_line1_in_y,
          rcases T'_covers_y_uniquely with
            ⟨contradiction_corner_at_line1_corner, contradiction_corner_at_line1_corner_in_T',
             contradiction_corner_at_line1_in_contradiction_corner_at_line1_corner, contradiction_corner_at_line1_corner_unique⟩,
          have contradiction_corner_at_line1_in_contradiction_corner : in_cube contradiction_corner contradiction_corner_at_line1 :=
            begin
              rw in_cube,
              simp only [not_exists, ge_iff_le, vector.nth_of_fn],
              intro i,
              by_cases i_eq_j : i = j,
              { rw [if_pos i_eq_j, i_eq_j],
                clear,
                exact ⟨by linarith, by linarith⟩,
              },
              rename i_eq_j i_ne_j,
              rw if_neg i_ne_j,
              rw in_cube at contradiction_point_in_contradiction_corner,
              simp only [not_exists, ge_iff_le, vector.nth_of_fn] at contradiction_point_in_contradiction_corner,
              replace contradiction_point_in_contradiction_corner := contradiction_point_in_contradiction_corner i,
              rw [if_neg i_ne_j] at contradiction_point_in_contradiction_corner,
              exact contradiction_point_in_contradiction_corner,
            end,
          have contradiction_corner_at_line1_corner_eq_contradiction_corner :=
            contradiction_corner_at_line1_corner_unique contradiction_corner contradiction_corner_in_T'
            contradiction_corner_at_line1_in_contradiction_corner,
          have contradiction_corner_at_line1_in_corner0 : in_cube corner0 contradiction_corner_at_line1 :=
            begin
              rw in_cube,
              simp only [not_exists, ge_iff_le, vector.nth_of_fn],
              intro i,
              by_cases i_eq_j : i = j,
              { rw [if_pos i_eq_j, i_eq_j],
                rw in_cube at contradiction_point_in_contradiction_corner,
                simp only [not_exists, ge_iff_le, vector.nth_of_fn] at contradiction_point_in_contradiction_corner,
                replace contradiction_point_in_contradiction_corner := contradiction_point_in_contradiction_corner i,
                rw [if_pos i_eq_j, i_eq_j] at contradiction_point_in_contradiction_corner,
                simp only [add_lt_add_iff_right] at contradiction_point_in_contradiction_corner,
                cases contradiction_point_in_contradiction_corner,
                dsimp only[contradiction_point] at contradiction_corner_lt_contradiction_point_at_j,
                simp only [if_true, eq_self_iff_true, vector.nth_of_fn] at contradiction_corner_lt_contradiction_point_at_j,
                exact ⟨le_of_lt contradiction_point_in_contradiction_corner_right, contradiction_corner_lt_contradiction_point_at_j⟩,
              },
              rename i_eq_j i_ne_j,
              rw if_neg i_ne_j,
              replace x_j_set_to_y_in_corner0 := x_j_set_to_y_in_corner0 i,
              rw [if_neg i_ne_j] at x_j_set_to_y_in_corner0,
              exact x_j_set_to_y_in_corner0,
            end,
          have contradiction_corner_at_line1_corner_eq_corner0 :=
            contradiction_corner_at_line1_corner_unique corner0 corner0_in_T' contradiction_corner_at_line1_in_corner0,
          have contradiction_corner_eq_corner0 : contradiction_corner = corner0 :=
            begin
              rw contradiction_corner_at_line1_corner_eq_contradiction_corner at contradiction_corner_at_line1_corner_eq_corner0,
              exact contradiction_corner_at_line1_corner_eq_corner0,
            end,
          rw [contradiction_corner_eq_corner0, in_cube] at contradiction_point_in_contradiction_corner,
          simp only [not_exists, ge_iff_le, vector.nth_of_fn] at contradiction_point_in_contradiction_corner,
          replace contradiction_point_in_contradiction_corner := contradiction_point_in_contradiction_corner j,
          rw [if_pos ((by refl) : j = j)] at contradiction_point_in_contradiction_corner,
          simp only [lt_self_iff_false, and_false] at contradiction_point_in_contradiction_corner,
          exact contradiction_point_in_contradiction_corner,
        },
        rw in_cube at contradiction_point_in_contradiction_corner,
        simp only [not_exists, ge_iff_le, vector.nth_of_fn] at contradiction_point_in_contradiction_corner,
        replace contradiction_point_in_contradiction_corner := contradiction_point_in_contradiction_corner j,
        simp only [eq_self_iff_true, if_true, add_lt_add_iff_right] at contradiction_point_in_contradiction_corner,
        dsimp only[contradiction_point] at contradiction_corner_gt_contradiction_point_at_j,
        simp only [gt_iff_lt, if_true, eq_self_iff_true, vector.nth_of_fn] at contradiction_corner_gt_contradiction_point_at_j,
        clear_except contradiction_point_in_contradiction_corner contradiction_corner_gt_contradiction_point_at_j,
        linarith,
      },
      exfalso, --In this case, contradiction point is in both corner0 and corner1
      let contradiction_point := vector.of_fn (λ i : fin d, if(i = j) then corner1.nth j else x.nth i),
      have contradiction_point_in_y :
        ∀ i : fin d, contradiction_point.nth i ≥ ↑(vector.nth y i) ∧ contradiction_point.nth i ≤ ↑(vector.nth y i) + 1 :=
        begin
          intro i,
          dsimp only[contradiction_point],
          simp only [ge_iff_le, vector.nth_of_fn],
          replace x_in_y_add_ej := x_in_y_add_ej i,
          rw [int_unit_basis_vector, add_int_vectors] at x_in_y_add_ej,
          simp only [int.cast_add, ge_iff_le, vector.nth_of_fn] at x_in_y_add_ej,
          by_cases i_eq_j : i = j,
          { rw [if_pos i_eq_j, i_eq_j],
            have j_eq_i : j = i := by {symmetry, exact i_eq_j},
            rw [if_pos j_eq_i, i_eq_j, int.cast_one] at x_in_y_add_ej,
            clear_except x_in_y_add_ej x_j_set_to_y_add_one_in_corner1_at_j,
            exact ⟨by linarith, by linarith⟩,
          },
          rename i_eq_j i_ne_j,
          rw if_neg i_ne_j,
          have j_ne_i : ¬(j = i) := by {intro j_eq_i, symmetry' at j_eq_i, exact i_ne_j j_eq_i},
          rw [if_neg j_ne_i, int.cast_zero, add_zero] at x_in_y_add_ej,
          exact x_in_y_add_ej,
        end,
      replace T'_covers_y_uniquely := T'_covers_y_uniquely contradiction_point contradiction_point_in_y,
      rcases T'_covers_y_uniquely with
        ⟨contradiction_corner, contradiction_corner_in_T', contradiction_point_in_contradiction_corner, contradiction_corner_unique⟩,
      have contradiction_point_in_corner0 : in_cube corner0 contradiction_point :=
        begin
          rw in_cube,
          simp only [not_exists, ge_iff_le, vector.nth_of_fn],
          intro i,
          by_cases i_eq_j : i = j,
          { rw [if_pos i_eq_j, i_eq_j],
            split,
            { clear_except x_j_set_to_y_add_one_in_corner1_at_j x_j_set_to_y_in_corner0_at_j,
              linarith,
            },
            clear_except corner0_add_one_gt_corner1,
            linarith,
          },
          rename i_eq_j i_ne_j,
          rw if_neg i_ne_j,
          replace x_j_set_to_y_in_corner0 := x_j_set_to_y_in_corner0 i,
          replace x_j_set_to_y_add_one_in_corner1 := x_j_set_to_y_add_one_in_corner1 i,
          rw [if_neg i_ne_j] at x_j_set_to_y_in_corner0 x_j_set_to_y_add_one_in_corner1,
          clear_except x_j_set_to_y_in_corner0 x_j_set_to_y_add_one_in_corner1,
          exact ⟨by linarith, by linarith⟩,
        end,
      have contradiction_point_in_corner1 : in_cube corner1 contradiction_point :=
        begin
          rw in_cube,
          simp only [not_exists, ge_iff_le, vector.nth_of_fn],
          intro i,
          by_cases i_eq_j : i = j,
          { rw [if_pos i_eq_j, i_eq_j],
            split,
            { clear_except x_j_set_to_y_add_one_in_corner1_at_j x_j_set_to_y_in_corner0_at_j,
              linarith,
            },
            clear_except corner0_add_one_gt_corner1,
            linarith,
          },
          rename i_eq_j i_ne_j,
          rw if_neg i_ne_j,
          replace x_j_set_to_y_in_corner0 := x_j_set_to_y_in_corner0 i,
          replace x_j_set_to_y_add_one_in_corner1 := x_j_set_to_y_add_one_in_corner1 i,
          rw [if_neg i_ne_j] at x_j_set_to_y_in_corner0 x_j_set_to_y_add_one_in_corner1,
          clear_except x_j_set_to_y_in_corner0 x_j_set_to_y_add_one_in_corner1,
          exact ⟨by linarith, by linarith⟩,
        end,
      have contradiction_corner_eq_corner0 := contradiction_corner_unique corner0 corner0_in_T' contradiction_point_in_corner0,
      have contradiciton_corner_eq_corner1 := contradiction_corner_unique corner1 corner1_in_T' contradiction_point_in_corner1,
      have corner0_eq_corner1 : corner0 = corner1 :=
        by {rw contradiction_corner_eq_corner0 at contradiciton_corner_eq_corner1, exact contradiciton_corner_eq_corner1},
      rw corner0_eq_corner1 at x_j_set_to_y_in_corner0_at_j,
      clear_except x_j_set_to_y_in_corner0_at_j x_j_set_to_y_add_one_in_corner1_at_j,
      linarith,
    end,
  --Next, need to show that line_1 is uniquely covered by corner0 and corner1
  have line1_uniquely_covered : ∀ p ∈ line1,
    (in_cube corner0 p ∧ (∀ alt_corner ∈ T', in_cube alt_corner p → alt_corner = corner0)) ∨
    (in_cube corner1 p ∧ (∀ alt_corner ∈ T', in_cube alt_corner p → alt_corner = corner1)) :=
    begin
      intros p p_in_line1,
      have p_in_y : ∀ i : fin d, vector.nth p i ≥ ↑(vector.nth y i) ∧ vector.nth p i ≤ ↑(vector.nth y i) + 1 :=
        begin
          intro i,
          replace p_in_line1 := p_in_line1 i,
          cases p_in_line1,
          by_cases i_eq_j : i = j, {rw i_eq_j, exact p_in_line1_left i_eq_j,},
          rename i_eq_j i_ne_j,
          have p_eq_x := p_in_line1_right i_ne_j,
          rw p_eq_x,
          replace x_in_y_add_ej := x_in_y_add_ej i,
          rw [int_unit_basis_vector, add_int_vectors] at x_in_y_add_ej,
          simp only [int.cast_add, vector.nth_of_fn] at x_in_y_add_ej,
          have j_ne_i : ¬(j = i) := by {intro j_eq_i, symmetry' at j_eq_i, exact i_ne_j j_eq_i},
          rw [if_neg j_ne_i, int.cast_zero, add_zero] at x_in_y_add_ej,
          exact x_in_y_add_ej,
        end,
      have p_has_unique_corner := T'_covers_y_uniquely p p_in_y,
        rcases p_has_unique_corner with ⟨p_corner, p_corner_in_T', p_in_p_corner, p_corner_unique⟩,
      by_cases p_lt_corner0_add_one : p.nth j < corner0.nth j + 1,
      { left,
        have p_in_corner0 : in_cube corner0 p :=
          begin
            rw in_cube,
            intro i,
            replace p_in_line1 := p_in_line1 i,
            cases p_in_line1,
            rw in_cube at x_j_set_to_y_in_corner0,
            simp only [not_exists, ge_iff_le, vector.nth_of_fn] at x_j_set_to_y_in_corner0,
            replace x_j_set_to_y_in_corner0 := x_j_set_to_y_in_corner0 i,
            by_cases i_eq_j : i = j,
            { replace p_in_line1_left := p_in_line1_left i_eq_j,
              rw i_eq_j,
              rw [if_pos i_eq_j, i_eq_j] at x_j_set_to_y_in_corner0,
              clear_except x_j_set_to_y_in_corner0 p_in_line1_left p_lt_corner0_add_one,
              exact ⟨by linarith, p_lt_corner0_add_one⟩,
            },
            rename i_eq_j i_ne_j,
            have p_eq_x := p_in_line1_right i_ne_j,
            rw p_eq_x,
            rw [if_neg i_ne_j] at x_j_set_to_y_in_corner0,
            exact x_j_set_to_y_in_corner0,
          end,
        split, exact p_in_corner0,
        intros alt_corner alt_corner_in_T' p_in_alt_corner,
        have p_corner_eq_alt_corner := p_corner_unique alt_corner alt_corner_in_T' p_in_alt_corner,
        have p_corner_eq_corner0 := p_corner_unique corner0 corner0_in_T' p_in_corner0,
        rw [← p_corner_eq_alt_corner, ← p_corner_eq_corner0],
      },
      rename p_lt_corner0_add_one p_ge_corner0_add_one,
      simp only [not_lt] at p_ge_corner0_add_one,
      right,
      have p_in_corner1 : in_cube corner1 p :=
        begin
          rw in_cube,
          intro i,
          replace p_in_line1 := p_in_line1 i,
          cases p_in_line1,
          rw in_cube at x_j_set_to_y_add_one_in_corner1,
          simp only [not_exists, ge_iff_le, vector.nth_of_fn] at x_j_set_to_y_add_one_in_corner1,
          replace x_j_set_to_y_add_one_in_corner1 := x_j_set_to_y_add_one_in_corner1 i,
          by_cases i_eq_j : i = j,
          { replace p_in_line1_left := p_in_line1_left i_eq_j,
            rw i_eq_j,
            rw [if_pos i_eq_j, i_eq_j] at x_j_set_to_y_add_one_in_corner1,
            rw corner0_add_one_eq_corner1_at_j at p_ge_corner0_add_one,
            clear_except x_j_set_to_y_add_one_in_corner1 p_in_line1_left p_ge_corner0_add_one,
            exact ⟨p_ge_corner0_add_one, by linarith⟩,
          },
          rename i_eq_j i_ne_j,
          have p_eq_x := p_in_line1_right i_ne_j,
          rw p_eq_x,
          rw [if_neg i_ne_j] at x_j_set_to_y_add_one_in_corner1,
          exact x_j_set_to_y_add_one_in_corner1,
        end,
      split, exact p_in_corner1,
      intros alt_corner alt_corner_in_T' p_in_alt_corner,
      have p_corner_eq_alt_corner := p_corner_unique alt_corner alt_corner_in_T' p_in_alt_corner,
      have p_corner_eq_corner1 := p_corner_unique corner1 corner1_in_T' p_in_corner1,
      rw [← p_corner_eq_alt_corner, ← p_corner_eq_corner1],
    end,
  --Build corner2, which will contain x_j_set_to_y_add_two
  let corner2 :=
    add_vectors corner0_core (int_point_to_point (double_int_vector (add_int_vectors corner0_offset (int_unit_basis_vector j)))),
  have corner2_in_T' : corner2 ∈ T' :=
    by {use [corner0_core, corner0_core_in_T_core, (add_int_vectors corner0_offset (int_unit_basis_vector j))],},
  have line2_uniquely_covered : ∀ p ∈ line2,
    (in_cube corner1 p ∧ (∀ alt_corner ∈ T', in_cube alt_corner p → corner1 = alt_corner)) ∨
    (in_cube corner2 p ∧ (∀ alt_corner ∈ T', in_cube alt_corner p → corner2 = alt_corner)) :=
    line2_uniquely_covered_cube_induction_step_pos_helper d d_gt_zero T T_is_tiling T_faceshare_free j y x x_in_y_add_ej corner0
      corner0_core corner0_offset corner0_def corner1 corner1_core corner1_offset corner1_def corner0_add_one_eq_corner1_at_j
      T'_covers_y_uniquely x_j_set_to_y_in_y x_j_set_to_y_add_one_in_y corner0_core_in_T_core x_j_set_to_y_in_corner0
      corner0_unique corner1_in_T' x_j_set_to_y_add_one_in_corner1 corner1_unique corner1_core_in_T_core line1_uniquely_covered corner2_in_T',
  have x_in_line2 : x ∈ line2 :=
    begin
      intro i,
      split,
      { intro i_eq_j,
        replace x_in_y_add_ej := x_in_y_add_ej j,
        rw [int_unit_basis_vector, add_int_vectors] at x_in_y_add_ej,
        simp only [int.cast_add, if_true, eq_self_iff_true, int.cast_one, vector.nth_of_fn] at x_in_y_add_ej,
        have one_add_one_eq_two : (1 : ℝ) + 1 = 2 := by norm_num,
        rw [add_assoc, one_add_one_eq_two] at x_in_y_add_ej,
        exact x_in_y_add_ej,
      },
      intro,
      refl,
    end,
  replace line2_uniquely_covered := line2_uniquely_covered x x_in_line2,
  cases line2_uniquely_covered with x_uniquely_in_corner1 x_uniquely_in_corner2,
  { use [corner1, corner1_in_T'],
    exact x_uniquely_in_corner1,
  },
  use [corner2, corner2_in_T'],
  exact x_uniquely_in_corner2,
end

lemma line2_uniquely_covered_cube_induction_step_neg_helper (d : ℕ) (d_gt_zero : d > 0) (T : set (point d)) (T_is_tiling : is_tiling T)
  (T_faceshare_free : tiling_faceshare_free T) (j : fin d) (y : int_point d) (x : point d)
  (x_in_y_sub_ej : ∀ (i : fin d), vector.nth x i ≥ ↑((add_int_vectors y (int_neg_unit_basis_vector j)).nth i) ∧
                                  vector.nth x i ≤ ↑((add_int_vectors y (int_neg_unit_basis_vector j)).nth i) + 1)
  (corner0 corner0_core : point d)(corner0_offset : int_point d)
  (corner0_def : corner0 = add_vectors corner0_core (int_point_to_point (double_int_vector corner0_offset)))
  (corner1 corner1_core : point d) (corner1_offset : int_point d)
  (corner1_def : corner1 = add_vectors corner1_core (int_point_to_point (double_int_vector corner1_offset)))
  (corner0_add_one_eq_corner1_at_j : vector.nth corner0 j + 1 = vector.nth corner1 j) :
  let core_points : set (point d) :=
        {x :
           point d | ∀ (i : fin d),
           vector.nth x i = 0 ∨ vector.nth x i = 1},
      T_core : set (point d) :=
        {t ∈ T | ∃ (p : point d) (H : p ∈ core_points), in_cube t p},
      T' : set (point d) :=
        {t' :
           point d | ∃ (t : point d) (H : t ∈ T_core) (x : int_point d),
           t' = add_vectors t (int_point_to_point (double_int_vector x))},
      x_j_set_to_y : point d :=
        vector.of_fn
          (λ (i : fin d), ite (i = j) ↑(vector.nth y j) (vector.nth x i)),
      x_j_set_to_y_add_one : point d :=
        vector.of_fn
          (λ (i : fin d),
             ite (i = j) (↑(vector.nth y j) + 1) (vector.nth x i)),
      x_j_set_to_y_sub_one : point d :=
        vector.of_fn
          (λ (i : fin d),
             ite (i = j) (↑(vector.nth y j) - 1) (vector.nth x i)),
      line1 : set (point d) :=
        {p :
           point d | ∀ (i : fin d),
           (i = j →
              vector.nth p j ≥ ↑(vector.nth y j) ∧
                vector.nth p j ≤ ↑(vector.nth y j) + 1) ∧
             (i ≠ j → vector.nth p i = vector.nth x i)},
      line2 : set (point d) :=
        {p :
           point d | ∀ (i : fin d),
           (i = j →
              vector.nth p j ≥ ↑(vector.nth y j) - 1 ∧
                vector.nth p j ≤ ↑(vector.nth y j)) ∧
             (i ≠ j → vector.nth p i = vector.nth x i)},
      corner2 : vector ℝ d :=
        add_vectors corner1_core
          (int_point_to_point
             (double_int_vector
                (add_int_vectors corner1_offset (int_neg_unit_basis_vector j))))
  in (∀ (x : point d),
        (∀ (i : fin d),
           vector.nth x i ≥ ↑(vector.nth y i) ∧
             vector.nth x i ≤ ↑(vector.nth y i) + 1) →
        (∃ (t : point d) (H : t ∈ T'),
           in_cube t x ∧
             ∀ (alt_t : point d),
               alt_t ∈ T' → in_cube alt_t x → t = alt_t)) →
     (∀ (i : fin d),
        vector.nth x_j_set_to_y i ≥ ↑(vector.nth y i) ∧
          vector.nth x_j_set_to_y i ≤ ↑(vector.nth y i) + 1) →
     (∀ (i : fin d),
        vector.nth x_j_set_to_y_add_one i ≥ ↑(vector.nth y i) ∧
          vector.nth x_j_set_to_y_add_one i ≤ ↑(vector.nth y i) + 1) →
     corner0 ∈ T' →
     in_cube corner0 x_j_set_to_y →
     (∀ (alt_t : point d),
        alt_t ∈ T' → in_cube alt_t x_j_set_to_y → corner0 = alt_t) →
     corner0_core ∈ T_core →
     corner1 ∈ T' →
     in_cube corner1 x_j_set_to_y_add_one →
     (∀ (alt_t : point d),
        alt_t ∈ T' →
        in_cube alt_t x_j_set_to_y_add_one → corner1 = alt_t) →
     corner1_core ∈ T_core →
     (∀ (p : point d),
        p ∈ line1 →
        ((in_cube corner0 p ∧
              ∀ (alt_corner : point d),
                alt_corner ∈ T' →
                in_cube alt_corner p → alt_corner = corner0) ∨
           in_cube corner1 p ∧
             ∀ (alt_corner : point d),
               alt_corner ∈ T' →
               in_cube alt_corner p → alt_corner = corner1)) →
     corner2 ∈ T' →
     ∀ (p : point d),
       p ∈ line2 →
       ((in_cube corner0 p ∧
             ∀ (alt_corner : point d),
               alt_corner ∈ T' →
               in_cube alt_corner p → corner0 = alt_corner) ∨
          in_cube corner2 p ∧
            ∀ (alt_corner : point d),
              alt_corner ∈ T' →
              in_cube alt_corner p → corner2 = alt_corner) :=
begin
  intros core_points T_core T' x_j_set_to_y x_j_set_to_y_add_one x_j_set_to_y_sub_one line1 line2 corner2 T'_covers_y_uniquely
    x_j_set_to_y_in_y x_j_set_to_y_add_one_in_y corner0_in_T' x_j_set_to_y_in_corner0 corner0_unique corner0_core_in_T_core corner1_in_T'
    x_j_set_to_y_add_one_in_corner1 corner1_unique corner1_core_in_T_core line1_uniquely_covered corner2_in_T' p p_in_line2,
  let p_add_ej := vector.of_fn (λ i : fin d, if(i = j) then p.nth i + 1 else p.nth i),
  have p_add_ej_in_line1 : p_add_ej ∈ line1 :=
    begin
      intro i,
      replace p_in_line2 := p_in_line2 i,
      cases p_in_line2,
      dsimp only[p_add_ej],
      simp only [if_true, ge_iff_le, eq_self_iff_true, vector.nth_of_fn, ne.def],
      split,
      { intro i_eq_j,
        replace p_in_line2_left := p_in_line2_left i_eq_j,
        clear_except p_in_line2_left,
        exact ⟨by linarith, by linarith⟩,
      },
      intro i_ne_j,
      rw if_neg i_ne_j,
      exact p_in_line2_right i_ne_j,
    end,
  replace line1_uniquely_covered := line1_uniquely_covered p_add_ej p_add_ej_in_line1,
  rcases line1_uniquely_covered with
    ⟨p_add_ej_in_corner0, p_add_ej_only_in_corner0⟩ | ⟨p_add_ej_in_corner1, p_add_ej_only_in_corner1⟩,
  { right, --p should uniquely be in corner2 because p_add_ej is uniquely in corner0
    have p_in_corner2 : in_cube corner2 p :=
      begin
        rw in_cube,
        intro i,
        rw in_cube at p_add_ej_in_corner0,
        simp only [not_exists, ge_iff_le, vector.nth_of_fn] at p_add_ej_in_corner0,
        replace p_add_ej_in_corner0 := p_add_ej_in_corner0 i,
        by_cases i_eq_j : i = j,
        { rw ← i_eq_j at corner0_add_one_eq_corner1_at_j,
          rw [if_pos i_eq_j, corner0_add_one_eq_corner1_at_j] at p_add_ej_in_corner0,
          dsimp only[corner2],
          rw [int_neg_unit_basis_vector, add_int_vectors, double_int_vector, int_point_to_point, add_vectors],
          simp only [int.cast_add, int.cast_bit0, int.cast_mul, int.cast_one, vector.nth_of_fn],
          have j_eq_i : j = i := by {symmetry, exact i_eq_j,},
          rw [if_pos j_eq_i, mul_add, ← add_assoc],
          simp only [mul_one, int.cast_one],
          have corner1_def_at_i :
            corner1.nth i = (add_vectors corner1_core (int_point_to_point (double_int_vector corner1_offset))).nth i :=
            by rw corner1_def,
          rw [double_int_vector, int_point_to_point, add_vectors] at corner1_def_at_i,
          simp only [int.cast_bit0, int.cast_mul, int.cast_one, vector.nth_of_fn] at corner1_def_at_i,
          rw ← corner1_def_at_i,
          simp only [int.cast_neg, int.cast_one, mul_neg, mul_one, add_neg_le_iff_le_add'],
          have corner0_eq_corner1_sub_one_at_j : corner0.nth i = corner1.nth i - 1 :=
            begin
              clear_except corner0_add_one_eq_corner1_at_j,
              linarith,
            end,
          rw corner0_eq_corner1_sub_one_at_j at p_add_ej_in_corner0,
          clear_except p_add_ej_in_corner0,
          exact ⟨by linarith, by linarith⟩,
        },
        rename i_eq_j i_ne_j,
        rw in_cube at x_j_set_to_y_add_one_in_corner1,
        simp only [not_exists, ge_iff_le, vector.nth_of_fn] at x_j_set_to_y_add_one_in_corner1,
        replace x_j_set_to_y_add_one_in_corner1 := x_j_set_to_y_add_one_in_corner1 i,
        rw [if_neg i_ne_j] at x_j_set_to_y_add_one_in_corner1,
        have p_eq_x_at_i : p.nth i = x.nth i :=
          begin
            replace p_in_line2 := p_in_line2 i,
            cases p_in_line2,
            exact p_in_line2_right i_ne_j,
          end,
        have corner2_eq_corner1_at_i : corner2.nth i = corner1.nth i :=
          begin
            dsimp only[corner2],
            rw [corner1_def, int_neg_unit_basis_vector, add_int_vectors, double_int_vector, double_int_vector, int_point_to_point,
              int_point_to_point, add_vectors, add_vectors],
            simp only [int.cast_add, int.cast_bit0, int.cast_mul, int.cast_one, vector.nth_of_fn],
            have j_ne_i : ¬(j = i) := by {intro j_eq_i, symmetry' at j_eq_i, exact i_ne_j j_eq_i},
            rw [if_neg j_ne_i, int.cast_zero, add_zero],
          end,
        rw [p_eq_x_at_i, corner2_eq_corner1_at_i],
        exact x_j_set_to_y_add_one_in_corner1,
      end,
    split, exact p_in_corner2,
    intros alt_corner alt_corner_in_T' p_in_alt_corner,
    have alt_corner_covers_x_j_set_to_y_sub_zero_or_one :
      in_cube alt_corner x_j_set_to_y ∨ in_cube alt_corner x_j_set_to_y_sub_one :=
      begin
        rw in_cube at p_in_alt_corner,
        by_cases alt_corner_le_y_sub_one : alt_corner.nth j ≤ y.nth j - 1,
        { right,
          rw in_cube,
          simp only [not_exists, ge_iff_le, vector.nth_of_fn],
          intro i,
          replace p_in_alt_corner := p_in_alt_corner i,
          by_cases i_eq_j : i = j,
          { rw [if_pos i_eq_j, i_eq_j],
            split, exact alt_corner_le_y_sub_one,
            replace p_in_line2 := p_in_line2 j,
            cases p_in_line2,
            replace p_in_line2_left := p_in_line2_left (by refl),
            cases p_in_line2_left,
            simp only [ge_iff_le] at p_in_line2_left_left,
            rw i_eq_j at p_in_alt_corner,
            cases p_in_alt_corner,
            exact le_lt_trans p_in_line2_left_left p_in_alt_corner_right,
          },
          rename i_eq_j i_ne_j,
          rw if_neg i_ne_j,
          replace p_in_line2 := p_in_line2 i,
          cases p_in_line2,
          replace p_in_line2_right := p_in_line2_right i_ne_j,
          rw ← p_in_line2_right,
          exact p_in_alt_corner,
        },
        left,
        rw in_cube,
        simp only [not_exists, ge_iff_le, vector.nth_of_fn],
        intro i,
        replace p_in_alt_corner := p_in_alt_corner i,
        by_cases i_eq_j : i = j,
        { rw [if_pos i_eq_j, i_eq_j],
          split,
          { replace p_in_line2 := p_in_line2 j,
            cases p_in_line2,
            replace p_in_line2_left := p_in_line2_left (by refl),
            cases p_in_line2_left,
            rw i_eq_j at p_in_alt_corner,
            cases p_in_alt_corner,
            exact le_trans p_in_alt_corner_left p_in_line2_left_right,
          },
          clear_except alt_corner_le_y_sub_one,
          linarith,
        },
        rename i_eq_j i_ne_j,
        rw if_neg i_ne_j,
        replace p_in_line2 := p_in_line2 i,
        cases p_in_line2,
        replace p_in_line2_right := p_in_line2_right i_ne_j,
        rw ← p_in_line2_right,
        exact p_in_alt_corner,
      end,
    cases alt_corner_covers_x_j_set_to_y_sub_zero_or_one with x_j_set_to_y_in_alt_corner x_j_set_to_y_sub_one_in_alt_corner,
    { exfalso,
      have corner0_eq_alt_corner := corner0_unique alt_corner alt_corner_in_T' x_j_set_to_y_in_alt_corner,
      rw in_cube at p_add_ej_in_corner0 p_in_alt_corner,
      simp only [not_exists, ge_iff_le, vector.nth_of_fn] at p_add_ej_in_corner0 p_in_alt_corner,
      replace p_add_ej_in_corner0 := p_add_ej_in_corner0 j,
      replace p_in_alt_corner := p_in_alt_corner j,
      rw [← corner0_eq_alt_corner] at p_in_alt_corner,
      rw [if_pos ((by refl) : j=j)] at p_add_ej_in_corner0,
      clear_except p_in_alt_corner p_add_ej_in_corner0,
      linarith,
    },
    rcases alt_corner_in_T' with ⟨alt_corner_core, alt_corner_core_in_T_core, alt_corner_offset, alt_corner_def⟩,
    let alt_corner_add_2ej :=
      add_vectors alt_corner_core (int_point_to_point (double_int_vector (add_int_vectors alt_corner_offset (int_unit_basis_vector j)))),
    have alt_corner_add_2ej_in_T' : alt_corner_add_2ej ∈ T' :=
      by use [alt_corner_core, alt_corner_core_in_T_core, add_int_vectors alt_corner_offset (int_unit_basis_vector j)],
    have x_j_set_to_y_add_one_in_alt_corner_add_2ej : in_cube alt_corner_add_2ej x_j_set_to_y_add_one :=
      begin
        rw in_cube,
        simp only [not_exists, ge_iff_le, vector.nth_of_fn],
        intro i,
        dsimp only[alt_corner_add_2ej],
        rw [int_unit_basis_vector, add_int_vectors, double_int_vector, int_point_to_point, add_vectors],
        simp only [int.cast_add, int.cast_bit0, int.cast_mul, int.cast_one, vector.nth_of_fn],
        have alt_corner_def_at_i :
          alt_corner.nth i = (add_vectors alt_corner_core (int_point_to_point (double_int_vector alt_corner_offset))).nth i :=
          by rw alt_corner_def,
        rw [double_int_vector, int_point_to_point, add_vectors] at alt_corner_def_at_i,
        simp only [int.cast_bit0, int.cast_mul, int.cast_one, vector.nth_of_fn] at alt_corner_def_at_i,
        rw [mul_add, ← add_assoc, ← alt_corner_def_at_i],
        by_cases i_eq_j : i = j,
        { have j_eq_i : j = i := by {symmetry, exact i_eq_j},
          rw [if_pos i_eq_j, if_pos j_eq_i],
          simp only [int.cast_one, mul_one, add_lt_add_iff_right],
          rw in_cube at x_j_set_to_y_sub_one_in_alt_corner,
          simp only [not_exists, ge_iff_le, vector.nth_of_fn] at x_j_set_to_y_sub_one_in_alt_corner,
          replace x_j_set_to_y_sub_one_in_alt_corner := x_j_set_to_y_sub_one_in_alt_corner i,
          rw [if_pos i_eq_j] at x_j_set_to_y_sub_one_in_alt_corner,
          clear_except x_j_set_to_y_sub_one_in_alt_corner,
          exact ⟨by linarith, by linarith⟩,
        },
        rename i_eq_j i_ne_j,
        have j_ne_i : j ≠ i := by {intro j_eq_i, symmetry' at j_eq_i, exact i_ne_j j_eq_i},
        rw [if_neg i_ne_j, if_neg j_ne_i],
        simp only [add_zero, int.cast_zero, mul_zero],
        rw in_cube at p_in_alt_corner,
        replace p_in_alt_corner := p_in_alt_corner i,
        replace p_in_line2 := p_in_line2 i,
        cases p_in_line2,
        replace p_in_line2_right := p_in_line2_right i_ne_j,
        rw ← p_in_line2_right,
        exact p_in_alt_corner,
      end,
    have corner1_eq_alt_corner_add_2ej :=
      corner1_unique alt_corner_add_2ej alt_corner_add_2ej_in_T' x_j_set_to_y_add_one_in_alt_corner_add_2ej,
    apply vector.ext,
    intro i,
    dsimp only[corner2],
    rw [int_neg_unit_basis_vector, add_int_vectors, double_int_vector, int_point_to_point, add_vectors],
    simp only [int.cast_add, int.cast_bit0, int.cast_mul, int.cast_one, vector.nth_of_fn],
    have corner1_def_at_i : corner1.nth i = (add_vectors corner1_core (int_point_to_point (double_int_vector corner1_offset))).nth i :=
      by rw corner1_def,
    rw [double_int_vector, int_point_to_point, add_vectors] at corner1_def_at_i,
    simp only [int.cast_add, int.cast_bit0, int.cast_mul, int.cast_one, vector.nth_of_fn] at corner1_def_at_i,
    rw [mul_add, ← add_assoc, ← corner1_def_at_i, corner1_eq_alt_corner_add_2ej],
    dsimp only[alt_corner_add_2ej],
    rw [alt_corner_def, int_unit_basis_vector, add_int_vectors, double_int_vector, double_int_vector, int_point_to_point,
        int_point_to_point, add_vectors, add_vectors],
    simp only [int.cast_add, int.cast_bit0, int.cast_mul, int.cast_one, vector.nth_of_fn],
    by_cases j_eq_i : j = i,
    { rw [if_pos j_eq_i, if_pos j_eq_i, mul_add],
      simp only [int.cast_one, mul_one, int.cast_neg, mul_neg],
      clear_except,
      linarith,
    },
    rename j_eq_i j_ne_i,
    rw [if_neg j_ne_i, if_neg j_ne_i],
    simp only [add_zero, int.cast_zero, mul_zero],
  },
  left, --p should uniquely be in corner0 because p_add_ej is uniquely in corner1
  have p_in_corner0 : in_cube corner0 p :=
    begin
      rw in_cube,
      intro i,
      rw in_cube at p_add_ej_in_corner1,
      simp only [not_exists, ge_iff_le, vector.nth_of_fn] at p_add_ej_in_corner1,
      replace p_add_ej_in_corner1 := p_add_ej_in_corner1 i,
      by_cases i_eq_j : i = j,
      { rw if_pos i_eq_j at p_add_ej_in_corner1,
        rw ← i_eq_j at corner0_add_one_eq_corner1_at_j,
        rw ← corner0_add_one_eq_corner1_at_j at p_add_ej_in_corner1,
        clear_except p_add_ej_in_corner1,
        cases p_add_ej_in_corner1,
        exact ⟨by linarith, by linarith⟩,
      },
      rename i_eq_j i_ne_j,
      rw in_cube at x_j_set_to_y_in_corner0,
      simp only [not_exists, ge_iff_le, vector.nth_of_fn] at x_j_set_to_y_in_corner0,
      replace x_j_set_to_y_in_corner0 := x_j_set_to_y_in_corner0 i,
      rw [if_neg i_ne_j] at x_j_set_to_y_in_corner0,
      have p_eq_x_at_i : p.nth i = x.nth i :=
        begin
          replace p_in_line2 := p_in_line2 i,
          cases p_in_line2,
          exact p_in_line2_right i_ne_j,
        end,
      rw p_eq_x_at_i,
      exact x_j_set_to_y_in_corner0,
    end,
  split, exact p_in_corner0,
  intros alt_corner alt_corner_in_T' p_in_alt_corner,
  have alt_corner_covers_x_j_set_to_y_sub_zero_or_one :
    in_cube alt_corner x_j_set_to_y ∨ in_cube alt_corner x_j_set_to_y_sub_one :=
    begin
      rw in_cube at p_in_alt_corner,
      by_cases alt_corner_le_y_sub_one : alt_corner.nth j ≤ y.nth j - 1,
      { right,
        rw in_cube,
        simp only [not_exists, ge_iff_le, vector.nth_of_fn],
        intro i,
        replace p_in_alt_corner := p_in_alt_corner i,
        by_cases i_eq_j : i = j,
        { rw [if_pos i_eq_j, i_eq_j],
          split, exact alt_corner_le_y_sub_one,
          replace p_in_line2 := p_in_line2 j,
          cases p_in_line2,
          replace p_in_line2_left := p_in_line2_left (by refl),
          cases p_in_line2_left,
          simp only [ge_iff_le] at p_in_line2_left_left,
          rw i_eq_j at p_in_alt_corner,
          cases p_in_alt_corner,
          exact le_lt_trans p_in_line2_left_left p_in_alt_corner_right,
        },
        rename i_eq_j i_ne_j,
        rw if_neg i_ne_j,
        replace p_in_line2 := p_in_line2 i,
        cases p_in_line2,
        replace p_in_line2_right := p_in_line2_right i_ne_j,
        rw ← p_in_line2_right,
        exact p_in_alt_corner,
      },
      left,
      rw in_cube,
      simp only [not_exists, ge_iff_le, vector.nth_of_fn],
      intro i,
      replace p_in_alt_corner := p_in_alt_corner i,
      by_cases i_eq_j : i = j,
      { rw [if_pos i_eq_j, i_eq_j],
        split,
        { replace p_in_line2 := p_in_line2 j,
          cases p_in_line2,
          replace p_in_line2_left := p_in_line2_left (by refl),
          cases p_in_line2_left,
          rw i_eq_j at p_in_alt_corner,
          cases p_in_alt_corner,
          exact le_trans p_in_alt_corner_left p_in_line2_left_right,
        },
        clear_except alt_corner_le_y_sub_one,
        linarith,
      },
      rename i_eq_j i_ne_j,
      rw if_neg i_ne_j,
      replace p_in_line2 := p_in_line2 i,
      cases p_in_line2,
      replace p_in_line2_right := p_in_line2_right i_ne_j,
      rw ← p_in_line2_right,
      exact p_in_alt_corner,
    end,
  cases alt_corner_covers_x_j_set_to_y_sub_zero_or_one with x_j_set_to_y_in_alt_corner x_j_set_to_y_sub_one_in_alt_corner,
  { exact corner0_unique alt_corner alt_corner_in_T' x_j_set_to_y_in_alt_corner,
  },
  exfalso,
  rcases alt_corner_in_T' with ⟨alt_corner_core, alt_corner_core_in_T_core, alt_corner_offset, alt_corner_def⟩,
  let alt_corner_add_2ej :=
    add_vectors alt_corner_core (int_point_to_point (double_int_vector (add_int_vectors alt_corner_offset (int_unit_basis_vector j)))),
  have alt_corner_add_2ej_in_T' : alt_corner_add_2ej ∈ T' :=
    by use [alt_corner_core, alt_corner_core_in_T_core, add_int_vectors alt_corner_offset (int_unit_basis_vector j)],
  have x_j_set_to_y_add_one_in_alt_corner_add_2ej : in_cube alt_corner_add_2ej x_j_set_to_y_add_one :=
    begin
      rw in_cube,
      simp only [not_exists, ge_iff_le, vector.nth_of_fn],
      intro i,
      dsimp only[alt_corner_add_2ej],
      rw [int_unit_basis_vector, add_int_vectors, double_int_vector, int_point_to_point, add_vectors],
      simp only [int.cast_add, int.cast_bit0, int.cast_mul, int.cast_one, vector.nth_of_fn],
      have alt_corner_def_at_i :
        alt_corner.nth i = (add_vectors alt_corner_core (int_point_to_point (double_int_vector alt_corner_offset))).nth i :=
        by rw alt_corner_def,
      rw [double_int_vector, int_point_to_point, add_vectors] at alt_corner_def_at_i,
      simp only [int.cast_bit0, int.cast_mul, int.cast_one, vector.nth_of_fn] at alt_corner_def_at_i,
      rw [mul_add, ← add_assoc, ← alt_corner_def_at_i],
      by_cases i_eq_j : i = j,
      { have j_eq_i : j = i := by {symmetry, exact i_eq_j},
        rw [if_pos i_eq_j, if_pos j_eq_i],
        simp only [int.cast_one, mul_one, add_lt_add_iff_right],
        rw in_cube at x_j_set_to_y_sub_one_in_alt_corner,
        simp only [not_exists, ge_iff_le, vector.nth_of_fn] at x_j_set_to_y_sub_one_in_alt_corner,
        replace x_j_set_to_y_sub_one_in_alt_corner := x_j_set_to_y_sub_one_in_alt_corner i,
        rw [if_pos i_eq_j] at x_j_set_to_y_sub_one_in_alt_corner,
        clear_except x_j_set_to_y_sub_one_in_alt_corner,
        exact ⟨by linarith, by linarith⟩,
      },
      rename i_eq_j i_ne_j,
      have j_ne_i : j ≠ i := by {intro j_eq_i, symmetry' at j_eq_i, exact i_ne_j j_eq_i},
      rw [if_neg i_ne_j, if_neg j_ne_i],
      simp only [add_zero, int.cast_zero, mul_zero],
      rw in_cube at p_in_alt_corner,
      replace p_in_alt_corner := p_in_alt_corner i,
      replace p_in_line2 := p_in_line2 i,
      cases p_in_line2,
      replace p_in_line2_right := p_in_line2_right i_ne_j,
      rw ← p_in_line2_right,
      exact p_in_alt_corner,
    end,
  have corner1_eq_alt_corner_add_2ej :=
    corner1_unique alt_corner_add_2ej alt_corner_add_2ej_in_T' x_j_set_to_y_add_one_in_alt_corner_add_2ej,
  rw corner1_eq_alt_corner_add_2ej at corner0_add_one_eq_corner1_at_j,
  dsimp only[alt_corner_add_2ej] at corner0_add_one_eq_corner1_at_j,
  rw [int_unit_basis_vector, add_int_vectors, double_int_vector, int_point_to_point, add_vectors]
    at corner0_add_one_eq_corner1_at_j,
  simp only [int.cast_add, int.cast_bit0, if_true, int.cast_mul, eq_self_iff_true, int.cast_one, vector.nth_of_fn, int.cast_neg]
    at corner0_add_one_eq_corner1_at_j,
  rw [mul_add, ← add_assoc] at corner0_add_one_eq_corner1_at_j,
  have alt_corner_def_at_j :
    alt_corner.nth j = (add_vectors alt_corner_core (int_point_to_point (double_int_vector alt_corner_offset))).nth j :=
    by rw alt_corner_def,
  rw [double_int_vector, int_point_to_point, add_vectors] at alt_corner_def_at_j,
  simp only [int.cast_bit0, int.cast_mul, int.cast_one, vector.nth_of_fn] at alt_corner_def_at_j,
  rw ← alt_corner_def_at_j at corner0_add_one_eq_corner1_at_j,
  rw in_cube at p_in_corner0,
  replace p_in_corner0 := p_in_corner0 j,
  rw in_cube at p_in_alt_corner,
  replace p_in_alt_corner := p_in_alt_corner j,
  clear_except corner0_add_one_eq_corner1_at_j p_in_corner0 p_in_alt_corner,
  linarith,
end

lemma T'_is_tiling_cube_induction_step_neg (d : ℕ) (d_gt_zero : d > 0) (T : set (point d)) (T_is_tiling : is_tiling T)
  (T_faceshare_free : tiling_faceshare_free T) :
  let core_points : set (point d) :=
        {x :
           point d | ∀ (i : fin d),
           vector.nth x i = 0 ∨ vector.nth x i = 1},
      T_core : set (point d) :=
        {t ∈ T | ∃ (p : point d) (H : p ∈ core_points), in_cube t p},
      T' : set (point d) :=
        {t' :
           point d | ∃ (t : point d) (H : t ∈ T_core) (x : int_point d),
           t' = add_vectors t (int_point_to_point (double_int_vector x))}
  in ∀ (j : fin d) (y : int_point d),
       (∀ (x : point d),
          (∀ (i : fin d),
             vector.nth x i ≥ ↑(vector.nth y i) ∧
               vector.nth x i ≤ ↑(vector.nth y i) + 1) →
          (∃ (t : point d) (H : t ∈ T'),
             in_cube t x ∧
               ∀ (alt_t : point d),
                 alt_t ∈ T' → in_cube alt_t x → t = alt_t)) →
       ∀ (x : point d),
         (∀ (i : fin d),
            vector.nth x i ≥
                ↑((add_int_vectors y (int_neg_unit_basis_vector j)).nth i) ∧
              vector.nth x i ≤
                ↑((add_int_vectors y (int_neg_unit_basis_vector j)).nth i) +
                  1) →
         (∃ (t : point d) (H : t ∈ T'),
            in_cube t x ∧
              ∀ (alt_t : point d),
                alt_t ∈ T' → in_cube alt_t x → t = alt_t) :=
begin
  intros core_points T_core T' j y T'_covers_y_uniquely x x_in_y_sub_ej, --ej is shorthand for int_unit_basis_vector j
  let x_j_set_to_y : point d := vector.of_fn (λ i : fin d, if(i = j) then y.nth j else x.nth i),
  let x_j_set_to_y_add_one : point d := vector.of_fn (λ i : fin d, if (i = j) then y.nth j + 1 else x.nth i),
  let x_j_set_to_y_sub_one : point d := vector.of_fn (λ i : fin d, if (i = j) then y.nth j - 1 else x.nth i),
  let line1 : set (point d) :=
    {p : point d | ∀ i : fin d, (i = j → (p.nth j ≥ y.nth j ∧ p.nth j ≤ y.nth j + 1)) ∧ (i ≠ j → p.nth i = x.nth i)},
  let line2 : set (point d) :=
    {p : point d | ∀ i : fin d, (i = j → (p.nth j ≥ y.nth j - 1 ∧ p.nth j ≤ y.nth j)) ∧ (i ≠ j → p.nth i = x.nth i)},
  have x_j_set_to_y_in_y : ∀ i : fin d, x_j_set_to_y.nth i ≥ ↑(y.nth i) ∧ x_j_set_to_y.nth i ≤ ↑(y.nth i) + 1 :=
    begin
      intro i,
      dsimp only[x_j_set_to_y],
      simp only [ge_iff_le, vector.nth_of_fn],
      replace x_in_y_sub_ej := x_in_y_sub_ej i,
      rw [int_neg_unit_basis_vector, add_int_vectors] at x_in_y_sub_ej,
      simp only [int.cast_add, ge_iff_le, vector.nth_of_fn] at x_in_y_sub_ej,
      by_cases i_eq_j : i = j,
      { rw [if_pos i_eq_j, i_eq_j],
        split, exact_mod_cast le_refl (y.nth j),
        exact_mod_cast le_of_lt (lt_add_one (y.nth j)),
      },
      rename i_eq_j i_ne_j,
      rw if_neg i_ne_j,
      have j_ne_i : ¬(j = i) := by {intro j_eq_i, symmetry' at j_eq_i, exact i_ne_j j_eq_i},
      rw if_neg j_ne_i at x_in_y_sub_ej,
      simp only [add_zero, int.cast_zero] at x_in_y_sub_ej,
      exact x_in_y_sub_ej,
    end,
  have x_j_set_to_y_uniquely_covered := T'_covers_y_uniquely x_j_set_to_y x_j_set_to_y_in_y,
  have x_j_set_to_y_add_one_in_y : ∀ i : fin d, x_j_set_to_y_add_one.nth i ≥ ↑(y.nth i) ∧ x_j_set_to_y_add_one.nth i ≤ ↑(y.nth i) + 1 :=
    begin
      intro i,
      dsimp only[x_j_set_to_y_add_one],
      simp only [ge_iff_le, vector.nth_of_fn],
      replace x_in_y_sub_ej := x_in_y_sub_ej i,
      rw [int_neg_unit_basis_vector, add_int_vectors] at x_in_y_sub_ej,
      simp only [int.cast_add, ge_iff_le, vector.nth_of_fn] at x_in_y_sub_ej,
      by_cases i_eq_j : i = j,
      { rw [if_pos i_eq_j, i_eq_j],
        split, exact_mod_cast le_of_lt (lt_add_one (y.nth j)),
        exact_mod_cast le_refl (y.nth j + 1),
      },
      rename i_eq_j i_ne_j,
      rw if_neg i_ne_j,
      have j_ne_i : ¬(j = i) := by {intro j_eq_i, symmetry' at j_eq_i, exact i_ne_j j_eq_i},
      rw if_neg j_ne_i at x_in_y_sub_ej,
      simp only [add_zero, int.cast_zero] at x_in_y_sub_ej,
      exact x_in_y_sub_ej,
    end,
  have x_j_set_to_y_add_one_uniquely_covered := T'_covers_y_uniquely x_j_set_to_y_add_one x_j_set_to_y_add_one_in_y,
  --corner0 and corner1 are the corners of x_j_set_to_y(_add_zero) and x_j_set_to_y_add_one respectively
  rcases x_j_set_to_y_uniquely_covered with ⟨corner0, corner0_in_T', x_j_set_to_y_in_corner0, corner0_unique⟩,
  have corner0_in_T'_copy := corner0_in_T',
  rcases corner0_in_T'_copy with ⟨corner0_core, corner0_core_in_T_core, corner0_offset, corner0_def⟩,
  rcases x_j_set_to_y_add_one_uniquely_covered with ⟨corner1, corner1_in_T', x_j_set_to_y_add_one_in_corner1, corner1_unique⟩,
  have corner1_in_T'_copy := corner1_in_T',
  rcases corner1_in_T'_copy with ⟨corner1_core, corner1_core_in_T_core, corner1_offset, corner1_def⟩,
  --Show relationship between corner0 and corner1's j values
  have corner0_add_one_eq_corner1_at_j : corner0.nth j + 1 = corner1.nth j :=
    begin
      rw in_cube at x_j_set_to_y_in_corner0 x_j_set_to_y_add_one_in_corner1,
      simp only [not_exists, ge_iff_le, vector.nth_of_fn] at x_j_set_to_y_in_corner0 x_j_set_to_y_add_one_in_corner1,
      have x_j_set_to_y_in_corner0_at_j := x_j_set_to_y_in_corner0 j,
      have x_j_set_to_y_add_one_in_corner1_at_j := x_j_set_to_y_add_one_in_corner1 j,
      rw [if_pos ((by refl) : j = j)] at x_j_set_to_y_in_corner0_at_j x_j_set_to_y_add_one_in_corner1_at_j,
      have h := real_eq_or_lt_or_gt (corner0.nth j + 1) (corner1.nth j),
      rcases h with corner0_add_one_eq_corner1 | corner0_add_one_lt_corner1 | corner0_add_one_gt_corner1, exact corner0_add_one_eq_corner1,
      { exfalso, --In this case, contradiction point is in neither corner0 nor corner1
        let contradiction_point := vector.of_fn (λ i : fin d, if(i = j) then corner0.nth j + 1 else x.nth i),
        have contradiction_point_in_y :
          ∀ i : fin d, contradiction_point.nth i ≥ ↑(vector.nth y i) ∧ contradiction_point.nth i ≤ ↑(vector.nth y i) + 1 :=
          begin
            intro i,
            dsimp only[contradiction_point],
            simp only [ge_iff_le, vector.nth_of_fn],
            replace x_in_y_sub_ej := x_in_y_sub_ej i,
            rw [int_neg_unit_basis_vector, add_int_vectors] at x_in_y_sub_ej,
            simp only [int.cast_add, ge_iff_le, vector.nth_of_fn] at x_in_y_sub_ej,
            by_cases i_eq_j : i = j,
            { rw [if_pos i_eq_j, i_eq_j],
              have j_eq_i : j = i := by {symmetry, exact i_eq_j},
              rw [if_pos j_eq_i, i_eq_j] at x_in_y_sub_ej,
              simp only [neg_add_cancel_right, int.cast_one, int.cast_neg, add_neg_le_iff_le_add'] at x_in_y_sub_ej,
              clear_except x_in_y_sub_ej x_j_set_to_y_in_corner0_at_j,
              exact ⟨by linarith, by linarith⟩,
            },
            rename i_eq_j i_ne_j,
            rw if_neg i_ne_j,
            have j_ne_i : ¬(j = i) := by {intro j_eq_i, symmetry' at j_eq_i, exact i_ne_j j_eq_i},
            rw [if_neg j_ne_i, int.cast_zero, add_zero] at x_in_y_sub_ej,
            exact x_in_y_sub_ej,
          end,
        have T'_covers_y_uniquely_copy := T'_covers_y_uniquely contradiction_point contradiction_point_in_y,
        rcases T'_covers_y_uniquely_copy with
          ⟨contradiction_corner, contradiction_corner_in_T', contradiction_point_in_contradiction_corner, contradiction_corner_unique⟩,
        have h := real_eq_or_lt_or_gt (contradiction_corner.nth j) (contradiction_point.nth j),
        rcases h with
          contradiction_corner_eq_contradiction_point_at_j | contradiction_corner_lt_contradiction_point_at_j |
          contradiction_corner_gt_contradiction_point_at_j,
        { have x_j_set_to_y_add_one_in_contradiction_corner : in_cube contradiction_corner x_j_set_to_y_add_one :=
            begin
              rw in_cube,
              simp only [not_exists, ge_iff_le, vector.nth_of_fn],
              intro i,
              by_cases i_eq_j : i = j,
              { rw [if_pos i_eq_j, i_eq_j, contradiction_corner_eq_contradiction_point_at_j],
                dsimp only[contradiction_point],
                simp only [if_true, eq_self_iff_true, vector.nth_of_fn, add_le_add_iff_right, add_lt_add_iff_right],
                clear_except x_j_set_to_y_in_corner0_at_j,
                exact ⟨by linarith, by linarith⟩,
              },
              rename i_eq_j i_ne_j,
              rw if_neg i_ne_j,
              rw in_cube at contradiction_point_in_contradiction_corner,
              simp only [not_exists, ge_iff_le, vector.nth_of_fn] at contradiction_point_in_contradiction_corner,
              replace contradiction_point_in_contradiction_corner := contradiction_point_in_contradiction_corner i,
              rw if_neg i_ne_j at contradiction_point_in_contradiction_corner,
              exact contradiction_point_in_contradiction_corner,
            end,
          have corner1_eq_contradiction_corner :=
            corner1_unique contradiction_corner contradiction_corner_in_T' x_j_set_to_y_add_one_in_contradiction_corner,
          rw [← corner1_eq_contradiction_corner, in_cube] at contradiction_point_in_contradiction_corner,
          simp only [not_exists, ge_iff_le, vector.nth_of_fn] at contradiction_point_in_contradiction_corner,
          replace contradiction_point_in_contradiction_corner := contradiction_point_in_contradiction_corner j,
          simp only [if_true, not_lt, not_le, eq_self_iff_true, add_le_add_iff_right] at contradiction_point_in_contradiction_corner,
          clear_except contradiction_point_in_contradiction_corner corner0_add_one_lt_corner1,
          linarith,
        },
        { by_cases contradiction_corner_lt_y_at_j : contradiction_corner.nth j < y.nth j,
          { have x_j_set_to_y_in_contradiction_corner : in_cube contradiction_corner x_j_set_to_y :=
              begin
                rw in_cube,
                simp only [not_exists, ge_iff_le, vector.nth_of_fn],
                intro i,
                by_cases i_eq_j : i = j,
                { rw [if_pos i_eq_j, i_eq_j],
                  rw in_cube at contradiction_point_in_contradiction_corner,
                  simp only [not_exists, ge_iff_le, vector.nth_of_fn] at contradiction_point_in_contradiction_corner,
                  replace contradiction_point_in_contradiction_corner := contradiction_point_in_contradiction_corner i,
                  rw [if_pos i_eq_j, i_eq_j] at contradiction_point_in_contradiction_corner,
                  clear_except x_j_set_to_y_in_corner0_at_j contradiction_point_in_contradiction_corner contradiction_corner_lt_y_at_j,
                  exact ⟨le_of_lt contradiction_corner_lt_y_at_j, by linarith⟩,
                },
                rename i_eq_j i_ne_j,
                rw [if_neg i_ne_j],
                rw in_cube at contradiction_point_in_contradiction_corner,
                simp only [not_exists, ge_iff_le, vector.nth_of_fn] at contradiction_point_in_contradiction_corner,
                replace contradiction_point_in_contradiction_corner := contradiction_point_in_contradiction_corner i,
                rw [if_neg i_ne_j] at contradiction_point_in_contradiction_corner,
                exact contradiction_point_in_contradiction_corner,
              end,
            have corner0_eq_contradiction_corner :=
              corner0_unique contradiction_corner contradiction_corner_in_T' x_j_set_to_y_in_contradiction_corner,
            rw [← corner0_eq_contradiction_corner, in_cube] at contradiction_point_in_contradiction_corner,
            simp only [not_exists, ge_iff_le, vector.nth_of_fn] at contradiction_point_in_contradiction_corner,
            replace contradiction_point_in_contradiction_corner := contradiction_point_in_contradiction_corner j,
            rw [if_pos ((by refl) : j = j)] at contradiction_point_in_contradiction_corner,
            cases contradiction_point_in_contradiction_corner,
            clear_except contradiction_point_in_contradiction_corner_right,
            linarith,
          },
          rename contradiction_corner_lt_y_at_j contradiction_corner_ge_y_at_j,
          let contradiction_corner_at_line1 := vector.of_fn (λ i : fin d, if (i = j) then contradiction_corner.nth j else x.nth i),
          have contradiction_corner_at_line1_in_y :
            ∀ i : fin d, contradiction_corner_at_line1.nth i ≥ ↑(y.nth i) ∧ contradiction_corner_at_line1.nth i ≤ ↑(y.nth i) + 1 :=
            begin
              intro i,
              dsimp only[contradiction_corner_at_line1],
              simp only [ge_iff_le, vector.nth_of_fn],
              by_cases i_eq_j : i = j,
              { rw [if_pos i_eq_j, i_eq_j],
                split,
                { simp only [not_lt] at contradiction_corner_ge_y_at_j,
                  exact contradiction_corner_ge_y_at_j,
                },
                dsimp only[contradiction_point] at contradiction_corner_lt_contradiction_point_at_j,
                simp only [if_true, eq_self_iff_true, vector.nth_of_fn] at contradiction_corner_lt_contradiction_point_at_j,
                clear_except contradiction_corner_lt_contradiction_point_at_j x_j_set_to_y_in_corner0_at_j,
                linarith,
              },
              rename i_eq_j i_ne_j,
              rw if_neg i_ne_j,
              replace x_in_y_sub_ej := x_in_y_sub_ej i,
              rw [int_neg_unit_basis_vector, add_int_vectors] at x_in_y_sub_ej,
              simp only [int.cast_add, ge_iff_le, vector.nth_of_fn] at x_in_y_sub_ej,
              have j_ne_i : ¬(j = i) := by {intro j_eq_i, symmetry' at j_eq_i, exact i_ne_j j_eq_i},
              rw [if_neg j_ne_i, int.cast_zero, add_zero] at x_in_y_sub_ej,
              exact x_in_y_sub_ej,
            end,
          replace T'_covers_y_uniquely := T'_covers_y_uniquely contradiction_corner_at_line1 contradiction_corner_at_line1_in_y,
          rcases T'_covers_y_uniquely with
            ⟨contradiction_corner_at_line1_corner, contradiction_corner_at_line1_corner_in_T',
             contradiction_corner_at_line1_in_contradiction_corner_at_line1_corner, contradiction_corner_at_line1_corner_unique⟩,
          have contradiction_corner_at_line1_in_contradiction_corner : in_cube contradiction_corner contradiction_corner_at_line1 :=
            begin
              rw in_cube,
              simp only [not_exists, ge_iff_le, vector.nth_of_fn],
              intro i,
              by_cases i_eq_j : i = j,
              { rw [if_pos i_eq_j, i_eq_j],
                clear,
                exact ⟨by linarith, by linarith⟩,
              },
              rename i_eq_j i_ne_j,
              rw if_neg i_ne_j,
              rw in_cube at contradiction_point_in_contradiction_corner,
              simp only [not_exists, ge_iff_le, vector.nth_of_fn] at contradiction_point_in_contradiction_corner,
              replace contradiction_point_in_contradiction_corner := contradiction_point_in_contradiction_corner i,
              rw [if_neg i_ne_j] at contradiction_point_in_contradiction_corner,
              exact contradiction_point_in_contradiction_corner,
            end,
          have contradiction_corner_at_line1_corner_eq_contradiction_corner :=
            contradiction_corner_at_line1_corner_unique contradiction_corner contradiction_corner_in_T'
            contradiction_corner_at_line1_in_contradiction_corner,
          have contradiction_corner_at_line1_in_corner0 : in_cube corner0 contradiction_corner_at_line1 :=
            begin
              rw in_cube,
              simp only [not_exists, ge_iff_le, vector.nth_of_fn],
              intro i,
              by_cases i_eq_j : i = j,
              { rw [if_pos i_eq_j, i_eq_j],
                rw in_cube at contradiction_point_in_contradiction_corner,
                simp only [not_exists, ge_iff_le, vector.nth_of_fn] at contradiction_point_in_contradiction_corner,
                replace contradiction_point_in_contradiction_corner := contradiction_point_in_contradiction_corner i,
                rw [if_pos i_eq_j, i_eq_j] at contradiction_point_in_contradiction_corner,
                simp only [add_lt_add_iff_right] at contradiction_point_in_contradiction_corner,
                cases contradiction_point_in_contradiction_corner,
                dsimp only[contradiction_point] at contradiction_corner_lt_contradiction_point_at_j,
                simp only [if_true, eq_self_iff_true, vector.nth_of_fn] at contradiction_corner_lt_contradiction_point_at_j,
                exact ⟨le_of_lt contradiction_point_in_contradiction_corner_right, contradiction_corner_lt_contradiction_point_at_j⟩,
              },
              rename i_eq_j i_ne_j,
              rw if_neg i_ne_j,
              replace x_j_set_to_y_in_corner0 := x_j_set_to_y_in_corner0 i,
              rw [if_neg i_ne_j] at x_j_set_to_y_in_corner0,
              exact x_j_set_to_y_in_corner0,
            end,
          have contradiction_corner_at_line1_corner_eq_corner0 :=
            contradiction_corner_at_line1_corner_unique corner0 corner0_in_T' contradiction_corner_at_line1_in_corner0,
          have contradiction_corner_eq_corner0 : contradiction_corner = corner0 :=
            begin
              rw contradiction_corner_at_line1_corner_eq_contradiction_corner at contradiction_corner_at_line1_corner_eq_corner0,
              exact contradiction_corner_at_line1_corner_eq_corner0,
            end,
          rw [contradiction_corner_eq_corner0, in_cube] at contradiction_point_in_contradiction_corner,
          simp only [not_exists, ge_iff_le, vector.nth_of_fn] at contradiction_point_in_contradiction_corner,
          replace contradiction_point_in_contradiction_corner := contradiction_point_in_contradiction_corner j,
          rw [if_pos ((by refl) : j = j)] at contradiction_point_in_contradiction_corner,
          simp only [lt_self_iff_false, and_false] at contradiction_point_in_contradiction_corner,
          exact contradiction_point_in_contradiction_corner,
        },
        rw in_cube at contradiction_point_in_contradiction_corner,
        simp only [not_exists, ge_iff_le, vector.nth_of_fn] at contradiction_point_in_contradiction_corner,
        replace contradiction_point_in_contradiction_corner := contradiction_point_in_contradiction_corner j,
        simp only [if_true, not_lt, not_le, eq_self_iff_true, add_le_add_iff_right] at contradiction_point_in_contradiction_corner,
        dsimp only[contradiction_point] at contradiction_corner_gt_contradiction_point_at_j,
        simp only [gt_iff_lt, if_true, eq_self_iff_true, vector.nth_of_fn] at contradiction_corner_gt_contradiction_point_at_j,
        clear_except contradiction_point_in_contradiction_corner contradiction_corner_gt_contradiction_point_at_j,
        linarith,
      },
      exfalso, --In this case, contradiction point is in both corner0 and corner1
      let contradiction_point := vector.of_fn (λ i : fin d, if(i = j) then corner1.nth j else x.nth i),
      have contradiction_point_in_y :
        ∀ i : fin d, contradiction_point.nth i ≥ ↑(vector.nth y i) ∧ contradiction_point.nth i ≤ ↑(vector.nth y i) + 1 :=
        begin
          intro i,
          dsimp only[contradiction_point],
          simp only [ge_iff_le, vector.nth_of_fn],
          replace x_in_y_sub_ej := x_in_y_sub_ej i,
          rw [int_neg_unit_basis_vector, add_int_vectors] at x_in_y_sub_ej,
          simp only [int.cast_add, ge_iff_le, vector.nth_of_fn] at x_in_y_sub_ej,
          by_cases i_eq_j : i = j,
          { rw [if_pos i_eq_j, i_eq_j],
            have j_eq_i : j = i := by {symmetry, exact i_eq_j},
            rw [if_pos j_eq_i, i_eq_j] at x_in_y_sub_ej,
            simp only [neg_add_cancel_right, int.cast_one, int.cast_neg, add_neg_le_iff_le_add'] at x_in_y_sub_ej,
            clear_except x_in_y_sub_ej x_j_set_to_y_add_one_in_corner1_at_j,
            exact ⟨by linarith, by linarith⟩,
          },
          rename i_eq_j i_ne_j,
          rw if_neg i_ne_j,
          have j_ne_i : ¬(j = i) := by {intro j_eq_i, symmetry' at j_eq_i, exact i_ne_j j_eq_i},
          rw [if_neg j_ne_i, int.cast_zero, add_zero] at x_in_y_sub_ej,
          exact x_in_y_sub_ej,
        end,
      replace T'_covers_y_uniquely := T'_covers_y_uniquely contradiction_point contradiction_point_in_y,
      rcases T'_covers_y_uniquely with
        ⟨contradiction_corner, contradiction_corner_in_T', contradiction_point_in_contradiction_corner, contradiction_corner_unique⟩,
      have contradiction_point_in_corner0 : in_cube corner0 contradiction_point :=
        begin
          rw in_cube,
          simp only [not_exists, ge_iff_le, vector.nth_of_fn],
          intro i,
          by_cases i_eq_j : i = j,
          { rw [if_pos i_eq_j, i_eq_j],
            split,
            { clear_except x_j_set_to_y_add_one_in_corner1_at_j x_j_set_to_y_in_corner0_at_j,
              linarith,
            },
            clear_except corner0_add_one_gt_corner1,
            linarith,
          },
          rename i_eq_j i_ne_j,
          rw if_neg i_ne_j,
          replace x_j_set_to_y_in_corner0 := x_j_set_to_y_in_corner0 i,
          replace x_j_set_to_y_add_one_in_corner1 := x_j_set_to_y_add_one_in_corner1 i,
          rw [if_neg i_ne_j] at x_j_set_to_y_in_corner0 x_j_set_to_y_add_one_in_corner1,
          clear_except x_j_set_to_y_in_corner0 x_j_set_to_y_add_one_in_corner1,
          exact ⟨by linarith, by linarith⟩,
        end,
      have contradiction_point_in_corner1 : in_cube corner1 contradiction_point :=
        begin
          rw in_cube,
          simp only [not_exists, ge_iff_le, vector.nth_of_fn],
          intro i,
          by_cases i_eq_j : i = j,
          { rw [if_pos i_eq_j, i_eq_j],
            split,
            { clear_except x_j_set_to_y_add_one_in_corner1_at_j x_j_set_to_y_in_corner0_at_j,
              linarith,
            },
            clear_except corner0_add_one_gt_corner1,
            linarith,
          },
          rename i_eq_j i_ne_j,
          rw if_neg i_ne_j,
          replace x_j_set_to_y_in_corner0 := x_j_set_to_y_in_corner0 i,
          replace x_j_set_to_y_add_one_in_corner1 := x_j_set_to_y_add_one_in_corner1 i,
          rw [if_neg i_ne_j] at x_j_set_to_y_in_corner0 x_j_set_to_y_add_one_in_corner1,
          clear_except x_j_set_to_y_in_corner0 x_j_set_to_y_add_one_in_corner1,
          exact ⟨by linarith, by linarith⟩,
        end,
      have contradiction_corner_eq_corner0 := contradiction_corner_unique corner0 corner0_in_T' contradiction_point_in_corner0,
      have contradiciton_corner_eq_corner1 := contradiction_corner_unique corner1 corner1_in_T' contradiction_point_in_corner1,
      have corner0_eq_corner1 : corner0 = corner1 :=
        by {rw contradiction_corner_eq_corner0 at contradiciton_corner_eq_corner1, exact contradiciton_corner_eq_corner1},
      rw corner0_eq_corner1 at x_j_set_to_y_in_corner0_at_j,
      clear_except x_j_set_to_y_in_corner0_at_j x_j_set_to_y_add_one_in_corner1_at_j,
      linarith,
    end,
  --Next, need to show that line_1 is uniquely covered by corner0 and corner1
  have line1_uniquely_covered : ∀ p ∈ line1,
    (in_cube corner0 p ∧ (∀ alt_corner ∈ T', in_cube alt_corner p → alt_corner = corner0)) ∨
    (in_cube corner1 p ∧ (∀ alt_corner ∈ T', in_cube alt_corner p → alt_corner = corner1)) :=
    begin
      intros p p_in_line1,
      have p_in_y : ∀ i : fin d, vector.nth p i ≥ ↑(vector.nth y i) ∧ vector.nth p i ≤ ↑(vector.nth y i) + 1 :=
        begin
          intro i,
          replace p_in_line1 := p_in_line1 i,
          cases p_in_line1,
          by_cases i_eq_j : i = j, {rw i_eq_j, exact p_in_line1_left i_eq_j,},
          rename i_eq_j i_ne_j,
          have p_eq_x := p_in_line1_right i_ne_j,
          rw p_eq_x,
          replace x_in_y_sub_ej := x_in_y_sub_ej i,
          rw [int_neg_unit_basis_vector, add_int_vectors] at x_in_y_sub_ej,
          simp only [int.cast_add, vector.nth_of_fn] at x_in_y_sub_ej,
          have j_ne_i : ¬(j = i) := by {intro j_eq_i, symmetry' at j_eq_i, exact i_ne_j j_eq_i},
          rw [if_neg j_ne_i, int.cast_zero, add_zero] at x_in_y_sub_ej,
          exact x_in_y_sub_ej,
        end,
      have p_has_unique_corner := T'_covers_y_uniquely p p_in_y,
        rcases p_has_unique_corner with ⟨p_corner, p_corner_in_T', p_in_p_corner, p_corner_unique⟩,
      by_cases p_lt_corner0_add_one : p.nth j < corner0.nth j + 1,
      { left,
        have p_in_corner0 : in_cube corner0 p :=
          begin
            rw in_cube,
            intro i,
            replace p_in_line1 := p_in_line1 i,
            cases p_in_line1,
            rw in_cube at x_j_set_to_y_in_corner0,
            simp only [not_exists, ge_iff_le, vector.nth_of_fn] at x_j_set_to_y_in_corner0,
            replace x_j_set_to_y_in_corner0 := x_j_set_to_y_in_corner0 i,
            by_cases i_eq_j : i = j,
            { replace p_in_line1_left := p_in_line1_left i_eq_j,
              rw i_eq_j,
              rw [if_pos i_eq_j, i_eq_j] at x_j_set_to_y_in_corner0,
              clear_except x_j_set_to_y_in_corner0 p_in_line1_left p_lt_corner0_add_one,
              exact ⟨by linarith, p_lt_corner0_add_one⟩,
            },
            rename i_eq_j i_ne_j,
            have p_eq_x := p_in_line1_right i_ne_j,
            rw p_eq_x,
            rw [if_neg i_ne_j] at x_j_set_to_y_in_corner0,
            exact x_j_set_to_y_in_corner0,
          end,
        split, exact p_in_corner0,
        intros alt_corner alt_corner_in_T' p_in_alt_corner,
        have p_corner_eq_alt_corner := p_corner_unique alt_corner alt_corner_in_T' p_in_alt_corner,
        have p_corner_eq_corner0 := p_corner_unique corner0 corner0_in_T' p_in_corner0,
        rw [← p_corner_eq_alt_corner, ← p_corner_eq_corner0],
      },
      rename p_lt_corner0_add_one p_ge_corner0_add_one,
      simp only [not_lt] at p_ge_corner0_add_one,
      right,
      have p_in_corner1 : in_cube corner1 p :=
        begin
          rw in_cube,
          intro i,
          replace p_in_line1 := p_in_line1 i,
          cases p_in_line1,
          rw in_cube at x_j_set_to_y_add_one_in_corner1,
          simp only [not_exists, ge_iff_le, vector.nth_of_fn] at x_j_set_to_y_add_one_in_corner1,
          replace x_j_set_to_y_add_one_in_corner1 := x_j_set_to_y_add_one_in_corner1 i,
          by_cases i_eq_j : i = j,
          { replace p_in_line1_left := p_in_line1_left i_eq_j,
            rw i_eq_j,
            rw [if_pos i_eq_j, i_eq_j] at x_j_set_to_y_add_one_in_corner1,
            rw corner0_add_one_eq_corner1_at_j at p_ge_corner0_add_one,
            clear_except x_j_set_to_y_add_one_in_corner1 p_in_line1_left p_ge_corner0_add_one,
            exact ⟨p_ge_corner0_add_one, by linarith⟩,
          },
          rename i_eq_j i_ne_j,
          have p_eq_x := p_in_line1_right i_ne_j,
          rw p_eq_x,
          rw [if_neg i_ne_j] at x_j_set_to_y_add_one_in_corner1,
          exact x_j_set_to_y_add_one_in_corner1,
        end,
      split, exact p_in_corner1,
      intros alt_corner alt_corner_in_T' p_in_alt_corner,
      have p_corner_eq_alt_corner := p_corner_unique alt_corner alt_corner_in_T' p_in_alt_corner,
      have p_corner_eq_corner1 := p_corner_unique corner1 corner1_in_T' p_in_corner1,
      rw [← p_corner_eq_alt_corner, ← p_corner_eq_corner1],
    end,
  --Build corner2, which will contain x_j_set_to_y_sub_one
  let corner2 :=
    add_vectors corner1_core (int_point_to_point (double_int_vector (add_int_vectors corner1_offset (int_neg_unit_basis_vector j)))),
  have corner2_in_T' : corner2 ∈ T' :=
    by {use [corner1_core, corner1_core_in_T_core, (add_int_vectors corner1_offset (int_neg_unit_basis_vector j))],},
  have line2_uniquely_covered : ∀ p ∈ line2,
    (in_cube corner0 p ∧ (∀ alt_corner ∈ T', in_cube alt_corner p → corner0 = alt_corner)) ∨
    (in_cube corner2 p ∧ (∀ alt_corner ∈ T', in_cube alt_corner p → corner2 = alt_corner)) :=
    line2_uniquely_covered_cube_induction_step_neg_helper d d_gt_zero T T_is_tiling T_faceshare_free j y x x_in_y_sub_ej corner0
      corner0_core corner0_offset corner0_def corner1 corner1_core corner1_offset corner1_def corner0_add_one_eq_corner1_at_j
      T'_covers_y_uniquely x_j_set_to_y_in_y x_j_set_to_y_add_one_in_y corner0_in_T' x_j_set_to_y_in_corner0 corner0_unique
      corner0_core_in_T_core corner1_in_T' x_j_set_to_y_add_one_in_corner1 corner1_unique corner1_core_in_T_core
      line1_uniquely_covered corner2_in_T',
  have x_in_line2 : x ∈ line2 :=
    begin
      intro i,
      split,
      { intro i_eq_j,
        replace x_in_y_sub_ej := x_in_y_sub_ej j,
        rw [int_neg_unit_basis_vector, add_int_vectors] at x_in_y_sub_ej,
        simp only [if_true, sub_add_cancel, ge_iff_le, eq_self_iff_true, int.cast_one, vector.nth_of_fn, int.add_neg_one, int.cast_sub]
          at x_in_y_sub_ej,
        exact x_in_y_sub_ej,
      },
      intro,
      refl,
    end,
  replace line2_uniquely_covered := line2_uniquely_covered x x_in_line2,
  cases line2_uniquely_covered with x_uniquely_in_corner0 x_uniquely_in_corner2,
  { use [corner0, corner0_in_T'],
    exact x_uniquely_in_corner0,
  },
  use [corner2, corner2_in_T'],
  exact x_uniquely_in_corner2,
end

lemma T'_is_tiling (d : ℕ) (d_gt_zero : d > 0) (T : set (point d)) (T_is_tiling : is_tiling T) (T_faceshare_free : tiling_faceshare_free T) :
  let core_points : set (point d) :=
        {x :
           point d | ∀ (i : fin d),
           vector.nth x i = 0 ∨ vector.nth x i = 1},
      T_core : set (point d) :=
        {t ∈ T | ∃ (p : point d) (H : p ∈ core_points), in_cube t p},
      T' : set (point d) :=
        {t' :
           point d | ∃ (t : point d) (H : t ∈ T_core) (x : int_point d),
           t' = add_vectors t (int_point_to_point (double_int_vector x))}
  in (∀ (x : point d),
        (∀ (i : fin d), vector.nth x i ≥ 0 ∧ vector.nth x i ≤ 1) →
        (∃ (t' : point d) (H : t' ∈ T'),
           in_cube t' x ∧
             ∀ (alt_t' : point d),
               alt_t' ∈ T' → in_cube alt_t' x → t' = alt_t')) →
     is_tiling T' :=
begin
  intros core_points T_core T' T'_covers_core,
  rw is_tiling,
  intro x,
  let z : int_point d := vector.of_fn (λ j : fin d, int.floor(x.nth j)),
  let z_approx : ℕ → int_point d :=
    λ approx_num : ℕ,
      if(approx_num ≥ d) then z
      else vector.of_fn (λ j : fin d, if(j.val < approx_num) then z.nth j else 0),
  have cube_induction_step_pos :
    ∀ j : fin d, ∀ y : int_point d,
    (∀ x : point d, (∀ i : fin d, x.nth i ≥ y.nth i ∧ x.nth i ≤ y.nth i + 1) →
    ∃ t ∈ T', in_cube t x ∧ (∀ alt_t : point d, alt_t ∈ T' → in_cube alt_t x → t = alt_t)) →
    (∀ x : point d, (∀ i : fin d,
    x.nth i ≥ (add_int_vectors y (int_unit_basis_vector j)).nth i ∧
    x.nth i ≤ (add_int_vectors y (int_unit_basis_vector j)).nth i + 1) →
    ∃ t ∈ T', in_cube t x ∧ (∀ alt_t : point d, alt_t ∈ T' → in_cube alt_t x → t = alt_t))
    := T'_is_tiling_cube_induction_step_pos d d_gt_zero T T_is_tiling T_faceshare_free,
  have cube_induction_step_neg :
    ∀ j : fin d, ∀ y : int_point d,
    (∀ x : point d, (∀ i : fin d, x.nth i ≥ y.nth i ∧ x.nth i ≤ y.nth i + 1) →
    ∃ t ∈ T', in_cube t x ∧ (∀ alt_t : point d, alt_t ∈ T' → in_cube alt_t x → t = alt_t)) →
    (∀ x : point d, (∀ i : fin d,
    x.nth i ≥ (add_int_vectors y (int_neg_unit_basis_vector j)).nth i ∧
    x.nth i ≤ (add_int_vectors y (int_neg_unit_basis_vector j)).nth i + 1) →
    ∃ t ∈ T', in_cube t x ∧ (∀ alt_t : point d, alt_t ∈ T' → in_cube alt_t x → t = alt_t))
    := T'_is_tiling_cube_induction_step_neg d d_gt_zero T T_is_tiling T_faceshare_free,
  have axis_induction_step_pos :
    ∀ j : fin d, ∀ y : int_point d,
    (∀ x : point d, (∀ i : fin d, x.nth i ≥ y.nth i ∧ x.nth i ≤ y.nth i + 1) →
    ∃ t ∈ T', in_cube t x ∧ (∀ alt_t : point d, alt_t ∈ T' → in_cube alt_t x → t = alt_t)) →
    (∀ z : ℕ,
    (∀ x : point d, (∀ i : fin d,
    x.nth i ≥ (add_int_vectors y (int_scaled_basis_vector z j)).nth i ∧
    x.nth i ≤ (add_int_vectors y (int_scaled_basis_vector z j)).nth i + 1) →
    ∃ t ∈ T', in_cube t x ∧ (∀ alt_t : point d, alt_t ∈ T' → in_cube alt_t x → t = alt_t))) :=
    begin
      intros j y source_cube_covered z,
      induction z with z ih,
      { conv
        begin
          find ↑((add_int_vectors y (int_scaled_basis_vector ↑0 _)).nth _) {rw [int_scaled_basis_vector, add_int_vectors],},
          find ↑((add_int_vectors y (int_scaled_basis_vector ↑0 _)).nth _) {rw [int_scaled_basis_vector, add_int_vectors],},
        end,
        simp only [if_t_t, add_zero, int.cast_zero, int.coe_nat_zero, vector.nth_of_fn],
        exact source_cube_covered,
      },
      replace cube_induction_step_pos := cube_induction_step_pos j (add_int_vectors y (int_scaled_basis_vector ↑z j)) ih,
      have int_scaled_basis_vector_z_succ_val :
        int_scaled_basis_vector ↑(z.succ) j =
        add_int_vectors (int_scaled_basis_vector ↑z j) (int_unit_basis_vector j) :=
        begin
          apply vector.ext,
          intro k,
          rw [int_unit_basis_vector, int_scaled_basis_vector, int_scaled_basis_vector, add_int_vectors],
          simp only [int.coe_nat_succ, vector.nth_of_fn],
          by_cases j_eq_k : j = k,
          { rw j_eq_k,
            simp only [int.cast_add, if_true, eq_self_iff_true, int.cast_one],
          },
          repeat{rw if_neg j_eq_k},
          norm_num,
        end,
      rw [add_int_vectors_assoc, ← int_scaled_basis_vector_z_succ_val] at cube_induction_step_pos,
      exact cube_induction_step_pos,
    end,
  have axis_induction_step_neg :
    ∀ j : fin d, ∀ y : int_point d,
    (∀ x : point d, (∀ i : fin d, x.nth i ≥ y.nth i ∧ x.nth i ≤ y.nth i + 1) →
    ∃ t ∈ T', in_cube t x ∧ (∀ alt_t : point d, alt_t ∈ T' → in_cube alt_t x → t = alt_t)) →
    (∀ z : ℕ,
    (∀ x : point d, (∀ i : fin d,
    x.nth i ≥ (add_int_vectors y (int_scaled_basis_vector (-z) j)).nth i ∧
    x.nth i ≤ (add_int_vectors y (int_scaled_basis_vector (-z) j)).nth i + 1) →
    ∃ t ∈ T', in_cube t x ∧ (∀ alt_t : point d, alt_t ∈ T' → in_cube alt_t x → t = alt_t))) :=
    begin
      intros j y source_cube_covered z,
      induction z with z ih,
      { conv
        begin
          find ↑((add_int_vectors y (int_scaled_basis_vector (-↑0) _)).nth _) {rw [int_scaled_basis_vector, add_int_vectors],},
          find ↑((add_int_vectors y (int_scaled_basis_vector (-↑0) _)).nth _) {rw [int_scaled_basis_vector, add_int_vectors],},
        end,
        simp only [if_t_t, add_zero, int.cast_zero, int.coe_nat_zero, vector.nth_of_fn, neg_zero],
        exact source_cube_covered,
      },
      replace cube_induction_step_pos := cube_induction_step_neg j (add_int_vectors y (int_scaled_basis_vector (-↑z) j)) ih,
      have int_scaled_basis_vector_z_succ_val :
        int_scaled_basis_vector (-↑(z.succ)) j =
        add_int_vectors (int_scaled_basis_vector (-↑z) j) (int_neg_unit_basis_vector j) :=
        begin
          apply vector.ext,
          intro k,
          rw [int_neg_unit_basis_vector, int_scaled_basis_vector, int_scaled_basis_vector, add_int_vectors],
          simp only [int.coe_nat_succ, vector.nth_of_fn],
          by_cases j_eq_k : j = k,
          { rw j_eq_k,
            simp only [if_true, eq_self_iff_true, neg_add_rev, int.add_neg_one],
            rw add_comm,
            norm_num,
          },
          repeat{rw if_neg j_eq_k},
          norm_num,
        end,
      rw [add_int_vectors_assoc, ← int_scaled_basis_vector_z_succ_val] at cube_induction_step_pos,
      exact cube_induction_step_pos,
    end,
  have axis_induction_step :
    ∀ j : fin d, ∀ y : int_point d,
    (∀ x : point d, (∀ i : fin d, x.nth i ≥ y.nth i ∧ x.nth i ≤ y.nth i + 1) →
    ∃ t ∈ T', in_cube t x ∧ (∀ alt_t : point d, alt_t ∈ T' → in_cube alt_t x → t = alt_t)) →
    (∀ z : ℤ,
    (∀ x : point d, (∀ i : fin d,
    x.nth i ≥ (add_int_vectors y (int_scaled_basis_vector z j)).nth i ∧
    x.nth i ≤ (add_int_vectors y (int_scaled_basis_vector z j)).nth i + 1) →
    ∃ t ∈ T', in_cube t x ∧ (∀ alt_t : point d, alt_t ∈ T' → in_cube alt_t x → t = alt_t))) :=
    begin
      intros j y source_cube_covered z,
      by_cases z_ge_zero : z ≥ 0,
      { have z'_def : ∃ z' : ℕ, ↑z' = z := can_lift.prf z z_ge_zero,
        cases z'_def with z' z'_def,
        rw ← z'_def,
        exact axis_induction_step_pos j y source_cube_covered z',
      },
      rename z_ge_zero z_le_zero,
      replace z_le_zero := le_of_lt (lt_of_not_ge z_le_zero),
      have neg_z_ge_zero : -z ≥ 0 := by linarith,
      have z'_def : ∃ z' : ℕ, ↑z' = -z := can_lift.prf (-z) neg_z_ge_zero,
      cases z'_def with z' z'_def,
      replace z'_def : -↑z' = z := by linarith,
      rw ← z'_def,
      exact axis_induction_step_neg j y source_cube_covered z',
    end,
  have z_approx_induction :
    ∀ approx_num : ℕ, ∀ x : point d,
    (∀ i : fin d, x.nth i ≥ (z_approx approx_num).nth i ∧ x.nth i ≤ (z_approx approx_num).nth i + 1) →
    ∃ t ∈ T', in_cube t x ∧ (∀ alt_t : point d, alt_t ∈ T' → in_cube alt_t x → t = alt_t) :=
    begin
      intro approx_num,
      induction approx_num with approx_num ih,
      { dsimp only[z_approx],
        have not_zero_ge_d : ¬(0 ≥ d) := by linarith,
        rw if_neg not_zero_ge_d,
        simp only [nat.not_lt_zero, int.cast_zero, vector.nth_of_fn, if_false, zero_add],
        exact T'_covers_core,
      },
      by_cases approx_num_ge_d : approx_num ≥ d,
      { have approx_num_succ_ge_d : approx_num.succ ≥ d := by {rw ← nat.add_one, linarith,},
        have next_z_approx_val : (z_approx approx_num.succ) = z_approx approx_num :=
          begin
            dsimp only[z_approx],
            rw [if_pos approx_num_succ_ge_d, if_pos approx_num_ge_d],
          end,
        rw next_z_approx_val,
        exact ih,
      },
      rename approx_num_ge_d approx_num_lt_d,
      replace approx_num_lt_d := lt_of_not_ge approx_num_lt_d,
      let fin_approx_num : fin d := ⟨approx_num, approx_num_lt_d⟩,
      have next_z_approx_val :
        (z_approx approx_num.succ) = add_int_vectors (z_approx approx_num) (int_scaled_basis_vector (z.nth fin_approx_num) fin_approx_num) :=
        begin
          apply vector.ext,
          intro i,
          dsimp only[z_approx],
          rw [int_scaled_basis_vector, add_int_vectors],
          simp only [ge_iff_le, vector.nth_of_fn],
          have not_d_le_approx_num : ¬(d ≤ approx_num) := by linarith,
          rw if_neg not_d_le_approx_num,
          simp only [ge_iff_le, vector.nth_of_fn],
          by_cases d_le_approx_num_succ : d ≤ approx_num.succ,
          { rw if_pos d_le_approx_num_succ,
            simp only [vector.nth_of_fn],
            rw ← nat.add_one at d_le_approx_num_succ,
            have d_eq_approx_num_succ : d = approx_num + 1 := by {clear fin_approx_num, omega,},
            have i_lt_d := i.property,
            replace i_lt_d : i.val < approx_num + 1 := by linarith,
            replace i_lt_d := eq_or_lt_of_le (nat_le_of_lt_add_one i_lt_d),
            cases i_lt_d with i_eq_approx_num i_lt_approx_num,
            { have not_i_lt_approx_num : ¬(i.val < approx_num) := by linarith,
              have fin_approx_num_eq_i : fin_approx_num = i := fin.ext (eq.symm i_eq_approx_num),
              rw [if_neg not_i_lt_approx_num, if_pos fin_approx_num_eq_i, fin_approx_num_eq_i],
              simp only [zero_add],
            },
            have fin_approx_num_ne_i : ¬(fin_approx_num = i) :=
              begin
                intro fin_approx_num_eq_i,
                rw ← fin_approx_num_eq_i at i_lt_approx_num,
                linarith,
              end,
            rw [if_pos i_lt_approx_num, if_neg fin_approx_num_ne_i],
            simp only [add_zero],
          },
          rw if_neg d_le_approx_num_succ,
          simp only [vector.nth_of_fn],
          by_cases i_lt_approx_num_succ : i.val < approx_num.succ,
          { rw if_pos i_lt_approx_num_succ,
            rw ← nat.add_one at i_lt_approx_num_succ,
            replace i_lt_approx_num_succ := eq_or_lt_of_le (nat_le_of_lt_add_one i_lt_approx_num_succ),
            cases i_lt_approx_num_succ with i_eq_approx_num i_lt_approx_num,
            { have fin_approx_num_eq_i : fin_approx_num = i := fin.ext (eq.symm i_eq_approx_num),
              have not_i_lt_approx_num : ¬(i.val < approx_num) := by {clear_except i_eq_approx_num, linarith,},
              rw [if_pos fin_approx_num_eq_i, if_neg not_i_lt_approx_num, zero_add, fin_approx_num_eq_i],
            },
            have fin_approx_num_ne_i : ¬(fin_approx_num = i) :=
              begin
                intro fin_approx_num_eq_i,
                rw ← fin_approx_num_eq_i at i_lt_approx_num,
                clear_except i_lt_approx_num,
                linarith,
              end,
            rw [if_pos i_lt_approx_num, if_neg fin_approx_num_ne_i, add_zero],
          },
          have not_i_lt_approx_num : ¬(i.val < approx_num) := by {clear_except i_lt_approx_num_succ, omega,},
          have fin_approx_num_ne_i : ¬(fin_approx_num = i) :=
            begin
              intro fin_approx_num_eq_i,
              rw [← fin_approx_num_eq_i, ← nat.add_one] at i_lt_approx_num_succ,
              clear_except i_lt_approx_num_succ,
              linarith,
            end,
          rw [if_neg i_lt_approx_num_succ, if_neg not_i_lt_approx_num, if_neg fin_approx_num_ne_i, zero_add],
        end,
      rw next_z_approx_val,
      exact axis_induction_step fin_approx_num (z_approx approx_num) ih (z.nth fin_approx_num),
    end,
  have x_in_cube_z : ∀ i : fin d, vector.nth x i ≥ ↑(vector.nth z i) ∧ vector.nth x i ≤ ↑(vector.nth z i) + 1 :=
    begin
      intro i,
      dsimp[z],
      simp only [ge_iff_le, vector.nth_of_fn],
      exact ⟨int.floor_le (x.nth i), le_of_lt (int.lt_floor_add_one (x.nth i))⟩,
    end,
  have z_approx_d_val : z_approx d = z :=
    begin
      dsimp[z_approx],
      rw if_pos,
      have d_eq_d : d = d := by refl,
      exact ge_of_eq d_eq_d,
    end,
  rw ← z_approx_d_val at x_in_cube_z,
  replace z_approx_induction := z_approx_induction d x x_in_cube_z,
  rcases z_approx_induction with ⟨corner, H, ⟨x_in_corner, corner_unique⟩⟩,
  use [corner, H],
  split, {rw [cube, set.mem_set_of_eq], exact x_in_corner,},
  intros alt_t alt_t_in_T' x_in_cube_alt_t,
  rw [cube, set.mem_set_of_eq] at x_in_cube_alt_t,
  symmetry,
  exact corner_unique alt_t alt_t_in_T' x_in_cube_alt_t,
end

lemma T'_is_periodic_helper_lemma_helper
  (d : ℕ) (T : set (point d)) (T_is_tiling : is_tiling T) (T_faceshare_free : tiling_faceshare_free T)
  (x y : int_point d) (x_core_point_corner' : point d) (zero_vector : int_point d) :
  let core_points : set (point d) :=
        {x :
           point d | ∀ (i : fin d),
           vector.nth x i = 0 ∨ vector.nth x i = 1},
      T_core : set (point d) :=
        {t ∈ T | ∃ (p : point d) (H : p ∈ core_points), in_cube t p},
      T' : set (point d) :=
        {t' :
           point d | ∃ (t : point d) (H : t ∈ T_core) (x : int_point d),
           t' = add_vectors t (int_point_to_point (double_int_vector x))}
  in (∀ (x : point d),
        (∀ (i : fin d), vector.nth x i ≥ 0 ∧ vector.nth x i ≤ 1) →
        (∃ (t' : point d) (H : t' ∈ T'),
           in_cube t' x ∧
             ∀ (alt_t' : point d),
               alt_t' ∈ T' → in_cube alt_t' x → t' = alt_t')) →
     ∀ (T'_is_tiling : is_tiling T'),
       (let x_add_2y_corner : {corner // corner ∈ T' ∧
               int_point_to_point (add_int_vectors x (double_int_vector y)) ∈
                   cube corner ∧
                 ∀ (alt_corner : point d),
                   alt_corner ∈ T' →
                   int_point_to_point
                       (add_int_vectors x (double_int_vector y)) ∈
                     cube alt_corner →
                   alt_corner = corner} :=
              int_point_to_corner T'_is_tiling
                (add_int_vectors x (double_int_vector y))
        in x_add_2y_corner =
             int_point_to_corner T'_is_tiling
               (add_int_vectors x (double_int_vector y)) →
           (let x_corner : {corner // corner ∈ T' ∧
                   int_point_to_point x ∈ cube corner ∧
                     ∀ (alt_corner : point d),
                       alt_corner ∈ T' →
                       int_point_to_point x ∈ cube alt_corner →
                       alt_corner = corner} :=
                  int_point_to_corner T'_is_tiling x
            in x_corner = int_point_to_corner T'_is_tiling x →
               (let x_corner_add_2y : vector ℝ d :=
                      add_vectors x_corner.val
                        (int_point_to_point (double_int_vector y))
                in x_corner_add_2y =
                     add_vectors x_corner.val
                       (int_point_to_point (double_int_vector y)) →
                   x_add_2y_corner.val ∈ T' →
                   int_point_to_point
                       (add_int_vectors x (double_int_vector y)) ∈
                     cube x_add_2y_corner.val →
                   (∀ (alt_corner : point d),
                      alt_corner ∈ T' →
                      int_point_to_point
                          (add_int_vectors x (double_int_vector y)) ∈
                        cube alt_corner →
                      alt_corner = x_add_2y_corner.val) →
                   x_corner.val ∈ T' →
                   int_point_to_point x ∈ cube x_corner.val →
                   (∀ (alt_corner : point d),
                      alt_corner ∈ T' →
                      int_point_to_point x ∈ cube alt_corner →
                      alt_corner = x_corner.val) →
                   (let x_core_point : point d :=
                          vector.of_fn
                            (λ (i : fin d), ↑(vector.nth x i % 2)),
                        x_core_point_corner : {corner // corner ∈ T' ∧
                           x_core_point ∈ cube corner ∧
                             ∀ (alt_corner : point d),
                               alt_corner ∈ T' →
                               x_core_point ∈ cube alt_corner →
                               alt_corner = corner} :=
                          point_to_corner T'_is_tiling x_core_point
                    in x_core_point ∈ cube x_core_point_corner.val →
                       (∀ (alt_corner : point d),
                          alt_corner ∈ T' →
                          x_core_point ∈ cube alt_corner →
                          alt_corner = x_core_point_corner.val) →
                       x_core_point_corner' ∈ T_core →
                       x_core_point_corner.val =
                         add_vectors x_core_point_corner'
                           (int_point_to_point
                              (double_int_vector zero_vector)) →
                       ∀ (i : fin d), vector.nth zero_vector i = 0)))) :=
begin
  intros core_points T_core T' T'_covers_core T'_is_tiling x_add_2y_corner x_add_2y_corner_def x_corner x_corner_def
    x_corner_add_2y x_corner_add_2y_def x_add_2y_corner_in_T' x_add_2y_in_x_add_2y_corner x_add_2y_corner_unique x_corner_in_T'
    x_in_x_corner x_corner_unique x_core_point x_core_point_corner x_core_point_in_x_core_point_corner
    x_core_point_corner_unique x_core_point_corner'_in_T_core x_core_point_corner_def,
    intro i,
    rcases x_core_point_corner'_in_T_core with
      ⟨x_core_point_corner'_in_T, x_core_point', x_core_point'_in_core_points, x_core_point'_in_x_core_point_corner'⟩,
    rw in_cube at x_core_point'_in_x_core_point_corner',
    replace x_core_point'_in_x_core_point_corner' := x_core_point'_in_x_core_point_corner' i,
    replace x_core_point'_in_core_points := x_core_point'_in_core_points i,
    have x_core_point'_ge_zero : vector.nth x_core_point' i ≥ 0 :=
      by {cases x_core_point'_in_core_points, linarith, linarith,},
    have x_core_point'_le_one : vector.nth x_core_point' i ≤ 1 :=
      by {cases x_core_point'_in_core_points, linarith, linarith,},
    cases x_core_point'_in_x_core_point_corner' with x_core_point_corner'_le_one neg_one_lt_x_core_point_corner',
    replace x_core_point_corner'_le_one : x_core_point_corner'.nth i ≤ 1 := by linarith,
    replace neg_one_lt_x_core_point_corner' : -1 < x_core_point_corner'.nth i := by linarith,
    rw cube at x_core_point_in_x_core_point_corner,
    simp at x_core_point_in_x_core_point_corner,
    rw in_cube at x_core_point_in_x_core_point_corner,
    simp at x_core_point_in_x_core_point_corner,
    replace x_core_point_in_x_core_point_corner := x_core_point_in_x_core_point_corner i,
    dsimp[x_core_point] at x_core_point_in_x_core_point_corner,
    have x_mod_two_ge_zero : ↑(vector.nth x i % 2) ≥ (0 : ℝ) :=
      begin
        by_cases x_mod_two_eq_zero : vector.nth x i % 2 = 0,
        { have coe_goal : vector.nth x i % 2 ≥ 0 := by linarith,
          assumption_mod_cast,
        },
        rw int.mod_two_ne_zero at x_mod_two_eq_zero,
        have coe_goal : vector.nth x i % 2 ≥ 0 := by linarith,
        assumption_mod_cast,
      end,
    have x_mod_two_le_one : ↑(vector.nth x i % 2) ≤ (1 : ℝ) :=
      begin
        by_cases x_mod_two_eq_zero : vector.nth x i % 2 = 0,
        { have coe_goal : vector.nth x i % 2 ≤ 1 := by linarith,
          assumption_mod_cast,
        },
        rw int.mod_two_ne_zero at x_mod_two_eq_zero,
        have coe_goal : vector.nth x i % 2 ≤ 1 := by linarith,
        assumption_mod_cast,
      end,
    change vector.nth x_core_point_corner.val i ≤ ↑(vector.nth x i % 2) ∧
            ↑(vector.nth x i % 2) < vector.nth x_core_point_corner.val i + 1 at x_core_point_in_x_core_point_corner,
    cases x_core_point_in_x_core_point_corner with x_core_point_corner_le_one neg_one_lt_x_core_point_corner,
    replace x_core_point_corner_le_one : vector.nth x_core_point_corner.val i ≤ 1 := by linarith,
    replace neg_one_lt_x_core_point_corner : -1 < vector.nth x_core_point_corner.val i := by linarith,

    have x_core_point_corner_def_at_i :
      vector.nth x_core_point_corner.val i =
      (add_vectors x_core_point_corner' (int_point_to_point (double_int_vector zero_vector))).nth i
      := by {rw x_core_point_corner_def,},
    rw [double_int_vector, add_vectors] at x_core_point_corner_def_at_i,
    simp at x_core_point_corner_def_at_i,
    conv at x_core_point_corner_def_at_i
    begin
      find (int_point_to_point _) {rw int_point_to_point},
    end,
    simp at x_core_point_corner_def_at_i,
    change vector.nth x_core_point_corner.val i = vector.nth x_core_point_corner' i + 2 * ↑(vector.nth zero_vector i)
      at x_core_point_corner_def_at_i,
    have zero_vector_possibilities := eq_or_lt_or_gt (zero_vector.nth i) 0,
    rcases zero_vector_possibilities with _ | _ | _, {exact zero_vector_possibilities,},
    { replace zero_vector_possibilities : zero_vector.nth i < -1 + 1 := by linarith,
      replace zero_vector_possibilities := int.le_of_lt_add_one zero_vector_possibilities,
      replace zero_vector_possibilities : ↑(vector.nth zero_vector i) ≤ (-1 : ℝ) := by assumption_mod_cast,
      linarith,
    },
    have zero_le_zero_vector : 0 < (zero_vector.nth i - 1) + 1 := by linarith,
    replace zero_le_zero_vector := int.le_of_lt_add_one zero_le_zero_vector,
    replace zero_le_zero_vector : 1 ≤ zero_vector.nth i := by linarith,
    replace zero_le_zero_vector : (1 : ℝ) ≤ ↑(zero_vector.nth i) := by assumption_mod_cast,
    linarith,
end

lemma T'_is_periodic_helper_lemma
  (d : ℕ) (T : set (point d)) (T_is_tiling : is_tiling T) (T_faceshare_free : tiling_faceshare_free T)
  (x y : int_point d) :
  let core_points : set (point d) :=
        {x :
           point d | ∀ (i : fin d),
           vector.nth x i = 0 ∨ vector.nth x i = 1},
      T_core : set (point d) :=
        {t ∈ T | ∃ (p : point d) (H : p ∈ core_points), in_cube t p},
      T' : set (point d) :=
        {t' :
           point d | ∃ (t : point d) (H : t ∈ T_core) (x : int_point d),
           t' = add_vectors t (int_point_to_point (double_int_vector x))}
  in (∀ (x : point d),
        (∀ (i : fin d), vector.nth x i ≥ 0 ∧ vector.nth x i ≤ 1) →
        (∃ (t' : point d) (H : t' ∈ T'),
           in_cube t' x ∧
             ∀ (alt_t' : point d),
               alt_t' ∈ T' → in_cube alt_t' x → t' = alt_t')) →
     ∀ (T'_is_tiling : is_tiling T'),
       (let x_add_2y_corner : {corner // corner ∈ T' ∧
               int_point_to_point (add_int_vectors x (double_int_vector y)) ∈
                   cube corner ∧
                 ∀ (alt_corner : point d),
                   alt_corner ∈ T' →
                   int_point_to_point
                       (add_int_vectors x (double_int_vector y)) ∈
                     cube alt_corner →
                   alt_corner = corner} :=
              int_point_to_corner T'_is_tiling
                (add_int_vectors x (double_int_vector y))
        in x_add_2y_corner =
             int_point_to_corner T'_is_tiling
               (add_int_vectors x (double_int_vector y)) →
           (let x_corner : {corner // corner ∈ T' ∧
                   int_point_to_point x ∈ cube corner ∧
                     ∀ (alt_corner : point d),
                       alt_corner ∈ T' →
                       int_point_to_point x ∈ cube alt_corner →
                       alt_corner = corner} :=
                  int_point_to_corner T'_is_tiling x
            in x_corner = int_point_to_corner T'_is_tiling x →
               (let x_corner_add_2y : vector ℝ d :=
                      add_vectors x_corner.val
                        (int_point_to_point (double_int_vector y))
                in x_corner_add_2y =
                     add_vectors x_corner.val
                       (int_point_to_point (double_int_vector y)) →
                   x_add_2y_corner.val ∈ T' →
                   int_point_to_point
                       (add_int_vectors x (double_int_vector y)) ∈
                     cube x_add_2y_corner.val →
                   (∀ (alt_corner : point d),
                      alt_corner ∈ T' →
                      int_point_to_point
                          (add_int_vectors x (double_int_vector y)) ∈
                        cube alt_corner →
                      alt_corner = x_add_2y_corner.val) →
                   x_corner.val ∈ T' →
                   int_point_to_point x ∈ cube x_corner.val →
                   (∀ (alt_corner : point d),
                      alt_corner ∈ T' →
                      int_point_to_point x ∈ cube alt_corner →
                      alt_corner = x_corner.val) →
                   x_corner_add_2y ∈ T'))) :=
begin
  intros core_points T_core T' T'_covers_core T'_is_tiling x_add_2y_corner x_add_2y_corner_def x_corner x_corner_def
  x_corner_add_2y x_corner_add_2y_def x_add_2y_corner_in_T' x_add_2y_in_x_add_2y_corner x_add_2y_corner_unique x_corner_in_T'
  x_in_x_corner x_corner_unique,
  change ∃ t ∈ T_core, ∃ z : int_point d, x_corner_add_2y = add_vectors t (int_point_to_point (double_int_vector z)),
  let x_core_point : point d := vector.of_fn(λ i : fin d, ↑((x.nth i) % 2)),
  let x_core_point_corner := point_to_corner T'_is_tiling x_core_point,
  have x_core_point_corner_prop := x_core_point_corner.property,
  rcases x_core_point_corner_prop with
    ⟨x_core_point_corner_in_T', x_core_point_in_x_core_point_corner, x_core_point_corner_unique⟩,
  have x_core_point_corner_in_T_core : x_core_point_corner.val ∈ T_core :=
    begin
      rcases x_core_point_corner_in_T' with
        ⟨x_core_point_corner', x_core_point_corner'_in_T_core, zero_vector, x_core_point_corner_def⟩,
      have zero_vector_def : ∀ i : fin d, zero_vector.nth i = 0 :=
        begin
          exact T'_is_periodic_helper_lemma_helper d T T_is_tiling T_faceshare_free x y x_core_point_corner' zero_vector
            T'_covers_core T'_is_tiling x_add_2y_corner_def x_corner_def x_corner_add_2y_def x_add_2y_corner_in_T'
            x_add_2y_in_x_add_2y_corner x_add_2y_corner_unique x_corner_in_T' x_in_x_corner x_corner_unique
            x_core_point_in_x_core_point_corner x_core_point_corner_unique x_core_point_corner'_in_T_core x_core_point_corner_def,
        end,
      have x_core_point_corner_eq_x_core_point_corner' : x_core_point_corner.val = x_core_point_corner' :=
        begin
          apply vector.ext,
          intro i,
          rw [x_core_point_corner_def, double_int_vector, int_point_to_point, add_vectors],
          simp,
          exact zero_vector_def i,
        end,
      rw x_core_point_corner_eq_x_core_point_corner',
      exact x_core_point_corner'_in_T_core,
    end,
  let z := vector.of_fn (λ i : fin d, (y.nth i) + ((↑(x.nth i) - ↑((x.nth i) % 2)) / 2)),
  let double_z_without_y := vector.of_fn (λ i : fin d, ((↑(x.nth i) : ℝ) - ↑((x.nth i) % 2))),
  have x_corner_eq_x_core_point_corner_add_z_without_y : x_corner.val = add_vectors x_core_point_corner.val double_z_without_y :=
    begin
      let x_core_point_corner_add_z_without_y := add_vectors x_core_point_corner.val double_z_without_y,
      have x_core_point_corner_add_z_without_y_in_T' : x_core_point_corner_add_z_without_y ∈ T' :=
        begin
          let int_double_z_without_y := vector.of_fn (λ i : fin d, (x.nth i - (x.nth i % 2)) / 2),
          use [x_core_point_corner.val, x_core_point_corner_in_T_core, int_double_z_without_y],
          dsimp[x_core_point_corner_add_z_without_y],
          rw [double_int_vector, add_vectors, add_vectors],
          apply vector.ext,
          intro i,
          simp,
          rw int_point_to_point,
          simp,
          have x_sub_x_mod_2_is_even : even (vector.nth x i - vector.nth x i % 2) :=
            begin
              have even_or_odd := int.even_or_odd (vector.nth x i),
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
          have rhs_rw := mul_div_two_of_even x_sub_x_mod_2_is_even,
          have coe_rhs_rw : (2 : ℝ) * ↑((vector.nth x i - vector.nth x i % 2) / 2) = ↑(vector.nth x i - vector.nth x i % 2) :=
            by assumption_mod_cast,
          rw coe_rhs_rw,
          have coe_goal : (vector.nth x i) - (vector.nth x i) % 2 = (vector.nth x i - vector.nth x i % 2) := by refl,
          assumption_mod_cast,
        end,
      have x_in_x_core_point_corner_add_z_without_y : int_point_to_point x ∈ cube x_core_point_corner_add_z_without_y :=
        begin
          rw cube,
          simp only [set.mem_set_of_eq],
          rw in_cube,
          intro i,
          dsimp[x_core_point_corner_add_z_without_y],
          rw add_vectors,
          simp only [vector.nth_of_fn],
          rw cube at x_core_point_in_x_core_point_corner,
          simp only [set.mem_set_of_eq] at x_core_point_in_x_core_point_corner,
          rw in_cube at x_core_point_in_x_core_point_corner,
          replace x_core_point_in_x_core_point_corner := x_core_point_in_x_core_point_corner i,
          simp only [not_lt, not_le, vector.nth_of_fn, subtype.val_eq_coe] at x_core_point_in_x_core_point_corner,
          cases x_core_point_in_x_core_point_corner,
          rw int_point_to_point,
          simp only [vector.nth_of_fn],
          exact ⟨by linarith, by linarith⟩,
        end,
      symmetry,
      exact x_corner_unique x_core_point_corner_add_z_without_y x_core_point_corner_add_z_without_y_in_T'
        x_in_x_core_point_corner_add_z_without_y,
    end,
  use [x_core_point_corner, x_core_point_corner_in_T_core, z],
  dsimp[x_corner_add_2y],
  apply vector.ext,
  intro i,
  rw [double_int_vector, add_vectors, double_int_vector, add_vectors],
  simp,
  conv
  begin
    find (int_point_to_point _) {rw int_point_to_point},
    find (int_point_to_point _) {rw int_point_to_point},
  end,
  simp,
  have x_corner_eq_x_core_point_corner_add_z_without_y :
    vector.nth x_corner.val i = vector.nth x_core_point_corner.val i + 2 * ↑((vector.nth x i - (vector.nth x i) % 2) / 2) :=
    begin
      rw x_corner_eq_x_core_point_corner_add_z_without_y,
      dsimp[double_z_without_y],
      rw add_vectors,
      simp,
      have x_sub_x_mod_2_is_even : even (vector.nth x i - vector.nth x i % 2) :=
        begin
          have even_or_odd := int.even_or_odd (vector.nth x i),
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
      have rhs_rw := mul_div_two_of_even x_sub_x_mod_2_is_even,
      have coe_rhs_rw : (2 : ℝ) * ↑((vector.nth x i - vector.nth x i % 2) / 2) = ↑(vector.nth x i - vector.nth x i % 2) :=
        by assumption_mod_cast,
      rw coe_rhs_rw,
      have coe_goal : (vector.nth x i) - (vector.nth x i) % 2 = (vector.nth x i - vector.nth x i % 2) := by refl,
      assumption_mod_cast,
    end,
  change vector.nth x_corner.val i + 2 * ↑(vector.nth y i) =
    vector.nth x_core_point_corner.val i + 2 * (↑(vector.nth y i) + ↑((vector.nth x i - vector.nth x i % 2) / 2)),
  linarith,
end

lemma T'_is_periodic (d : ℕ) (T : set (point d)) (T_is_tiling : is_tiling T) (T_faceshare_free : tiling_faceshare_free T) :
  let core_points : set (point d) :=
        {x :
           point d | ∀ (i : fin d),
           vector.nth x i = 0 ∨ vector.nth x i = 1},
      T_core : set (point d) :=
        {t ∈ T | ∃ (p : point d) (H : p ∈ core_points), in_cube t p},
      T' : set (point d) :=
        {t' :
           point d | ∃ (t : point d) (H : t ∈ T_core) (x : int_point d),
           t' = add_vectors t (int_point_to_point (double_int_vector x))}
  in (∀ (x : point d),
        (∀ (i : fin d), vector.nth x i ≥ 0 ∧ vector.nth x i ≤ 1) →
        (∃ (t' : point d) (H : t' ∈ T'),
           in_cube t' x ∧
             ∀ (alt_t' : point d),
               alt_t' ∈ T' → in_cube alt_t' x → t' = alt_t')) →
     ∀ (T'_is_tiling : is_tiling T'), is_periodic T'_is_tiling :=
begin
  intros core_points T_core T' T'_covers_core T'_is_tiling x y,
  let x_add_2y_corner := int_point_to_corner T'_is_tiling (add_int_vectors x (double_int_vector y)),
  have x_add_2y_corner_def : x_add_2y_corner = int_point_to_corner T'_is_tiling (add_int_vectors x (double_int_vector y)) := by refl,
  let x_corner := int_point_to_corner T'_is_tiling x,
  have x_corner_def : x_corner = int_point_to_corner T'_is_tiling x := by refl,
  let x_corner_add_2y := add_vectors x_corner.val (int_point_to_point (double_int_vector y)),
  have x_corner_add_2y_def : x_corner_add_2y = add_vectors x_corner.val (int_point_to_point (double_int_vector y)) := by refl,
  rw [← x_add_2y_corner_def, ← x_corner_def, ← x_corner_add_2y_def],
  have x_add_2y_corner_prop := x_add_2y_corner.property,
  rcases x_add_2y_corner_prop with ⟨x_add_2y_corner_in_T', x_add_2y_in_x_add_2y_corner, x_add_2y_corner_unique⟩,
  have x_corner_prop := x_corner.property,
  rcases x_corner_prop with ⟨x_corner_in_T', x_in_x_corner, x_corner_unique⟩,
  have x_corner_add_2y_in_T' : x_corner_add_2y ∈ T' :=
    begin
      exact T'_is_periodic_helper_lemma d T T_is_tiling T_faceshare_free x y T'_covers_core T'_is_tiling
        x_add_2y_corner_def x_corner_def x_corner_add_2y_def x_add_2y_corner_in_T' x_add_2y_in_x_add_2y_corner
        x_add_2y_corner_unique x_corner_in_T' x_in_x_corner x_corner_unique,
    end,
  have x_add_2y_in_x_corner_add_2y : int_point_to_point (add_int_vectors x (double_int_vector y)) ∈ cube x_corner_add_2y :=
    begin
      rw cube,
      simp,
      rw in_cube,
      intro i,
      dsimp[x_corner_add_2y],
      rw [add_vectors, add_int_vectors, double_int_vector],
      conv
      begin
        find (int_point_to_point _) {rw int_point_to_point},
        find (int_point_to_point _) {rw int_point_to_point},
      end,
      simp,
      rw cube at x_in_x_corner,
      simp at x_in_x_corner,
      rw in_cube at x_in_x_corner,
      replace x_in_x_corner := x_in_x_corner i,
      conv at x_in_x_corner
      begin
        find (int_point_to_point _) {rw int_point_to_point},
        find (int_point_to_point _) {rw int_point_to_point},
      end,
      simp at x_in_x_corner,
      cases x_in_x_corner with x_corner_le_x x_lt_x_corner_add_one,
      split, exact x_corner_le_x,
      conv
      begin
        find (int_point_to_point _) {rw int_point_to_point},
        find (int_point_to_point _) {rw int_point_to_point},
      end,
      simp only [vector.nth_of_fn, int.cast_add, int.cast_mul, int.cast_bit0, int.cast_one],
      linarith,
    end,
  symmetry,
  exact x_add_2y_corner_unique x_corner_add_2y x_corner_add_2y_in_T' x_add_2y_in_x_corner_add_2y,
end

lemma T'_faceshare_free_helper1 (d : ℕ) (T : set (point d)) (T_is_tiling : is_tiling T) (T_faceshare_free : tiling_faceshare_free T)
  (x : int_point d) (i : fin d) (x_corner x_corner_core : point d) (x_corner_core_in_T : x_corner_core ∈ T) (x_core : point d)
  (x_core_in_x_corner_core : in_cube x_corner_core x_core) (y : int_point d)
  (x_corner_def : x_corner = add_vectors x_corner_core (int_point_to_point (double_int_vector y)))
  (x_in_x_corner : int_point_to_point x ∈ cube x_corner) :
  let core_points : set (point d) :=
        {x :
           point d | ∀ (i : fin d),
           vector.nth x i = 0 ∨ vector.nth x i = 1},
      T_core : set (point d) :=
        {t ∈ T | ∃ (p : point d) (H : p ∈ core_points), in_cube t p},
      T' : set (point d) :=
        {t' :
           point d | ∃ (t : point d) (H : t ∈ T_core) (x : int_point d),
           t' = add_vectors t (int_point_to_point (double_int_vector x))},
      int_x_core : int_point d :=
        vector.of_fn (λ (i : fin d), ite (vector.nth x_core i < 1 / 2) 0 1)
  in (∀ (x : point d),
        (∀ (i : fin d), vector.nth x i ≥ 0 ∧ vector.nth x i ≤ 1) →
        (∃ (t' : point d) (H : t' ∈ T'),
           in_cube t' x ∧
             ∀ (alt_t' : point d),
               alt_t' ∈ T' → in_cube alt_t' x → t' = alt_t')) →
     ∀ (T'_is_tiling : is_tiling T'),
       is_periodic T'_is_tiling →
       is_facesharing (int_point_to_corner T'_is_tiling x).val
         (point_to_corner T'_is_tiling
            (add_vectors (int_point_to_point x) (unit_basis_vector i))).val →
       x_core ∈ core_points →
       (∀ (alt_corner : point d),
          alt_corner ∈ T' →
          int_point_to_point x ∈ cube alt_corner →
          alt_corner = x_corner) →
       x_corner_core ∈ T' →
       (∀ (i : fin d), vector.nth x_core i = ↑(vector.nth int_x_core i)) →
       x_corner_core = (int_point_to_corner T'_is_tiling int_x_core).val →
       add_vectors (int_point_to_corner T'_is_tiling int_x_core).val
           (int_point_to_point (double_int_vector y)) =
         (int_point_to_corner T'_is_tiling
            (add_int_vectors int_x_core (double_int_vector y))).val →
       (int_point_to_corner T'_is_tiling
            (add_int_vectors int_x_core (double_int_vector y))).val =
         x_corner →
       add_vectors (int_point_to_corner T'_is_tiling int_x_core).val
           (int_point_to_point (double_int_vector y)) =
         x_corner →
       add_vectors
           (add_vectors (int_point_to_corner T'_is_tiling int_x_core).val
              (int_point_to_point (double_int_vector y)))
           (unit_basis_vector i) =
         add_vectors x_corner (unit_basis_vector i) →
       add_vectors x_corner (unit_basis_vector i) =
         (point_to_corner T'_is_tiling
            (add_vectors (int_point_to_point x) (unit_basis_vector i))).val :=
begin
  intros core_points T_core T' int_x_core T'_covers_core T'_is_tiling T'_is_periodic T'_has_facesharing x_core_in_core_points
    x_corner_unique x_corner_core_in_T' x_core_eq_int_x_core x_corner_core_eq_int_x_core_corner
    x_corner_core_add_2y_eq_x_core_add_2y_corner x_core_add_2y_corner_eq_x_corner x_corner_core_add_2y_eq_x_corner
    x_corner_core_add_2y_add_unit_basis_vector_eq_x_corner_add_unit_basis_vector,
  --xei is shorthand for x plus unit_basis_vector i
  rcases T'_has_facesharing with ⟨i', x_and_xei_differ_at_i', x_and_xei_same_outside_of_i'⟩,
  have i_eq_i' : i = i' :=
    begin
      by_cases i_eq_i' : i = i', exact i_eq_i',
      rename i_eq_i' i_ne_i',
      exfalso,
      replace x_and_xei_same_outside_of_i' := x_and_xei_same_outside_of_i' i,
      cases x_and_xei_same_outside_of_i',
      { symmetry' at x_and_xei_same_outside_of_i',
        exact i_ne_i' x_and_xei_same_outside_of_i',
      },
      --Derive a contradiction from x_and_xei_same_outside_of_i' and i_ne_i'
      rw int_point_to_corner at x_and_xei_same_outside_of_i',
      let x_corner' := (point_to_corner T'_is_tiling (int_point_to_point x)).val,
      have x_corner'_def : x_corner' = (point_to_corner T'_is_tiling (int_point_to_point x)).val := by refl,
      have x_corner'_prop := (point_to_corner T'_is_tiling (int_point_to_point x)).property,
      rw ← x_corner'_def at x_corner'_prop,
      rcases x_corner'_prop with ⟨x_corner'_in_T', x_in_x_corner', x_corner'_unique⟩,
      rw ← x_corner'_def at x_and_xei_same_outside_of_i',
      rw cube at x_in_x_corner',
      simp only [set.mem_set_of_eq] at x_in_x_corner',
      rw [int_point_to_point, in_cube] at x_in_x_corner',
      simp only [not_exists, ge_iff_le, vector.nth_of_fn] at x_in_x_corner',
      replace x_in_x_corner' := x_in_x_corner' i,
      cases x_in_x_corner',
      rw x_and_xei_same_outside_of_i' at x_in_x_corner'_left,
      have xei_corner_prop := (point_to_corner T'_is_tiling (add_vectors (int_point_to_point x) (unit_basis_vector i))).property,
      rcases xei_corner_prop with ⟨xei_corner_in_T', xei_in_xei_corner, xei_corner_unique⟩,
      rw cube at xei_in_xei_corner,
      simp only [set.mem_set_of_eq] at xei_in_xei_corner,
      rw in_cube at xei_in_xei_corner,
      replace xei_in_xei_corner := xei_in_xei_corner i,
      cases xei_in_xei_corner,
      let xei_corner := vector.nth (point_to_corner T'_is_tiling (add_vectors (int_point_to_point x) (unit_basis_vector i))).val i,
      have xei_corner_def : xei_corner =
        vector.nth (point_to_corner T'_is_tiling (add_vectors (int_point_to_point x) (unit_basis_vector i))).val i := by refl,
      rw ← xei_corner_def at xei_in_xei_corner_right,
      rw [unit_basis_vector, int_point_to_point, add_vectors] at xei_in_xei_corner_right,
      simp only [if_true, eq_self_iff_true, vector.nth_of_fn, add_lt_add_iff_right] at xei_in_xei_corner_right,
      rw ← xei_corner_def at x_in_x_corner'_left,
      linarith,
    end,
  have x_corner_eq_int_point_to_corner_x : x_corner = (int_point_to_corner T'_is_tiling x).val :=
    begin
      rw int_point_to_corner,
      let x_corner' := (point_to_corner T'_is_tiling (int_point_to_point x)).val,
      have x_corner'_def : x_corner' = (point_to_corner T'_is_tiling (int_point_to_point x)).val := by refl,
      have x_corner'_prop := (point_to_corner T'_is_tiling (int_point_to_point x)).property,
      rw ← x_corner'_def at x_corner'_prop,
      rcases x_corner'_prop with ⟨x_corner'_in_T', x_in_x_corner', x_corner'_unique⟩,
      have x_corner_in_T' : x_corner ∈ T' :=
        begin
          have x_corner_core_in_T_core : x_corner_core ∈ T_core :=
            begin
              split, exact x_corner_core_in_T,
              use [x_core, x_core_in_core_points],
              exact x_core_in_x_corner_core,
            end,
          use [x_corner_core, x_corner_core_in_T_core, y],
          exact x_corner_def,
        end,
      rw ← x_corner'_def,
      exact x_corner'_unique x_corner x_corner_in_T' x_in_x_corner,
    end,

  apply vector.ext,
  intro j,
  by_cases i_eq_j : i = j,
  { rw ← i_eq_j,
    rw [← i_eq_i', ← x_corner_eq_int_point_to_corner_x] at x_and_xei_differ_at_i',
    cases x_and_xei_differ_at_i',
    { exfalso, --x_corner doesn't have a greater i value than the corner of x + unit_basis_vector i
      let xei_corner := (point_to_corner T'_is_tiling (add_vectors (int_point_to_point x) (unit_basis_vector i))).val,
      have xei_corner_def : xei_corner =
        (point_to_corner T'_is_tiling (add_vectors (int_point_to_point x) (unit_basis_vector i))).val := by refl,
      have xei_corner_prop := (point_to_corner T'_is_tiling (add_vectors (int_point_to_point x) (unit_basis_vector i))).property,
      rw ← xei_corner_def at xei_corner_prop,
      rcases xei_corner_prop with ⟨xei_corner_in_T', xei_in_xei_corner, xei_corner_unique⟩,
      conv at x_and_xei_differ_at_i'
      begin
        find (point_to_corner T'_is_tiling (add_vectors (int_point_to_point x) (unit_basis_vector i))).val {rw ← xei_corner_def},
      end,
      rw cube at xei_in_xei_corner,
      simp only [set.mem_set_of_eq] at xei_in_xei_corner,
      rw [in_cube, unit_basis_vector, int_point_to_point, add_vectors] at xei_in_xei_corner,
      simp only [not_exists, ge_iff_le, vector.nth_of_fn] at xei_in_xei_corner,
      replace xei_in_xei_corner := xei_in_xei_corner i,
      simp only [if_true, not_lt, not_le, eq_self_iff_true, add_le_add_iff_right] at xei_in_xei_corner,
      cases xei_in_xei_corner,
      rw cube at x_in_x_corner,
      simp only [set.mem_set_of_eq] at x_in_x_corner,
      rw [in_cube, int_point_to_point] at x_in_x_corner,
      simp only [not_exists, ge_iff_le, vector.nth_of_fn] at x_in_x_corner,
      replace x_in_x_corner := x_in_x_corner i,
      cases x_in_x_corner,
      linarith,
    },
    have x_corner_val : x_corner.nth i =
      vector.nth (point_to_corner T'_is_tiling (add_vectors (int_point_to_point x) (unit_basis_vector i))).val i - 1
      := by linarith,
    rw add_vectors,
    simp only [vector.nth_of_fn],
    rw [x_corner_val, unit_basis_vector],
    simp only [if_true, sub_add_cancel, eq_self_iff_true, vector.nth_of_fn],
  },
  rename i_eq_j i_ne_j,
  replace x_and_xei_same_outside_of_i' := x_and_xei_same_outside_of_i' j,
  cases x_and_xei_same_outside_of_i', {exfalso, rw i_eq_i' at i_ne_j, exact i_ne_j x_and_xei_same_outside_of_i',},
  rw ← x_and_xei_same_outside_of_i',
  rw ← x_corner_eq_int_point_to_corner_x,
  rw [unit_basis_vector, add_vectors],
  simp only [add_right_eq_self, vector.nth_of_fn, ite_eq_right_iff, one_ne_zero],
  exact i_ne_j,
end

lemma T'_faceshare_free_helper2 (d : ℕ) (T : set (point d)) (T_is_tiling : is_tiling T) (T_faceshare_free : tiling_faceshare_free T)
  (x : int_point d) (i : fin d) (x_corner x_corner_core : point d) (x_corner_core_in_T : x_corner_core ∈ T) (x_core : point d)
  (x_core_in_x_corner_core : in_cube x_corner_core x_core) (y : int_point d)
  (x_corner_def : x_corner = add_vectors x_corner_core (int_point_to_point (double_int_vector y)))
  (x_in_x_corner : int_point_to_point x ∈ cube x_corner) :
  let core_points : set (point d) :=
        {x :
           point d | ∀ (i : fin d),
           vector.nth x i = 0 ∨ vector.nth x i = 1},
      T_core : set (point d) :=
        {t ∈ T | ∃ (p : point d) (H : p ∈ core_points), in_cube t p},
      T' : set (point d) :=
        {t' :
           point d | ∃ (t : point d) (H : t ∈ T_core) (x : int_point d),
           t' = add_vectors t (int_point_to_point (double_int_vector x))},
      int_x_core : int_point d :=
        vector.of_fn (λ (i : fin d), ite (vector.nth x_core i < 1 / 2) 0 1)
  in (∀ (x : point d),
        (∀ (i : fin d), vector.nth x i ≥ 0 ∧ vector.nth x i ≤ 1) →
        (∃ (t' : point d) (H : t' ∈ T'),
           in_cube t' x ∧
             ∀ (alt_t' : point d),
               alt_t' ∈ T' → in_cube alt_t' x → t' = alt_t')) →
     ∀ (T'_is_tiling : is_tiling T'),
       is_periodic T'_is_tiling →
       is_facesharing (int_point_to_corner T'_is_tiling x).val
         (point_to_corner T'_is_tiling
            (add_vectors (int_point_to_point x) (unit_basis_vector i))).val →
       x_core ∈ core_points →
       (∀ (alt_corner : point d),
          alt_corner ∈ T' →
          int_point_to_point x ∈ cube alt_corner →
          alt_corner = x_corner) →
       x_corner_core ∈ T' →
       (∀ (i : fin d), vector.nth x_core i = ↑(vector.nth int_x_core i)) →
       x_corner_core = (int_point_to_corner T'_is_tiling int_x_core).val →
       add_vectors (int_point_to_corner T'_is_tiling int_x_core).val
           (int_point_to_point (double_int_vector y)) =
         (int_point_to_corner T'_is_tiling
            (add_int_vectors int_x_core (double_int_vector y))).val →
       (int_point_to_corner T'_is_tiling
            (add_int_vectors int_x_core (double_int_vector y))).val =
         x_corner →
       add_vectors (int_point_to_corner T'_is_tiling int_x_core).val
           (int_point_to_point (double_int_vector y)) =
         x_corner →
       add_vectors
           (add_vectors (int_point_to_corner T'_is_tiling int_x_core).val
              (int_point_to_point (double_int_vector y)))
           (unit_basis_vector i) =
         add_vectors x_corner (unit_basis_vector i) →
       add_vectors x_corner (unit_basis_vector i) =
         (point_to_corner T'_is_tiling
            (add_vectors (int_point_to_point x) (unit_basis_vector i))).val →
       add_vectors
           (add_vectors (int_point_to_corner T'_is_tiling int_x_core).val
              (int_point_to_point (double_int_vector y)))
           (unit_basis_vector i) =
         (point_to_corner T'_is_tiling
            (add_vectors (int_point_to_point x) (unit_basis_vector i))).val →
       int_point_to_point x =
         add_vectors x_core (int_point_to_point (double_int_vector y)) :=
begin
  intros core_points T_core T' int_x_core T'_covers_core T'_is_tiling T'_is_periodic T'_has_facesharing x_core_in_core_points
    x_corner_unique x_corner_core_in_T' x_core_eq_int_x_core x_corner_core_eq_int_x_core_corner
    x_corner_core_add_2y_eq_x_core_add_2y_corner x_core_add_2y_corner_eq_x_corner x_corner_core_add_2y_eq_x_corner
    x_corner_core_add_2y_add_unit_basis_vector_eq_x_corner_add_unit_basis_vector
    x_corner_add_unit_basis_vector_eq_x_add_unit_basis_vector_corner
    x_corner_core_add_2y_add_unit_basis_vector_eq_x_add_unit_basis_vector_corner,
  apply vector.ext,
  intro j,
  rw [double_int_vector, int_point_to_point, int_point_to_point, add_vectors],
  simp only [int.cast_bit0, int.cast_mul, int.cast_one, vector.nth_of_fn],
  have x_corner_def_j : x_corner.nth j = (add_vectors x_corner_core (int_point_to_point (double_int_vector y))).nth j :=
    by rw x_corner_def,
  rw [double_int_vector, int_point_to_point, add_vectors] at x_corner_def_j,
  simp only [int.cast_bit0, int.cast_mul, int.cast_one, vector.nth_of_fn] at x_corner_def_j,
  have x_eq_x_corner_ceil : x.nth j = int.ceil(x_corner.nth j) :=
    begin
      rw [cube, int_point_to_point] at x_in_x_corner,
      simp only [set.mem_set_of_eq] at x_in_x_corner,
      rw in_cube at x_in_x_corner,
      simp only [not_exists, ge_iff_le, vector.nth_of_fn] at x_in_x_corner,
      replace x_in_x_corner := x_in_x_corner j,
      cases x_in_x_corner,
      have le_ceil_fact := int.le_ceil (x_corner.nth j),
      have ceil_lt_add_one_fact := int.ceil_lt_add_one (x_corner.nth j),
      have x_lt_ceil_x_corner_add_one : ↑(vector.nth x j) < ↑⌈vector.nth x_corner j⌉ + (1 : ℝ) := by linarith,
      have coe_x_lt_ceil_x_corner_add_one : x.nth j < ⌈vector.nth x_corner j⌉ + 1 := by assumption_mod_cast,
      have x_le_x_ceil_x_corner : x.nth j - 1 < ⌈vector.nth x_corner j⌉ := by linarith,
      rw int.sub_one_lt_iff at x_le_x_ceil_x_corner,
      have x_corner_add_one_le_x_add_one : vector.nth x_corner j + 1 ≤ ↑(vector.nth x j) + 1 := by linarith,
      have ceil_x_corner_lt_x_add_one := lt_le_trans ceil_lt_add_one_fact x_corner_add_one_le_x_add_one,
      have coe_ceil_x_corner_lt_x_add_one : ⌈vector.nth x_corner j⌉ < (vector.nth x j) + 1 := by assumption_mod_cast,
      have ceil_x_corner_le_x : ⌈vector.nth x_corner j⌉ - 1 < x.nth j := by linarith,
      rw int.sub_one_lt_iff at ceil_x_corner_le_x,
      exact eq_of_le_and_ge x_le_x_ceil_x_corner ceil_x_corner_le_x,
    end,
  have x_core_eq_x_corner_core_ceil : int_x_core.nth j = int.ceil(x_corner_core.nth j) :=
    begin
      rw in_cube at x_core_in_x_corner_core,
      replace x_core_in_x_corner_core := x_core_in_x_corner_core j,
      rw [x_core_eq_int_x_core j] at x_core_in_x_corner_core,
      simp only [not_lt, not_le, vector.nth_of_fn] at x_core_in_x_corner_core,
      rw x_core_eq_int_x_core j at x_core_in_x_corner_core,
      have ite_simplification : ite (↑(vector.nth int_x_core j) < (1 / 2 : ℝ)) 0 1 = int_x_core.nth j :=
        begin
          replace x_core_in_core_points := x_core_in_core_points j,
          rw x_core_eq_int_x_core j at x_core_in_core_points,
          cases x_core_in_core_points,
          { have x_core_eq_zero : vector.nth int_x_core j = 0 := by assumption_mod_cast,
            rw x_core_eq_zero,
            simp only [one_div, int.cast_zero, if_true, zero_lt_bit0, zero_lt_one, inv_pos],
          },
          have x_core_eq_one : vector.nth int_x_core j = 1 := by assumption_mod_cast,
          rw x_core_eq_one,
          have one_ge_one_half : ¬(1 < (1/2 : ℝ)) := by linarith,
          have coe_one_ge_one_half : ¬(↑(1 : ℤ) < (1 / 2 : ℝ)) := by assumption_mod_cast,
          rw if_neg coe_one_ge_one_half,
        end,
      rw ite_simplification at x_core_in_x_corner_core,
      cases x_core_in_x_corner_core,
      have le_ceil_fact := int.le_ceil (x_corner_core.nth j),
      have ceil_lt_add_one_fact := int.ceil_lt_add_one (x_corner_core.nth j),
      have x_core_lt_ceil_x_corner_core_add_one : ↑(vector.nth int_x_core j) < ↑(⌈vector.nth x_corner_core j⌉) + (1 : ℝ) :=
        by linarith,
      have coe_x_core_lt_ceil_x_corner_core_add_one : vector.nth int_x_core j < ⌈vector.nth x_corner_core j⌉ + 1 :=
        by assumption_mod_cast,
      have x_core_le_ceil_x_corner_core : vector.nth int_x_core j - 1 < ⌈vector.nth x_corner_core j⌉ := by linarith,
      rw int.sub_one_lt_iff at x_core_le_ceil_x_corner_core,
      have x_corner_core_add_one_le_x_core_add_one : vector.nth x_corner_core j + 1 ≤ ↑(vector.nth int_x_core j) + 1 :=
        by linarith,
      have ceil_x_corner_core_le_x_core_add_one := lt_le_trans ceil_lt_add_one_fact x_corner_core_add_one_le_x_core_add_one,
      have coe_ceil_x_corner_core_lt_x_core_add_one : ⌈vector.nth x_corner_core j⌉ < (vector.nth int_x_core j) + 1 :=
        by assumption_mod_cast,
      have ceil_x_corner_core_le_x_core : ⌈vector.nth x_corner_core j⌉ - 1 < (vector.nth int_x_core j) := by linarith,
      rw int.sub_one_lt_iff at ceil_x_corner_core_le_x_core,
      exact eq_of_le_and_ge x_core_le_ceil_x_corner_core ceil_x_corner_core_le_x_core,
    end,
  rw x_core_eq_int_x_core j,
  have coe_goal : vector.nth x j = vector.nth int_x_core j + 2 * vector.nth y j :=
    begin
      replace x_corner_def_j := ceil_mono_eq x_corner_def_j,
      have refl_fact : 2 * (y.nth j) = 2 * (y.nth j) := by refl,
      have coe_fact : (2 : ℝ) * ↑(y.nth j) = ↑((2 : ℤ) * (y.nth j)) := by assumption_mod_cast,
      rw [coe_fact, int.ceil_add_int (vector.nth x_corner_core j) (2 * vector.nth y j),
          ← x_eq_x_corner_ceil, ← x_core_eq_x_corner_core_ceil] at x_corner_def_j,
      exact x_corner_def_j,
    end,
  assumption_mod_cast,
end

lemma floor_x_core_add_ei_corner_val (d : ℕ) (a : ℝ) (floor_x_corner_core floor_x_core_add_ei_corner : ℤ) (T : set (point d))
  (T_is_tiling : is_tiling T) (x : int_point d) (i : fin d) (x_corner x_corner_core : point d)
  (x_corner_core_in_T : x_corner_core ∈ T) (x_core : point d) (x_core_in_x_corner_core : in_cube x_corner_core x_core)
  (y : int_point d) (x_corner_def : x_corner = add_vectors x_corner_core (int_point_to_point (double_int_vector y)))
  (x_in_x_corner : int_point_to_point x ∈ cube x_corner)
  (x_eq_x_core_add_2y : int_point_to_point x = add_vectors x_core (int_point_to_point (double_int_vector y)))
  (zero_le_a : 0 ≤ a) (a_lt_one : a < 1)
  (x_corner_core_eq_a_mod_one : vector.nth x_corner_core i = ↑floor_x_corner_core + a)
  (floor_x_corner_core_val : a ≠ 0 ∧ floor_x_corner_core = -1 ∨ a = 0 ∧ floor_x_corner_core = 0) :
  let core_points : set (point d) :=
        {x :
           point d | ∀ (i : fin d),
           vector.nth x i = 0 ∨ vector.nth x i = 1},
      T_core : set (point d) :=
        {t ∈ T | ∃ (p : point d) (H : p ∈ core_points), in_cube t p},
      T' : set (point d) :=
        {t' :
           point d | ∃ (t : point d) (H : t ∈ T_core) (x : int_point d),
           t' = add_vectors t (int_point_to_point (double_int_vector x))}
  in (∀ (x : point d),
        (∀ (i : fin d), vector.nth x i ≥ 0 ∧ vector.nth x i ≤ 1) →
        (∃ (t' : point d) (H : t' ∈ T'),
           in_cube t' x ∧
             ∀ (alt_t' : point d),
               alt_t' ∈ T' → in_cube alt_t' x → t' = alt_t')) →
     ∀ (T'_is_tiling : is_tiling T'),
       is_periodic T'_is_tiling →
       is_facesharing (int_point_to_corner T'_is_tiling x).val
         (point_to_corner T'_is_tiling
            (add_vectors (int_point_to_point x) (unit_basis_vector i))).val →
       x_core ∈ core_points →
       (∀ (alt_corner : point d),
          alt_corner ∈ T' →
          int_point_to_point x ∈ cube alt_corner →
          alt_corner = x_corner) →
       x_corner_core ∈ T' →
       (let int_x_core : int_point d :=
              vector.of_fn
                (λ (i : fin d), ite (vector.nth x_core i < 1 / 2) 0 1)
        in (∀ (i : fin d),
              vector.nth x_core i = ↑(vector.nth int_x_core i)) →
           x_corner_core = (int_point_to_corner T'_is_tiling int_x_core).val →
           add_vectors (int_point_to_corner T'_is_tiling int_x_core).val
               (int_point_to_point (double_int_vector y)) =
             (int_point_to_corner T'_is_tiling
                (add_int_vectors int_x_core (double_int_vector y))).val →
           (int_point_to_corner T'_is_tiling
                (add_int_vectors int_x_core (double_int_vector y))).val =
             x_corner →
           add_vectors (int_point_to_corner T'_is_tiling int_x_core).val
               (int_point_to_point (double_int_vector y)) =
             x_corner →
           add_vectors
               (add_vectors (int_point_to_corner T'_is_tiling int_x_core).val
                  (int_point_to_point (double_int_vector y)))
               (unit_basis_vector i) =
             add_vectors x_corner (unit_basis_vector i) →
           add_vectors x_corner (unit_basis_vector i) =
             (point_to_corner T'_is_tiling
                (add_vectors (int_point_to_point x)
                   (unit_basis_vector i))).val →
           add_vectors
               (add_vectors (int_point_to_corner T'_is_tiling int_x_core).val
                  (int_point_to_point (double_int_vector y)))
               (unit_basis_vector i) =
             (point_to_corner T'_is_tiling
                (add_vectors (int_point_to_point x)
                   (unit_basis_vector i))).val →
           ∀
           (x_core_add_2y_add_unit_basis_vector_corner_h :
             {corner // corner ∈ T' ∧
                add_vectors
                      (add_vectors x_core
                         (int_point_to_point (double_int_vector y)))
                      (unit_basis_vector i) ∈
                    cube corner ∧
                  ∀ (alt_corner : point d),
                    alt_corner ∈ T' →
                    add_vectors
                        (add_vectors x_core
                           (int_point_to_point (double_int_vector y)))
                        (unit_basis_vector i) ∈
                      cube alt_corner →
                    alt_corner = corner}),
             let x_core_add_2y_add_unit_basis_vector_corner : point d :=
                   x_core_add_2y_add_unit_basis_vector_corner_h.val
             in x_core_add_2y_add_unit_basis_vector_corner =
                  x_core_add_2y_add_unit_basis_vector_corner_h.val →
                x_core_add_2y_add_unit_basis_vector_corner_h.val ∈ T' →
                add_vectors
                    (add_vectors x_core
                       (int_point_to_point (double_int_vector y)))
                    (unit_basis_vector i) ∈
                  cube x_core_add_2y_add_unit_basis_vector_corner_h.val →
                (∀ (alt_corner : point d),
                   alt_corner ∈ T' →
                   add_vectors
                       (add_vectors x_core
                          (int_point_to_point (double_int_vector y)))
                       (unit_basis_vector i) ∈
                     cube alt_corner →
                   alt_corner =
                     x_core_add_2y_add_unit_basis_vector_corner_h.val) →
                (let int_x_core_add_ei : int_point d :=
                       vector.of_fn
                         (λ (j : fin d),
                            ite (i = j) (vector.nth int_x_core j + 1)
                              (vector.nth int_x_core j))
                 in (int_point_to_corner T'_is_tiling
                         (add_int_vectors int_x_core_add_ei
                            (double_int_vector y))).val =
                      add_vectors
                        (int_point_to_corner T'_is_tiling int_x_core_add_ei).val
                        (int_point_to_point (double_int_vector y)) →
                    add_vectors
                        (add_vectors x_core
                           (int_point_to_point (double_int_vector y)))
                        (unit_basis_vector i) =
                      int_point_to_point
                        (add_int_vectors int_x_core_add_ei
                           (double_int_vector y)) →
                    (int_point_to_corner T'_is_tiling
                         (add_int_vectors int_x_core_add_ei
                            (double_int_vector y))).val =
                      (point_to_corner T'_is_tiling
                         (int_point_to_point
                            (add_int_vectors int_x_core_add_ei
                               (double_int_vector y)))).val →
                    add_vectors
                        (add_vectors
                           (int_point_to_corner T'_is_tiling int_x_core).val
                           (int_point_to_point (double_int_vector y)))
                        (unit_basis_vector i) =
                      add_vectors
                        (int_point_to_corner T'_is_tiling int_x_core_add_ei).val
                        (int_point_to_point (double_int_vector y)) →
                    add_vectors
                        (int_point_to_corner T'_is_tiling int_x_core).val
                        (unit_basis_vector i) =
                      (int_point_to_corner T'_is_tiling
                         int_x_core_add_ei).val →
                    (let int_x_core_sub_ei : int_point d :=
                           vector.of_fn
                             (λ (j : fin d),
                                ite (i = j) (vector.nth int_x_core j - 1)
                                  (vector.nth int_x_core j)),
                         facesharing_corner : point d :=
                           ite (vector.nth int_x_core i = 0)
                             (int_point_to_corner T'_is_tiling
                                int_x_core_add_ei).val
                             (int_point_to_corner T'_is_tiling
                                int_x_core_sub_ei).val
                     in facesharing_corner ∈ T →
                        (∀ (x : fin d),
                           vector.nth x_corner_core x -
                                 vector.nth facesharing_corner x =
                               1 ∨
                             vector.nth facesharing_corner x -
                                 vector.nth x_corner_core x =
                               1 →
                           (∃ (x_1 : fin d),
                              ¬(x = x_1 ∨
                                   vector.nth x_corner_core x_1 =
                                     vector.nth facesharing_corner x_1))) →
                        (∀ (t : vector ℝ d),
                           t ∈ T_i T' i x_core →
                           (∃ (z : ℤ), t.nth i = ↑z + a)) →
                        (∀ (y : ℤ),
                           ∃ (t : vector ℝ d) (H : t ∈ T_i T' i x_core),
                             t.nth i = ↑y + a ∧
                               ∀ (t' : vector ℝ d),
                                 t' ∈ T_i T' i x_core →
                                 t'.nth i = ↑y + a → t' = t) →
                        x_corner_core ∈ T_i T' i x_core →
                        vector.nth int_x_core i = 0 →
                        (int_point_to_corner T'_is_tiling
                             int_x_core_add_ei).val ∈
                          T' →
                        int_point_to_point int_x_core_add_ei ∈
                          cube
                            (int_point_to_corner T'_is_tiling
                               int_x_core_add_ei).val →
                        (∀ (alt_corner : point d),
                           alt_corner ∈ T' →
                           int_point_to_point int_x_core_add_ei ∈
                             cube alt_corner →
                           alt_corner =
                             (int_point_to_corner T'_is_tiling
                                int_x_core_add_ei).val) →
                        (int_point_to_corner T'_is_tiling
                             int_x_core_add_ei).val ∈
                          T_i T' i x_core →
                        vector.nth
                            (int_point_to_corner T'_is_tiling
                               int_x_core_add_ei).val
                            i =
                          ↑floor_x_core_add_ei_corner + a →
                        a ≠ 0 ∧ floor_x_core_add_ei_corner = 0 ∨
                          a = 0 ∧ floor_x_core_add_ei_corner = 1))) :=
begin
  intros core_points T_core T' T'_covers_core T'_is_tiling T'_is_periodic T'_has_facesharing x_core_in_core_points
    x_corner_unique x_corner_core_in_T' int_x_core x_core_eq_int_x_core x_corner_core_eq_int_x_core_corner
    x_corner_core_add_2y_eq_x_core_add_2y_corner x_core_add_2y_corner_eq_x_corner x_corner_core_add_2y_eq_x_corner
    x_corner_core_add_2y_add_unit_basis_vector_eq_x_corner_add_unit_basis_vector
    x_corner_add_unit_basis_vector_eq_x_add_unit_basis_vector_corner
    x_corner_core_add_2y_add_unit_basis_vector_eq_x_add_unit_basis_vector_corner x_core_add_2y_add_unit_basis_vector_corner_h
    x_core_add_2y_add_unit_basis_vector_corner x_core_add_2y_add_unit_basis_vector_corner_def
    x_core_add_2y_add_unit_basis_vector_corner_in_T' x_core_add_2y_add_unit_basis_vector_in_its_corner
    x_core_add_2y_add_unit_basis_vector_corner_unique
    int_x_core_add_ei x_core_add_2y_add_unit_basis_vector_corner_eq_x_core_add_unit_basis_vector_corner_add_2y
    x_core_add_2y_add_ei_eq_int_x_core_add_ei_add_2y coe_step
    x_corner_core_add_2y_add_unit_basis_vector_eq_x_core_add_2y_add_unit_basis_vector_corner
    x_core_corner_add_unit_basis_vector_eq_int_x_core_add_ei_corner int_x_core_sub_ei facesharing_corner facesharing_corner_in_T
    T_faceshare_free all_corners_eq_a_mod_one all_ints_covered_with_corner x_corner_core_in_T'_i_x_core x_core_eq_zero
    x_core_add_ei_corner_in_T' x_core_add_ei_in_x_core_add_ei_corner x_core_add_ei_corner_unique
    x_core_add_ei_corner_in_T'_i_x_core x_core_add_ei_corner_eq_a_mod_one,
  rw cube at x_core_add_ei_in_x_core_add_ei_corner,
  simp only [set.mem_set_of_eq] at x_core_add_ei_in_x_core_add_ei_corner,
  rw in_cube at x_core_add_ei_in_x_core_add_ei_corner,
  replace x_core_add_ei_in_x_core_add_ei_corner := x_core_add_ei_in_x_core_add_ei_corner i,
  have int_x_core_add_ei_def :
    int_x_core_add_ei = vector.of_fn (λ (j : fin d), ite (i = j) (vector.nth int_x_core j + 1) (vector.nth int_x_core j))
    := by refl,
  conv at x_core_add_ei_in_x_core_add_ei_corner
  begin
    find int_x_core_add_ei {rw int_x_core_add_ei_def},
    find (vector.nth (int_point_to_point int_x_core_add_ei) i < _) {rw int_x_core_add_ei_def},
    find (int_point_to_point _) {rw int_point_to_point},
    find (int_point_to_point _) {rw int_point_to_point},
  end,
  simp only [vector.nth_of_fn, one_div, eq_self_iff_true, if_true, int.cast_add, int.cast_one,
    add_lt_add_iff_right] at x_core_add_ei_in_x_core_add_ei_corner,
  rw [x_core_eq_int_x_core i, x_core_eq_zero, x_core_add_ei_corner_eq_a_mod_one]
    at x_core_add_ei_in_x_core_add_ei_corner,
  simp only [one_div, int.cast_zero, if_true, zero_lt_bit0, zero_add, zero_lt_one, inv_pos]
    at x_core_add_ei_in_x_core_add_ei_corner,
  by_cases a_eq_zero : a = 0,
  { right,
    rw [a_eq_zero, add_zero] at x_core_add_ei_in_x_core_add_ei_corner,
    cases x_core_add_ei_in_x_core_add_ei_corner with
      floor_x_core_add_ei_corner_le_1 zero_lt_floor_x_core_add_ei_corner,
    replace zero_lt_floor_x_core_add_ei_corner : 0 < floor_x_core_add_ei_corner := by assumption_mod_cast,
    replace zero_lt_floor_x_core_add_ei_corner := int.le_sub_one_of_lt zero_lt_floor_x_core_add_ei_corner,
    replace floor_x_core_add_ei_corner_le_1 : floor_x_core_add_ei_corner ≤ 1 := by assumption_mod_cast,
    exact ⟨a_eq_zero, by linarith⟩,
  },
  left,
  rename a_eq_zero a_ne_zero,
  cases x_core_add_ei_in_x_core_add_ei_corner with
    floor_x_core_add_ei_corner_add_a_le_one zero_lt_floor_x_core_add_ei_corner_add_a,
  replace zero_lt_floor_x_core_add_ei_corner_add_a := int.floor_mono (le_of_lt zero_lt_floor_x_core_add_ei_corner_add_a),
  have coe_zero_le_a : ↑(0 : ℤ) ≤ a := by assumption_mod_cast,
  have a_lt_zero_add_one : a < 0 + 1 := by linarith,
  have coe_a_lt_zero_add_one : a < ↑(0 : ℤ) + 1 := by assumption_mod_cast,
  have floor_a_val := floor_val coe_zero_le_a coe_a_lt_zero_add_one,
  rw [add_comm, int.floor_add_int a floor_x_core_add_ei_corner, int.floor_zero, floor_a_val]
    at zero_lt_floor_x_core_add_ei_corner_add_a,
  replace floor_x_core_add_ei_corner_add_a_le_one := int.ceil_mono floor_x_core_add_ei_corner_add_a_le_one,
  have a_le_one : a ≤ 1 := le_of_lt a_lt_one,
  have coe_a_le_one : a ≤ ↑(1 : ℤ) := by assumption_mod_cast,
  have zero_ne_a : 0 ≠ a := by {intro zero_eq_a, symmetry' at zero_eq_a, exact a_ne_zero zero_eq_a},
  have zero_lt_a := lt_of_le_of_ne zero_le_a zero_ne_a,
  have one_sub_one_lt_a : 1 - 1 < a := by linarith,
  have coe_one_sub_one_lt_a : ↑(1 : ℤ) - 1 < a := by assumption_mod_cast,
  have ceil_a_val := ceil_val coe_one_sub_one_lt_a coe_a_le_one,
  rw [add_comm, int.ceil_add_int a floor_x_core_add_ei_corner, ceil_one, ceil_a_val]
    at floor_x_core_add_ei_corner_add_a_le_one,
  exact ⟨a_ne_zero, by linarith⟩,
end

lemma facesharing_corner_faceshares_case_one (d : ℕ) (a : ℝ) (floor_x_corner_core : ℤ) (T : set (point d))
  (T_is_tiling : is_tiling T) (x : int_point d) (i : fin d) (x_corner x_corner_core : point d)
  (x_corner_core_in_T : x_corner_core ∈ T) (x_core : point d) (x_core_in_x_corner_core : in_cube x_corner_core x_core)
  (y : int_point d) (x_corner_def : x_corner = add_vectors x_corner_core (int_point_to_point (double_int_vector y)))
  (x_in_x_corner : int_point_to_point x ∈ cube x_corner)
  (x_eq_x_core_add_2y : int_point_to_point x = add_vectors x_core (int_point_to_point (double_int_vector y)))
  (zero_le_a : 0 ≤ a) (a_lt_one : a < 1)
  (x_corner_core_eq_a_mod_one : vector.nth x_corner_core i = ↑floor_x_corner_core + a) :
  let core_points : set (point d) :=
        {x :
           point d | ∀ (i : fin d),
           vector.nth x i = 0 ∨ vector.nth x i = 1},
      T_core : set (point d) :=
        {t ∈ T | ∃ (p : point d) (H : p ∈ core_points), in_cube t p},
      T' : set (point d) :=
        {t' :
           point d | ∃ (t : point d) (H : t ∈ T_core) (x : int_point d),
           t' = add_vectors t (int_point_to_point (double_int_vector x))}
  in (∀ (x : point d),
        (∀ (i : fin d), vector.nth x i ≥ 0 ∧ vector.nth x i ≤ 1) →
        (∃ (t' : point d) (H : t' ∈ T'),
           in_cube t' x ∧
             ∀ (alt_t' : point d),
               alt_t' ∈ T' → in_cube alt_t' x → t' = alt_t')) →
     ∀ (T'_is_tiling : is_tiling T'),
       is_periodic T'_is_tiling →
       is_facesharing (int_point_to_corner T'_is_tiling x).val
         (point_to_corner T'_is_tiling
            (add_vectors (int_point_to_point x) (unit_basis_vector i))).val →
       x_core ∈ core_points →
       (∀ (alt_corner : point d),
          alt_corner ∈ T' →
          int_point_to_point x ∈ cube alt_corner →
          alt_corner = x_corner) →
       x_corner_core ∈ T' →
       (let int_x_core : int_point d :=
              vector.of_fn
                (λ (i : fin d), ite (vector.nth x_core i < 1 / 2) 0 1)
        in (∀ (i : fin d),
              vector.nth x_core i = ↑(vector.nth int_x_core i)) →
           x_corner_core = (int_point_to_corner T'_is_tiling int_x_core).val →
           add_vectors (int_point_to_corner T'_is_tiling int_x_core).val
               (int_point_to_point (double_int_vector y)) =
             (int_point_to_corner T'_is_tiling
                (add_int_vectors int_x_core (double_int_vector y))).val →
           (int_point_to_corner T'_is_tiling
                (add_int_vectors int_x_core (double_int_vector y))).val =
             x_corner →
           add_vectors (int_point_to_corner T'_is_tiling int_x_core).val
               (int_point_to_point (double_int_vector y)) =
             x_corner →
           add_vectors
               (add_vectors (int_point_to_corner T'_is_tiling int_x_core).val
                  (int_point_to_point (double_int_vector y)))
               (unit_basis_vector i) =
             add_vectors x_corner (unit_basis_vector i) →
           add_vectors x_corner (unit_basis_vector i) =
             (point_to_corner T'_is_tiling
                (add_vectors (int_point_to_point x)
                   (unit_basis_vector i))).val →
           add_vectors
               (add_vectors (int_point_to_corner T'_is_tiling int_x_core).val
                  (int_point_to_point (double_int_vector y)))
               (unit_basis_vector i) =
             (point_to_corner T'_is_tiling
                (add_vectors (int_point_to_point x)
                   (unit_basis_vector i))).val →
           ∀
           (x_core_add_2y_add_unit_basis_vector_corner_h :
             {corner // corner ∈ T' ∧
                add_vectors
                      (add_vectors x_core
                         (int_point_to_point (double_int_vector y)))
                      (unit_basis_vector i) ∈
                    cube corner ∧
                  ∀ (alt_corner : point d),
                    alt_corner ∈ T' →
                    add_vectors
                        (add_vectors x_core
                           (int_point_to_point (double_int_vector y)))
                        (unit_basis_vector i) ∈
                      cube alt_corner →
                    alt_corner = corner}),
             let x_core_add_2y_add_unit_basis_vector_corner : point d :=
                   x_core_add_2y_add_unit_basis_vector_corner_h.val
             in x_core_add_2y_add_unit_basis_vector_corner =
                  x_core_add_2y_add_unit_basis_vector_corner_h.val →
                x_core_add_2y_add_unit_basis_vector_corner_h.val ∈ T' →
                add_vectors
                    (add_vectors x_core
                       (int_point_to_point (double_int_vector y)))
                    (unit_basis_vector i) ∈
                  cube x_core_add_2y_add_unit_basis_vector_corner_h.val →
                (∀ (alt_corner : point d),
                   alt_corner ∈ T' →
                   add_vectors
                       (add_vectors x_core
                          (int_point_to_point (double_int_vector y)))
                       (unit_basis_vector i) ∈
                     cube alt_corner →
                   alt_corner =
                     x_core_add_2y_add_unit_basis_vector_corner_h.val) →
                (let int_x_core_add_ei : int_point d :=
                       vector.of_fn
                         (λ (j : fin d),
                            ite (i = j) (vector.nth int_x_core j + 1)
                              (vector.nth int_x_core j))
                 in (int_point_to_corner T'_is_tiling
                         (add_int_vectors int_x_core_add_ei
                            (double_int_vector y))).val =
                      add_vectors
                        (int_point_to_corner T'_is_tiling int_x_core_add_ei).val
                        (int_point_to_point (double_int_vector y)) →
                    add_vectors
                        (add_vectors x_core
                           (int_point_to_point (double_int_vector y)))
                        (unit_basis_vector i) =
                      int_point_to_point
                        (add_int_vectors int_x_core_add_ei
                           (double_int_vector y)) →
                    (int_point_to_corner T'_is_tiling
                         (add_int_vectors int_x_core_add_ei
                            (double_int_vector y))).val =
                      (point_to_corner T'_is_tiling
                         (int_point_to_point
                            (add_int_vectors int_x_core_add_ei
                               (double_int_vector y)))).val →
                    add_vectors
                        (add_vectors
                           (int_point_to_corner T'_is_tiling int_x_core).val
                           (int_point_to_point (double_int_vector y)))
                        (unit_basis_vector i) =
                      add_vectors
                        (int_point_to_corner T'_is_tiling int_x_core_add_ei).val
                        (int_point_to_point (double_int_vector y)) →
                    add_vectors
                        (int_point_to_corner T'_is_tiling int_x_core).val
                        (unit_basis_vector i) =
                      (int_point_to_corner T'_is_tiling
                         int_x_core_add_ei).val →
                    (let int_x_core_sub_ei : int_point d :=
                           vector.of_fn
                             (λ (j : fin d),
                                ite (i = j) (vector.nth int_x_core j - 1)
                                  (vector.nth int_x_core j)),
                         facesharing_corner : point d :=
                           ite (vector.nth int_x_core i = 0)
                             (int_point_to_corner T'_is_tiling
                                int_x_core_add_ei).val
                             (int_point_to_corner T'_is_tiling
                                int_x_core_sub_ei).val
                     in facesharing_corner ∈ T →
                        (∀ (x : fin d),
                           vector.nth x_corner_core x -
                                 vector.nth facesharing_corner x =
                               1 ∨
                             vector.nth facesharing_corner x -
                                 vector.nth x_corner_core x =
                               1 →
                           (∃ (x_1 : fin d),
                              ¬(x = x_1 ∨
                                   vector.nth x_corner_core x_1 =
                                     vector.nth facesharing_corner x_1))) →
                        (∀ (t : vector ℝ d),
                           t ∈ T_i T' i x_core →
                           (∃ (z : ℤ), t.nth i = ↑z + a)) →
                        (∀ (y : ℤ),
                           ∃ (t : vector ℝ d) (H : t ∈ T_i T' i x_core),
                             t.nth i = ↑y + a ∧
                               ∀ (t' : vector ℝ d),
                                 t' ∈ T_i T' i x_core →
                                 t'.nth i = ↑y + a → t' = t) →
                        x_corner_core ∈ T_i T' i x_core →
                        vector.nth int_x_core i = 0 →
                        vector.nth x_corner_core i -
                              vector.nth
                                (ite (vector.nth int_x_core i = 0)
                                   (int_point_to_corner T'_is_tiling
                                      int_x_core_add_ei).val
                                   (int_point_to_corner T'_is_tiling
                                      int_x_core_sub_ei).val)
                                i =
                            1 ∨
                          vector.nth
                                (ite (vector.nth int_x_core i = 0)
                                   (int_point_to_corner T'_is_tiling
                                      int_x_core_add_ei).val
                                   (int_point_to_corner T'_is_tiling
                                      int_x_core_sub_ei).val)
                                i -
                              vector.nth x_corner_core i =
                            1))) :=
begin
  intros core_points T_core T' T'_covers_core T'_is_tiling T'_is_periodic T'_has_facesharing x_core_in_core_points
    x_corner_unique x_corner_core_in_T' int_x_core x_core_eq_int_x_core x_corner_core_eq_int_x_core_corner
    x_corner_core_add_2y_eq_x_core_add_2y_corner x_core_add_2y_corner_eq_x_corner x_corner_core_add_2y_eq_x_corner
    x_corner_core_add_2y_add_unit_basis_vector_eq_x_corner_add_unit_basis_vector
    x_corner_add_unit_basis_vector_eq_x_add_unit_basis_vector_corner
    x_corner_core_add_2y_add_unit_basis_vector_eq_x_add_unit_basis_vector_corner x_core_add_2y_add_unit_basis_vector_corner_h
    x_core_add_2y_add_unit_basis_vector_corner x_core_add_2y_add_unit_basis_vector_corner_def
    x_core_add_2y_add_unit_basis_vector_corner_in_T' x_core_add_2y_add_unit_basis_vector_in_its_corner
    x_core_add_2y_add_unit_basis_vector_corner_unique int_x_core_add_ei
    x_core_add_2y_add_unit_basis_vector_corner_eq_x_core_add_unit_basis_vector_corner_add_2y
    x_core_add_2y_add_ei_eq_int_x_core_add_ei_add_2y
    coe_step x_corner_core_add_2y_add_unit_basis_vector_eq_x_core_add_2y_add_unit_basis_vector_corner
    x_core_corner_add_unit_basis_vector_eq_int_x_core_add_ei_corner int_x_core_sub_ei facesharing_corner facesharing_corner_in_T
    T_faceshare_free all_corners_eq_a_mod_one all_ints_covered_with_corner x_corner_core_in_T'_i_x_core x_core_eq_zero,
  rw x_core_eq_zero,
  simp only [if_true, eq_self_iff_true],
  right,
  have floor_x_corner_core_val : (a ≠ 0 ∧ floor_x_corner_core = -1) ∨ (a = 0 ∧ floor_x_corner_core = 0) :=
    begin
      rw in_cube at x_core_in_x_corner_core,
      replace x_core_in_x_corner_core := x_core_in_x_corner_core i,
      rw [x_core_eq_int_x_core i, x_core_eq_zero, x_corner_core_eq_a_mod_one] at x_core_in_x_corner_core,
      simp only [int.cast_zero, not_lt, not_le] at x_core_in_x_corner_core,
      cases x_core_in_x_corner_core,
      replace x_core_in_x_corner_core_left := int.ceil_mono x_core_in_x_corner_core_left,
      rw [add_comm, int.ceil_add_int a floor_x_corner_core, int.ceil_zero] at x_core_in_x_corner_core_left,
      by_cases a_eq_zero : 0 = a,
      { right,
        split, {symmetry, exact a_eq_zero},
        rw [← a_eq_zero, int.ceil_zero] at x_core_in_x_corner_core_left,
        rw ← a_eq_zero at x_core_in_x_corner_core_right,
        replace x_core_in_x_corner_core_right : 0 < floor_x_corner_core + 0 + 1 := by assumption_mod_cast,
        linarith,
      },
      rename a_eq_zero a_ne_zero,
      left,
      split, {intro a_eq_zero, symmetry' at a_eq_zero, exact a_ne_zero a_eq_zero,},
      have zero_lt_a := lt_of_le_of_ne zero_le_a a_ne_zero,
      have ceil_a_eq_one : int.ceil(a) = 1 :=
        begin
          have one_sub_one_lt_a : 1 - 1 < a := by linarith,
          have coe_one_sub_one_lt_a : ↑(1 : ℤ) - 1 < a := by assumption_mod_cast,
          have a_le_one := le_of_lt a_lt_one,
          have coe_a_le_one : a ≤ ↑(1 : ℤ) := by assumption_mod_cast,
          exact ceil_val coe_one_sub_one_lt_a coe_a_le_one,
        end,
      rw ceil_a_eq_one at x_core_in_x_corner_core_left,
      replace x_core_in_x_corner_core_right := int.floor_mono (le_of_lt x_core_in_x_corner_core_right),
      rw [add_comm (↑floor_x_corner_core : ℝ) a, add_assoc] at x_core_in_x_corner_core_right,
      replace x_core_in_x_corner_core_right : ⌊(0 : ℝ)⌋ ≤ ⌊a + ↑(floor_x_corner_core + 1)⌋ := by assumption_mod_cast,
      have coe_zero_le_a : ↑(0 : ℤ) ≤ a := by assumption_mod_cast,
      have a_lt_zero_add_one : a < 0 + 1 := by linarith,
      have coe_a_lt_zero_add_one : a < ↑(0 : ℤ) + 1 := by assumption_mod_cast,
      have a_floor_val := floor_val coe_zero_le_a coe_a_lt_zero_add_one,
      rw [int.floor_zero, int.floor_add_int a (floor_x_corner_core + 1), a_floor_val] at x_core_in_x_corner_core_right,
      linarith,
    end,
  have x_core_add_ei_corner_property := (int_point_to_corner T'_is_tiling int_x_core_add_ei).property,
  rcases x_core_add_ei_corner_property with
    ⟨x_core_add_ei_corner_in_T', x_core_add_ei_in_x_core_add_ei_corner, x_core_add_ei_corner_unique⟩,
  have x_core_add_ei_corner_in_T'_i_x_core : (int_point_to_corner T'_is_tiling int_x_core_add_ei).val ∈ T_i T' i x_core :=
    begin
      split, exact x_core_add_ei_corner_in_T',
      simp only,
      rw [set.ne_empty_iff_nonempty, set.nonempty_def, cube, line_i],
      use (int_point_to_point int_x_core_add_ei),
      simp only [set.mem_inter_eq, set.mem_set_of_eq],
      rw cube at x_core_add_ei_in_x_core_add_ei_corner,
      simp only [set.mem_set_of_eq] at x_core_add_ei_in_x_core_add_ei_corner,
      split, exact x_core_add_ei_in_x_core_add_ei_corner,
      intro j,
      by_cases i_eq_j : i = j, {left, exact i_eq_j,},
      rename i_eq_j i_ne_j,
      right,
      dsimp[int_x_core_add_ei],
      conv
      begin
        find (int_point_to_point _) {rw int_point_to_point},
      end,
      simp only [vector.nth_of_fn],
      rw if_neg i_ne_j,
      replace x_core_in_core_points := x_core_in_core_points j,
      cases x_core_in_core_points,
      { rw x_core_in_core_points,
        simp only [one_div, int.cast_zero, if_true, zero_lt_bit0, zero_lt_one, inv_pos],
      },
      rw x_core_in_core_points,
      have one_ge_one_half : ¬(1 < (1/2 : ℝ)) := by linarith,
      rw if_neg one_ge_one_half,
      simp only [int.cast_one],
    end,
  have x_core_add_ei_corner_eq_a_mod_one :=
    all_corners_eq_a_mod_one (int_point_to_corner T'_is_tiling int_x_core_add_ei).val x_core_add_ei_corner_in_T'_i_x_core,
  cases x_core_add_ei_corner_eq_a_mod_one with floor_x_core_add_ei_corner x_core_add_ei_corner_eq_a_mod_one,
  have floor_x_core_add_ei_corner_val :
    (a ≠ 0 ∧ floor_x_core_add_ei_corner = 0) ∨ (a = 0 ∧ floor_x_core_add_ei_corner = 1) :=
    begin
      exact floor_x_core_add_ei_corner_val d a floor_x_corner_core floor_x_core_add_ei_corner T T_is_tiling x i x_corner
        x_corner_core x_corner_core_in_T x_core x_core_in_x_corner_core y x_corner_def x_in_x_corner x_eq_x_core_add_2y
        zero_le_a a_lt_one x_corner_core_eq_a_mod_one floor_x_corner_core_val T'_covers_core T'_is_tiling T'_is_periodic
        T'_has_facesharing x_core_in_core_points x_corner_unique x_corner_core_in_T' x_core_eq_int_x_core
        x_corner_core_eq_int_x_core_corner x_corner_core_add_2y_eq_x_core_add_2y_corner x_core_add_2y_corner_eq_x_corner
        x_corner_core_add_2y_eq_x_corner x_corner_core_add_2y_add_unit_basis_vector_eq_x_corner_add_unit_basis_vector
        x_corner_add_unit_basis_vector_eq_x_add_unit_basis_vector_corner
        x_corner_core_add_2y_add_unit_basis_vector_eq_x_add_unit_basis_vector_corner
        x_core_add_2y_add_unit_basis_vector_corner_h x_core_add_2y_add_unit_basis_vector_corner_def
        x_core_add_2y_add_unit_basis_vector_corner_in_T' x_core_add_2y_add_unit_basis_vector_in_its_corner
        x_core_add_2y_add_unit_basis_vector_corner_unique
        x_core_add_2y_add_unit_basis_vector_corner_eq_x_core_add_unit_basis_vector_corner_add_2y
        x_core_add_2y_add_ei_eq_int_x_core_add_ei_add_2y coe_step
        x_corner_core_add_2y_add_unit_basis_vector_eq_x_core_add_2y_add_unit_basis_vector_corner
        x_core_corner_add_unit_basis_vector_eq_int_x_core_add_ei_corner facesharing_corner_in_T T_faceshare_free
        all_corners_eq_a_mod_one all_ints_covered_with_corner x_corner_core_in_T'_i_x_core x_core_eq_zero
        x_core_add_ei_corner_in_T' x_core_add_ei_in_x_core_add_ei_corner x_core_add_ei_corner_unique
        x_core_add_ei_corner_in_T'_i_x_core x_core_add_ei_corner_eq_a_mod_one,
    end,
  by_cases a_eq_zero : a = 0,
  { rcases floor_x_corner_core_val with ⟨a_ne_zero, floor_x_corner_core_val⟩ | ⟨a_eq_zero, floor_x_corner_core_val⟩,
    { exfalso,
      exact a_ne_zero a_eq_zero,
    },
    rcases floor_x_core_add_ei_corner_val with
      ⟨a_ne_zero, floor_x_core_add_ei_corner_val⟩ | ⟨a_eq_zero, floor_x_core_add_ei_corner_val⟩,
    { exfalso,
      exact a_ne_zero a_eq_zero,
    },
    rw [x_corner_core_eq_a_mod_one, x_core_add_ei_corner_eq_a_mod_one, floor_x_corner_core_val,
        floor_x_core_add_ei_corner_val],
    simp only [int.cast_zero, int.cast_one, zero_add, int.cast_neg],
    linarith,
  },
  rename a_eq_zero a_ne_zero,
  rcases floor_x_corner_core_val with ⟨a_ne_zero, floor_x_corner_core_val⟩ | ⟨a_eq_zero, floor_x_corner_core_val⟩,
  { rcases floor_x_core_add_ei_corner_val with
      ⟨a_ne_zero, floor_x_core_add_ei_corner_val⟩ | ⟨a_eq_zero, floor_x_core_add_ei_corner_val⟩,
    { rw [x_corner_core_eq_a_mod_one, x_core_add_ei_corner_eq_a_mod_one, floor_x_corner_core_val,
          floor_x_core_add_ei_corner_val],
      simp only [int.cast_zero, int.cast_one, zero_add, int.cast_neg],
      linarith,
    },
    exfalso,
    exact a_ne_zero a_eq_zero,
  },
  exfalso,
  exact a_ne_zero a_eq_zero,
end

lemma floor_x_core_sub_ei_corner_val (d : ℕ) (a : ℝ) (floor_x_corner_core floor_x_core_sub_ei_corner : ℤ) (T : set (point d))
  (T_is_tiling : is_tiling T) (x : int_point d) (i : fin d) (x_corner x_corner_core : point d)
  (x_corner_core_in_T : x_corner_core ∈ T) (x_core : point d) (x_core_in_x_corner_core : in_cube x_corner_core x_core)
  (y : int_point d) (x_corner_def : x_corner = add_vectors x_corner_core (int_point_to_point (double_int_vector y)))
  (x_in_x_corner : int_point_to_point x ∈ cube x_corner)
  (x_eq_x_core_add_2y : int_point_to_point x = add_vectors x_core (int_point_to_point (double_int_vector y)))
  (zero_le_a : 0 ≤ a) (a_lt_one : a < 1)
  (x_corner_core_eq_a_mod_one : vector.nth x_corner_core i = ↑floor_x_corner_core + a)
  (coe_x_core_ne_zero : ¬vector.nth x_core i = 0) (x_core_eq_one : vector.nth x_core i = 1)
  (floor_x_corner_core_val : a ≠ 0 ∧ floor_x_corner_core = 0 ∨ a = 0 ∧ floor_x_corner_core = 1) :
  let core_points : set (point d) :=
        {x :
           point d | ∀ (i : fin d),
           vector.nth x i = 0 ∨ vector.nth x i = 1},
      T_core : set (point d) :=
        {t ∈ T | ∃ (p : point d) (H : p ∈ core_points), in_cube t p},
      T' : set (point d) :=
        {t' :
           point d | ∃ (t : point d) (H : t ∈ T_core) (x : int_point d),
           t' = add_vectors t (int_point_to_point (double_int_vector x))}
  in (∀ (x : point d),
        (∀ (i : fin d), vector.nth x i ≥ 0 ∧ vector.nth x i ≤ 1) →
        (∃ (t' : point d) (H : t' ∈ T'),
           in_cube t' x ∧
             ∀ (alt_t' : point d),
               alt_t' ∈ T' → in_cube alt_t' x → t' = alt_t')) →
     ∀ (T'_is_tiling : is_tiling T'),
       is_periodic T'_is_tiling →
       is_facesharing (int_point_to_corner T'_is_tiling x).val
         (point_to_corner T'_is_tiling
            (add_vectors (int_point_to_point x) (unit_basis_vector i))).val →
       x_core ∈ core_points →
       (∀ (alt_corner : point d),
          alt_corner ∈ T' →
          int_point_to_point x ∈ cube alt_corner →
          alt_corner = x_corner) →
       x_corner_core ∈ T' →
       (let int_x_core : int_point d :=
              vector.of_fn
                (λ (i : fin d), ite (vector.nth x_core i < 1 / 2) 0 1)
        in (∀ (i : fin d),
              vector.nth x_core i = ↑(vector.nth int_x_core i)) →
           x_corner_core = (int_point_to_corner T'_is_tiling int_x_core).val →
           add_vectors (int_point_to_corner T'_is_tiling int_x_core).val
               (int_point_to_point (double_int_vector y)) =
             (int_point_to_corner T'_is_tiling
                (add_int_vectors int_x_core (double_int_vector y))).val →
           (int_point_to_corner T'_is_tiling
                (add_int_vectors int_x_core (double_int_vector y))).val =
             x_corner →
           add_vectors (int_point_to_corner T'_is_tiling int_x_core).val
               (int_point_to_point (double_int_vector y)) =
             x_corner →
           add_vectors
               (add_vectors (int_point_to_corner T'_is_tiling int_x_core).val
                  (int_point_to_point (double_int_vector y)))
               (unit_basis_vector i) =
             add_vectors x_corner (unit_basis_vector i) →
           add_vectors x_corner (unit_basis_vector i) =
             (point_to_corner T'_is_tiling
                (add_vectors (int_point_to_point x)
                   (unit_basis_vector i))).val →
           add_vectors
               (add_vectors (int_point_to_corner T'_is_tiling int_x_core).val
                  (int_point_to_point (double_int_vector y)))
               (unit_basis_vector i) =
             (point_to_corner T'_is_tiling
                (add_vectors (int_point_to_point x)
                   (unit_basis_vector i))).val →
           ∀
           (x_core_add_2y_add_unit_basis_vector_corner_h :
             {corner // corner ∈ T' ∧
                add_vectors
                      (add_vectors x_core
                         (int_point_to_point (double_int_vector y)))
                      (unit_basis_vector i) ∈
                    cube corner ∧
                  ∀ (alt_corner : point d),
                    alt_corner ∈ T' →
                    add_vectors
                        (add_vectors x_core
                           (int_point_to_point (double_int_vector y)))
                        (unit_basis_vector i) ∈
                      cube alt_corner →
                    alt_corner = corner}),
             let x_core_add_2y_add_unit_basis_vector_corner : point d :=
                   x_core_add_2y_add_unit_basis_vector_corner_h.val
             in x_core_add_2y_add_unit_basis_vector_corner =
                  x_core_add_2y_add_unit_basis_vector_corner_h.val →
                x_core_add_2y_add_unit_basis_vector_corner_h.val ∈ T' →
                add_vectors
                    (add_vectors x_core
                       (int_point_to_point (double_int_vector y)))
                    (unit_basis_vector i) ∈
                  cube x_core_add_2y_add_unit_basis_vector_corner_h.val →
                (∀ (alt_corner : point d),
                   alt_corner ∈ T' →
                   add_vectors
                       (add_vectors x_core
                          (int_point_to_point (double_int_vector y)))
                       (unit_basis_vector i) ∈
                     cube alt_corner →
                   alt_corner =
                     x_core_add_2y_add_unit_basis_vector_corner_h.val) →
                (let int_x_core_add_ei : int_point d :=
                       vector.of_fn
                         (λ (j : fin d),
                            ite (i = j) (vector.nth int_x_core j + 1)
                              (vector.nth int_x_core j))
                 in (int_point_to_corner T'_is_tiling
                         (add_int_vectors int_x_core_add_ei
                            (double_int_vector y))).val =
                      add_vectors
                        (int_point_to_corner T'_is_tiling int_x_core_add_ei).val
                        (int_point_to_point (double_int_vector y)) →
                    add_vectors
                        (add_vectors x_core
                           (int_point_to_point (double_int_vector y)))
                        (unit_basis_vector i) =
                      int_point_to_point
                        (add_int_vectors int_x_core_add_ei
                           (double_int_vector y)) →
                    (int_point_to_corner T'_is_tiling
                         (add_int_vectors int_x_core_add_ei
                            (double_int_vector y))).val =
                      (point_to_corner T'_is_tiling
                         (int_point_to_point
                            (add_int_vectors int_x_core_add_ei
                               (double_int_vector y)))).val →
                    add_vectors
                        (add_vectors
                           (int_point_to_corner T'_is_tiling int_x_core).val
                           (int_point_to_point (double_int_vector y)))
                        (unit_basis_vector i) =
                      add_vectors
                        (int_point_to_corner T'_is_tiling int_x_core_add_ei).val
                        (int_point_to_point (double_int_vector y)) →
                    add_vectors
                        (int_point_to_corner T'_is_tiling int_x_core).val
                        (unit_basis_vector i) =
                      (int_point_to_corner T'_is_tiling
                         int_x_core_add_ei).val →
                    (let int_x_core_sub_ei : int_point d :=
                           vector.of_fn
                             (λ (j : fin d),
                                ite (i = j) (vector.nth int_x_core j - 1)
                                  (vector.nth int_x_core j)),
                         facesharing_corner : point d :=
                           ite (vector.nth int_x_core i = 0)
                             (int_point_to_corner T'_is_tiling
                                int_x_core_add_ei).val
                             (int_point_to_corner T'_is_tiling
                                int_x_core_sub_ei).val
                     in facesharing_corner ∈ T →
                        (∀ (x : fin d),
                           vector.nth x_corner_core x -
                                 vector.nth facesharing_corner x =
                               1 ∨
                             vector.nth facesharing_corner x -
                                 vector.nth x_corner_core x =
                               1 →
                           (∃ (x_1 : fin d),
                              ¬(x = x_1 ∨
                                   vector.nth x_corner_core x_1 =
                                     vector.nth facesharing_corner x_1))) →
                        (∀ (t : vector ℝ d),
                           t ∈ T_i T' i x_core →
                           (∃ (z : ℤ), t.nth i = ↑z + a)) →
                        (∀ (y : ℤ),
                           ∃ (t : vector ℝ d) (H : t ∈ T_i T' i x_core),
                             t.nth i = ↑y + a ∧
                               ∀ (t' : vector ℝ d),
                                 t' ∈ T_i T' i x_core →
                                 t'.nth i = ↑y + a → t' = t) →
                        x_corner_core ∈ T_i T' i x_core →
                        ¬vector.nth int_x_core i = 0 →
                        (int_point_to_corner T'_is_tiling
                             int_x_core_sub_ei).val ∈
                          T' →
                        int_point_to_point int_x_core_sub_ei ∈
                          cube
                            (int_point_to_corner T'_is_tiling
                               int_x_core_sub_ei).val →
                        (∀ (alt_corner : point d),
                           alt_corner ∈ T' →
                           int_point_to_point int_x_core_sub_ei ∈
                             cube alt_corner →
                           alt_corner =
                             (int_point_to_corner T'_is_tiling
                                int_x_core_sub_ei).val) →
                        (int_point_to_corner T'_is_tiling
                             int_x_core_sub_ei).val ∈
                          T_i T' i x_core →
                        vector.nth
                            (int_point_to_corner T'_is_tiling
                               int_x_core_sub_ei).val
                            i =
                          ↑floor_x_core_sub_ei_corner + a →
                        a ≠ 0 ∧ floor_x_core_sub_ei_corner = -1 ∨
                          a = 0 ∧ floor_x_core_sub_ei_corner = 0))) :=
begin
  intros core_points T_core T' T'_covers_core T'_is_tiling T'_is_periodic T'_has_facesharing x_core_in_core_points
    x_corner_unique x_corner_core_in_T' int_x_core x_core_eq_int_x_core x_corner_core_eq_int_x_core_corner
    x_corner_core_add_2y_eq_x_core_add_2y_corner x_core_add_2y_corner_eq_x_corner x_corner_core_add_2y_eq_x_corner
    x_corner_core_add_2y_add_unit_basis_vector_eq_x_corner_add_unit_basis_vector
    x_corner_add_unit_basis_vector_eq_x_add_unit_basis_vector_corner
    x_corner_core_add_2y_add_unit_basis_vector_eq_x_add_unit_basis_vector_corner x_core_add_2y_add_unit_basis_vector_corner_h
    x_core_add_2y_add_unit_basis_vector_corner x_core_add_2y_add_unit_basis_vector_corner_def
    x_core_add_2y_add_unit_basis_vector_corner_in_T' x_core_add_2y_add_unit_basis_vector_in_its_corner
    x_core_add_2y_add_unit_basis_vector_corner_unique int_x_core_add_ei
    x_core_add_2y_add_unit_basis_vector_corner_eq_x_core_add_unit_basis_vector_corner_add_2y
    x_core_add_2y_add_ei_eq_int_x_core_add_ei_add_2y coe_step
    x_corner_core_add_2y_add_unit_basis_vector_eq_x_core_add_2y_add_unit_basis_vector_corner
    x_core_corner_add_unit_basis_vector_eq_int_x_core_add_ei_corner int_x_core_sub_ei facesharing_corner facesharing_corner_in_T
    T_faceshare_free all_corners_eq_a_mod_one all_ints_covered_with_corner x_corner_core_in_T'_i_x_core x_core_ne_zero
    x_core_sub_ei_corner_in_T' x_core_sub_ei_in_x_core_sub_ei_corner x_core_sub_ei_corner_unique
    x_core_sub_ei_corner_in_T'_i_x_core x_core_sub_ei_corner_eq_a_mod_one,
  rw cube at x_core_sub_ei_in_x_core_sub_ei_corner,
  simp only [set.mem_set_of_eq] at x_core_sub_ei_in_x_core_sub_ei_corner,
  rw in_cube at x_core_sub_ei_in_x_core_sub_ei_corner,
  replace x_core_sub_ei_in_x_core_sub_ei_corner := x_core_sub_ei_in_x_core_sub_ei_corner i,
  have int_x_core_sub_ei_def :
    int_x_core_sub_ei = vector.of_fn (λ (j : fin d), ite (i = j) (vector.nth int_x_core j - 1) (vector.nth int_x_core j))
    := by refl,
  conv at x_core_sub_ei_in_x_core_sub_ei_corner
  begin
    find int_x_core_sub_ei {rw int_x_core_sub_ei_def},
    find (vector.nth (int_point_to_point int_x_core_sub_ei) i < _) {rw int_x_core_sub_ei_def},
    find (int_point_to_point _) {rw int_point_to_point},
    find (int_point_to_point _) {rw int_point_to_point},
  end,
  simp only [vector.nth_of_fn, eq_self_iff_true, if_true, int.cast_sub, int.cast_one] at x_core_sub_ei_in_x_core_sub_ei_corner,
  rw [x_core_eq_one, x_core_sub_ei_corner_eq_a_mod_one] at x_core_sub_ei_in_x_core_sub_ei_corner,
  have one_ge_one_half : ¬(1 < (1 / 2 : ℝ)) := by linarith,
  rw if_neg one_ge_one_half at x_core_sub_ei_in_x_core_sub_ei_corner,
  by_cases a_eq_zero : a = 0,
  { right,
    rw [a_eq_zero, add_zero] at x_core_sub_ei_in_x_core_sub_ei_corner,
    cases x_core_sub_ei_in_x_core_sub_ei_corner with
      floor_x_core_sub_ei_corner_le_zero zero_lt_floor_x_core_sub_ei_corner_add_one,
    replace floor_x_core_sub_ei_corner_le_zero : floor_x_core_sub_ei_corner ≤ 1 - 1 := by assumption_mod_cast,
    replace zero_lt_floor_x_core_sub_ei_corner_add_one : 1 - 1 < floor_x_core_sub_ei_corner + 1 :=
      by assumption_mod_cast,
    exact ⟨a_eq_zero, by linarith⟩,
  },
  left,
  rename a_eq_zero a_ne_zero,
  cases x_core_sub_ei_in_x_core_sub_ei_corner with
    floor_x_core_sub_ei_corner_add_a_le_zero zero_lt_floor_x_core_sub_ei_corner_add_a_add_one,
  replace zero_lt_floor_x_core_sub_ei_corner_add_a_add_one :=
    int.floor_mono (le_of_lt zero_lt_floor_x_core_sub_ei_corner_add_a_add_one),
  have coe_zero_le_a : ↑(0 : ℤ) ≤ a := by exact_mod_cast zero_le_a,
  have a_lt_zero_add_one : a < 0 + 1 := by {rw zero_add, exact a_lt_one},
  have coe_a_lt_zero_add_one : a < ↑(0 : ℤ) + 1 := by exact_mod_cast a_lt_zero_add_one,
  have floor_a_val := floor_val coe_zero_le_a coe_a_lt_zero_add_one,
  have one_sub_one_eq_zero_int : 1 - 1 = (0 : ℤ) := by linarith,
  rw [add_comm ↑floor_x_core_sub_ei_corner a, add_assoc]
    at zero_lt_floor_x_core_sub_ei_corner_add_a_add_one,
  have refl_fact : ↑floor_x_core_sub_ei_corner + (1 : ℝ) = ↑floor_x_core_sub_ei_corner + (1 : ℝ) := by refl,
  have coe_rw : ↑floor_x_core_sub_ei_corner + (1 : ℝ) = ↑(floor_x_core_sub_ei_corner + (1 : ℤ)) :=
    by assumption_mod_cast,
  have floor_zero : int.floor((0 : ℝ)) = (0 : ℤ) := int.floor_zero,
  have coe_floor_zero : int.floor(↑(0 : ℤ)) = 0 := by exact_mod_cast floor_zero,
  simp only [int.cast_one, sub_self, int.floor_zero] at zero_lt_floor_x_core_sub_ei_corner_add_a_add_one,
  rw [coe_rw, int.floor_add_int a (floor_x_core_sub_ei_corner + (1 : ℤ)), floor_a_val] at zero_lt_floor_x_core_sub_ei_corner_add_a_add_one,
  have a_le_one : a ≤ 1 := le_of_lt a_lt_one,
  have coe_a_le_one : a ≤ ↑(1 : ℤ) := by exact_mod_cast a_le_one,
  have zero_ne_a : 0 ≠ a := by {intro zero_eq_a, symmetry' at zero_eq_a, exact a_ne_zero zero_eq_a},
  have zero_lt_a := lt_of_le_of_ne zero_le_a zero_ne_a,
  have one_sub_one_eq_zero_real : 1 - 1 = (0 : ℝ) := by linarith,
  have one_sub_one_lt_a : 1 - 1 < a := by {rw one_sub_one_eq_zero_real, exact zero_lt_a,},
  have coe_one_sub_one_lt_a : ↑(1 : ℤ) - 1 < a := by assumption_mod_cast,
  have ceil_a_val := ceil_val coe_one_sub_one_lt_a coe_a_le_one,
  have one_sub_one_eq_zero_coe : ↑((1 - 1) : ℤ) = (0 : ℝ) := by assumption_mod_cast,
  replace floor_x_core_sub_ei_corner_add_a_le_zero := int.ceil_mono floor_x_core_sub_ei_corner_add_a_le_zero,
  simp only [int.cast_one, sub_self, int.ceil_zero] at floor_x_core_sub_ei_corner_add_a_le_zero,
  rw [add_comm, int.ceil_add_int a floor_x_core_sub_ei_corner, ceil_a_val] at floor_x_core_sub_ei_corner_add_a_le_zero,
  exact ⟨a_ne_zero, by linarith⟩,
end

lemma facesharing_corner_faceshares_case_two (d : ℕ) (a : ℝ) (floor_x_corner_core : ℤ) (T : set (point d))
  (T_is_tiling : is_tiling T) (x : int_point d) (i : fin d) (x_corner x_corner_core : point d)
  (x_corner_core_in_T : x_corner_core ∈ T) (x_core : point d) (x_core_in_x_corner_core : in_cube x_corner_core x_core)
  (y : int_point d) (x_corner_def : x_corner = add_vectors x_corner_core (int_point_to_point (double_int_vector y)))
  (x_in_x_corner : int_point_to_point x ∈ cube x_corner)
  (x_eq_x_core_add_2y : int_point_to_point x = add_vectors x_core (int_point_to_point (double_int_vector y)))
  (zero_le_a : 0 ≤ a) (a_lt_one : a < 1)
  (x_corner_core_eq_a_mod_one : vector.nth x_corner_core i = ↑floor_x_corner_core + a) :
  let core_points : set (point d) :=
        {x :
           point d | ∀ (i : fin d),
           vector.nth x i = 0 ∨ vector.nth x i = 1},
      T_core : set (point d) :=
        {t ∈ T | ∃ (p : point d) (H : p ∈ core_points), in_cube t p},
      T' : set (point d) :=
        {t' :
           point d | ∃ (t : point d) (H : t ∈ T_core) (x : int_point d),
           t' = add_vectors t (int_point_to_point (double_int_vector x))}
  in (∀ (x : point d),
        (∀ (i : fin d), vector.nth x i ≥ 0 ∧ vector.nth x i ≤ 1) →
        (∃ (t' : point d) (H : t' ∈ T'),
           in_cube t' x ∧
             ∀ (alt_t' : point d),
               alt_t' ∈ T' → in_cube alt_t' x → t' = alt_t')) →
     ∀ (T'_is_tiling : is_tiling T'),
       is_periodic T'_is_tiling →
       is_facesharing (int_point_to_corner T'_is_tiling x).val
         (point_to_corner T'_is_tiling
            (add_vectors (int_point_to_point x) (unit_basis_vector i))).val →
       x_core ∈ core_points →
       (∀ (alt_corner : point d),
          alt_corner ∈ T' →
          int_point_to_point x ∈ cube alt_corner →
          alt_corner = x_corner) →
       x_corner_core ∈ T' →
       (let int_x_core : int_point d :=
              vector.of_fn
                (λ (i : fin d), ite (vector.nth x_core i < 1 / 2) 0 1)
        in (∀ (i : fin d),
              vector.nth x_core i = ↑(vector.nth int_x_core i)) →
           x_corner_core = (int_point_to_corner T'_is_tiling int_x_core).val →
           add_vectors (int_point_to_corner T'_is_tiling int_x_core).val
               (int_point_to_point (double_int_vector y)) =
             (int_point_to_corner T'_is_tiling
                (add_int_vectors int_x_core (double_int_vector y))).val →
           (int_point_to_corner T'_is_tiling
                (add_int_vectors int_x_core (double_int_vector y))).val =
             x_corner →
           add_vectors (int_point_to_corner T'_is_tiling int_x_core).val
               (int_point_to_point (double_int_vector y)) =
             x_corner →
           add_vectors
               (add_vectors (int_point_to_corner T'_is_tiling int_x_core).val
                  (int_point_to_point (double_int_vector y)))
               (unit_basis_vector i) =
             add_vectors x_corner (unit_basis_vector i) →
           add_vectors x_corner (unit_basis_vector i) =
             (point_to_corner T'_is_tiling
                (add_vectors (int_point_to_point x)
                   (unit_basis_vector i))).val →
           add_vectors
               (add_vectors (int_point_to_corner T'_is_tiling int_x_core).val
                  (int_point_to_point (double_int_vector y)))
               (unit_basis_vector i) =
             (point_to_corner T'_is_tiling
                (add_vectors (int_point_to_point x)
                   (unit_basis_vector i))).val →
           ∀
           (x_core_add_2y_add_unit_basis_vector_corner_h :
             {corner // corner ∈ T' ∧
                add_vectors
                      (add_vectors x_core
                         (int_point_to_point (double_int_vector y)))
                      (unit_basis_vector i) ∈
                    cube corner ∧
                  ∀ (alt_corner : point d),
                    alt_corner ∈ T' →
                    add_vectors
                        (add_vectors x_core
                           (int_point_to_point (double_int_vector y)))
                        (unit_basis_vector i) ∈
                      cube alt_corner →
                    alt_corner = corner}),
             let x_core_add_2y_add_unit_basis_vector_corner : point d :=
                   x_core_add_2y_add_unit_basis_vector_corner_h.val
             in x_core_add_2y_add_unit_basis_vector_corner =
                  x_core_add_2y_add_unit_basis_vector_corner_h.val →
                x_core_add_2y_add_unit_basis_vector_corner_h.val ∈ T' →
                add_vectors
                    (add_vectors x_core
                       (int_point_to_point (double_int_vector y)))
                    (unit_basis_vector i) ∈
                  cube x_core_add_2y_add_unit_basis_vector_corner_h.val →
                (∀ (alt_corner : point d),
                   alt_corner ∈ T' →
                   add_vectors
                       (add_vectors x_core
                          (int_point_to_point (double_int_vector y)))
                       (unit_basis_vector i) ∈
                     cube alt_corner →
                   alt_corner =
                     x_core_add_2y_add_unit_basis_vector_corner_h.val) →
                (let int_x_core_add_ei : int_point d :=
                       vector.of_fn
                         (λ (j : fin d),
                            ite (i = j) (vector.nth int_x_core j + 1)
                              (vector.nth int_x_core j))
                 in (int_point_to_corner T'_is_tiling
                         (add_int_vectors int_x_core_add_ei
                            (double_int_vector y))).val =
                      add_vectors
                        (int_point_to_corner T'_is_tiling int_x_core_add_ei).val
                        (int_point_to_point (double_int_vector y)) →
                    add_vectors
                        (add_vectors x_core
                           (int_point_to_point (double_int_vector y)))
                        (unit_basis_vector i) =
                      int_point_to_point
                        (add_int_vectors int_x_core_add_ei
                           (double_int_vector y)) →
                    (int_point_to_corner T'_is_tiling
                         (add_int_vectors int_x_core_add_ei
                            (double_int_vector y))).val =
                      (point_to_corner T'_is_tiling
                         (int_point_to_point
                            (add_int_vectors int_x_core_add_ei
                               (double_int_vector y)))).val →
                    add_vectors
                        (add_vectors
                           (int_point_to_corner T'_is_tiling int_x_core).val
                           (int_point_to_point (double_int_vector y)))
                        (unit_basis_vector i) =
                      add_vectors
                        (int_point_to_corner T'_is_tiling int_x_core_add_ei).val
                        (int_point_to_point (double_int_vector y)) →
                    add_vectors
                        (int_point_to_corner T'_is_tiling int_x_core).val
                        (unit_basis_vector i) =
                      (int_point_to_corner T'_is_tiling
                         int_x_core_add_ei).val →
                    (let int_x_core_sub_ei : int_point d :=
                           vector.of_fn
                             (λ (j : fin d),
                                ite (i = j) (vector.nth int_x_core j - 1)
                                  (vector.nth int_x_core j)),
                         facesharing_corner : point d :=
                           ite (vector.nth int_x_core i = 0)
                             (int_point_to_corner T'_is_tiling
                                int_x_core_add_ei).val
                             (int_point_to_corner T'_is_tiling
                                int_x_core_sub_ei).val
                     in facesharing_corner ∈ T →
                        (∀ (x : fin d),
                           vector.nth x_corner_core x -
                                 vector.nth facesharing_corner x =
                               1 ∨
                             vector.nth facesharing_corner x -
                                 vector.nth x_corner_core x =
                               1 →
                           (∃ (x_1 : fin d),
                              ¬(x = x_1 ∨
                                   vector.nth x_corner_core x_1 =
                                     vector.nth facesharing_corner x_1))) →
                        (∀ (t : vector ℝ d),
                           t ∈ T_i T' i x_core →
                           (∃ (z : ℤ), t.nth i = ↑z + a)) →
                        (∀ (y : ℤ),
                           ∃ (t : vector ℝ d) (H : t ∈ T_i T' i x_core),
                             t.nth i = ↑y + a ∧
                               ∀ (t' : vector ℝ d),
                                 t' ∈ T_i T' i x_core →
                                 t'.nth i = ↑y + a → t' = t) →
                        x_corner_core ∈ T_i T' i x_core →
                        ¬vector.nth int_x_core i = 0 →
                        vector.nth x_corner_core i -
                              vector.nth
                                (ite (vector.nth int_x_core i = 0)
                                   (int_point_to_corner T'_is_tiling
                                      int_x_core_add_ei).val
                                   (int_point_to_corner T'_is_tiling
                                      int_x_core_sub_ei).val)
                                i =
                            1 ∨
                          vector.nth
                                (ite (vector.nth int_x_core i = 0)
                                   (int_point_to_corner T'_is_tiling
                                      int_x_core_add_ei).val
                                   (int_point_to_corner T'_is_tiling
                                      int_x_core_sub_ei).val)
                                i -
                              vector.nth x_corner_core i =
                            1))) :=
begin
  intros core_points T_core T' T'_covers_core T'_is_tiling T'_is_periodic T'_has_facesharing x_core_in_core_points
    x_corner_unique x_corner_core_in_T' int_x_core x_core_eq_int_x_core x_corner_core_eq_int_x_core_corner
    x_corner_core_add_2y_eq_x_core_add_2y_corner x_core_add_2y_corner_eq_x_corner x_corner_core_add_2y_eq_x_corner
    x_corner_core_add_2y_add_unit_basis_vector_eq_x_corner_add_unit_basis_vector
    x_corner_add_unit_basis_vector_eq_x_add_unit_basis_vector_corner
    x_corner_core_add_2y_add_unit_basis_vector_eq_x_add_unit_basis_vector_corner x_core_add_2y_add_unit_basis_vector_corner_h
    x_core_add_2y_add_unit_basis_vector_corner x_core_add_2y_add_unit_basis_vector_corner_def
    x_core_add_2y_add_unit_basis_vector_corner_in_T' x_core_add_2y_add_unit_basis_vector_in_its_corner
    x_core_add_2y_add_unit_basis_vector_corner_unique int_x_core_add_ei
    x_core_add_2y_add_unit_basis_vector_corner_eq_x_core_add_unit_basis_vector_corner_add_2y
    x_core_add_2y_add_ei_eq_int_x_core_add_ei_add_2y coe_step
    x_corner_core_add_2y_add_unit_basis_vector_eq_x_core_add_2y_add_unit_basis_vector_corner
    x_core_corner_add_unit_basis_vector_eq_int_x_core_add_ei_corner int_x_core_sub_ei facesharing_corner facesharing_corner_in_T
    T_faceshare_free all_corners_eq_a_mod_one all_ints_covered_with_corner x_corner_core_in_T'_i_x_core x_core_eq_zero,
  rename x_core_eq_zero x_core_ne_zero,
  rw if_neg x_core_ne_zero,
  have coe_x_core_ne_zero : ¬↑(vector.nth int_x_core i) = (0 : ℝ) := by assumption_mod_cast,
  rw ← x_core_eq_int_x_core i at coe_x_core_ne_zero,
  have x_core_eq_one := x_core_in_core_points i,
  cases x_core_eq_one, {exfalso, exact coe_x_core_ne_zero x_core_eq_one},
  left,
  have floor_x_corner_core_val : (a ≠ 0 ∧ floor_x_corner_core = 0) ∨ (a = 0 ∧ floor_x_corner_core = 1) :=
    begin
      rw in_cube at x_core_in_x_corner_core,
      replace x_core_in_x_corner_core := x_core_in_x_corner_core i,
      rw [x_core_eq_one, x_corner_core_eq_a_mod_one] at x_core_in_x_corner_core,
      cases x_core_in_x_corner_core,
      replace x_core_in_x_corner_core_left := int.ceil_mono x_core_in_x_corner_core_left,
      rw [add_comm, int.ceil_add_int a floor_x_corner_core, ceil_one] at x_core_in_x_corner_core_left,
      by_cases a_eq_zero : 0 = a,
      { right,
        split, {symmetry, exact a_eq_zero},
        rw [← a_eq_zero, int.ceil_zero] at x_core_in_x_corner_core_left,
        rw ← a_eq_zero at x_core_in_x_corner_core_right,
        replace x_core_in_x_corner_core_right : 1 < floor_x_corner_core + 0 + 1 := by assumption_mod_cast,
        linarith,
      },
      rename a_eq_zero a_ne_zero,
      left,
      split, {intro a_eq_zero, symmetry' at a_eq_zero, exact a_ne_zero a_eq_zero,},
      have zero_lt_a := lt_of_le_of_ne zero_le_a a_ne_zero,
      have ceil_a_eq_one : int.ceil(a) = 1 :=
        begin
          have one_sub_one_lt_a : 1 - 1 < a := by linarith,
          have coe_one_sub_one_lt_a : ↑(1 : ℤ) - 1 < a := by assumption_mod_cast,
          have a_le_one := le_of_lt a_lt_one,
          have coe_a_le_one : a ≤ ↑(1 : ℤ) := by assumption_mod_cast,
          exact ceil_val coe_one_sub_one_lt_a coe_a_le_one,
        end,
      rw ceil_a_eq_one at x_core_in_x_corner_core_left,
      replace x_core_in_x_corner_core_right := int.floor_mono (le_of_lt x_core_in_x_corner_core_right),
      rw [add_comm (↑floor_x_corner_core : ℝ) a, add_assoc] at x_core_in_x_corner_core_right,
      replace x_core_in_x_corner_core_right : ⌊(1 : ℝ)⌋ ≤ ⌊a + ↑(floor_x_corner_core + 1)⌋ := by assumption_mod_cast,
      have coe_zero_le_a : ↑(0 : ℤ) ≤ a := by assumption_mod_cast,
      have a_lt_zero_add_one : a < 0 + 1 := by linarith,
      have coe_a_lt_zero_add_one : a < ↑(0 : ℤ) + 1 := by assumption_mod_cast,
      have a_floor_val := floor_val coe_zero_le_a coe_a_lt_zero_add_one,
      rw [int.floor_one, int.floor_add_int a (floor_x_corner_core + 1), a_floor_val] at x_core_in_x_corner_core_right,
      linarith,
    end,
  have x_core_sub_ei_corner_property := (int_point_to_corner T'_is_tiling int_x_core_sub_ei).property,
  rcases x_core_sub_ei_corner_property with
      ⟨x_core_sub_ei_corner_in_T', x_core_sub_ei_in_x_core_sub_ei_corner, x_core_sub_ei_corner_unique⟩,
  have x_core_sub_ei_corner_in_T'_i_x_core : (int_point_to_corner T'_is_tiling int_x_core_sub_ei).val ∈ T_i T' i x_core :=
    begin
      split, exact x_core_sub_ei_corner_in_T',
      simp only,
      rw [set.ne_empty_iff_nonempty, set.nonempty_def, cube, line_i],
      use (int_point_to_point int_x_core_sub_ei),
      simp only [set.mem_inter_eq, set.mem_set_of_eq],
      rw cube at x_core_sub_ei_in_x_core_sub_ei_corner,
      simp only [set.mem_set_of_eq] at x_core_sub_ei_in_x_core_sub_ei_corner,
      split, exact x_core_sub_ei_in_x_core_sub_ei_corner,
      intro j,
      by_cases i_eq_j : i = j, {left, exact i_eq_j,},
      rename i_eq_j i_ne_j,
      right,
      dsimp[int_x_core_sub_ei],
      conv
      begin
        find (int_point_to_point _) {rw int_point_to_point},
      end,
      simp only [vector.nth_of_fn],
      rw if_neg i_ne_j,
      replace x_core_in_core_points := x_core_in_core_points j,
      cases x_core_in_core_points,
      { rw x_core_in_core_points,
        simp only [one_div, int.cast_zero, if_true, zero_lt_bit0, zero_lt_one, inv_pos],
      },
      rw x_core_in_core_points,
      have one_ge_one_half : ¬(1 < (1/2 : ℝ)) := by linarith,
      rw if_neg one_ge_one_half,
      simp only [int.cast_one],
    end,
  have x_core_sub_ei_corner_eq_a_mod_one :=
    all_corners_eq_a_mod_one (int_point_to_corner T'_is_tiling int_x_core_sub_ei).val x_core_sub_ei_corner_in_T'_i_x_core,
  cases x_core_sub_ei_corner_eq_a_mod_one with floor_x_core_sub_ei_corner x_core_sub_ei_corner_eq_a_mod_one,
  have floor_x_core_sub_ei_corner_val :
    (a ≠ 0 ∧ floor_x_core_sub_ei_corner = -1) ∨ (a = 0 ∧ floor_x_core_sub_ei_corner = 0) :=
    begin
      exact floor_x_core_sub_ei_corner_val d a floor_x_corner_core floor_x_core_sub_ei_corner T T_is_tiling x i x_corner
        x_corner_core x_corner_core_in_T x_core x_core_in_x_corner_core y x_corner_def x_in_x_corner x_eq_x_core_add_2y
        zero_le_a a_lt_one x_corner_core_eq_a_mod_one coe_x_core_ne_zero x_core_eq_one floor_x_corner_core_val T'_covers_core
        T'_is_tiling T'_is_periodic T'_has_facesharing x_core_in_core_points x_corner_unique x_corner_core_in_T'
        x_core_eq_int_x_core x_corner_core_eq_int_x_core_corner x_corner_core_add_2y_eq_x_core_add_2y_corner
        x_core_add_2y_corner_eq_x_corner x_corner_core_add_2y_eq_x_corner
        x_corner_core_add_2y_add_unit_basis_vector_eq_x_corner_add_unit_basis_vector
        x_corner_add_unit_basis_vector_eq_x_add_unit_basis_vector_corner
        x_corner_core_add_2y_add_unit_basis_vector_eq_x_add_unit_basis_vector_corner
        x_core_add_2y_add_unit_basis_vector_corner_h x_core_add_2y_add_unit_basis_vector_corner_def
        x_core_add_2y_add_unit_basis_vector_corner_in_T' x_core_add_2y_add_unit_basis_vector_in_its_corner
        x_core_add_2y_add_unit_basis_vector_corner_unique
        x_core_add_2y_add_unit_basis_vector_corner_eq_x_core_add_unit_basis_vector_corner_add_2y
        x_core_add_2y_add_ei_eq_int_x_core_add_ei_add_2y coe_step
        x_corner_core_add_2y_add_unit_basis_vector_eq_x_core_add_2y_add_unit_basis_vector_corner
        x_core_corner_add_unit_basis_vector_eq_int_x_core_add_ei_corner facesharing_corner_in_T T_faceshare_free
        all_corners_eq_a_mod_one all_ints_covered_with_corner x_corner_core_in_T'_i_x_core x_core_ne_zero
        x_core_sub_ei_corner_in_T' x_core_sub_ei_in_x_core_sub_ei_corner x_core_sub_ei_corner_unique
        x_core_sub_ei_corner_in_T'_i_x_core x_core_sub_ei_corner_eq_a_mod_one,
    end,
  by_cases a_eq_zero : a = 0,
  { rcases floor_x_corner_core_val with ⟨a_ne_zero, floor_x_corner_core_val⟩ | ⟨a_eq_zero, floor_x_corner_core_val⟩,
    { exfalso,
      exact a_ne_zero a_eq_zero,
    },
    rcases floor_x_core_sub_ei_corner_val with
      ⟨a_ne_zero, floor_x_core_sub_ei_corner_val⟩ | ⟨a_eq_zero, floor_x_core_sub_ei_corner_val⟩,
    { exfalso,
      exact a_ne_zero a_eq_zero,
    },
    rw [x_corner_core_eq_a_mod_one, x_core_sub_ei_corner_eq_a_mod_one, floor_x_corner_core_val,
        floor_x_core_sub_ei_corner_val],
    simp only [int.cast_zero, int.cast_one, zero_add, int.cast_neg],
    linarith,
  },
  rename a_eq_zero a_ne_zero,
  rcases floor_x_corner_core_val with ⟨a_ne_zero, floor_x_corner_core_val⟩ | ⟨a_eq_zero, floor_x_corner_core_val⟩,
  { rcases floor_x_core_sub_ei_corner_val with
      ⟨a_ne_zero, floor_x_core_sub_ei_corner_val⟩ | ⟨a_eq_zero, floor_x_core_sub_ei_corner_val⟩,
    { rw [x_corner_core_eq_a_mod_one, x_core_sub_ei_corner_eq_a_mod_one, floor_x_corner_core_val,
          floor_x_core_sub_ei_corner_val],
      simp only [int.cast_zero, int.cast_one, zero_add, int.cast_neg],
      linarith,
    },
    exfalso,
    exact a_ne_zero a_eq_zero,
  },
  exfalso,
  exact a_ne_zero a_eq_zero,
end

lemma T_has_facesharing_from_T_core_has_facesharing (d : ℕ) (T : set (point d)) (T_is_tiling : is_tiling T)
  (T_faceshare_free : tiling_faceshare_free T) (x : int_point d) (i : fin d) (x_corner x_corner_core : point d)
  (x_corner_core_in_T : x_corner_core ∈ T) (x_core : point d) (x_core_in_x_corner_core : in_cube x_corner_core x_core)
  (y : int_point d) (x_corner_def : x_corner = add_vectors x_corner_core (int_point_to_point (double_int_vector y)))
  (x_in_x_corner : int_point_to_point x ∈ cube x_corner)
  (x_eq_x_core_add_2y : int_point_to_point x = add_vectors x_core (int_point_to_point (double_int_vector y))) :
  let core_points : set (point d) :=
        {x :
           point d | ∀ (i : fin d),
           vector.nth x i = 0 ∨ vector.nth x i = 1},
      T_core : set (point d) :=
        {t ∈ T | ∃ (p : point d) (H : p ∈ core_points), in_cube t p},
      T' : set (point d) :=
        {t' :
           point d | ∃ (t : point d) (H : t ∈ T_core) (x : int_point d),
           t' = add_vectors t (int_point_to_point (double_int_vector x))}
  in (∀ (x : point d),
        (∀ (i : fin d), vector.nth x i ≥ 0 ∧ vector.nth x i ≤ 1) →
        (∃ (t' : point d) (H : t' ∈ T'),
           in_cube t' x ∧
             ∀ (alt_t' : point d),
               alt_t' ∈ T' → in_cube alt_t' x → t' = alt_t')) →
     ∀ (T'_is_tiling : is_tiling T'),
       is_periodic T'_is_tiling →
       is_facesharing (int_point_to_corner T'_is_tiling x).val
         (point_to_corner T'_is_tiling
            (add_vectors (int_point_to_point x) (unit_basis_vector i))).val →
       x_core ∈ core_points →
       (∀ (alt_corner : point d),
          alt_corner ∈ T' →
          int_point_to_point x ∈ cube alt_corner →
          alt_corner = x_corner) →
       x_corner_core ∈ T' →
       (let int_x_core : int_point d :=
              vector.of_fn
                (λ (i : fin d), ite (vector.nth x_core i < 1 / 2) 0 1)
        in (∀ (i : fin d),
              vector.nth x_core i = ↑(vector.nth int_x_core i)) →
           x_corner_core = (int_point_to_corner T'_is_tiling int_x_core).val →
           add_vectors (int_point_to_corner T'_is_tiling int_x_core).val
               (int_point_to_point (double_int_vector y)) =
             (int_point_to_corner T'_is_tiling
                (add_int_vectors int_x_core (double_int_vector y))).val →
           (int_point_to_corner T'_is_tiling
                (add_int_vectors int_x_core (double_int_vector y))).val =
             x_corner →
           add_vectors (int_point_to_corner T'_is_tiling int_x_core).val
               (int_point_to_point (double_int_vector y)) =
             x_corner →
           add_vectors
               (add_vectors (int_point_to_corner T'_is_tiling int_x_core).val
                  (int_point_to_point (double_int_vector y)))
               (unit_basis_vector i) =
             add_vectors x_corner (unit_basis_vector i) →
           add_vectors x_corner (unit_basis_vector i) =
             (point_to_corner T'_is_tiling
                (add_vectors (int_point_to_point x)
                   (unit_basis_vector i))).val →
           add_vectors
               (add_vectors (int_point_to_corner T'_is_tiling int_x_core).val
                  (int_point_to_point (double_int_vector y)))
               (unit_basis_vector i) =
             (point_to_corner T'_is_tiling
                (add_vectors (int_point_to_point x)
                   (unit_basis_vector i))).val →
           ∀
           (x_core_add_2y_add_unit_basis_vector_corner_h :
             {corner // corner ∈ T' ∧
                add_vectors
                      (add_vectors x_core
                         (int_point_to_point (double_int_vector y)))
                      (unit_basis_vector i) ∈
                    cube corner ∧
                  ∀ (alt_corner : point d),
                    alt_corner ∈ T' →
                    add_vectors
                        (add_vectors x_core
                           (int_point_to_point (double_int_vector y)))
                        (unit_basis_vector i) ∈
                      cube alt_corner →
                    alt_corner = corner}),
             let x_core_add_2y_add_unit_basis_vector_corner : point d :=
                   x_core_add_2y_add_unit_basis_vector_corner_h.val
             in x_core_add_2y_add_unit_basis_vector_corner =
                  x_core_add_2y_add_unit_basis_vector_corner_h.val →
                x_core_add_2y_add_unit_basis_vector_corner_h.val ∈ T' →
                add_vectors
                    (add_vectors x_core
                       (int_point_to_point (double_int_vector y)))
                    (unit_basis_vector i) ∈
                  cube x_core_add_2y_add_unit_basis_vector_corner_h.val →
                (∀ (alt_corner : point d),
                   alt_corner ∈ T' →
                   add_vectors
                       (add_vectors x_core
                          (int_point_to_point (double_int_vector y)))
                       (unit_basis_vector i) ∈
                     cube alt_corner →
                   alt_corner =
                     x_core_add_2y_add_unit_basis_vector_corner_h.val) →
                (let int_x_core_add_ei : int_point d :=
                       vector.of_fn
                         (λ (j : fin d),
                            ite (i = j) (vector.nth int_x_core j + 1)
                              (vector.nth int_x_core j))
                 in (int_point_to_corner T'_is_tiling
                         (add_int_vectors int_x_core_add_ei
                            (double_int_vector y))).val =
                      add_vectors
                        (int_point_to_corner T'_is_tiling int_x_core_add_ei).val
                        (int_point_to_point (double_int_vector y)) →
                    add_vectors
                        (add_vectors x_core
                           (int_point_to_point (double_int_vector y)))
                        (unit_basis_vector i) =
                      int_point_to_point
                        (add_int_vectors int_x_core_add_ei
                           (double_int_vector y)) →
                    (int_point_to_corner T'_is_tiling
                         (add_int_vectors int_x_core_add_ei
                            (double_int_vector y))).val =
                      (point_to_corner T'_is_tiling
                         (int_point_to_point
                            (add_int_vectors int_x_core_add_ei
                               (double_int_vector y)))).val →
                    add_vectors
                        (add_vectors
                           (int_point_to_corner T'_is_tiling int_x_core).val
                           (int_point_to_point (double_int_vector y)))
                        (unit_basis_vector i) =
                      add_vectors
                        (int_point_to_corner T'_is_tiling int_x_core_add_ei).val
                        (int_point_to_point (double_int_vector y)) →
                    add_vectors
                        (int_point_to_corner T'_is_tiling int_x_core).val
                        (unit_basis_vector i) =
                      (int_point_to_corner T'_is_tiling
                         int_x_core_add_ei).val →
                    false)) :=
begin
  intros core_points T_core T' T'_covers_core T'_is_tiling T'_is_periodic T'_has_facesharing x_core_in_core_points x_corner_unique
    x_corner_core_in_T' int_x_core x_core_eq_int_x_core x_corner_core_eq_int_x_core_corner
    x_corner_core_add_2y_eq_x_core_add_2y_corner x_core_add_2y_corner_eq_x_corner x_corner_core_add_2y_eq_x_corner
    x_corner_core_add_2y_add_unit_basis_vector_eq_x_corner_add_unit_basis_vector
    x_corner_add_unit_basis_vector_eq_x_add_unit_basis_vector_corner
    x_corner_core_add_2y_add_unit_basis_vector_eq_x_add_unit_basis_vector_corner
    x_core_add_2y_add_unit_basis_vector_corner_h x_core_add_2y_add_unit_basis_vector_corner
    x_core_add_2y_add_unit_basis_vector_corner_def x_core_add_2y_add_unit_basis_vector_corner_in_T'
    x_core_add_2y_add_unit_basis_vector_in_its_corner x_core_add_2y_add_unit_basis_vector_corner_unique int_x_core_add_ei
    x_core_add_2y_add_unit_basis_vector_corner_eq_x_core_add_unit_basis_vector_corner_add_2y
    x_core_add_2y_add_ei_eq_int_x_core_add_ei_add_2y coe_step
    x_corner_core_add_2y_add_unit_basis_vector_eq_x_core_add_2y_add_unit_basis_vector_corner
    x_core_corner_add_unit_basis_vector_eq_int_x_core_add_ei_corner,
  let int_x_core_sub_ei : int_point d := vector.of_fn (λ j : fin d, if(i = j) then int_x_core.nth j - 1 else int_x_core.nth j),
  let facesharing_corner : point d :=
    if(int_x_core.nth i = 0) then (int_point_to_corner T'_is_tiling int_x_core_add_ei).val
    else (int_point_to_corner T'_is_tiling int_x_core_sub_ei).val,
  have facesharing_corner_in_T : facesharing_corner ∈ T :=
    begin
      dsimp only[facesharing_corner],
      by_cases int_x_core_eq_zero : int_x_core.nth i = 0,
      { rw int_x_core_eq_zero,
        simp only [if_true, eq_self_iff_true],
        have int_x_core_add_ei_corner_property := (int_point_to_corner T'_is_tiling int_x_core_add_ei).property,
        rcases int_x_core_add_ei_corner_property with
          ⟨int_x_core_add_ei_corner_in_T', int_x_core_add_ei_in_int_x_core_add_ei_corner, int_x_core_add_ei_corner_unique⟩,
        have int_x_core_add_ei_corner'_property := (int_point_to_corner T_is_tiling int_x_core_add_ei).property,
        rcases int_x_core_add_ei_corner'_property with
          ⟨int_x_core_add_ei_corner'_in_T, int_x_core_add_ei_in_int_x_core_add_ei_corner', int_x_core_add_ei_corner'_unique⟩,
        have int_x_core_add_ei_corner'_in_T_core : (int_point_to_corner T_is_tiling int_x_core_add_ei).val ∈ T_core :=
          begin
            split, exact int_x_core_add_ei_corner'_in_T,
            simp only [exists_prop, set.mem_set_of_eq],
            use (int_point_to_point int_x_core_add_ei),
            split,
            { intro j,
              by_cases i_eq_j : i = j,
              { right,
                dsimp only[int_x_core_add_ei],
                rw [int_point_to_point, ← i_eq_j],
                simp only [add_left_eq_self, one_div, int.cast_eq_zero, int.cast_add, if_true, not_lt, eq_self_iff_true,
                  int.cast_one, vector.nth_of_fn, one_ne_zero, ite_eq_left_iff],
                rw [x_core_eq_int_x_core i, int_x_core_eq_zero],
                simp only [int.cast_zero, inv_nonpos],
                intro two_le_zero,
                linarith,
              },
              rename i_eq_j i_ne_j,
              have int_x_core_add_ei_eq_int_x_core : int_x_core_add_ei.nth j = int_x_core.nth j :=
                begin
                  dsimp only[int_x_core_add_ei],
                  simp only [add_right_eq_self, vector.nth_of_fn, ite_eq_right_iff, one_ne_zero],
                  exact i_ne_j,
                end,
              replace x_core_in_core_points := x_core_in_core_points j,
              conv
              begin
                find (int_point_to_point _) {rw int_point_to_point},
                find (int_point_to_point _) {rw int_point_to_point},
              end,
              simp only [int.cast_eq_zero, vector.nth_of_fn],
              rw if_neg i_ne_j,
              by_cases ite_cond : vector.nth x_core j < 1 / 2,
              { rw if_pos ite_cond,
                left,
                refl,
              },
              rw if_neg ite_cond,
              right,
              have one_eq_one : 1 = 1 := by refl,
              exact_mod_cast one_eq_one,
            },
            exact int_x_core_add_ei_in_int_x_core_add_ei_corner',
          end,
        have int_x_core_add_ei_corner'_in_T' : (int_point_to_corner T_is_tiling int_x_core_add_ei).val ∈ T' :=
          begin
            use [(int_point_to_corner T_is_tiling int_x_core_add_ei).val, int_x_core_add_ei_corner'_in_T_core, int_zero_vector],
            apply vector.ext,
            intro j,
            dsimp[int_zero_vector],
            rw [double_int_vector, add_vectors],
            conv
            begin
              find (int_point_to_point _) {rw int_point_to_point},
            end,
            simp only [int.cast_eq_zero, false_or, vector.nth_of_fn, self_eq_add_right, bit0_eq_zero, one_ne_zero, mul_eq_zero],
          end,
        have int_x_core_add_ei_corner'_eq_int_x_core_add_ei_corner :=
          int_x_core_add_ei_corner_unique (int_point_to_corner T_is_tiling int_x_core_add_ei).val int_x_core_add_ei_corner'_in_T'
          int_x_core_add_ei_in_int_x_core_add_ei_corner',
        rw ← int_x_core_add_ei_corner'_eq_int_x_core_add_ei_corner,
        exact int_x_core_add_ei_corner'_in_T,
      },
      rename int_x_core_eq_zero int_x_core_ne_zero,
      have x_core_i_eq_one := x_core_in_core_points i,
      rw x_core_eq_int_x_core i at x_core_i_eq_one,
      cases x_core_i_eq_one,
      { have int_x_core_eq_zero : vector.nth int_x_core i = 0 := by exact_mod_cast x_core_i_eq_one,
        exfalso,
        exact int_x_core_ne_zero int_x_core_eq_zero,
      },
      have int_x_core_eq_one : int_x_core.nth i = 1 := by exact_mod_cast x_core_i_eq_one,
      rw int_x_core_eq_one,
      simp only [if_false, one_ne_zero],
      have int_x_core_sub_ei_corner_property := (int_point_to_corner T'_is_tiling int_x_core_sub_ei).property,
      rcases int_x_core_sub_ei_corner_property with
        ⟨int_x_core_sub_ei_corner_in_T', int_x_core_sub_ei_in_int_x_core_sub_ei_corner, int_x_core_sub_ei_corner_unique⟩,
      have int_x_core_sub_ei_corner'_property := (int_point_to_corner T_is_tiling int_x_core_sub_ei).property,
      rcases int_x_core_sub_ei_corner'_property with
        ⟨int_x_core_sub_ei_corner'_in_T, int_x_core_sub_ei_in_int_x_core_sub_ei_corner', int_x_core_sub_ei_corner'_unique⟩,
      have int_x_core_sub_ei_corner'_in_T_core : (int_point_to_corner T_is_tiling int_x_core_sub_ei).val ∈ T_core :=
        begin
          split, exact int_x_core_sub_ei_corner'_in_T,
          simp only [exists_prop, set.mem_set_of_eq],
          use (int_point_to_point int_x_core_sub_ei),
          split,
          { intro j,
            by_cases i_eq_j : i = j,
            { left,
              dsimp only[int_x_core_sub_ei],
              rw [int_point_to_point, ← i_eq_j],
              simp only [add_left_eq_self, int.cast_eq_zero, int.cast_add, if_true, not_lt, eq_self_iff_true, int.cast_one,
                vector.nth_of_fn, one_ne_zero, ite_eq_left_iff],
              by_cases ite_cond : vector.nth x_core i < 1 / 2,
              { exfalso,
                rw [x_core_eq_int_x_core i, int_x_core_eq_one] at ite_cond,
                simp only [int.cast_one, inv_nonpos] at ite_cond,
                linarith,
              },
              rw if_neg ite_cond,
              linarith,
            },
            rename i_eq_j i_ne_j,
            have int_x_core_sub_ei_eq_int_x_core : int_x_core_sub_ei.nth j = int_x_core.nth j :=
              begin
                dsimp only[int_x_core_sub_ei],
                simp only [sub_eq_self, vector.nth_of_fn, ite_eq_right_iff, one_ne_zero],
                exact i_ne_j,
              end,
            replace x_core_in_core_points := x_core_in_core_points j,
            conv
            begin
              find (int_point_to_point _) {rw int_point_to_point},
              find (int_point_to_point _) {rw int_point_to_point},
            end,
            simp only [int.cast_eq_zero, vector.nth_of_fn],
            rw if_neg i_ne_j,
            by_cases ite_cond : vector.nth x_core j < 1 / 2,
            { rw if_pos ite_cond,
              left,
              refl,
            },
            rw if_neg ite_cond,
            right,
            have one_eq_one : 1 = 1 := by refl,
            exact_mod_cast one_eq_one,
          },
          exact int_x_core_sub_ei_in_int_x_core_sub_ei_corner',
        end,
      have int_x_core_sub_ei_corner'_in_T' : (int_point_to_corner T_is_tiling int_x_core_sub_ei).val ∈ T' :=
        begin
          use [(int_point_to_corner T_is_tiling int_x_core_sub_ei).val, int_x_core_sub_ei_corner'_in_T_core, int_zero_vector],
          apply vector.ext,
          intro j,
          dsimp[int_zero_vector],
          rw [double_int_vector, add_vectors],
          conv
          begin
            find (int_point_to_point _) {rw int_point_to_point},
          end,
          simp only [int.cast_eq_zero, false_or, vector.nth_of_fn, self_eq_add_right, bit0_eq_zero, one_ne_zero, mul_eq_zero],
        end,
      have int_x_core_sub_ei_corner'_eq_int_x_core_sub_ei_corner :=
        int_x_core_sub_ei_corner_unique (int_point_to_corner T_is_tiling int_x_core_sub_ei).val int_x_core_sub_ei_corner'_in_T'
        int_x_core_sub_ei_in_int_x_core_sub_ei_corner',
      rw ← int_x_core_sub_ei_corner'_eq_int_x_core_sub_ei_corner,
      exact int_x_core_sub_ei_corner'_in_T,
    end,
  replace T_faceshare_free := T_faceshare_free x_corner_core x_corner_core_in_T facesharing_corner facesharing_corner_in_T,
  rw is_facesharing at T_faceshare_free,
  simp only [not_exists, not_and, not_forall] at T_faceshare_free,
  have facesharing_corner_faceshares : vector.nth x_corner_core i - vector.nth facesharing_corner i = 1 ∨
    vector.nth facesharing_corner i - vector.nth x_corner_core i = 1 :=
    begin
      rw tiling_lattice_structure d T' i at T'_is_tiling,
      replace T'_is_tiling := T'_is_tiling x_core,
      rw is_i_lattice at T'_is_tiling,
      rcases T'_is_tiling with ⟨a, zero_le_a, a_lt_one, all_corners_eq_a_mod_one, all_ints_covered_with_corner⟩,
      have x_corner_core_in_T'_i_x_core : x_corner_core ∈ T_i T' i x_core :=
        begin
          split, exact x_corner_core_in_T',
          simp only,
          rw [set.ne_empty_iff_nonempty, set.nonempty_def, cube, line_i],
          use x_core,
          simp only [set.mem_inter_eq, set.mem_set_of_eq],
          exact ⟨x_core_in_x_corner_core, by {intro j, right, refl,}⟩,
        end,
      have x_corner_core_eq_a_mod_one := all_corners_eq_a_mod_one x_corner_core x_corner_core_in_T'_i_x_core,
      cases x_corner_core_eq_a_mod_one with floor_x_corner_core x_corner_core_eq_a_mod_one,
      dsimp only[facesharing_corner],
      by_cases x_core_eq_zero : vector.nth int_x_core i = 0,
      { exact facesharing_corner_faceshares_case_one d a floor_x_corner_core T T_is_tiling x i x_corner x_corner_core
          x_corner_core_in_T x_core x_core_in_x_corner_core y x_corner_def x_in_x_corner x_eq_x_core_add_2y zero_le_a
          a_lt_one x_corner_core_eq_a_mod_one T'_covers_core T'_is_tiling T'_is_periodic T'_has_facesharing
          x_core_in_core_points x_corner_unique x_corner_core_in_T' x_core_eq_int_x_core x_corner_core_eq_int_x_core_corner
          x_corner_core_add_2y_eq_x_core_add_2y_corner x_core_add_2y_corner_eq_x_corner x_corner_core_add_2y_eq_x_corner
          x_corner_core_add_2y_add_unit_basis_vector_eq_x_corner_add_unit_basis_vector
          x_corner_add_unit_basis_vector_eq_x_add_unit_basis_vector_corner
          x_corner_core_add_2y_add_unit_basis_vector_eq_x_add_unit_basis_vector_corner
          x_core_add_2y_add_unit_basis_vector_corner_h x_core_add_2y_add_unit_basis_vector_corner_def
          x_core_add_2y_add_unit_basis_vector_corner_in_T' x_core_add_2y_add_unit_basis_vector_in_its_corner
          x_core_add_2y_add_unit_basis_vector_corner_unique
          x_core_add_2y_add_unit_basis_vector_corner_eq_x_core_add_unit_basis_vector_corner_add_2y
          x_core_add_2y_add_ei_eq_int_x_core_add_ei_add_2y coe_step
          x_corner_core_add_2y_add_unit_basis_vector_eq_x_core_add_2y_add_unit_basis_vector_corner
          x_core_corner_add_unit_basis_vector_eq_int_x_core_add_ei_corner facesharing_corner_in_T T_faceshare_free
          all_corners_eq_a_mod_one all_ints_covered_with_corner x_corner_core_in_T'_i_x_core x_core_eq_zero,
      },
      exact facesharing_corner_faceshares_case_two d a floor_x_corner_core T T_is_tiling x i x_corner x_corner_core
        x_corner_core_in_T x_core x_core_in_x_corner_core y x_corner_def x_in_x_corner x_eq_x_core_add_2y zero_le_a
        a_lt_one x_corner_core_eq_a_mod_one T'_covers_core T'_is_tiling T'_is_periodic T'_has_facesharing
        x_core_in_core_points x_corner_unique x_corner_core_in_T' x_core_eq_int_x_core x_corner_core_eq_int_x_core_corner
        x_corner_core_add_2y_eq_x_core_add_2y_corner x_core_add_2y_corner_eq_x_corner x_corner_core_add_2y_eq_x_corner
        x_corner_core_add_2y_add_unit_basis_vector_eq_x_corner_add_unit_basis_vector
        x_corner_add_unit_basis_vector_eq_x_add_unit_basis_vector_corner
        x_corner_core_add_2y_add_unit_basis_vector_eq_x_add_unit_basis_vector_corner
        x_core_add_2y_add_unit_basis_vector_corner_h x_core_add_2y_add_unit_basis_vector_corner_def
        x_core_add_2y_add_unit_basis_vector_corner_in_T' x_core_add_2y_add_unit_basis_vector_in_its_corner
        x_core_add_2y_add_unit_basis_vector_corner_unique
        x_core_add_2y_add_unit_basis_vector_corner_eq_x_core_add_unit_basis_vector_corner_add_2y
        x_core_add_2y_add_ei_eq_int_x_core_add_ei_add_2y coe_step
        x_corner_core_add_2y_add_unit_basis_vector_eq_x_core_add_2y_add_unit_basis_vector_corner
        x_core_corner_add_unit_basis_vector_eq_int_x_core_add_ei_corner facesharing_corner_in_T T_faceshare_free
        all_corners_eq_a_mod_one all_ints_covered_with_corner x_corner_core_in_T'_i_x_core x_core_eq_zero,
    end,
  replace T_faceshare_free := T_faceshare_free i facesharing_corner_faceshares,
  cases T_faceshare_free with coord x_corner_core_ne_facesharing_corner_at_coord,
  rw not_or_distrib at x_corner_core_ne_facesharing_corner_at_coord,
  cases x_corner_core_ne_facesharing_corner_at_coord with i_ne_coord x_corner_core_ne_facesharing_corner_at_coord,
  by_cases int_x_core_eq_zero_at_i : vector.nth int_x_core i = 0,
  { have facesharing_corner_rw : facesharing_corner = (int_point_to_corner T'_is_tiling int_x_core_add_ei).val :=
      begin
        dsimp[facesharing_corner],
        rw int_x_core_eq_zero_at_i,
        simp only [if_true, eq_self_iff_true],
      end,
    rw [facesharing_corner_rw, ← x_core_corner_add_unit_basis_vector_eq_int_x_core_add_ei_corner,
        x_corner_core_eq_int_x_core_corner, unit_basis_vector, add_vectors] at x_corner_core_ne_facesharing_corner_at_coord,
    simp only [exists_prop, and_true, vector.nth_of_fn, ite_eq_right_iff, self_eq_add_right, not_false_iff, one_ne_zero, not_forall]
      at x_corner_core_ne_facesharing_corner_at_coord,
    exact i_ne_coord x_corner_core_ne_facesharing_corner_at_coord,
  },
  rename int_x_core_eq_zero_at_i int_x_core_ne_zero_at_i,
  have facesharing_corner_rw : facesharing_corner = (int_point_to_corner T'_is_tiling int_x_core_sub_ei).val :=
    by {dsimp[facesharing_corner], rw if_neg int_x_core_ne_zero_at_i,},
  have x_core_corner_sub_unit_basis_vector_eq_int_x_core_sub_ei_corner :
    add_vectors (int_point_to_corner T'_is_tiling int_x_core).val (neg_unit_basis_vector i) =
    (int_point_to_corner T'_is_tiling int_x_core_sub_ei).val :=
    begin
      have x_core_add_ei_corner_property := (int_point_to_corner T'_is_tiling int_x_core_add_ei).property,
      rcases x_core_add_ei_corner_property with
        ⟨x_core_sub_ei_corner_in_T', x_core_add_ei_in_x_core_add_ei_corner, x_core_add_ei_corner_unique⟩,
      have x_core_sub_ei_corner_add_two_eq_x_core_add_ei_corner :
        add_vectors (int_point_to_corner T'_is_tiling int_x_core_sub_ei).val (add_vectors (unit_basis_vector i) (unit_basis_vector i))
        = (int_point_to_corner T'_is_tiling int_x_core_add_ei).val :=
        begin
          let translated_corner := add_vectors (int_point_to_corner T'_is_tiling int_x_core_sub_ei).val
            (add_vectors (unit_basis_vector i) (unit_basis_vector i)),
          have translated_corner_in_T' : translated_corner ∈ T' :=
            begin
              have int_x_core_sub_ei_corner_in_T_core : (int_point_to_corner T'_is_tiling int_x_core_sub_ei).val ∈ T_core :=
                begin
                  have int_x_core_sub_ei_corner_property := (int_point_to_corner T'_is_tiling int_x_core_sub_ei).property,
                  rcases int_x_core_sub_ei_corner_property with
                    ⟨int_x_core_sub_ei_corner_in_T', int_x_core_sub_ei_in_int_x_core_sub_ei_corner, int_x_core_sub_ei_corner_unique⟩,
                  rw facesharing_corner_rw at facesharing_corner_in_T,
                  change (int_point_to_corner T'_is_tiling int_x_core_sub_ei).val ∈ T ∧
                    ∃ (p : point d) (H : p ∈ core_points), in_cube (int_point_to_corner T'_is_tiling int_x_core_sub_ei).val p,
                  split, exact facesharing_corner_in_T,
                  have int_x_core_sub_ei_in_core_points : (int_point_to_point int_x_core_sub_ei) ∈ core_points :=
                    begin
                      intro j,
                      by_cases i_eq_j : i = j,
                      { have coe_int_x_core_ne_zero_at_i : ¬↑(vector.nth int_x_core i) = (0 : ℝ) := by assumption_mod_cast,
                        rw ← x_core_eq_int_x_core i at coe_int_x_core_ne_zero_at_i,
                        replace x_core_in_core_points := x_core_in_core_points i,
                        cases x_core_in_core_points, {exfalso, exact coe_int_x_core_ne_zero_at_i x_core_in_core_points,},
                        left,
                        dsimp only[int_x_core_sub_ei],
                        rw int_point_to_point,
                        simp only [int.cast_eq_zero, vector.nth_of_fn],
                        have one_ge_one_half : ¬(1 < (1/2 : ℝ)) := by linarith,
                        rw ← i_eq_j,
                        simp only [if_true, eq_self_iff_true],
                        rw [x_core_in_core_points, if_neg one_ge_one_half],
                        linarith,
                      },
                      rename i_eq_j i_ne_j,
                      replace x_core_in_core_points := x_core_in_core_points j,
                      rw x_core_eq_int_x_core j at x_core_in_core_points,
                      have int_x_core_sub_ei_eq_int_x_core : (int_point_to_point int_x_core_sub_ei).nth j = ↑(int_x_core.nth j) :=
                        begin
                          rw int_point_to_point,
                          dsimp[int_x_core_sub_ei],
                          simp only [sub_eq_self, int.cast_inj, vector.nth_of_fn, ite_eq_right_iff, one_ne_zero],
                          exact i_ne_j,
                        end,
                      rw int_x_core_sub_ei_eq_int_x_core,
                      exact x_core_in_core_points,
                    end,
                  use [int_point_to_point int_x_core_sub_ei, int_x_core_sub_ei_in_core_points],
                  assumption,
                end,
              let int_unit_basis_vector : int_point d := vector.of_fn (λ j : fin d, if(i = j) then 1 else 0),
              use [(int_point_to_corner T'_is_tiling int_x_core_sub_ei).val, int_x_core_sub_ei_corner_in_T_core, int_unit_basis_vector],
              dsimp only[translated_corner],
              rw [add_vectors_comm (int_point_to_corner T'_is_tiling int_x_core_sub_ei).val
                  (add_vectors (unit_basis_vector i) (unit_basis_vector i)), add_vectors_comm
                  (int_point_to_corner T'_is_tiling int_x_core_sub_ei).val
                  (int_point_to_point (double_int_vector int_unit_basis_vector))],
              apply add_same_vector (int_point_to_corner T'_is_tiling int_x_core_sub_ei).val,
              apply vector.ext,
              intro j,
              rw [double_int_vector, int_point_to_point, unit_basis_vector, add_vectors],
              simp only [mul_boole, vector.nth_of_fn],
              by_cases i_eq_j : i = j,
              { rw i_eq_j,
                simp only [int.cast_bit0, if_true, eq_self_iff_true, int.cast_one],
                linarith,
              },
              rw [if_neg i_eq_j, if_neg i_eq_j, add_zero],
              have zero_eq_zero : 0 = 0 := by refl,
              assumption_mod_cast,
            end,
          have x_core_add_ei_in_translated_corner : int_point_to_point int_x_core_add_ei ∈ cube translated_corner :=
            begin
              rw cube,
              simp only [set.mem_set_of_eq],
              rw in_cube,
              intro j,
              have int_x_core_sub_ei_corner_property := (int_point_to_corner T'_is_tiling int_x_core_sub_ei).property,
              rcases int_x_core_sub_ei_corner_property with
                ⟨int_x_core_sub_ei_corner_in_T', int_x_core_sub_ei_in_int_x_core_sub_ei_corner, int_x_core_sub_ei_corner_unique⟩,
              rw cube at int_x_core_sub_ei_in_int_x_core_sub_ei_corner,
              simp only [set.mem_set_of_eq] at int_x_core_sub_ei_in_int_x_core_sub_ei_corner,
              rw in_cube at int_x_core_sub_ei_in_int_x_core_sub_ei_corner,
              replace int_x_core_sub_ei_in_int_x_core_sub_ei_corner := int_x_core_sub_ei_in_int_x_core_sub_ei_corner j,
              cases int_x_core_sub_ei_in_int_x_core_sub_ei_corner,
              dsimp only[translated_corner],
              rw [unit_basis_vector, add_vectors],
              simp only [vector.nth_of_fn],
              rw add_vectors,
              simp only [vector.nth_of_fn],
              dsimp only [int_x_core_add_ei],
              simp only [vector.nth_of_fn],
              conv
              begin
                find (int_point_to_point _) {rw int_point_to_point},
                find (int_point_to_point _) {rw int_point_to_point},
              end,
              simp only [vector.nth_of_fn],
              by_cases i_eq_j : i = j,
              { rw ← i_eq_j,
                simp only [int.cast_add, if_true, eq_self_iff_true, int.cast_one, add_lt_add_iff_right],
                have coe_int_x_core_ne_zero_at_i : ¬↑(vector.nth int_x_core i) = (0 : ℝ) := by assumption_mod_cast,
                rw ← x_core_eq_int_x_core i at coe_int_x_core_ne_zero_at_i,
                replace x_core_in_core_points := x_core_in_core_points i,
                cases x_core_in_core_points, {exfalso, exact coe_int_x_core_ne_zero_at_i x_core_in_core_points,},
                rw x_core_in_core_points,
                have one_ge_one_half : ¬(1 < (1/2 : ℝ)) := by linarith,
                rw if_neg one_ge_one_half,
                rw ← i_eq_j at int_x_core_sub_ei_in_int_x_core_sub_ei_corner_left,
                rw ← i_eq_j at int_x_core_sub_ei_in_int_x_core_sub_ei_corner_right,
                conv at int_x_core_sub_ei_in_int_x_core_sub_ei_corner_left
                begin
                  find (int_point_to_point _) {rw int_point_to_point},
                end,
                conv at int_x_core_sub_ei_in_int_x_core_sub_ei_corner_right
                begin
                  find (int_point_to_point _) {rw int_point_to_point},
                end,
                simp only [if_true, eq_self_iff_true, int.cast_one, vector.nth_of_fn, int.cast_sub]
                  at int_x_core_sub_ei_in_int_x_core_sub_ei_corner_left,
                simp only [if_true, eq_self_iff_true, int.cast_one, vector.nth_of_fn, int.cast_sub]
                  at int_x_core_sub_ei_in_int_x_core_sub_ei_corner_right,
                rw [x_core_in_core_points, if_neg one_ge_one_half] at int_x_core_sub_ei_in_int_x_core_sub_ei_corner_left,
                rw [x_core_in_core_points, if_neg one_ge_one_half] at int_x_core_sub_ei_in_int_x_core_sub_ei_corner_right,
                rw x_core_eq_int_x_core i at x_core_in_core_points,
                have one_sub_one_rw : ↑(1 : ℤ) - (1 : ℝ) = 1 - 1 :=
                  begin
                    have one_refl : 1 = (1 : ℝ) := by refl,
                    have one_rw : ↑(1 : ℤ) = (1 : ℝ) := by assumption_mod_cast,
                    rw one_rw,
                  end,
                have one_plus_one_rw : ↑(1 : ℤ) + (1 : ℝ) = 1 + 1 :=
                  begin
                    have one_refl : 1 = (1 : ℝ) := by refl,
                    have one_rw : ↑(1 : ℤ) = (1 : ℝ) := by assumption_mod_cast,
                    rw one_rw,
                  end,
                rw one_sub_one_rw at int_x_core_sub_ei_in_int_x_core_sub_ei_corner_left,
                rw one_sub_one_rw at int_x_core_sub_ei_in_int_x_core_sub_ei_corner_right,
                rw one_plus_one_rw,
                split, linarith,
                linarith,
              },
              rename i_eq_j i_ne_j,
              repeat{rw if_neg i_ne_j,},
              repeat{rw add_zero},
              have ite_x_core_eq_int_x_core :
                ↑(ite (vector.nth x_core j < 1 / 2) 0 (1 : ℤ)) = vector.nth (int_point_to_point int_x_core_sub_ei) j :=
                begin
                  dsimp[int_x_core_sub_ei],
                  rw int_point_to_point,
                  simp only [int.cast_inj, vector.nth_of_fn],
                  rw if_neg i_ne_j,
                end,
              rw ite_x_core_eq_int_x_core,
              exact ⟨int_x_core_sub_ei_in_int_x_core_sub_ei_corner_left, int_x_core_sub_ei_in_int_x_core_sub_ei_corner_right⟩,
            end,
          exact x_core_add_ei_corner_unique translated_corner translated_corner_in_T' x_core_add_ei_in_translated_corner,
        end,
      apply @remove_same_vector d (add_vectors (int_point_to_corner T'_is_tiling int_x_core).val (neg_unit_basis_vector i))
        (int_point_to_corner T'_is_tiling int_x_core_sub_ei).val (add_vectors (unit_basis_vector i) (unit_basis_vector i)),
      rw [x_core_sub_ei_corner_add_two_eq_x_core_add_ei_corner, add_vectors_assoc (int_point_to_corner T'_is_tiling int_x_core).val
          (neg_unit_basis_vector i) (add_vectors (unit_basis_vector i) (unit_basis_vector i)), ← add_vectors_assoc
          (neg_unit_basis_vector i) (unit_basis_vector i) (unit_basis_vector i), add_vectors_comm (neg_unit_basis_vector i)
          (unit_basis_vector i), unit_basis_vector_add_neg_unit_basis_vector_eq_zero, zero_vector_add],
      exact x_core_corner_add_unit_basis_vector_eq_int_x_core_add_ei_corner,
    end,
  rw [facesharing_corner_rw, ← x_core_corner_sub_unit_basis_vector_eq_int_x_core_sub_ei_corner,
       x_corner_core_eq_int_x_core_corner, neg_unit_basis_vector, add_vectors] at x_corner_core_ne_facesharing_corner_at_coord,
  simp only [exists_prop, and_true, vector.nth_of_fn, ite_eq_right_iff, self_eq_add_right, not_false_iff, neg_eq_zero, one_ne_zero,
    not_forall] at x_corner_core_ne_facesharing_corner_at_coord,
  exact i_ne_coord x_corner_core_ne_facesharing_corner_at_coord,
end

lemma T'_faceshare_free (d : ℕ) (T : set (point d)) (T_is_tiling : is_tiling T) (T_faceshare_free : tiling_faceshare_free T) :
  let core_points : set (point d) :=
        {x :
           point d | ∀ (i : fin d),
           vector.nth x i = 0 ∨ vector.nth x i = 1},
      T_core : set (point d) :=
        {t ∈ T | ∃ (p : point d) (H : p ∈ core_points), in_cube t p},
      T' : set (point d) :=
        {t' :
           point d | ∃ (t : point d) (H : t ∈ T_core) (x : int_point d),
           t' = add_vectors t (int_point_to_point (double_int_vector x))}
  in (∀ (x : point d),
        (∀ (i : fin d), vector.nth x i ≥ 0 ∧ vector.nth x i ≤ 1) →
        (∃ (t' : point d) (H : t' ∈ T'),
           in_cube t' x ∧
             ∀ (alt_t' : point d),
               alt_t' ∈ T' → in_cube alt_t' x → t' = alt_t')) →
     ∀ (T'_is_tiling : is_tiling T'),
       is_periodic T'_is_tiling → tiling_faceshare_free T' :=
begin
  intros core_points T_core T' T'_covers_core T'_is_tiling T'_is_periodic,
  rw faceshare_free_lemma d T' T'_is_tiling,
  intros x i T'_has_facesharing,
  have x_corner := int_point_to_corner T'_is_tiling x,
  rcases x_corner with
    ⟨x_corner, ⟨x_corner_core, ⟨x_corner_core_in_T, x_core, x_core_in_core_points, x_core_in_x_corner_core⟩, y, x_corner_def⟩,
    x_in_x_corner, x_corner_unique⟩,
  have x_corner_core_in_T' : x_corner_core ∈ T' :=
    begin
      have x_corner_core_in_T_core : x_corner_core ∈ T_core :=
        begin
          split, exact x_corner_core_in_T,
          use [x_core, x_core_in_core_points],
          exact x_core_in_x_corner_core,
        end,
      let zero_vector : int_point d := vector.of_fn (λ j : fin d, 0),
      use [x_corner_core, x_corner_core_in_T_core, zero_vector],
      rw [double_int_vector, int_point_to_point, add_vectors],
      simp only [add_zero, int.cast_zero, vector.of_fn_nth, vector.nth_of_fn, mul_zero],
    end,
  let int_x_core : int_point d := vector.of_fn (λ i : fin d, if(vector.nth x_core i < 0.5) then 0 else 1),
  have x_core_eq_int_x_core : ∀ i : fin d, x_core.nth i = ↑(int_x_core.nth i) :=
    begin
      intro i,
      replace x_core_in_core_points := x_core_in_core_points i,
      dsimp[int_x_core],
      cases x_core_in_core_points,
      { rw x_core_in_core_points,
        simp only [one_div, vector.nth_of_fn],
        rw x_core_in_core_points,
        simp only [int.cast_zero, if_true, zero_lt_bit0, zero_lt_one, inv_pos],
      },
      rw x_core_in_core_points,
      simp only [vector.nth_of_fn],
      rw x_core_in_core_points,
      have one_ge_one_half : ¬(1 : ℝ) < 1/2 := by linarith,
      rw if_neg one_ge_one_half,
      have one_eq_one : (1 : ℝ) = 1 := by refl,
      assumption_mod_cast,
    end,
  have x_corner_core_eq_int_x_core_corner : x_corner_core = (int_point_to_corner T'_is_tiling int_x_core).val :=
    begin
      have int_x_core_corner := int_point_to_corner T'_is_tiling int_x_core,
      let x_core_corner' := (int_point_to_corner T'_is_tiling int_x_core).val,
      have x_core_corner'_def : x_core_corner' = (int_point_to_corner T'_is_tiling int_x_core).val := by refl,
      have x_core_corner'_property := (int_point_to_corner T'_is_tiling int_x_core).property,
      rw ← x_core_corner'_def at x_core_corner'_property,
      rcases x_core_corner'_property with ⟨x_core_corner'_in_T', int_x_core_in_x_core_corner', x_core_corner'_unique⟩,
      rw ← x_core_corner'_def,
      have int_x_core_in_x_corner_core : int_point_to_point int_x_core ∈ cube x_corner_core :=
        begin
          rw cube,
          simp only [set.mem_set_of_eq],
          rw in_cube,
          intro i,
          rw int_point_to_point,
          simp only [vector.nth_of_fn],
          rw in_cube at x_core_in_x_corner_core,
          dsimp only[core_points] at x_core_in_core_points,
          simp only [set.mem_set_of_eq] at x_core_in_core_points,
          cases x_core_in_core_points i with x_core_eq_zero x_core_eq_one,
          { rw x_core_eq_zero,
            simp only [one_div, inv_pos, zero_lt_bit0, zero_lt_one, if_true, int.cast_zero],
            rw ← x_core_eq_zero,
            exact x_core_in_x_corner_core i,
          },
          have one_ge_one_half : ¬((1 : ℝ) < 1 / 2) := by linarith,
          rw [x_core_eq_one, if_neg one_ge_one_half],
          simp only [int.cast_one],
          replace x_core_in_x_corner_core := x_core_in_x_corner_core i,
          rw x_core_eq_one at x_core_in_x_corner_core,
          exact x_core_in_x_corner_core,
        end,
      exact x_core_corner'_unique x_corner_core x_corner_core_in_T' int_x_core_in_x_corner_core,
    end,
  --t'(x')+2y = t'(x'+2y)
  have x_corner_core_add_2y_eq_x_core_add_2y_corner := T'_is_periodic int_x_core y,
  symmetry' at x_corner_core_add_2y_eq_x_core_add_2y_corner,
  --t'(x'+2y) = t'(x)
  have x_core_add_2y_corner_eq_x_corner := x_corner_core_add_2y_eq_x_core_add_2y_corner,
  rw [← x_corner_core_eq_int_x_core_corner, ← x_corner_def] at x_core_add_2y_corner_eq_x_corner,
  symmetry' at x_core_add_2y_corner_eq_x_corner,
  --t'(x')+2y = t'(x)
  have x_corner_core_add_2y_eq_x_corner :
    add_vectors (int_point_to_corner T'_is_tiling int_x_core).val (int_point_to_point (double_int_vector y)) = x_corner :=
    by rw [x_corner_core_add_2y_eq_x_core_add_2y_corner, x_core_add_2y_corner_eq_x_corner],
  --t'(x')+2y+ei = t'(x)+ei
  have x_corner_core_add_2y_add_unit_basis_vector_eq_x_corner_add_unit_basis_vector :=
    add_same_vector (unit_basis_vector i) x_corner_core_add_2y_eq_x_corner,
  --t'(x)+ei = t'(x+ei)
  have x_corner_add_unit_basis_vector_eq_x_add_unit_basis_vector_corner :=
    T'_faceshare_free_helper1 d T T_is_tiling T_faceshare_free x i x_corner x_corner_core x_corner_core_in_T x_core
      x_core_in_x_corner_core y x_corner_def x_in_x_corner T'_covers_core T'_is_tiling T'_is_periodic T'_has_facesharing
      x_core_in_core_points x_corner_unique x_corner_core_in_T' x_core_eq_int_x_core x_corner_core_eq_int_x_core_corner
      x_corner_core_add_2y_eq_x_core_add_2y_corner x_core_add_2y_corner_eq_x_corner x_corner_core_add_2y_eq_x_corner
      x_corner_core_add_2y_add_unit_basis_vector_eq_x_corner_add_unit_basis_vector,
  --t'(x')+2y+ei = t'(x+ei)
  have x_corner_core_add_2y_add_unit_basis_vector_eq_x_add_unit_basis_vector_corner :=
    x_corner_core_add_2y_add_unit_basis_vector_eq_x_corner_add_unit_basis_vector,
  rw x_corner_add_unit_basis_vector_eq_x_add_unit_basis_vector_corner
    at x_corner_core_add_2y_add_unit_basis_vector_eq_x_add_unit_basis_vector_corner,
  --x = x'+2y
  have x_eq_x_core_add_2y : int_point_to_point x = add_vectors x_core (int_point_to_point (double_int_vector y)) :=
    T'_faceshare_free_helper2 d T T_is_tiling T_faceshare_free x i x_corner x_corner_core x_corner_core_in_T x_core
      x_core_in_x_corner_core y x_corner_def x_in_x_corner T'_covers_core T'_is_tiling T'_is_periodic T'_has_facesharing
      x_core_in_core_points x_corner_unique x_corner_core_in_T' x_core_eq_int_x_core x_corner_core_eq_int_x_core_corner
      x_corner_core_add_2y_eq_x_core_add_2y_corner x_core_add_2y_corner_eq_x_corner x_corner_core_add_2y_eq_x_corner
      x_corner_core_add_2y_add_unit_basis_vector_eq_x_corner_add_unit_basis_vector
      x_corner_add_unit_basis_vector_eq_x_add_unit_basis_vector_corner
      x_corner_core_add_2y_add_unit_basis_vector_eq_x_add_unit_basis_vector_corner,
  --t'(x')+2y+ei = t'(x'+2y+ei)
  have x_corner_core_add_2y_add_unit_basis_vector_eq_x_core_add_2y_add_unit_basis_vector_corner :=
    x_corner_core_add_2y_add_unit_basis_vector_eq_x_add_unit_basis_vector_corner,
  rw x_eq_x_core_add_2y at x_corner_core_add_2y_add_unit_basis_vector_eq_x_core_add_2y_add_unit_basis_vector_corner,
  have x_core_add_2y_add_unit_basis_vector_corner_h :=
    point_to_corner T'_is_tiling (add_vectors (add_vectors x_core (int_point_to_point (double_int_vector y))) (unit_basis_vector i)),
  let x_core_add_2y_add_unit_basis_vector_corner := x_core_add_2y_add_unit_basis_vector_corner_h.val,
  have x_core_add_2y_add_unit_basis_vector_corner_def :
    x_core_add_2y_add_unit_basis_vector_corner = x_core_add_2y_add_unit_basis_vector_corner_h.val := by refl,
  rcases x_core_add_2y_add_unit_basis_vector_corner_h.property with
    ⟨x_core_add_2y_add_unit_basis_vector_corner_in_T', x_core_add_2y_add_unit_basis_vector_in_its_corner,
    x_core_add_2y_add_unit_basis_vector_corner_unique⟩,
  let int_x_core_add_ei : int_point d :=
    vector.of_fn (λ j : fin d, if(i = j) then int_x_core.nth j + 1 else int_x_core.nth j),
  have x_core_add_2y_add_unit_basis_vector_corner_eq_x_core_add_unit_basis_vector_corner_add_2y :=
    T'_is_periodic int_x_core_add_ei y,
  have x_core_add_2y_add_ei_eq_int_x_core_add_ei_add_2y :
    add_vectors (add_vectors x_core (int_point_to_point (double_int_vector y))) (unit_basis_vector i) =
    int_point_to_point (add_int_vectors int_x_core_add_ei (double_int_vector y)) :=
    begin
      rw [double_int_vector, unit_basis_vector, add_vectors, add_int_vectors],
      simp only [vector.nth_of_fn],
      apply vector.ext,
      intro j,
      simp only [vector.nth_of_fn],
      rw [add_vectors, int_point_to_point, int_point_to_point],
      simp only [int.cast_add, int.cast_bit0, int.cast_mul, int.cast_one, vector.nth_of_fn],
      replace x_core_in_core_points := x_core_in_core_points j,
      by_cases i_eq_j : i = j,
      { rw i_eq_j,
        simp only [int.cast_add, if_true, eq_self_iff_true, int.cast_one],
        cases x_core_in_core_points,
        { rw x_core_in_core_points,
          simp only [one_div, int.cast_zero, if_true, zero_lt_bit0, zero_add, zero_lt_one, inv_pos],
          rw add_comm,
        },
        rw x_core_in_core_points,
        have one_ge_one_half : ¬((1 : ℝ) < 1/2) := by linarith,
        rw if_neg one_ge_one_half,
        have coe_goal : (1 : ℝ) + 2 * ↑(vector.nth y j) + 1 = 1 + 1 + 2 * ↑(vector.nth y j) := by linarith,
        assumption_mod_cast,
      },
      rename i_eq_j i_ne_j,
      rw [if_neg i_ne_j, if_neg i_ne_j],
      simp only [add_zero, add_left_inj],
      cases x_core_in_core_points,
      { rw x_core_in_core_points,
        simp only [one_div, int.cast_zero, if_true, zero_lt_bit0, zero_lt_one, inv_pos],
      },
      rw x_core_in_core_points,
      have one_ge_one_half : ¬((1 : ℝ) < 1/2) := by linarith,
      rw if_neg one_ge_one_half,
      have one_eq_one : 1 = 1 := by refl,
      assumption_mod_cast,
    end,
  --From t'(x')+2y+ei = t'(x'+2y+ei) and above, get t'(x')+2y+ei = t'(x'_add_ei + 2y)
  rw x_core_add_2y_add_ei_eq_int_x_core_add_ei_add_2y at
    x_corner_core_add_2y_add_unit_basis_vector_eq_x_core_add_2y_add_unit_basis_vector_corner,
  --From t'(x'_add_ei + 2y) = t'(x'_add_ei) + 2y and above, get t'(x')+2y+ei = t'(x'_add_ei) + 2y
  have coe_step :
    (int_point_to_corner T'_is_tiling (add_int_vectors int_x_core_add_ei (double_int_vector y))).val =
    (point_to_corner T'_is_tiling (int_point_to_point (add_int_vectors int_x_core_add_ei (double_int_vector y)))).val
    := by rw int_point_to_corner,
  rw [← coe_step, x_core_add_2y_add_unit_basis_vector_corner_eq_x_core_add_unit_basis_vector_corner_add_2y]
    at x_corner_core_add_2y_add_unit_basis_vector_eq_x_core_add_2y_add_unit_basis_vector_corner,
  --Then use vector lemmas (comm and sub_both_sides) to get t'(x')+ei = t'(x'_add_ei)
  have x_core_corner_add_unit_basis_vector_eq_int_x_core_add_ei_corner :
    add_vectors (int_point_to_corner T'_is_tiling int_x_core).val (unit_basis_vector i) =
    (int_point_to_corner T'_is_tiling int_x_core_add_ei).val
    :=
    begin
      rw add_vectors_assoc (int_point_to_corner T'_is_tiling int_x_core).val (int_point_to_point (double_int_vector y))
        (unit_basis_vector i) at x_corner_core_add_2y_add_unit_basis_vector_eq_x_core_add_2y_add_unit_basis_vector_corner,
      rw add_vectors_comm (int_point_to_point (double_int_vector y)) (unit_basis_vector i) at
        x_corner_core_add_2y_add_unit_basis_vector_eq_x_core_add_2y_add_unit_basis_vector_corner,
      rw ← add_vectors_assoc (int_point_to_corner T'_is_tiling int_x_core).val (unit_basis_vector i)
        (int_point_to_point (double_int_vector y))
        at x_corner_core_add_2y_add_unit_basis_vector_eq_x_core_add_2y_add_unit_basis_vector_corner,
      exact remove_same_vector x_corner_core_add_2y_add_unit_basis_vector_eq_x_core_add_2y_add_unit_basis_vector_corner,
    end,
  --Then we have t'(x')+ei = t'(x'+ei), and we should be able to derive a contradiction with T_faceshare_free
  exact T_has_facesharing_from_T_core_has_facesharing d T T_is_tiling T_faceshare_free x i x_corner x_corner_core x_corner_core_in_T
    x_core x_core_in_x_corner_core y x_corner_def x_in_x_corner x_eq_x_core_add_2y T'_covers_core T'_is_tiling T'_is_periodic
    T'_has_facesharing x_core_in_core_points x_corner_unique x_corner_core_in_T' x_core_eq_int_x_core x_corner_core_eq_int_x_core_corner
    x_corner_core_add_2y_eq_x_core_add_2y_corner x_core_add_2y_corner_eq_x_corner x_corner_core_add_2y_eq_x_corner
    x_corner_core_add_2y_add_unit_basis_vector_eq_x_corner_add_unit_basis_vector
    x_corner_add_unit_basis_vector_eq_x_add_unit_basis_vector_corner
    x_corner_core_add_2y_add_unit_basis_vector_eq_x_add_unit_basis_vector_corner
    x_core_add_2y_add_unit_basis_vector_corner_h x_core_add_2y_add_unit_basis_vector_corner_def
    x_core_add_2y_add_unit_basis_vector_corner_in_T' x_core_add_2y_add_unit_basis_vector_in_its_corner
    x_core_add_2y_add_unit_basis_vector_corner_unique
    x_core_add_2y_add_unit_basis_vector_corner_eq_x_core_add_unit_basis_vector_corner_add_2y
    x_core_add_2y_add_ei_eq_int_x_core_add_ei_add_2y coe_step
    x_corner_core_add_2y_add_unit_basis_vector_eq_x_core_add_2y_add_unit_basis_vector_corner
    x_core_corner_add_unit_basis_vector_eq_int_x_core_add_ei_corner,
end

theorem periodic_reduction : ∀ d : ℕ, ∀ d_gt_zero : d > 0, periodic_Keller_conjecture d d_gt_zero → Keller_conjecture d :=
begin
  intros d d_gt_zero,
  contrapose,
  rw [Keller_conjecture, periodic_Keller_conjecture],
  simp only [and_imp, exists_prop, exists_and_distrib_right, not_not, exists_imp_distrib, not_forall],
  intros T T_is_tiling T_faceshare_free,
  change ∃ T' : set (point d), (∃ T'_is_tiling : is_tiling T', is_periodic T'_is_tiling) ∧ tiling_faceshare_free T',
  let core_points := {x : point d | ∀ i : fin d, x.nth i = 0 ∨ x.nth i = 1},
  let T_core := {t ∈ T | ∃ p ∈ core_points, in_cube t p},
  let T' := {t' : point d | ∃ t ∈ T_core, ∃ x : int_point d, t' = add_vectors t (int_point_to_point (double_int_vector x))},
  have T'_covers_core : ∀ (x : point d), (∀ (i : fin d), vector.nth x i ≥ 0 ∧ vector.nth x i ≤ 1) →
      (∃ (t' : point d) (H : t' ∈ T'), in_cube t' x ∧ ∀ (alt_t' : point d), alt_t' ∈ T' → in_cube alt_t' x → t' = alt_t')
      := T'_covers_core d T T_is_tiling T_faceshare_free,
  have T'_is_tiling : is_tiling T' := T'_is_tiling d d_gt_zero T T_is_tiling T_faceshare_free T'_covers_core,
  have T'_is_periodic : is_periodic T'_is_tiling := T'_is_periodic d T T_is_tiling T_faceshare_free T'_covers_core T'_is_tiling,
  have T'_faceshare_free : tiling_faceshare_free T' :=
    T'_faceshare_free d T T_is_tiling T_faceshare_free T'_covers_core T'_is_tiling T'_is_periodic,
  use [T', T'_is_tiling, T'_is_periodic, T'_faceshare_free],
end
