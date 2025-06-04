import cube_tilings

--Defines the line parallel to coordinate i that goes through int_point x
def line_i {d : ℕ} (i : fin d) (x : point d) : set (point d) :=
  { p : point d | ∀ j : fin d, i = j ∨ vector.nth x j = vector.nth p j }

/-
The function T_i(x) from A.2 of Brakensiek et al.'s paper takes a tiling T and a point x and 
returns the set of all cubes (corners) in the tiling that intersect with line_i d i x 
(or l_i(x) in the paper's notation)
-/
def T_i {d : ℕ} (T : set (point d)) (i : fin d) (x : point d) : set (point d) :=
  { t ∈ T | cube t ∩ line_i i x ≠ ∅ }

/-
States whether a set of corners whose cubes intersect a common line are equally spaced
by exactly one unit along the ith coordinate

This definition does not enforce that T_i_x all intersect a common line, it just states
whether the points are all equally spaced along the ith coordinate
-/
def is_i_lattice (d : ℕ) (T_i_x : set (point d)) (i : fin d) : Prop :=
  ∃ a : ℝ, 0 ≤ a ∧ a < 1 ∧ 
  (∀ t ∈ T_i_x, ∃ z : ℤ, vector.nth t i = (z : ℝ) + a) ∧
  (∀ y : ℤ, ∃ t ∈ T_i_x,
    vector.nth t i = (y : ℝ) + a ∧ 
    (∀ t' ∈ T_i_x, vector.nth t' i = (y : ℝ) + a → t' = t)
  )

lemma tiling_lattice_structure_left_implication :
  ∀ d : ℕ, ∀ T : set (point d), ∀ i : fin d, 
  (∀ x : point d, is_i_lattice d (T_i T i x) i) → is_tiling T :=
begin
  intros _ _ _ is_i_lattice_everywhere,
  rw is_tiling,
  intro x,
  have is_i_lattice_at_x := is_i_lattice_everywhere x,
  rw is_i_lattice at is_i_lattice_at_x,
  cases is_i_lattice_at_x with a is_i_lattice_at_x,
  cases is_i_lattice_at_x with zero_le_a is_i_lattice_at_x,
  cases is_i_lattice_at_x with a_lt_one is_i_lattice_at_x,
  cases is_i_lattice_at_x,
  have try_point_to_corner_x := try_point_to_corner T x,
  cases try_point_to_corner_x,
  { --No corner case, show contradiction with is_i_lattice_at_x
    rename try_point_to_corner_x x_has_no_corner,
    exfalso,
    let x_remainder : ℝ := vector.nth x i - ↑(int.floor(vector.nth x i)),
    have zero_le_x_remainder : 0 ≤ x_remainder :=
      begin
        dsimp only[x_remainder],
        rw le_sub,
        rw sub_zero,
        exact int.floor_le (vector.nth x i),
      end,
    have x_remainder_lt_one : x_remainder < 1 :=
      begin
        dsimp only[x_remainder],
        have : vector.nth x i < ↑⌊vector.nth x i⌋ + 1 := int.lt_floor_add_one (vector.nth x i),
        linarith,
      end,
    by_cases x_remainder_lt_a : x_remainder < a,
    { replace is_i_lattice_at_x_right := is_i_lattice_at_x_right (int.floor(vector.nth x i) - 1),
      cases is_i_lattice_at_x_right with corner_of_x is_i_lattice_at_x_right,
      cases is_i_lattice_at_x_right with corner_of_x_in_T_i_x is_i_lattice_at_x_right,
      cases is_i_lattice_at_x_right with corner_of_x_i_val is_i_lattice_at_x_right,
      have corner_of_x_doesn't_contain_x := x_has_no_corner corner_of_x,
      rw T_i at corner_of_x_in_T_i_x,
      change corner_of_x ∈ T ∧ cube corner_of_x ∩ line_i i x ≠ ∅ at corner_of_x_in_T_i_x,
      cases corner_of_x_in_T_i_x with corner_of_x_in_T corner_of_x_intersects_line_i_x,
      replace corner_of_x_doesn't_contain_x := corner_of_x_doesn't_contain_x corner_of_x_in_T,
      rw cube at corner_of_x_intersects_line_i_x,
      rw line_i at corner_of_x_intersects_line_i_x,
      rw set.inter_def at corner_of_x_intersects_line_i_x,
      rw set.ne_empty_iff_nonempty at corner_of_x_intersects_line_i_x,
      simp at corner_of_x_intersects_line_i_x,
      rw set.nonempty_def at corner_of_x_intersects_line_i_x,
      cases corner_of_x_intersects_line_i_x with intersection_point corner_of_x_intersects_line_i_x,
      simp at corner_of_x_intersects_line_i_x,
      rw cube at corner_of_x_doesn't_contain_x,
      simp at corner_of_x_doesn't_contain_x,
      rw in_cube at corner_of_x_doesn't_contain_x,
      simp at corner_of_x_doesn't_contain_x,
      cases corner_of_x_doesn't_contain_x with coord x_not_in_corner_of_x,
      by_cases i_eq_coord : i = coord,
      { rw ← i_eq_coord at x_not_in_corner_of_x,
        rw corner_of_x_i_val at x_not_in_corner_of_x,
        simp only [int.cast_sub, int.cast_one] at x_not_in_corner_of_x,
        have x_not_in_corner_of_x_assm : ↑⌊vector.nth x i⌋ - 1 + a ≤ vector.nth x i :=
          begin
            have h : ↑⌊vector.nth x i⌋ ≤ vector.nth x i := int.floor_le (vector.nth x i),
            linarith,
          end,
        replace x_not_in_corner_of_x := x_not_in_corner_of_x x_not_in_corner_of_x_assm,
        replace x_not_in_corner_of_x : ↑⌊vector.nth x i⌋ - 1 + a + 1 ≤ vector.nth x i := by assumption_mod_cast,
        replace x_not_in_corner_of_x : ↑⌊vector.nth x i⌋ + a ≤ vector.nth x i := by linarith,
        have x_remainder_val : x_remainder = vector.nth x i - ↑⌊vector.nth x i⌋ := by refl,
        linarith,
      },
      cases corner_of_x_intersects_line_i_x with intersection_point_in_corner_of_x intersection_point_line_property,
      replace intersection_point_line_property := intersection_point_line_property coord,
      cases intersection_point_line_property, exact i_eq_coord intersection_point_line_property,
      rw intersection_point_line_property at x_not_in_corner_of_x,
      rw in_cube at intersection_point_in_corner_of_x,
      contrapose intersection_point_in_corner_of_x,
      clear intersection_point_in_corner_of_x,
      simp,
      use coord,
      exact x_not_in_corner_of_x,
    },
    have x_remainder_def : x_remainder = vector.nth x i - ↑⌊vector.nth x i⌋ := by refl,
    replace is_i_lattice_at_x_right := is_i_lattice_at_x_right (int.floor(vector.nth x i)),
    cases is_i_lattice_at_x_right with corner_of_x is_i_lattice_at_x_right,
    cases is_i_lattice_at_x_right with corner_of_x_in_T_i_x is_i_lattice_at_x_right,
    cases is_i_lattice_at_x_right with corner_of_x_i_val is_i_lattice_at_x_right,
    have corner_of_x_doesn't_contain_x := x_has_no_corner corner_of_x,
    rw T_i at corner_of_x_in_T_i_x,
    change corner_of_x ∈ T ∧ cube corner_of_x ∩ line_i i x ≠ ∅ at corner_of_x_in_T_i_x,
    cases corner_of_x_in_T_i_x with corner_of_x_in_T corner_of_x_intersects_line_i_x,
    replace corner_of_x_doesn't_contain_x := corner_of_x_doesn't_contain_x corner_of_x_in_T,
    rw cube at corner_of_x_intersects_line_i_x,
    rw line_i at corner_of_x_intersects_line_i_x,
    rw set.inter_def at corner_of_x_intersects_line_i_x,
    rw set.ne_empty_iff_nonempty at corner_of_x_intersects_line_i_x,
    simp at corner_of_x_intersects_line_i_x,
    rw set.nonempty_def at corner_of_x_intersects_line_i_x,
    cases corner_of_x_intersects_line_i_x with intersection_point corner_of_x_intersects_line_i_x,
    simp at corner_of_x_intersects_line_i_x,
    rw cube at corner_of_x_doesn't_contain_x,
    simp at corner_of_x_doesn't_contain_x,
    rw in_cube at corner_of_x_doesn't_contain_x,
    simp at corner_of_x_doesn't_contain_x,
    cases corner_of_x_doesn't_contain_x with coord x_not_in_corner_of_x,
    by_cases i_eq_coord : i = coord,
    { rw ← i_eq_coord at x_not_in_corner_of_x,
      rw corner_of_x_i_val at x_not_in_corner_of_x,
      have x_not_in_corner_of_x_assm : ↑⌊vector.nth x i⌋ + a ≤ vector.nth x i :=
        by linarith,
      replace x_not_in_corner_of_x := x_not_in_corner_of_x x_not_in_corner_of_x_assm,
      linarith,
    },
    cases corner_of_x_intersects_line_i_x with intersection_point_in_corner_of_x intersection_point_line_property,
    replace intersection_point_line_property := intersection_point_line_property coord,
    cases intersection_point_line_property, exact i_eq_coord intersection_point_line_property,
    rw intersection_point_line_property at x_not_in_corner_of_x,
    rw in_cube at intersection_point_in_corner_of_x,
    contrapose intersection_point_in_corner_of_x,
    clear intersection_point_in_corner_of_x,
    simp,
    use coord,
    exact x_not_in_corner_of_x,
  },
  { --Unique corner case
    cases try_point_to_corner_x with corner corner_property,
    cases corner_property with corner_in_T corner_property,
    use corner,
    use corner_in_T,
    exact corner_property,
  },
  --Multiple corners case, show contradiction with is_i_lattice_at_x
  rename try_point_to_corner_x x_has_multiple_corners,
  exfalso,
  rcases x_has_multiple_corners with 
    ⟨corners, corners_fst_in_T, x_in_corners_fst, corners_snd_in_T, x_in_corners_snd, corners_fst_ne_corners_snd⟩,
  have corners_fst_in_T_i_x : corners.fst ∈ T_i T i x :=
    begin
      change corners.fst ∈ T ∧ cube corners.fst ∩ line_i i x ≠ ∅,
      split, exact corners_fst_in_T,
      rw [cube, line_i, set.inter_def, set.ne_empty_iff_nonempty, set.nonempty_def],
      use x,
      simp only [and_true, implies_true_iff, eq_self_iff_true, or_true, set.mem_set_of_eq],
      rw cube at x_in_corners_fst,
      simp only [set.mem_set_of_eq] at x_in_corners_fst,
      exact x_in_corners_fst,
    end,
  have corners_snd_in_T_i_x : corners.snd ∈ T_i T i x :=
    begin
      change corners.snd ∈ T ∧ cube corners.snd ∩ line_i i x ≠ ∅,
      split, exact corners_snd_in_T,
      rw [cube, line_i, set.inter_def, set.ne_empty_iff_nonempty, set.nonempty_def],
      use x,
      simp only [and_true, implies_true_iff, eq_self_iff_true, or_true, set.mem_set_of_eq],
      rw cube at x_in_corners_snd,
      simp only [set.mem_set_of_eq] at x_in_corners_snd,
      exact x_in_corners_snd,
    end,
  let x_remainder : ℝ := vector.nth x i - ↑(int.floor(vector.nth x i)),
  have zero_le_x_remainder : 0 ≤ x_remainder :=
    begin
      dsimp only[x_remainder],
      rw le_sub,
      rw sub_zero,
      exact int.floor_le (vector.nth x i),
    end,
  have x_remainder_lt_one : x_remainder < 1 :=
    begin
      dsimp only[x_remainder],
      have : vector.nth x i < ↑⌊vector.nth x i⌋ + 1 := int.lt_floor_add_one (vector.nth x i),
      linarith,
    end,
  by_cases x_remainder_lt_a : x_remainder < a,
  { replace is_i_lattice_at_x_right := is_i_lattice_at_x_right (int.floor(vector.nth x i) - 1),
    cases is_i_lattice_at_x_right with corner_of_x is_i_lattice_at_x_right,
    cases is_i_lattice_at_x_right with corner_of_x_in_T_i_x is_i_lattice_at_x_right,
    cases is_i_lattice_at_x_right with corner_of_x_i_val is_i_lattice_at_x_right,
    by_cases corner_of_x_eq_corners_fst : corner_of_x = corners.fst,
    { replace is_i_lattice_at_x_right := is_i_lattice_at_x_right corners.snd corners_snd_in_T_i_x,
      replace is_i_lattice_at_x_left := is_i_lattice_at_x_left corners.snd corners_snd_in_T_i_x,
      cases is_i_lattice_at_x_left with corners_snd_floor corners_snd_i_val,
      by_cases corners_snd_floor_eq_floor_x_sub_one : corners_snd_floor = ⌊vector.nth x i⌋ - 1,
      { rw ← corners_snd_floor_eq_floor_x_sub_one at is_i_lattice_at_x_right,
        replace is_i_lattice_at_x_right := is_i_lattice_at_x_right corners_snd_i_val,
        rw corner_of_x_eq_corners_fst at is_i_lattice_at_x_right,
        symmetry' at is_i_lattice_at_x_right,
        exact corners_fst_ne_corners_snd is_i_lattice_at_x_right,
      },
      rename corners_snd_floor_eq_floor_x_sub_one corners_snd_floor_neq_floor_x_sub_one,
      rw cube at x_in_corners_snd,
      simp at x_in_corners_snd,
      rw in_cube at x_in_corners_snd,
      replace x_in_corners_snd := x_in_corners_snd i,
      cases x_in_corners_snd with corners_snd_le_x x_lt_corners_snd_add_one,
      replace corners_snd_le_x : vector.nth corners.snd i ≤ vector.nth x i := by linarith,
      replace x_lt_corners_snd_add_one : vector.nth x i < vector.nth corners.snd i + 1 := by linarith,
      replace corners_snd_floor_neq_floor_x_sub_one := lt_or_gt_of_ne corners_snd_floor_neq_floor_x_sub_one,
      cases corners_snd_floor_neq_floor_x_sub_one,
      { rw ← int.add_one_le_iff at corners_snd_floor_neq_floor_x_sub_one,
        have corners_snd_floor_val : ↑corners_snd_floor = vector.nth corners.snd i - a := by linarith,
        have coe_corners_snd_floor_neq_floor_x_sub_one : (corners_snd_floor : ℝ) + 1 ≤ (⌊vector.nth x i⌋ : ℝ) - 1 :=
          by assumption_mod_cast,
        rw corners_snd_floor_val at coe_corners_snd_floor_neq_floor_x_sub_one,
        have x_lt_floor_x : vector.nth x i < ↑⌊vector.nth x i⌋ := by linarith,
        have floor_x_le_x := int.floor_le (vector.nth x i),
        linarith,
      },
      have floor_x_sub_one_lt_corners_snd_floor : ⌊vector.nth x i⌋ - 1 < corners_snd_floor := by linarith,
      rw ← int.add_one_le_iff at floor_x_sub_one_lt_corners_snd_floor,
      have floor_x_le_corners_snd_floor : ⌊vector.nth x i⌋ ≤ corners_snd_floor := by linarith,
      have coe_floor_x_le_corners_snd_floor : (⌊vector.nth x i⌋ : ℝ) ≤ (corners_snd_floor : ℝ) := by assumption_mod_cast,
      have floor_x_add_a_le_corners_snd_floor_add_a : ↑⌊vector.nth x i⌋ + a ≤ ↑corners_snd_floor + a := by linarith,
      rw ← corners_snd_i_val at floor_x_add_a_le_corners_snd_floor_add_a,
      dsimp only[x_remainder] at x_remainder_lt_a,
      linarith,
    },
    rename corner_of_x_eq_corners_fst corner_of_x_neq_corners_fst,
    replace is_i_lattice_at_x_right := is_i_lattice_at_x_right corners.fst corners_fst_in_T_i_x,
    replace is_i_lattice_at_x_left := is_i_lattice_at_x_left corners.fst corners_fst_in_T_i_x,
    cases is_i_lattice_at_x_left with corners_fst_floor corners_fst_i_val,
    by_cases corners_fst_floor_eq_floor_x_sub_one : corners_fst_floor = ⌊vector.nth x i⌋ - 1,
    { rw ← corners_fst_floor_eq_floor_x_sub_one at is_i_lattice_at_x_right,
      replace is_i_lattice_at_x_right := is_i_lattice_at_x_right corners_fst_i_val,
      symmetry' at is_i_lattice_at_x_right,
      exact corner_of_x_neq_corners_fst is_i_lattice_at_x_right,
    },
    rename corners_fst_floor_eq_floor_x_sub_one corners_fst_floor_neq_floor_x_sub_one,
    rw cube at x_in_corners_fst,
    simp at x_in_corners_fst,
    rw in_cube at x_in_corners_fst,
    replace x_in_corners_fst := x_in_corners_fst i,
    cases x_in_corners_fst with corners_fst_le_x x_lt_corners_fst_add_one,
    replace corners_fst_le_x : vector.nth corners.fst i ≤ vector.nth x i := by linarith,
    replace x_lt_corners_fst_add_one : vector.nth x i < vector.nth corners.fst i + 1 := by linarith,
    replace corners_fst_floor_neq_floor_x_sub_one := lt_or_gt_of_ne corners_fst_floor_neq_floor_x_sub_one,
    cases corners_fst_floor_neq_floor_x_sub_one,
    { rw ← int.add_one_le_iff at corners_fst_floor_neq_floor_x_sub_one,
      have corners_fst_floor_val : ↑corners_fst_floor = vector.nth corners.fst i - a := by linarith,
      have coe_corners_fst_floor_neq_floor_x_sub_one : (corners_fst_floor : ℝ) + 1 ≤ (⌊vector.nth x i⌋ : ℝ) - 1 :=
        by assumption_mod_cast,
      rw corners_fst_floor_val at coe_corners_fst_floor_neq_floor_x_sub_one,
      have x_lt_floor_x : vector.nth x i < ↑⌊vector.nth x i⌋ := by linarith,
      have floor_x_le_x := int.floor_le (vector.nth x i),
      linarith,
    },
    have floor_x_sub_one_lt_corners_fst_floor : ⌊vector.nth x i⌋ - 1 < corners_fst_floor := by linarith,
    rw ← int.add_one_le_iff at floor_x_sub_one_lt_corners_fst_floor,
    have floor_x_le_corners_fst_floor : ⌊vector.nth x i⌋ ≤ corners_fst_floor := by linarith,
    have coe_floor_x_le_corners_fst_floor : (⌊vector.nth x i⌋ : ℝ) ≤ (corners_fst_floor : ℝ) := by assumption_mod_cast,
    have floor_x_add_a_le_corners_fst_floor_add_a : ↑⌊vector.nth x i⌋ + a ≤ ↑corners_fst_floor + a := by linarith,
    rw ← corners_fst_i_val at floor_x_add_a_le_corners_fst_floor_add_a,
    dsimp only[x_remainder] at x_remainder_lt_a,
    linarith,
  },
  replace is_i_lattice_at_x_right := is_i_lattice_at_x_right (int.floor(vector.nth x i)),
  cases is_i_lattice_at_x_right with corner_of_x is_i_lattice_at_x_right,
  cases is_i_lattice_at_x_right with corner_of_x_in_T_i_x is_i_lattice_at_x_right,
  cases is_i_lattice_at_x_right with corner_of_x_i_val is_i_lattice_at_x_right,
  by_cases corner_of_x_eq_corners_fst : corner_of_x = corners.fst,
  { replace is_i_lattice_at_x_right := is_i_lattice_at_x_right corners.snd corners_snd_in_T_i_x,
    replace is_i_lattice_at_x_left := is_i_lattice_at_x_left corners.snd corners_snd_in_T_i_x,
    cases is_i_lattice_at_x_left with corners_snd_floor corners_snd_i_val,
    by_cases corners_snd_floor_eq_floor_x : corners_snd_floor = ⌊vector.nth x i⌋,
    { rw ← corners_snd_floor_eq_floor_x at is_i_lattice_at_x_right,
      replace is_i_lattice_at_x_right := is_i_lattice_at_x_right corners_snd_i_val,
      rw corner_of_x_eq_corners_fst at is_i_lattice_at_x_right,
      symmetry' at is_i_lattice_at_x_right,
      exact corners_fst_ne_corners_snd is_i_lattice_at_x_right,
    },
    rename corners_snd_floor_eq_floor_x corners_snd_floor_neq_floor_x,
    rw cube at x_in_corners_snd,
    simp at x_in_corners_snd,
    rw in_cube at x_in_corners_snd,
    replace x_in_corners_snd := x_in_corners_snd i,
    cases x_in_corners_snd with corners_snd_le_x x_lt_corners_snd_add_one,
    replace corners_snd_le_x : vector.nth corners.snd i ≤ vector.nth x i := by linarith,
    replace x_lt_corners_snd_add_one : vector.nth x i < vector.nth corners.snd i + 1 := by linarith,
    replace corners_snd_floor_neq_floor_x := lt_or_gt_of_ne corners_snd_floor_neq_floor_x,
    rename x_remainder_lt_a a_le_x_remainder,
    replace a_le_x_remainder : a ≤ x_remainder := by linarith,
    cases corners_snd_floor_neq_floor_x,
    { rw ← int.add_one_le_iff at corners_snd_floor_neq_floor_x,
      have coe_corners_snd_floor_neq_floor_x : (corners_snd_floor : ℝ) + 1 ≤ (⌊vector.nth x i⌋ : ℝ) := 
        by assumption_mod_cast,
      have corners_snd_floor_add_a_add_one_le_floor_x_add_a : ↑corners_snd_floor + a + 1≤ ↑⌊vector.nth x i⌋ + a :=
        by linarith,
      rw ← corners_snd_i_val at corners_snd_floor_add_a_add_one_le_floor_x_add_a,
      have x_lt_floor_x_add_a : vector.nth x i < ↑⌊vector.nth x i⌋ + a := by linarith,
      dsimp only[x_remainder] at a_le_x_remainder,
      linarith,
    },
    have floor_x_lt_corners_snd_floor : ⌊vector.nth x i⌋ < corners_snd_floor := by linarith,
    have floor_x_add_one_le_corners_snd_floor : ⌊vector.nth x i⌋ + 1 ≤ corners_snd_floor := by linarith,
    have coe_floor_x_add_one_le_corners_snd_floor : (⌊vector.nth x i⌋ : ℝ) + 1 ≤ (corners_snd_floor : ℝ) :=
      by assumption_mod_cast,
    have x_lt_floor_x_add_one := int.lt_floor_add_one (vector.nth x i),
    have x_lt_corners_snd_floor : vector.nth x i < ↑corners_snd_floor := by linarith,
    linarith,
  },
  rename corner_of_x_eq_corners_fst corner_of_x_neq_corners_fst,
  replace is_i_lattice_at_x_right := is_i_lattice_at_x_right corners.fst corners_fst_in_T_i_x,
  replace is_i_lattice_at_x_left := is_i_lattice_at_x_left corners.fst corners_fst_in_T_i_x,
  cases is_i_lattice_at_x_left with corners_fst_floor corners_fst_i_val,
  by_cases corners_fst_floor_eq_floor_x : corners_fst_floor = ⌊vector.nth x i⌋,
  { rw ← corners_fst_floor_eq_floor_x at is_i_lattice_at_x_right,
    replace is_i_lattice_at_x_right := is_i_lattice_at_x_right corners_fst_i_val,
    symmetry' at is_i_lattice_at_x_right,
    exact corner_of_x_neq_corners_fst is_i_lattice_at_x_right,
  },
  rename corners_fst_floor_eq_floor_x corners_fst_floor_neq_floor_x,
  rw cube at x_in_corners_fst,
  simp at x_in_corners_fst,
  rw in_cube at x_in_corners_fst,
  replace x_in_corners_fst := x_in_corners_fst i,
  cases x_in_corners_fst with corners_fst_le_x x_lt_corners_fst_add_one,
  replace corners_fst_le_x : vector.nth corners.fst i ≤ vector.nth x i := by linarith,
  replace x_lt_corners_fst_add_one : vector.nth x i < vector.nth corners.fst i + 1 := by linarith,
  replace corners_fst_floor_neq_floor_x := lt_or_gt_of_ne corners_fst_floor_neq_floor_x,
  rename x_remainder_lt_a a_le_x_remainder,
  replace a_le_x_remainder : a ≤ x_remainder := by linarith,
  cases corners_fst_floor_neq_floor_x,
  { rw ← int.add_one_le_iff at corners_fst_floor_neq_floor_x,
    have coe_corners_fst_floor_neq_floor_x : (corners_fst_floor : ℝ) + 1 ≤ (⌊vector.nth x i⌋ : ℝ) := 
      by assumption_mod_cast,
    have corners_fst_floor_add_a_add_one_le_floor_x_add_a : ↑corners_fst_floor + a + 1≤ ↑⌊vector.nth x i⌋ + a :=
      by linarith,
    rw ← corners_fst_i_val at corners_fst_floor_add_a_add_one_le_floor_x_add_a,
    have x_lt_floor_x_add_a : vector.nth x i < ↑⌊vector.nth x i⌋ + a := by linarith,
    dsimp only[x_remainder] at a_le_x_remainder,
    linarith,
  },
  have floor_x_lt_corners_fst_floor : ⌊vector.nth x i⌋ < corners_fst_floor := by linarith,
  have floor_x_add_one_le_corners_fst_floor : ⌊vector.nth x i⌋ + 1 ≤ corners_fst_floor := by linarith,
  have coe_floor_x_add_one_le_corners_fst_floor : (⌊vector.nth x i⌋ : ℝ) + 1 ≤ (corners_fst_floor : ℝ) :=
    by assumption_mod_cast,
  have x_lt_floor_x_add_one := int.lt_floor_add_one (vector.nth x i),
  have x_lt_corners_fst_floor : vector.nth x i < ↑corners_fst_floor := by linarith,
  linarith,
end

lemma tiling_lattice_structure_right_implication_helper_one
  (d : ℕ)
  (T : set (point d))
  (i : fin d)
  (x : point d)
  (not_i_lattice : ∀ (a : ℝ),
                     0 ≤ a →
                     a < 1 →
                     (∀ (t : vector ℝ d),
                        t ∈ T_i T i x →
                        (∃ (z : ℤ), t.nth i = ↑z + a)) →
                     (∃ (z_2 : ℤ),
                        ∀ (t_2 : vector ℝ d),
                          t_2 ∈ T_i T i x →
                          t_2.nth i = ↑z_2 + a →
                          (∃ (t_3 : vector ℝ d),
                             t_3 ∈ T_i T i x ∧
                               t_3.nth i = ↑z_2 + a ∧
                                 ¬t_3 = t_2)))
  (corner : point d)
  (corner_in_T : corner ∈ T)
  (t : vector ℝ d)
  (t_in_T_i_x : t ∈ T_i T i x)
  (corner_in_T_i_x : corner ∈ T_i T i x)
  (corner_lt_t : vector.nth corner i < t.nth i)
  (min_dist_corner : point d)
  (min_dist_corner_gt_corner : vector.nth min_dist_corner i >
                                 vector.nth corner i)
  (min_dist_corner_in_T : min_dist_corner ∈ T)
  (min_dist_corner_cube_intersects_line_i_x : ¬cube min_dist_corner ∩
                                                    line_i i x =
                                                  ∅)
  (exists_prev_corner : ∃ (prev_corner : vector ℝ d)
                          (H : prev_corner ∈ T_i T i x),
                          vector.nth min_dist_corner i - prev_corner.nth i >
                              0 ∧
                            vector.nth min_dist_corner i - prev_corner.nth i <
                              1) :
  let a : ℝ := vector.nth corner i - ↑⌊vector.nth corner i⌋,
      b : ℝ := t.nth i - ↑⌊t.nth i⌋
  in 0 ≤ a →
     a < 1 →
     (∀ (z : ℤ), ¬t.nth i = ↑z + a) →
     0 ≤ b →
     b < 1 →
     (∀ (z : ℤ), ¬vector.nth corner i = ↑z + b) →
     (let corners_not_in_lattice : set (point d) :=
            {t ∈ T_i T i x | t.nth i > vector.nth corner i ∧
               ∀ (z : ℤ), t.nth i ≠ ↑z + a},
          dists_of_corners_not_in_lattice : set ℕ :=
            {dist :
               ℕ | ∃ (t : vector ℝ d) (H : t ∈ corners_not_in_lattice),
               dist = (⌊vector.nth corner i⌋ - ⌊t.nth i⌋).nat_abs}
      in ∀
         (dists_of_corners_not_in_lattice_nonempty :
           dists_of_corners_not_in_lattice.nonempty),
           let min_dist_of_corners_not_in_lattice : ℕ :=
                 nat.lt_wf.min dists_of_corners_not_in_lattice
                   dists_of_corners_not_in_lattice_nonempty,
               corners_not_in_lattice_at_min_dist : set (point d) :=
                 {t ∈ corners_not_in_lattice | (⌊vector.nth corner i⌋ -
                       ⌊t.nth i⌋).nat_abs =
                    min_dist_of_corners_not_in_lattice}
           in (⌊vector.nth corner i⌋ -
                   ⌊vector.nth min_dist_corner i⌋).nat_abs =
                min_dist_of_corners_not_in_lattice →
              vector.nth min_dist_corner i <
                ↑⌊vector.nth min_dist_corner i⌋ + a →
              (let min_dist_corner_at_line_i_x : vector ℝ d :=
                     vector.of_fn
                       (λ (j : fin d),
                          ite (j = i) (vector.nth min_dist_corner j)
                            (vector.nth x j))
               in ∃ (p : point d),
                    ∀ (t1 : point d),
                      t1 ∈ T →
                      p ∈ cube t1 →
                      (∃ (t2 : point d),
                         t2 ∈ T ∧ p ∈ cube t2 ∧ ¬t2 = t1))) :=
begin
  intros a b zero_le_a a_lt_one t_not_a_mod_1 zero_le_b b_lt_one corner_not_b_mod_1 
    corners_not_in_lattice dists_of_corners_not_in_lattice dists_of_corners_not_in_lattice_nonempty 
    min_dist_of_corners_not_in_lattice corners_not_in_lattice_at_min_dist min_dist_corner_has_min_dist 
    min_dist_corner_not_a_mod_1 min_dist_corner_at_line_i_x,
  cases exists_prev_corner with prev_corner prev_corner_properties,
  cases prev_corner_properties with prev_corner_in_T_i_x min_dist_corner_at_line_i_x_in_cube_prev_corner,
  rw T_i at prev_corner_in_T_i_x,
  change prev_corner ∈ T ∧ cube prev_corner ∩ line_i i x ≠ ∅ at prev_corner_in_T_i_x,
  cases prev_corner_in_T_i_x with prev_corner_in_T prev_corner_intersects_line_i_x,
  use min_dist_corner_at_line_i_x,
  intros t1 t1_in_T min_dist_corner_at_line_i_x_in_cube_t1,
  by_cases t1_eq_prev_corner : t1 = prev_corner,
  {
  use min_dist_corner,
  split,
  exact min_dist_corner_in_T,
  split,
  {
  rw cube,
  simp,
  rw in_cube,
  intro coord,
  by_cases coord_eq_i : coord = i,
  {
  rw coord_eq_i,
  simp only [vector.nth_of_fn, eq_self_iff_true, if_true, le_refl, lt_add_iff_pos_right, zero_lt_one, and_self],
  },
  {
  rename coord_eq_i coord_neq_i,
  rw line_i at min_dist_corner_cube_intersects_line_i_x,
  rw set.inter_def at min_dist_corner_cube_intersects_line_i_x,
  simp at min_dist_corner_cube_intersects_line_i_x,
  change
    {a : point d | a ∈ cube min_dist_corner ∧ ∀ (j : fin d), i = j ∨ vector.nth x j = vector.nth a j} ≠ ∅
    at min_dist_corner_cube_intersects_line_i_x,
  rw set.ne_empty_iff_nonempty at min_dist_corner_cube_intersects_line_i_x,
  rw set.nonempty_def at min_dist_corner_cube_intersects_line_i_x,
  cases min_dist_corner_cube_intersects_line_i_x with p min_dist_corner_cube_intersects_line_i_x,
  simp at min_dist_corner_cube_intersects_line_i_x,
  cases min_dist_corner_cube_intersects_line_i_x with p_in_cube_min_dist_corner p_on_line_i_x,
  replace p_on_line_i_x := p_on_line_i_x coord,
  cases p_on_line_i_x,
  { exfalso,
    symmetry' at p_on_line_i_x,
    exact coord_neq_i p_on_line_i_x,
  },
  rw cube at p_in_cube_min_dist_corner,
  simp at p_in_cube_min_dist_corner,
  rw in_cube at p_in_cube_min_dist_corner,
  replace p_in_cube_min_dist_corner := p_in_cube_min_dist_corner coord,
  rw ← p_on_line_i_x at p_in_cube_min_dist_corner,
  dsimp only[min_dist_corner_at_line_i_x],
  simp only [vector.nth_of_fn],
  rw if_neg coord_neq_i,
  exact p_in_cube_min_dist_corner,
  },
  },
  {
  rw t1_eq_prev_corner,
  intro min_dist_corner_eq_corner,
  rw min_dist_corner_eq_corner at min_dist_corner_at_line_i_x_in_cube_prev_corner,
  linarith,
  },
  },
  {
  rename t1_eq_prev_corner t1_neq_prev_corner,
  use prev_corner,
  split, exact prev_corner_in_T,
  split,
  {
  rw cube,
  simp,
  rw in_cube,
  intro min_dist_corner_at_line_i_x_not_in_prev_corner_at_coord,
  cases min_dist_corner_at_line_i_x_not_in_prev_corner_at_coord with coord coord_lt_d,
  by_cases coord_eq_i : coord = i,
  {
  simp only [vector.nth_of_fn],
  have pos_hyp : (⟨coord, coord_lt_d⟩ : fin d) = i :=
    begin
      apply fin.eq_of_veq,
      rw fin.coe_eq_val at coord_eq_i,
      exact coord_eq_i,
    end,
  rw [if_pos pos_hyp, pos_hyp],
  cases min_dist_corner_at_line_i_x_in_cube_prev_corner,
  split, linarith,
  linarith,
  },
  rename coord_eq_i coord_neq_i,
  rw line_i at prev_corner_intersects_line_i_x,
  rw set.inter_def at prev_corner_intersects_line_i_x,
  simp at prev_corner_intersects_line_i_x,
  change 
    {a : point d | a ∈ cube prev_corner ∧ ∀ (j : fin d), i = j ∨ vector.nth x j = vector.nth a j} ≠ ∅
    at prev_corner_intersects_line_i_x,
  rw set.ne_empty_iff_nonempty at prev_corner_intersects_line_i_x,
  rw set.nonempty_def at prev_corner_intersects_line_i_x,
  cases prev_corner_intersects_line_i_x with p prev_corner_intersects_line_i_x,
  simp at prev_corner_intersects_line_i_x,
  cases prev_corner_intersects_line_i_x with p_in_cube_prev_corner p_on_line_i_x,
  replace p_on_line_i_x := p_on_line_i_x ⟨coord, coord_lt_d⟩,
  cases p_on_line_i_x,
  { exfalso,
    symmetry' at p_on_line_i_x,
    rw fin.coe_eq_val at coord_neq_i,
    exact coord_neq_i (fin.veq_of_eq p_on_line_i_x),
  },
  {
  rw cube at p_in_cube_prev_corner,
  simp at p_in_cube_prev_corner,
  rw in_cube at p_in_cube_prev_corner,
  replace p_in_cube_prev_corner := p_in_cube_prev_corner ⟨coord, coord_lt_d⟩,
  rw ← p_on_line_i_x at p_in_cube_prev_corner,
  dsimp only[min_dist_corner_at_line_i_x],
  simp only [vector.nth_of_fn],
  have neg_hyp : (⟨coord, coord_lt_d⟩ : fin d) ≠ i :=
    begin
      apply fin.ne_of_vne,
      simp only [fin.val_eq_coe, ne.def],
      exact coord_neq_i,
    end,
  rw if_neg neg_hyp,
  exact p_in_cube_prev_corner,
  },
  },
  {
  intro prev_corner_eq_t1,
  symmetry' at prev_corner_eq_t1,
  exact t1_neq_prev_corner prev_corner_eq_t1,
  },
  },
end

lemma tiling_lattice_structure_right_implication_helper_two_helper
  (d : ℕ)
  (T : set (point d))
  (i : fin d)
  (x : point d)
  (not_i_lattice : ∀ (a : ℝ),
                     0 ≤ a →
                     a < 1 →
                     (∀ (t : vector ℝ d),
                        t ∈ T_i T i x →
                        (∃ (z : ℤ), t.nth i = ↑z + a)) →
                     (∃ (z_2 : ℤ),
                        ∀ (t_2 : vector ℝ d),
                          t_2 ∈ T_i T i x →
                          t_2.nth i = ↑z_2 + a →
                          (∃ (t_3 : vector ℝ d),
                             t_3 ∈ T_i T i x ∧
                               t_3.nth i = ↑z_2 + a ∧
                                 ¬t_3 = t_2)))
  (corner : point d)
  (corner_in_T : corner ∈ T)
  (t : vector ℝ d)
  (t_in_T_i_x : t ∈ T_i T i x)
  (corner_in_T_i_x : corner ∈ T_i T i x)
  (corner_lt_t : vector.nth corner i < t.nth i)
  (min_dist_corner : point d)
  (min_dist_corner_gt_corner : vector.nth min_dist_corner i >
                                 vector.nth corner i)
  (min_dist_corner_in_T : min_dist_corner ∈ T)
  (min_dist_corner_cube_intersects_line_i_x : ¬cube min_dist_corner ∩
                                                    line_i i x =
                                                  ∅)
  (t1 : point d)
  (t1_in_T : t1 ∈ T)
  (no_prev_corner_exists : ∀ (x_1 : vector ℝ d),
                             x_1 ∈ T_i T i x →
                             x_1.nth i < vector.nth min_dist_corner i →
                             1 ≤ vector.nth min_dist_corner i - x_1.nth i)
  (t1_in_T_i_x : t1 ∈ T_i T i x)
  (prev_corner_doesn't_exist : 1 ≤
                                 vector.nth min_dist_corner i - vector.nth t1 i)
  (t1_gt_corner : vector.nth t1 i > vector.nth corner i) :
  let a : ℝ := vector.nth corner i - ↑⌊vector.nth corner i⌋,
      b : ℝ := t.nth i - ↑⌊t.nth i⌋
  in 0 ≤ a →
     a < 1 →
     (∀ (z : ℤ), ¬t.nth i = ↑z + a) →
     0 ≤ b →
     b < 1 →
     (∀ (z : ℤ), ¬vector.nth corner i = ↑z + b) →
     (let corners_not_in_lattice : set (point d) :=
            {t ∈ T_i T i x | vector.nth t i > vector.nth corner i ∧
               ∀ (z : ℤ), vector.nth t i ≠ ↑z + a},
          dists_of_corners_not_in_lattice : set ℕ :=
            {dist :
               ℕ | ∃ (t : vector ℝ d) (H : t ∈ corners_not_in_lattice),
               dist = (⌊vector.nth corner i⌋ - ⌊t.nth i⌋).nat_abs}
      in ∀
         (dists_of_corners_not_in_lattice_nonempty :
           dists_of_corners_not_in_lattice.nonempty),
           let min_dist_of_corners_not_in_lattice : ℕ :=
                 nat.lt_wf.min dists_of_corners_not_in_lattice
                   dists_of_corners_not_in_lattice_nonempty,
               corners_not_in_lattice_at_min_dist : set (point d) :=
                 {t ∈ corners_not_in_lattice | (⌊vector.nth corner i⌋ -
                       ⌊vector.nth t i⌋).nat_abs =
                    min_dist_of_corners_not_in_lattice}
           in (⌊vector.nth corner i⌋ -
                   ⌊vector.nth min_dist_corner i⌋).nat_abs =
                min_dist_of_corners_not_in_lattice →
              vector.nth min_dist_corner i <
                ↑⌊vector.nth min_dist_corner i⌋ + a →
              (let min_dist_corner_at_line_i_x : vector ℝ d :=
                     vector.of_fn
                       (λ (j : fin d),
                          ite (j = i) (vector.nth min_dist_corner j)
                            (vector.nth x j)),
                   coordinate_just_before_min_dist_corner : ℝ :=
                     ↑⌊vector.nth min_dist_corner i⌋ +
                       (a - 1) / 2,
                   point_just_before_min_dist_corner : point d :=
                     vector.of_fn
                       (λ (j : fin d),
                          ite (j = i) coordinate_just_before_min_dist_corner
                            (vector.nth x j))
               in coordinate_just_before_min_dist_corner <
                    vector.nth min_dist_corner i →
                  (∀ (z : ℤ), ¬vector.nth t1 i = ↑z + a) →
                  vector.nth t1 i + 1 ≤
                    coordinate_just_before_min_dist_corner)) :=
begin
  intros a b zero_le_a a_lt_one t_not_a_mod_1 zero_le_b b_lt_one corner_not_b_mod_1 corners_not_in_lattice 
  dists_of_corners_not_in_lattice dists_of_corners_not_in_lattice_nonempty min_dist_of_corners_not_in_lattice 
  corners_not_in_lattice_at_min_dist min_dist_corner_has_min_dist min_dist_corner_not_a_mod_1 min_dist_corner_at_line_i_x 
  coordinate_just_before_min_dist_corner point_just_before_min_dist_corner 
  coordinate_just_before_min_dist_corner_before_min_dist_corner t1_not_a_mod_1,
  have t1_in_corners_not_in_lattice : t1 ∈ corners_not_in_lattice :=
    begin
      dsimp[corners_not_in_lattice],
      change t1 ∈ T_i T i x ∧ t1.nth i > corner.nth i ∧ ∀ z : ℤ, t1.nth i ≠ ↑z + a,
      split, exact t1_in_T_i_x,
      split, exact t1_gt_corner,
      intro,
      exact t1_not_a_mod_1 z,
    end,
  let dist_t1 := (int.floor(vector.nth corner i) - int.floor(vector.nth t1 i)).nat_abs,
  have dist_t1_in_dists_of_corners_not_in_lattice : dist_t1 ∈ dists_of_corners_not_in_lattice :=
    begin
      change dist_t1 ∈ {dist : ℕ | ∃ (t : vector ℝ d) (H : t ∈ corners_not_in_lattice),
                        dist = (⌊vector.nth corner i⌋ - ⌊t.nth i⌋).nat_abs},
      simp,
      use t1,
      use t1_in_corners_not_in_lattice,
    end,
  have dist_t1_not_lt_min_dist_of_corners_not_in_lattice : ¬dist_t1 < min_dist_of_corners_not_in_lattice := 
    well_founded.not_lt_min
      nat.lt_wf dists_of_corners_not_in_lattice dists_of_corners_not_in_lattice_nonempty 
      dist_t1_in_dists_of_corners_not_in_lattice,
  have t1_add_two_le_min_dist_corner : vector.nth t1 i + 2 ≤ vector.nth min_dist_corner i :=
    begin
      /-
      The reason this is true is because min_dist_of_corners_not_in_lattice > 1 (min_dist_corner ≥ corner and
      no_prev_corner_exists so corner can't come right before min_dist_corner so the distance must be greater than 1).
      Therefore, t1, which doesn't have a mod 1, can't be in the last two corners
      -/
      have dist_t1_eq_corner_sub_t1_or_t1_sub_corner : 
        ↑dist_t1 = ⌊vector.nth corner i⌋ - ⌊vector.nth t1 i⌋ ∨ ↑dist_t1 = ⌊vector.nth t1 i⌋ - ⌊vector.nth corner i⌋ :=
        begin
          by_cases corner_geq_t1 : ⌊vector.nth corner i⌋ - ⌊vector.nth t1 i⌋ ≥ 0,
          {
          left,
          dsimp[dist_t1],
          have nat_abs_val := int.nat_abs_eq (⌊vector.nth corner i⌋ - ⌊vector.nth t1 i⌋),
          cases nat_abs_val,
          {
          rw nat_abs_val,
          refl,
          },
          {
          linarith,
          },
          },
          {
          rename corner_geq_t1 corner_lt_t1,
          right,
          dsimp[dist_t1],
          have nat_abs_val := int.nat_abs_eq (⌊vector.nth corner i⌋ - ⌊vector.nth t1 i⌋),
          cases nat_abs_val,
          {
          linarith,
          },
          {
          replace nat_abs_val : 
            ⌊vector.nth t1 i⌋ - ⌊vector.nth corner i⌋ = ↑((⌊vector.nth corner i⌋ - ⌊vector.nth t1 i⌋).nat_abs) := by linarith,
          rw nat_abs_val,
          },
          },
        end,
      cases dist_t1_eq_corner_sub_t1_or_t1_sub_corner,
      {
      rename dist_t1_eq_corner_sub_t1_or_t1_sub_corner dist_t1_eq_corner_sub_t1,
      replace min_dist_corner_geq_corner : vector.nth corner i ≤ vector.nth min_dist_corner i := by linarith,
      rename min_dist_corner_geq_corner corner_le_min_dist_corner,
      have nat_abs_val : 
        ↑((⌊vector.nth corner i⌋ - ⌊vector.nth min_dist_corner i⌋).nat_abs) = 
        ⌊vector.nth min_dist_corner i⌋ - ⌊vector.nth corner i⌋ :=
        begin
          have floor_corner_le_floor_min_dist_corner := int.floor_mono corner_le_min_dist_corner,
          have nat_abs_val := int.nat_abs_eq (⌊vector.nth corner i⌋ - ⌊vector.nth min_dist_corner i⌋),
          cases nat_abs_val,
          {
          --This case is false, derive a contradiction
          exfalso,
          have coe_nat_abs_ge_zero := coe_nat_abs_ge_zero (⌊vector.nth corner i⌋ - ⌊vector.nth min_dist_corner i⌋),
          rw ← nat_abs_val at coe_nat_abs_ge_zero,
          have corner_ne_min_dist_corner : int.floor(vector.nth corner i) ≠ int.floor(vector.nth min_dist_corner i) :=
            begin
              have corner_mod_a : vector.nth corner i = ↑(int.floor(vector.nth corner i)) + a :=
                begin
                  dsimp only[a],
                  linarith,
                end,
              rw corner_mod_a at corner_le_min_dist_corner,
              have h : ↑⌊vector.nth corner i⌋ + a < ↑⌊vector.nth min_dist_corner i⌋ + a := by linarith,
              intro h',
              rw h' at h,
              linarith,
            end,
          rename coe_nat_abs_ge_zero floor_min_dist_corner_le_floor_corner,
          replace floor_min_dist_corner_le_floor_corner : ⌊vector.nth min_dist_corner i⌋ ≤ ⌊vector.nth corner i⌋ := by linarith,
          have corner_eq_min_dist_corner := 
            eq_of_le_and_ge floor_corner_le_floor_min_dist_corner floor_min_dist_corner_le_floor_corner,
          exact corner_ne_min_dist_corner corner_eq_min_dist_corner,
          },
          {
          linarith,
          },
        end,
      have floor_min_dist_corner_sub_corner_ge_zero := 
        coe_nat_abs_ge_zero (⌊vector.nth corner i⌋ - ⌊vector.nth min_dist_corner i⌋),
      rw nat_abs_val at floor_min_dist_corner_sub_corner_ge_zero,
      have corner_lt_min_dist_corner : corner.nth i < min_dist_corner.nth i :=
        begin
          replace corner_le_min_dist_corner := eq_or_lt_of_le corner_le_min_dist_corner,
          cases corner_le_min_dist_corner,
          {
          exfalso,
          dsimp[a] at min_dist_corner_not_a_mod_1,
          rw ← corner_le_min_dist_corner at min_dist_corner_not_a_mod_1,
          linarith,
          },
          exact corner_le_min_dist_corner,
        end,
      have one_le_min_dist_corner_sub_corner : 1 ≤ vector.nth min_dist_corner i - corner.nth i :=
        no_prev_corner_exists corner corner_in_T_i_x corner_lt_min_dist_corner,
      have floor_min_dist_corner_ge_floor_corner_add_two : int.floor(vector.nth min_dist_corner i) ≥ int.floor(vector.nth corner i) + 2 :=
        begin
          by_cases floor_min_dist_corner_eq_floor_corner : int.floor(min_dist_corner.nth i) = int.floor(corner.nth i),
          {
          exfalso,
          have coe_floor_min_dist_corner_eq_floor_corner : (int.floor(min_dist_corner.nth i) : ℝ) = (int.floor(corner.nth i) : ℝ) :=
            by assumption_mod_cast,
          have floor_min_dist_corner_add_a_eq_floor_corner_add_a : 
            ↑⌊vector.nth min_dist_corner i⌋ + a = ↑⌊vector.nth corner i⌋ + a := by linarith,
          change 
            ↑⌊vector.nth min_dist_corner i⌋ + a = ↑⌊vector.nth corner i⌋ + (vector.nth corner i - ↑⌊vector.nth corner i⌋)
            at floor_min_dist_corner_add_a_eq_floor_corner_add_a,
          have floor_min_dist_corner_add_a_eq_corner : ↑⌊vector.nth min_dist_corner i⌋ + a = vector.nth corner i := by linarith,
          linarith,
          },
          {
          rename floor_min_dist_corner_eq_floor_corner floor_min_dist_corner_ne_floor_corner,
          by_cases floor_min_dist_corner_eq_floor_corner_add_one : int.floor(min_dist_corner.nth i) = int.floor(corner.nth i) + 1,
          {
          exfalso,
          have a_val : a = vector.nth corner i - ↑⌊vector.nth corner i⌋ := by refl,
          have corner_val : corner.nth i = ↑⌊vector.nth corner i⌋ + a := by linarith,
          rw corner_val at one_le_min_dist_corner_sub_corner,
          have floor_corner_add_one_le_min_dist_corner_sub_a : ↑⌊vector.nth corner i⌋ + 1 ≤ min_dist_corner.nth i + a := 
            by linarith,
          have coe_floor_min_dist_corner_eq_floor_corner_add_one : 
            (⌊vector.nth min_dist_corner i⌋ : ℝ) = (⌊vector.nth corner i⌋ : ℝ) + 1 := by assumption_mod_cast,
          rw ← coe_floor_min_dist_corner_eq_floor_corner_add_one at floor_corner_add_one_le_min_dist_corner_sub_a,
          linarith,
          },
          {
          rename floor_min_dist_corner_eq_floor_corner_add_one floor_min_dist_corner_ne_floor_corner_add_one,
          omega,
          },
          },
        end,
      have dist_t1_ge_one : dist_t1 ≥ 1 :=
        begin
          have coe_min_dist_corner_has_min_dist :
            ((⌊vector.nth corner i⌋ - ⌊vector.nth min_dist_corner i⌋).nat_abs : ℤ) = (min_dist_of_corners_not_in_lattice : ℤ)
            := by assumption_mod_cast,
          rw nat_abs_val at coe_min_dist_corner_has_min_dist,
          have coe_dist_t1_not_lt_min_dist_of_corners_not_in_lattice : 
            ¬(dist_t1 : ℤ) < (min_dist_of_corners_not_in_lattice : ℤ) := by assumption_mod_cast,
          linarith,
        end,
      have coe_dist_t1_ge_one : (dist_t1 : ℤ) ≥ 1 := by assumption_mod_cast,
      rw dist_t1_eq_corner_sub_t1 at coe_dist_t1_ge_one,
      have real_floor_corner_sub_floor_t1_ge_one : ((int.floor(corner.nth i)) : ℝ) - ((int.floor(t1.nth i)) : ℝ) ≥ 1 := 
        by assumption_mod_cast,
      have t1_lt_floor_t1_add_one : t1.nth i < int.floor(t1.nth i) + 1 := int.lt_floor_add_one (t1.nth i),
      have t1_lt_floor_corner : t1.nth i < int.floor(corner.nth i) := by linarith,
      have coe_floor_min_dist_corner_ge_floor_corner_add_two :
        (⌊vector.nth min_dist_corner i⌋ : ℝ) ≥ (⌊vector.nth corner i⌋ : ℝ) + 2 := by assumption_mod_cast,
      have t1_add_two_lt_floor_min_dist_corner : t1.nth i + 2 < ↑(int.floor(min_dist_corner.nth i)) := by linarith,
      have floor_min_dist_corner_le_min_dist_corner : ↑(int.floor(min_dist_corner.nth i)) ≤ min_dist_corner.nth i := 
        int.floor_le (min_dist_corner.nth i),
      linarith,
      },
      {
      rename dist_t1_eq_corner_sub_t1_or_t1_sub_corner dist_t1_eq_t1_sub_corner,
      /-
      dist_t1_eq_t1_sub_corner says t1 ≥ corner, but prev_corner_doesn't_exist says t1 is less than corner.
      So find a contradiction
      -/
      exfalso,
      have dist_t1_ge_zero : (dist_t1 : ℤ) ≥ 0 :=
        begin
          have dist_t1_not_lt_zero := nat.not_lt_zero dist_t1,
          linarith,
        end,
      rw dist_t1_eq_t1_sub_corner at dist_t1_ge_zero,
      rename dist_t1_ge_zero floor_corner_le_floor_t1,
      replace floor_corner_le_floor_t1 : ⌊vector.nth corner i⌋ ≤ ⌊vector.nth t1 i⌋ := by linarith,
      replace min_dist_corner_geq_corner : vector.nth corner i ≤ vector.nth min_dist_corner i := by linarith,
      rename min_dist_corner_geq_corner corner_le_min_dist_corner,
      rename dist_t1_not_lt_min_dist_of_corners_not_in_lattice min_dist_of_corners_not_in_lattice_le_dist_t1,
      replace min_dist_of_corners_not_in_lattice_le_dist_t1 : min_dist_of_corners_not_in_lattice ≤ dist_t1 := by linarith,
      have coe_min_dist_of_corners_not_in_lattice_le_dist_t1 : 
        (min_dist_of_corners_not_in_lattice : ℤ) ≤ (dist_t1 : ℤ) := by assumption_mod_cast,
      rw dist_t1_eq_t1_sub_corner at coe_min_dist_of_corners_not_in_lattice_le_dist_t1,
      rw ← min_dist_corner_has_min_dist at coe_min_dist_of_corners_not_in_lattice_le_dist_t1,
      have nat_abs_val : 
        ↑((⌊vector.nth corner i⌋ - ⌊vector.nth min_dist_corner i⌋).nat_abs) = 
        ⌊vector.nth min_dist_corner i⌋ - ⌊vector.nth corner i⌋ :=
        begin
          clear coe_min_dist_of_corners_not_in_lattice_le_dist_t1,
          have floor_corner_le_floor_min_dist_corner := int.floor_mono corner_le_min_dist_corner,
          have nat_abs_val := int.nat_abs_eq (⌊vector.nth corner i⌋ - ⌊vector.nth min_dist_corner i⌋),
          cases nat_abs_val,
          {
          --This case is false, derive a contradiction
          exfalso,
          have coe_nat_abs_ge_zero := coe_nat_abs_ge_zero (⌊vector.nth corner i⌋ - ⌊vector.nth min_dist_corner i⌋),
          rw ← nat_abs_val at coe_nat_abs_ge_zero,
          have corner_ne_min_dist_corner : int.floor(vector.nth corner i) ≠ int.floor(vector.nth min_dist_corner i) :=
            begin
              have corner_mod_a : vector.nth corner i = ↑(int.floor(vector.nth corner i)) + a :=
                begin
                  dsimp only[a],
                  linarith,
                end,
              rw corner_mod_a at corner_le_min_dist_corner,
              have h : ↑⌊vector.nth corner i⌋ + a < ↑⌊vector.nth min_dist_corner i⌋ + a := by linarith,
              intro h',
              rw h' at h,
              linarith,
            end,
          rename coe_nat_abs_ge_zero floor_min_dist_corner_le_floor_corner,
          replace floor_min_dist_corner_le_floor_corner : ⌊vector.nth min_dist_corner i⌋ ≤ ⌊vector.nth corner i⌋ := by linarith,
          have corner_eq_min_dist_corner := 
            eq_of_le_and_ge floor_corner_le_floor_min_dist_corner floor_min_dist_corner_le_floor_corner,
          exact corner_ne_min_dist_corner corner_eq_min_dist_corner,
          },
          {
          linarith,
          },
        end,
      rw nat_abs_val at coe_min_dist_of_corners_not_in_lattice_le_dist_t1,
      rename coe_min_dist_of_corners_not_in_lattice_le_dist_t1 floor_min_dist_corner_le_floor_t1,
      replace floor_min_dist_corner_le_floor_t1 : ⌊vector.nth min_dist_corner i⌋ ≤ ⌊vector.nth t1 i⌋ := by linarith,
      have t1_add_one_le_min_dist_corner : vector.nth t1 i + 1 ≤ vector.nth min_dist_corner i := by linarith,
      have floor_min_dist_corner_add_one_le_floor_t1_add_one : ⌊vector.nth min_dist_corner i⌋ + 1 ≤ ⌊vector.nth t1 i⌋ + 1 := 
        by linarith,
      have min_dist_corner_lt_floor_min_dist_corner_add_one := int.lt_floor_add_one (vector.nth min_dist_corner i),
      have t1_lt_floor_min_dist_corner_add_one : vector.nth t1 i + 1 < ↑⌊vector.nth min_dist_corner i⌋ + 1 := by linarith,
      have coe_floor_min_dist_corner_add_one_le_floor_t1_add_one : 
        (⌊vector.nth min_dist_corner i⌋ : ℝ) + 1 ≤ ⌊vector.nth t1 i⌋ + 1 := by assumption_mod_cast,
      have t1_lt_floor_t1_add_one : vector.nth t1 i + 1 < ↑⌊vector.nth t1 i⌋ + 1 := by linarith,
      have t1_lt_floor_t1 : vector.nth t1 i < ↑⌊vector.nth t1 i⌋ := by linarith,
      have floor_t1_le_t1 := int.floor_le (vector.nth t1 i),
      linarith,
      },
    end,
  change vector.nth t1 i + 1 ≤ ↑⌊vector.nth min_dist_corner i⌋ + (a - 1) / 2,
  linarith,
end

lemma tiling_lattice_structure_right_implication_helper_two 
  (d : ℕ)
  (T : set (point d))
  (i : fin d)
  (x : point d)
  (not_i_lattice : ∀ (a : ℝ),
                     0 ≤ a →
                     a < 1 →
                     (∀ (t : vector ℝ d),
                        t ∈ T_i T i x →
                        (∃ (z : ℤ), t.nth i = ↑z + a)) →
                     (∃ (z_2 : ℤ),
                        ∀ (t_2 : vector ℝ d),
                          t_2 ∈ T_i T i x →
                          t_2.nth i = ↑z_2 + a →
                          (∃ (t_3 : vector ℝ d),
                             t_3 ∈ T_i T i x ∧
                               t_3.nth i = ↑z_2 + a ∧
                                 ¬t_3 = t_2)))
  (corner : point d)
  (corner_in_T : corner ∈ T)
  (t : vector ℝ d)
  (t_in_T_i_x : t ∈ T_i T i x)
  (corner_in_T_i_x : corner ∈ T_i T i x)
  (corner_lt_t : vector.nth corner i < t.nth i)
  (min_dist_corner : point d)
  (min_dist_corner_gt_corner : vector.nth min_dist_corner i >
                                 vector.nth corner i)
  (min_dist_corner_in_T : min_dist_corner ∈ T)
  (min_dist_corner_cube_intersects_line_i_x : ¬cube min_dist_corner ∩
                                                    line_i i x =
                                                  ∅)
  (t1 : point d)
  (t1_in_T : t1 ∈ T)
  (no_prev_corner_exists : ∀ (x_1 : vector ℝ d),
                             x_1 ∈ T_i T i x →
                             x_1.nth i < vector.nth min_dist_corner i →
                             1 ≤ vector.nth min_dist_corner i - x_1.nth i)
  (t1_in_T_i_x : t1 ∈ T_i T i x)
  (prev_corner_doesn't_exist : 1 ≤
                                 vector.nth min_dist_corner i -
                                   vector.nth t1 i) :
  let a : ℝ := vector.nth corner i - ↑⌊vector.nth corner i⌋,
      b : ℝ := t.nth i - ↑⌊t.nth i⌋
  in 0 ≤ a →
     a < 1 →
     (∀ (z : ℤ), ¬t.nth i = ↑z + a) →
     0 ≤ b →
     b < 1 →
     (∀ (z : ℤ), ¬vector.nth corner i = z + b) →
     (let corners_not_in_lattice : set (point d) :=
            {t ∈ T_i T i x | t.nth i > vector.nth corner i ∧
               ∀ (z : ℤ), t.nth i ≠ z + a},
          dists_of_corners_not_in_lattice : set ℕ :=
            {dist :
               ℕ | ∃ (t : vector ℝ d) (H : t ∈ corners_not_in_lattice),
               dist = (⌊vector.nth corner i⌋ - ⌊t.nth i⌋).nat_abs}
      in ∀
         (dists_of_corners_not_in_lattice_nonempty :
           dists_of_corners_not_in_lattice.nonempty),
           let min_dist_of_corners_not_in_lattice : ℕ :=
                 nat.lt_wf.min dists_of_corners_not_in_lattice
                   dists_of_corners_not_in_lattice_nonempty,
               corners_not_in_lattice_at_min_dist : set (point d) :=
                 {t ∈ corners_not_in_lattice | (⌊vector.nth corner i⌋ -
                       ⌊t.nth i⌋).nat_abs =
                    min_dist_of_corners_not_in_lattice}
           in (⌊vector.nth corner i⌋ -
                   ⌊vector.nth min_dist_corner i⌋).nat_abs =
                min_dist_of_corners_not_in_lattice →
              vector.nth min_dist_corner i <
                ↑⌊vector.nth min_dist_corner i⌋ + a →
              (let min_dist_corner_at_line_i_x : vector ℝ d :=
                     vector.of_fn
                       (λ (j : fin d),
                          ite (j = i) (vector.nth min_dist_corner j)
                            (vector.nth x j)),
                   coordinate_just_before_min_dist_corner : ℝ :=
                     ⌊vector.nth min_dist_corner i⌋ +
                       (a - 1) / 2,
                   point_just_before_min_dist_corner : point d :=
                     vector.of_fn
                       (λ (j : fin d),
                          ite (j = i) coordinate_just_before_min_dist_corner
                            (vector.nth x j))
               in coordinate_just_before_min_dist_corner <
                    vector.nth min_dist_corner i →
                  (¬∃ (z : ℤ), vector.nth t1 i = ↑z + a) →
                  vector.nth t1 i + 1 ≤
                    coordinate_just_before_min_dist_corner)) :=
begin
  intros a b zero_le_a a_lt_one t_not_a_mod_1 zero_le_b b_lt_one corner_not_b_mod_1 corners_not_in_lattice 
  dists_of_corners_not_in_lattice dists_of_corners_not_in_lattice_nonempty min_dist_of_corners_not_in_lattice 
  corners_not_in_lattice_at_min_dist min_dist_corner_has_min_dist min_dist_corner_not_a_mod_1 min_dist_corner_at_line_i_x 
  coordinate_just_before_min_dist_corner point_just_before_min_dist_corner 
  coordinate_just_before_min_dist_corner_before_min_dist_corner t1_a_mod_1,
  rename t1_a_mod_1 t1_not_a_mod_1,
  simp at t1_not_a_mod_1,
  change ∀ (z : ℤ), ¬vector.nth t1 i = ↑z + a at t1_not_a_mod_1,
  by_cases t1_gt_corner : t1.nth i > corner.nth i,
  {
  exact tiling_lattice_structure_right_implication_helper_two_helper d T i x not_i_lattice corner corner_in_T t t_in_T_i_x corner_in_T_i_x
    corner_lt_t min_dist_corner min_dist_corner_gt_corner min_dist_corner_in_T min_dist_corner_cube_intersects_line_i_x
    t1 t1_in_T no_prev_corner_exists t1_in_T_i_x prev_corner_doesn't_exist t1_gt_corner zero_le_a a_lt_one t_not_a_mod_1 
    zero_le_b b_lt_one corner_not_b_mod_1 dists_of_corners_not_in_lattice_nonempty min_dist_corner_has_min_dist 
    min_dist_corner_not_a_mod_1 coordinate_just_before_min_dist_corner_before_min_dist_corner t1_not_a_mod_1,
  },
  {
  rename t1_gt_corner t1_le_corner,
  replace t1_le_corner : t1.nth i ≤ corner.nth i := by linarith,
  have corner_lt_min_dist_corner : corner.nth i < min_dist_corner.nth i := by linarith,
  have one_le_min_dist_corner_sub_corner : 1 ≤ vector.nth min_dist_corner i - corner.nth i :=
    no_prev_corner_exists corner corner_in_T_i_x corner_lt_min_dist_corner,
  have floor_min_dist_corner_ge_floor_corner_add_two : int.floor(vector.nth min_dist_corner i) ≥ int.floor(vector.nth corner i) + 2 :=
    begin
      by_cases floor_min_dist_corner_eq_floor_corner : int.floor(min_dist_corner.nth i) = int.floor(corner.nth i),
      {
      exfalso,
      have coe_floor_min_dist_corner_eq_floor_corner : (int.floor(min_dist_corner.nth i) : ℝ) = (int.floor(corner.nth i) : ℝ) :=
        by assumption_mod_cast,
      have floor_min_dist_corner_add_a_eq_floor_corner_add_a : 
        ↑⌊vector.nth min_dist_corner i⌋ + a = ↑⌊vector.nth corner i⌋ + a := by linarith,
      change 
        ↑⌊vector.nth min_dist_corner i⌋ + a = ↑⌊vector.nth corner i⌋ + (vector.nth corner i - ↑⌊vector.nth corner i⌋)
        at floor_min_dist_corner_add_a_eq_floor_corner_add_a,
      have floor_min_dist_corner_add_a_eq_corner : ↑⌊vector.nth min_dist_corner i⌋ + a = vector.nth corner i := by linarith,
      linarith,
      },
      {
      rename floor_min_dist_corner_eq_floor_corner floor_min_dist_corner_ne_floor_corner,
      by_cases floor_min_dist_corner_eq_floor_corner_add_one : int.floor(min_dist_corner.nth i) = int.floor(corner.nth i) + 1,
      {
      exfalso,
      have a_val : a = vector.nth corner i - ↑⌊vector.nth corner i⌋ := by refl,
      have corner_val : corner.nth i = ↑⌊vector.nth corner i⌋ + a := by linarith,
      rw corner_val at one_le_min_dist_corner_sub_corner,
      have floor_corner_add_one_le_min_dist_corner_sub_a : ↑⌊vector.nth corner i⌋ + 1 ≤ min_dist_corner.nth i + a := 
        by linarith,
      have coe_floor_min_dist_corner_eq_floor_corner_add_one : 
        (⌊vector.nth min_dist_corner i⌋ : ℝ) = (⌊vector.nth corner i⌋ : ℝ) + 1 := by assumption_mod_cast,
      rw ← coe_floor_min_dist_corner_eq_floor_corner_add_one at floor_corner_add_one_le_min_dist_corner_sub_a,
      linarith,
      },
      {
      rename floor_min_dist_corner_eq_floor_corner_add_one floor_min_dist_corner_ne_floor_corner_add_one,
      have corner_le_min_dist_corner : corner.nth i ≤ min_dist_corner.nth i := by linarith,
      have floor_corner_le_floor_min_dist_corner := int.floor_mono corner_le_min_dist_corner,
      omega,
      },
      },
    end,
  change vector.nth t1 i + 1 ≤ ↑⌊vector.nth min_dist_corner i⌋ + (a - 1) / 2,
  have corner_lt_floor_corner_add_one := int.lt_floor_add_one (corner.nth i),
  have coe_floor_min_dist_corner_ge_floor_corner_add_two : (⌊vector.nth min_dist_corner i⌋ : ℝ) ≥ ↑⌊vector.nth corner i⌋ + 2 :=
    by assumption_mod_cast,
  have corner_val : corner.nth i = ↑⌊vector.nth corner i⌋ + a := by {dsimp only[a], linarith},
  linarith,
  },
end

lemma tiling_lattice_structure_right_implication_helper_three_helper
  (d : ℕ)
  (T : set (point d))
  (i : fin d)
  (x : point d)
  (not_i_lattice : ∀ (a : ℝ),
                     0 ≤ a →
                     a < 1 →
                     (∀ (t : vector ℝ d),
                        t ∈ T_i T i x →
                        (∃ (z : ℤ), t.nth i = ↑z + a)) →
                     (∃ (z_2 : ℤ),
                        ∀ (t_2 : vector ℝ d),
                          t_2 ∈ T_i T i x →
                          t_2.nth i = ↑z_2 + a →
                          (∃ (t_3 : vector ℝ d),
                             t_3 ∈ T_i T i x ∧
                               t_3.nth i = ↑z_2 + a ∧
                                 ¬t_3 = t_2)))
  (corner : point d)
  (corner_in_T : corner ∈ T)
  (t : vector ℝ d)
  (t_in_T_i_x : t ∈ T_i T i x)
  (corner_in_T_i_x : corner ∈ T_i T i x)
  (corner_lt_t : vector.nth corner i < t.nth i)
  (min_dist_corner : point d)
  (min_dist_corner_gt_corner : vector.nth min_dist_corner i >
                                 vector.nth corner i)
  (min_dist_corner_in_T : min_dist_corner ∈ T)
  (min_dist_corner_cube_intersects_line_i_x : ¬cube min_dist_corner ∩
                                                    line_i i x =
                                                  ∅)
  (i' : fin d)
  (i_eq_i' : i = i')
  (corner_add_one_le_min_dist_corner : vector.nth corner i + 1 ≤
                                         vector.nth min_dist_corner i) :
  let a : ℝ := vector.nth corner i - ↑⌊vector.nth corner i⌋,
      b : ℝ := t.nth i - ↑⌊t.nth i⌋
  in 0 ≤ a →
     a < 1 →
     (∀ (z : ℤ), ¬t.nth i = ↑z + a) →
     0 ≤ b →
     b < 1 →
     (∀ (z : ℤ), ¬vector.nth corner i = ↑z + b) →
     (let corners_not_in_lattice : set (point d) :=
            {t ∈ T_i T i x | vector.nth t i > vector.nth corner i ∧
               ∀ (z : ℤ), vector.nth t i ≠ ↑z + a},
          dists_of_corners_not_in_lattice : set ℕ :=
            {dist :
               ℕ | ∃ (t : vector ℝ d) (H : t ∈ corners_not_in_lattice),
               dist = (⌊vector.nth corner i⌋ - ⌊t.nth i⌋).nat_abs}
      in ∀
         (dists_of_corners_not_in_lattice_nonempty :
           dists_of_corners_not_in_lattice.nonempty),
           let min_dist_of_corners_not_in_lattice : ℕ :=
                 nat.lt_wf.min dists_of_corners_not_in_lattice
                   dists_of_corners_not_in_lattice_nonempty,
               corners_not_in_lattice_at_min_dist : set (point d) :=
                 {t ∈ corners_not_in_lattice | (⌊vector.nth corner i⌋ -
                       ⌊vector.nth t i⌋).nat_abs =
                    min_dist_of_corners_not_in_lattice}
           in (⌊vector.nth corner i⌋ -
                   ⌊vector.nth min_dist_corner i⌋).nat_abs =
                min_dist_of_corners_not_in_lattice →
              vector.nth min_dist_corner i >
                ↑⌊vector.nth min_dist_corner i⌋ + a →
              (let point_on_line_i_x_where_min_dist_corner_is : point d :=
                     vector.of_fn
                       (λ (j : fin d),
                          ite (i = j) (vector.nth min_dist_corner i)
                            (vector.nth x j)),
                   point_on_line_i_x_where_min_dist_corner_should_be : point
                     d :=
                     vector.of_fn
                       (λ (j : fin d),
                          ite (i = j)
                            (↑⌊vector.nth min_dist_corner i⌋ + a)
                            (vector.nth x j))
               in (¬∃
                       (point_on_line_i_x_where_min_dist_corner_should_be_corner :
                         point d)
                       (H :
                         point_on_line_i_x_where_min_dist_corner_should_be_corner ∈
                           T),
                       point_on_line_i_x_where_min_dist_corner_should_be ∈
                         cube
                           point_on_line_i_x_where_min_dist_corner_should_be_corner) →
                  (¬∃
                       (point_on_line_i_x_where_min_dist_corner_is_corner :
                         point d)
                       (H :
                         point_on_line_i_x_where_min_dist_corner_is_corner ∈
                           T),
                       point_on_line_i_x_where_min_dist_corner_is ∈
                           cube
                             point_on_line_i_x_where_min_dist_corner_is_corner ∧
                         point_on_line_i_x_where_min_dist_corner_is_corner ≠
                           min_dist_corner) →
                  (∃ (p : point d),
                     ∀ (t1 : point d),
                       t1 ∈ T →
                       p ∈ cube t1 →
                       (∃ (t2 : point d),
                          t2 ∈ T ∧ p ∈ cube t2 ∧ ¬t2 = t1)))) :=
begin
  intros a b zero_le_a a_lt_one t_not_a_mod_1 zero_le_b b_lt_one corner_not_b_mod_1 corners_not_in_lattice 
  dists_of_corners_not_in_lattice dists_of_corners_not_in_lattice_nonempty min_dist_of_corners_not_in_lattice 
  corners_not_in_lattice_at_min_dist min_dist_corner_has_min_dist min_dist_corner_not_a_mod_1 
  point_on_line_i_x_where_min_dist_corner_is point_on_line_i_x_where_min_dist_corner_should_be 
  point_on_line_i_x_where_min_dist_corner_should_be_cornerless 
  point_on_line_i_x_where_min_dist_corner_is_has_corner_besides_min_dist_corner,
  rename point_on_line_i_x_where_min_dist_corner_is_has_corner_besides_min_dist_corner min_dist_corner_unique,
  simp at min_dist_corner_unique,
  use point_on_line_i_x_where_min_dist_corner_should_be,
  intros t1 t1_in_T,
  rw imp_iff_not_or,
  left,
  rw cube,
  change ¬(in_cube t1 point_on_line_i_x_where_min_dist_corner_should_be),
  rw in_cube,
  simp,
  by_cases t1_not_in_lattice : t1 ∈ corners_not_in_lattice,
  {
  use i,
  simp,
  intro t1_le_min_dist_corner_floor_add_a,
  /-
  Plan: show min_dist_corner.nth i ≤ t1.nth i (by min_dist_property and min_dist_corner_unique) and therefore 
  ⌊min_dist_corner.nth i⌋ + a < t1.nth i as desired
  -/
  let dist_t1 : ℕ := (int.floor(corner.nth i) - int.floor(t1.nth i)).nat_abs,
  have dist_t1_in_dists_of_corners_not_in_lattice : dist_t1 ∈ dists_of_corners_not_in_lattice :=
    begin
      simp,
      use t1,
      split, exact t1_not_in_lattice,
      refl,
    end,
  have dist_t1_not_lt_min_dist_of_corners_not_in_lattice : ¬dist_t1 < min_dist_of_corners_not_in_lattice := 
    well_founded.not_lt_min
      nat.lt_wf dists_of_corners_not_in_lattice dists_of_corners_not_in_lattice_nonempty 
      dist_t1_in_dists_of_corners_not_in_lattice,
  have nat_abs_val : 
    ↑(⌊vector.nth corner i⌋ - ⌊vector.nth min_dist_corner i⌋).nat_abs = ⌊vector.nth min_dist_corner i⌋ - ⌊vector.nth corner i⌋ :=
    begin
      have nat_abs_possible_vals := int.nat_abs_eq (⌊vector.nth corner i⌋ - ⌊vector.nth min_dist_corner i⌋),
      have nat_abs_val_ge_zero := coe_nat_abs_ge_zero (⌊vector.nth corner i⌋ - ⌊vector.nth min_dist_corner i⌋),
      cases nat_abs_possible_vals,
      {
      rw ← nat_abs_possible_vals at nat_abs_val_ge_zero,
      have corner_le_min_dist_corner : vector.nth corner i ≤ min_dist_corner.nth i := by linarith,
      have floor_corner_le_floor_min_dist_corner := int.floor_mono corner_le_min_dist_corner,
      have floor_corner_sub_floor_min_dist_corner_eq_zero : int.floor(corner.nth i) - int.floor(min_dist_corner.nth i) = 0 := by linarith,
      have floor_min_dist_corner_sub_floor_corner_eq_zero : int.floor(min_dist_corner.nth i) - int.floor(corner.nth i) = 0 := by linarith,
      rw [floor_corner_sub_floor_min_dist_corner_eq_zero, floor_min_dist_corner_sub_floor_corner_eq_zero],
      have coe_goal := int.nat_abs_zero,
      assumption_mod_cast,
      },
      linarith,
    end,
  have nat_abs_val2 :
    ↑(⌊vector.nth corner i⌋ - ⌊vector.nth t1 i⌋).nat_abs = ⌊vector.nth t1 i⌋ - ⌊vector.nth corner i⌋ :=
    begin
      have nat_abs_possible_vals := int.nat_abs_eq (⌊vector.nth corner i⌋ - ⌊vector.nth t1 i⌋),
      have nat_abs_val2_ge_zero := coe_nat_abs_ge_zero (⌊vector.nth corner i⌋ - ⌊vector.nth t1 i⌋),
      cases nat_abs_possible_vals,
      {
      rw ← nat_abs_possible_vals at nat_abs_val2_ge_zero,
      dsimp[corners_not_in_lattice] at t1_not_in_lattice,
      simp at t1_not_in_lattice,
      cases t1_not_in_lattice with t1_in_T_i_x t1_not_in_lattice,
      cases t1_not_in_lattice with corner_lt_t1 t1_not_a_mod_1,
      have corner_le_t1 : corner.nth i ≤ t1.nth i := by linarith,
      have floor_corner_le_floor_t1 := int.floor_mono corner_le_t1,
      have floor_corner_sub_floor_t1_eq_zero : int.floor(corner.nth i) - int.floor(t1.nth i) = 0 := by linarith,
      have floor_t1_sub_floor_corner_eq_zero : int.floor(t1.nth i) - int.floor(corner.nth i) = 0 := by linarith,
      rw [floor_corner_sub_floor_t1_eq_zero, floor_t1_sub_floor_corner_eq_zero],
      have coe_goal := int.nat_abs_zero,
      assumption_mod_cast,
      },
      linarith,
    end,
  have coe_dist_t1_not_lt_min_dist_of_corners_not_in_lattice : ¬(dist_t1 : ℤ) < (min_dist_of_corners_not_in_lattice : ℤ) := 
    by assumption_mod_cast,
  have coe_min_dist_corner_has_min_dist : 
    ((⌊vector.nth corner i⌋ - ⌊vector.nth min_dist_corner i⌋).nat_abs : ℤ) = ↑min_dist_of_corners_not_in_lattice :=
    by assumption_mod_cast,
  dsimp[dist_t1] at coe_dist_t1_not_lt_min_dist_of_corners_not_in_lattice,
  rw nat_abs_val2 at coe_dist_t1_not_lt_min_dist_of_corners_not_in_lattice,
  rw ← coe_min_dist_corner_has_min_dist at coe_dist_t1_not_lt_min_dist_of_corners_not_in_lattice,
  rw nat_abs_val at coe_dist_t1_not_lt_min_dist_of_corners_not_in_lattice,
  replace min_dist_corner_unique := min_dist_corner_unique t1 t1_in_T,
  rw imp_iff_not_or at min_dist_corner_unique,
  rw or_comm at min_dist_corner_unique,
  cases min_dist_corner_unique, 
  { rw min_dist_corner_unique,
    rw min_dist_corner_unique at t1_le_min_dist_corner_floor_add_a,
    linarith,
  },
  rw cube at min_dist_corner_unique,
  simp at min_dist_corner_unique,
  rw in_cube at min_dist_corner_unique,
  simp at min_dist_corner_unique,
  cases min_dist_corner_unique with i'' min_dist_corner_unique,
  have i_eq_i'' : i = i'' :=
    begin
      /-
      We have that t1 ∈ T_i_x because t1 ∈ corners_not_in_lattice, so the only coordinate where
      point_on_line_i_x_where_min_dist_corner_is could fail to be in t1 is i. Therefore, i'' must equal i
      -/
      have i_ne_i'' : true := true.intro,
      contrapose i_ne_i'',
      exfalso,
      rw if_neg i_ne_i'' at min_dist_corner_unique,
      dsimp[corners_not_in_lattice] at t1_not_in_lattice,
      cases t1_not_in_lattice with t1_in_T_i_x _,
      rw T_i at t1_in_T_i_x,
      simp at t1_in_T_i_x,
      cases t1_in_T_i_x with t1_in_T t1_intersects_line_i_x,
      change cube t1 ∩ line_i i x ≠ ∅ at t1_intersects_line_i_x,
      rw [cube, line_i, set.inter_def, set.ne_empty_iff_nonempty, set.nonempty_def] at t1_intersects_line_i_x,
      simp at t1_intersects_line_i_x,
      cases t1_intersects_line_i_x with intersection_point t1_intersects_line_i_x,
      cases t1_intersects_line_i_x with intersection_point_in_t1 intersection_point_on_line_i_x,
      replace intersection_point_on_line_i_x := intersection_point_on_line_i_x i'',
      cases intersection_point_on_line_i_x, exact i_ne_i'' intersection_point_on_line_i_x,
      rw in_cube at intersection_point_in_t1,
      replace intersection_point_in_t1 := intersection_point_in_t1 i'',
      rw ← intersection_point_on_line_i_x at intersection_point_in_t1,
      cases intersection_point_in_t1 with t1_le_x x_lt_t1_add_one,
      replace min_dist_corner_unique := min_dist_corner_unique t1_le_x,
      linarith,
    end,
  rw ← i_eq_i'' at min_dist_corner_unique,
  simp at min_dist_corner_unique,
  have t1_le_min_dist_corner : t1.nth i ≤ min_dist_corner.nth i :=
    begin
      linarith,
    end,
  replace min_dist_corner_unique := min_dist_corner_unique t1_le_min_dist_corner,
  exfalso, --min_dist_corner_unique inconsistent with coe_dist_t1_not_lt_min_dist_of_corners_not_in_lattice
  replace min_dist_corner_unique := int.floor_mono min_dist_corner_unique,
  rename min_dist_corner_unique floor_t1_add_one_le_floor_min_dist_corner,
  have coe_floor_t1_add_one_le_floor_min_dist_corner : ⌊vector.nth t1 i + (1 : ℤ)⌋ ≤ ⌊vector.nth min_dist_corner i⌋ :=
    by assumption_mod_cast,
  have floor_t1_add_one_eq_floor_t1_add_one := int.floor_add_int (vector.nth t1 i) 1,
  rw floor_t1_add_one_eq_floor_t1_add_one at coe_floor_t1_add_one_le_floor_min_dist_corner,
  linarith,
  },
  {
  rename t1_not_in_lattice t1_not_in_corners_not_in_lattice,
  dsimp[corners_not_in_lattice] at t1_not_in_corners_not_in_lattice,
  rw not_and_distrib at t1_not_in_corners_not_in_lattice,
  cases t1_not_in_corners_not_in_lattice,
  {
  rw T_i at t1_not_in_corners_not_in_lattice,
  change ¬(t1 ∈ T ∧ cube t1 ∩ line_i i x ≠ ∅) at t1_not_in_corners_not_in_lattice,
  rw not_and_distrib at t1_not_in_corners_not_in_lattice,
  cases t1_not_in_corners_not_in_lattice, exfalso, exact t1_not_in_corners_not_in_lattice t1_in_T,
  simp at t1_not_in_corners_not_in_lattice,
  rw [cube, line_i, set.inter_def, set.eq_empty_iff_forall_not_mem] at t1_not_in_corners_not_in_lattice,
  replace t1_not_in_corners_not_in_lattice := t1_not_in_corners_not_in_lattice point_on_line_i_x_where_min_dist_corner_should_be,
  change 
    ¬(in_cube t1 point_on_line_i_x_where_min_dist_corner_should_be ∧ 
      ∀ (j : fin d), i = j ∨ x.nth j = point_on_line_i_x_where_min_dist_corner_should_be.nth j) at t1_not_in_corners_not_in_lattice,
  rw not_and_distrib at t1_not_in_corners_not_in_lattice,
  cases t1_not_in_corners_not_in_lattice,
  {
  rw in_cube at t1_not_in_corners_not_in_lattice,
  simp at t1_not_in_corners_not_in_lattice,
  exact t1_not_in_corners_not_in_lattice,
  },
  {
  exfalso,
  simp at t1_not_in_corners_not_in_lattice,
  cases t1_not_in_corners_not_in_lattice with coord t1_not_in_corners_not_in_lattice,
  rw not_or_distrib at t1_not_in_corners_not_in_lattice,
  cases t1_not_in_corners_not_in_lattice with i_ne_coord _,
  rw if_neg i_ne_coord at t1_not_in_corners_not_in_lattice_right,
  exact t1_not_in_corners_not_in_lattice_right (by refl),
  },
  },
  {
  simp at point_on_line_i_x_where_min_dist_corner_should_be_cornerless,
  have point_on_line_i_x_where_min_dist_corner_should_be_not_in_cube_t1 :=
    point_on_line_i_x_where_min_dist_corner_should_be_cornerless t1 t1_in_T,
  rw cube at point_on_line_i_x_where_min_dist_corner_should_be_not_in_cube_t1,
  simp at point_on_line_i_x_where_min_dist_corner_should_be_not_in_cube_t1,
  rw in_cube at point_on_line_i_x_where_min_dist_corner_should_be_not_in_cube_t1,
  simp at point_on_line_i_x_where_min_dist_corner_should_be_not_in_cube_t1,
  exact point_on_line_i_x_where_min_dist_corner_should_be_not_in_cube_t1,
  },
  },
end

lemma tiling_lattice_structure_right_implication_helper_three
  (d : ℕ)
  (T : set (point d))
  (i : fin d)
  (x : point d)
  (not_i_lattice : ∀ (a : ℝ),
                     0 ≤ a →
                     a < 1 →
                     (∀ (t : vector ℝ d),
                        t ∈ T_i T i x →
                        (∃ (z : ℤ), t.nth i = ↑z + a)) →
                     (∃ (z_2 : ℤ),
                        ∀ (t_2 : vector ℝ d),
                          t_2 ∈ T_i T i x →
                          t_2.nth i = ↑z_2 + a →
                          (∃ (t_3 : vector ℝ d),
                             t_3 ∈ T_i T i x ∧
                               t_3.nth i = ↑z_2 + a ∧
                                 ¬t_3 = t_2)))
  (corner : point d)
  (corner_in_T : corner ∈ T)
  (t : vector ℝ d)
  (t_in_T_i_x : t ∈ T_i T i x)
  (corner_in_T_i_x : corner ∈ T_i T i x)
  (corner_lt_t : vector.nth corner i < t.nth i)
  (min_dist_corner : point d)
  (min_dist_corner_gt_corner : vector.nth min_dist_corner i >
                                 vector.nth corner i)
  (min_dist_corner_in_T : min_dist_corner ∈ T)
  (min_dist_corner_cube_intersects_line_i_x : ¬cube min_dist_corner ∩
                                                    line_i i x =
                                                  ∅) :
  let a : ℝ := vector.nth corner i - ↑⌊vector.nth corner i⌋,
      b : ℝ := t.nth i - ↑⌊t.nth i⌋
  in 0 ≤ a →
     a < 1 →
     (∀ (z : ℤ), ¬t.nth i = ↑z + a) →
     0 ≤ b →
     b < 1 →
     (∀ (z : ℤ), ¬vector.nth corner i = ↑z + b) →
     (let corners_not_in_lattice : set (point d) :=
            {t ∈ T_i T i x | t.nth i > vector.nth corner i ∧
               ∀ (z : ℤ), t.nth i ≠ ↑z + a},
          dists_of_corners_not_in_lattice : set ℕ :=
            {dist :
               ℕ | ∃ (t : vector ℝ d) (H : t ∈ corners_not_in_lattice),
               dist = (⌊vector.nth corner i⌋ - ⌊t.nth i⌋).nat_abs}
      in ∀
         (dists_of_corners_not_in_lattice_nonempty :
           dists_of_corners_not_in_lattice.nonempty),
           let min_dist_of_corners_not_in_lattice : ℕ :=
                 nat.lt_wf.min dists_of_corners_not_in_lattice
                   dists_of_corners_not_in_lattice_nonempty,
               corners_not_in_lattice_at_min_dist : set (point d) :=
                 {t ∈ corners_not_in_lattice | (⌊vector.nth corner i⌋ -
                       ⌊t.nth i⌋).nat_abs =
                    min_dist_of_corners_not_in_lattice}
           in (⌊vector.nth corner i⌋ -
                   ⌊vector.nth min_dist_corner i⌋).nat_abs =
                min_dist_of_corners_not_in_lattice →
              vector.nth min_dist_corner i >
                ↑⌊vector.nth min_dist_corner i⌋ + a →
              (∃ (p : point d),
                 ∀ (t1 : point d),
                   t1 ∈ T →
                   p ∈ cube t1 →
                   (∃ (t2 : point d),
                      t2 ∈ T ∧ p ∈ cube t2 ∧ ¬t2 = t1))) :=
begin
  intros a b zero_le_a a_lt_one t_not_a_mod_1 zero_le_b b_lt_one corner_not_b_mod_1 corners_not_in_lattice 
  dists_of_corners_not_in_lattice dists_of_corners_not_in_lattice_nonempty min_dist_of_corners_not_in_lattice 
  corners_not_in_lattice_at_min_dist min_dist_corner_has_min_dist min_dist_corner_not_a_mod_1,
  let point_on_line_i_x_where_min_dist_corner_is : point d :=
    vector.of_fn (λ j, if(i = j) then min_dist_corner.nth i else x.nth j),
  by_cases point_on_line_i_x_where_min_dist_corner_is_in_corner : point_on_line_i_x_where_min_dist_corner_is ∈ cube corner,
  {
  use point_on_line_i_x_where_min_dist_corner_is,
  intros t1 t1_in_T point_on_line_i_x_where_min_dist_corner_is_in_t1,
  by_cases t1_eq_corner : t1 = corner,
  {
  use min_dist_corner,
  split, exact min_dist_corner_in_T,
  split,
  {
  rw cube,
  simp,
  rw in_cube,
  simp,
  intro coord,
  by_cases i_eq_coord : i = coord, {rw i_eq_coord, simp,},
  rename i_eq_coord i_ne_coord,
  rw if_neg i_ne_coord,
  rw [cube, line_i] at min_dist_corner_cube_intersects_line_i_x,
  change {p : point d | in_cube min_dist_corner p} ∩ {p : point d | ∀ (j : fin d), i = j ∨ vector.nth x j = vector.nth p j} ≠ ∅
    at min_dist_corner_cube_intersects_line_i_x,
  rw [set.ne_empty_iff_nonempty, set.nonempty_def] at min_dist_corner_cube_intersects_line_i_x,
  cases min_dist_corner_cube_intersects_line_i_x with p min_dist_corner_cube_intersects_line_i_x,
  simp at min_dist_corner_cube_intersects_line_i_x,
  cases min_dist_corner_cube_intersects_line_i_x with p_in_min_dist_corner_cube p_on_line_i_x,
  rw in_cube at p_in_min_dist_corner_cube,
  replace p_in_min_dist_corner_cube := p_in_min_dist_corner_cube coord,
  replace p_on_line_i_x := p_on_line_i_x coord,
  cases p_on_line_i_x, {exfalso, exact i_ne_coord p_on_line_i_x},
  rw ← p_on_line_i_x at p_in_min_dist_corner_cube,
  exact p_in_min_dist_corner_cube,
  },
  {
  intro min_dist_corner_eq_t1,
  rw [min_dist_corner_eq_t1, ← t1_eq_corner] at min_dist_corner_gt_corner,
  linarith,
  },
  },
  {
  rename t1_eq_corner t1_ne_corner,
  use corner,
  use corner_in_T,
  split, exact point_on_line_i_x_where_min_dist_corner_is_in_corner,
  intro corner_eq_t1,
  symmetry' at corner_eq_t1,
  exact t1_ne_corner corner_eq_t1,
  },
  },
  {
  rename point_on_line_i_x_where_min_dist_corner_is_in_corner point_on_line_i_x_where_min_dist_corner_is_not_in_corner,
  /-
  Obtaining some facts that follow from point_on_line_i_x_where_min_dist_corner_is_not_in_corner before proceeding because
  they may be useful in multiple cases
  -/
  rw cube at point_on_line_i_x_where_min_dist_corner_is_not_in_corner,
  simp at point_on_line_i_x_where_min_dist_corner_is_not_in_corner,
  rw in_cube at point_on_line_i_x_where_min_dist_corner_is_not_in_corner,
  simp at point_on_line_i_x_where_min_dist_corner_is_not_in_corner,
  cases point_on_line_i_x_where_min_dist_corner_is_not_in_corner with i' point_on_line_i_x_where_min_dist_corner_is_not_in_corner,
  have i_eq_i' : i = i' :=
    begin
      contrapose point_on_line_i_x_where_min_dist_corner_is_not_in_corner,
      rename point_on_line_i_x_where_min_dist_corner_is_not_in_corner i_ne_i',
      intro point_on_line_i_x_where_min_dist_corner_is_not_in_corner,
      rw if_neg i_ne_i' at point_on_line_i_x_where_min_dist_corner_is_not_in_corner,
      rw T_i at corner_in_T_i_x,
      change corner ∈ T ∧ cube corner ∩ line_i i x ≠ ∅ at corner_in_T_i_x,
      cases corner_in_T_i_x with corner_in_T cube_corner_line_i_x_intersect,
      rw [cube, line_i, set.inter_def, set.ne_empty_iff_nonempty, set.nonempty_def] at cube_corner_line_i_x_intersect,
      cases cube_corner_line_i_x_intersect with cube_corner_line_i_x_intersection cube_corner_line_i_x_intersect,
      change 
        in_cube corner cube_corner_line_i_x_intersection ∧ ∀ (j : fin d), i = j ∨ x.nth j = cube_corner_line_i_x_intersection.nth j
        at cube_corner_line_i_x_intersect,
      cases cube_corner_line_i_x_intersect with intersection_in_cube intersection_on_line,
      replace intersection_on_line := intersection_on_line i',
      cases intersection_on_line, exact i_ne_i' intersection_on_line,
      rw in_cube at intersection_in_cube,
      replace intersection_in_cube := intersection_in_cube i',
      rw ← intersection_on_line at intersection_in_cube,
      cases intersection_in_cube with corner_le_x x_lt_corner_add_one,
      replace point_on_line_i_x_where_min_dist_corner_is_not_in_corner := point_on_line_i_x_where_min_dist_corner_is_not_in_corner corner_le_x,
      linarith,
    end,
  rw ← i_eq_i' at point_on_line_i_x_where_min_dist_corner_is_not_in_corner,
  simp at point_on_line_i_x_where_min_dist_corner_is_not_in_corner,
  have corner_le_min_dist_corner : vector.nth corner i ≤ vector.nth min_dist_corner i := by linarith,
  replace point_on_line_i_x_where_min_dist_corner_is_not_in_corner := point_on_line_i_x_where_min_dist_corner_is_not_in_corner corner_le_min_dist_corner,
  rename point_on_line_i_x_where_min_dist_corner_is_not_in_corner corner_add_one_le_min_dist_corner,
  let point_on_line_i_x_where_min_dist_corner_should_be : point d :=
    vector.of_fn (λ j, if(i = j) then ↑⌊vector.nth min_dist_corner i⌋ + a else x.nth j),
  /-
  I can't just use point_on_line_i_x_where_min_dist_corner_should_be. That's only if there's no corner that captures it.
  If there is a corner that captures it, then it will also capture point_on_line_i_x_where_min_dist_corner_is and we will need
  to use that point and choose right for the goal (after rewriting imp_iff_not_or as I do below)
  -/
  by_cases point_on_line_i_x_where_min_dist_corner_should_be_has_corner :
    ∃ point_on_line_i_x_where_min_dist_corner_should_be_corner ∈ T,
    point_on_line_i_x_where_min_dist_corner_should_be ∈ cube point_on_line_i_x_where_min_dist_corner_should_be_corner,
  {
  use point_on_line_i_x_where_min_dist_corner_is,
  intros t1 t1_in_T point_on_line_i_x_where_min_dist_corner_is_in_t1,
  cases point_on_line_i_x_where_min_dist_corner_should_be_has_corner with 
    point_on_line_i_x_where_min_dist_corner_should_be_corner point_on_line_i_x_where_min_dist_corner_should_be_has_corner,
  cases point_on_line_i_x_where_min_dist_corner_should_be_has_corner with
    point_on_line_i_x_where_min_dist_corner_should_be_corner_in_T point_on_line_i_x_where_min_dist_corner_should_be_has_corner,
  /-
  Adding this assumption so I can continue to modify point_on_line_i_x_where_min_dist_corner_should_be_has_corner while
  still being able to access the original statement at a later time
  -/
  have point_on_line_i_x_where_min_dist_corner_should_be_in_its_corner := 
    point_on_line_i_x_where_min_dist_corner_should_be_has_corner,
  by_cases t1_eq_min_dist_corner : t1 = min_dist_corner,
  {
  use point_on_line_i_x_where_min_dist_corner_should_be_corner,
  split, exact point_on_line_i_x_where_min_dist_corner_should_be_corner_in_T,
  split,
  {
  rw cube,
  simp,
  rw in_cube,
  simp,
  intro coord,
  by_cases i_eq_coord : i = coord,
  {
  rw i_eq_coord,
  simp,
  rw cube at point_on_line_i_x_where_min_dist_corner_should_be_has_corner,
  simp at point_on_line_i_x_where_min_dist_corner_should_be_has_corner,
  rw in_cube at point_on_line_i_x_where_min_dist_corner_should_be_has_corner,
  simp at point_on_line_i_x_where_min_dist_corner_should_be_has_corner,
  replace point_on_line_i_x_where_min_dist_corner_should_be_has_corner := 
    point_on_line_i_x_where_min_dist_corner_should_be_has_corner i,
  simp at point_on_line_i_x_where_min_dist_corner_should_be_has_corner,
  cases point_on_line_i_x_where_min_dist_corner_should_be_has_corner with
    point_on_line_i_x_where_min_dist_corner_should_be_corner_le_floor_corner_add_a 
    floor_corner_add_a_lt_point_on_line_i_x_where_min_dist_corner_should_be_corner_add_one,
  replace point_on_line_i_x_where_min_dist_corner_should_be_corner_le_floor_corner_add_a : 
    point_on_line_i_x_where_min_dist_corner_should_be_corner.nth i ≤ ↑(int.floor(min_dist_corner.nth i)) + a := by linarith,
  replace floor_corner_add_a_lt_point_on_line_i_x_where_min_dist_corner_should_be_add_one : 
    ↑(int.floor(min_dist_corner.nth i)) + a < point_on_line_i_x_where_min_dist_corner_should_be_corner.nth i + 1 := by linarith,
  rw ← i_eq_coord,
  split, linarith,
  have point_on_line_i_x_where_min_dist_corner_should_be_corner_add_one_le_min_dist_corner : true := true.intro,
  contrapose point_on_line_i_x_where_min_dist_corner_should_be_corner_add_one_le_min_dist_corner,
  simp only [not_true],
  simp only [not_lt] at point_on_line_i_x_where_min_dist_corner_should_be_corner_add_one_le_min_dist_corner,
  rename floor_corner_add_a_lt_point_on_line_i_x_where_min_dist_corner_should_be_corner_add_one 
    floor_min_dist_corner_add_a_lt_point_on_line_i_x_where_min_dist_corner_should_be_add_one,
  replace floor_min_dist_corner_add_a_lt_point_on_line_i_x_where_min_dist_corner_should_be_add_one :
    ↑⌊vector.nth min_dist_corner i⌋ + a < vector.nth point_on_line_i_x_where_min_dist_corner_should_be_corner i + 1 := by linarith,
  let dist_point_on_line_i_x_where_min_dist_should_be_corner :=
    (int.floor(corner.nth i) - int.floor(point_on_line_i_x_where_min_dist_corner_should_be_corner.nth i)).nat_abs,
  have dist_point_on_line_i_x_where_min_dist_corner_should_be_corner_in_dists_of_corners_not_in_lattice :
    dist_point_on_line_i_x_where_min_dist_should_be_corner ∈ dists_of_corners_not_in_lattice :=
    begin
      dsimp[dists_of_corners_not_in_lattice],
      simp,
      use point_on_line_i_x_where_min_dist_corner_should_be_corner,
      have point_on_line_i_x_where_min_dist_corner_should_be_corner_not_in_lattice :
        point_on_line_i_x_where_min_dist_corner_should_be_corner ∈ corners_not_in_lattice :=
        begin
          dsimp[corners_not_in_lattice],
          simp,
          split,
          {
          rw T_i,
          simp,
          split, exact point_on_line_i_x_where_min_dist_corner_should_be_corner_in_T,
          change cube point_on_line_i_x_where_min_dist_corner_should_be_corner ∩ line_i i x ≠ ∅,
          rw [line_i, set.inter_def, set.ne_empty_iff_nonempty, set.nonempty_def],
          use point_on_line_i_x_where_min_dist_corner_should_be,
          simp,
          split, exact point_on_line_i_x_where_min_dist_corner_should_be_in_its_corner,
          intro j,
          by_cases i_eq_j : i = j, {rw i_eq_j, left, refl,},
          right,
          rename i_eq_j i_ne_j,
          rw if_neg i_ne_j,
          },
          {
          split,
          {
          dsimp only[a] at floor_corner_add_a_lt_point_on_line_i_x_where_min_dist_corner_should_be_add_one,
          have floor_mono_fact := int.floor_mono corner_add_one_le_min_dist_corner,
          have coe_floor_mono_fact : ⌊vector.nth corner i + (1 : ℤ)⌋ ≤ ⌊vector.nth min_dist_corner i⌋ :=
            by assumption_mod_cast,
          have floor_fact2 := int.floor_add_int (vector.nth corner i ) 1,
          rw floor_fact2 at coe_floor_mono_fact,
          replace coe_floor_mono_fact : (⌊vector.nth corner i⌋ : ℝ) + 1 ≤ (⌊vector.nth min_dist_corner i⌋ : ℝ) :=
            by assumption_mod_cast,
          linarith,
          },
          {
          intro z,
          intro point_on_line_i_x_where_min_dist_corner_should_be_corner_val,
          have z_eq_or_lt_or_gt_floor_min_dist_corner := eq_or_lt_or_gt z (int.floor(min_dist_corner.nth i)),
          cases z_eq_or_lt_or_gt_floor_min_dist_corner,
          {
          have floor_fact := int.lt_floor_add_one (min_dist_corner.nth i),
          rw z_eq_or_lt_or_gt_floor_min_dist_corner at point_on_line_i_x_where_min_dist_corner_should_be_corner_val,
          rw point_on_line_i_x_where_min_dist_corner_should_be_corner_val at 
            point_on_line_i_x_where_min_dist_corner_should_be_corner_add_one_le_min_dist_corner,
          linarith,
          },
          {
          cases z_eq_or_lt_or_gt_floor_min_dist_corner,
          {
          replace z_eq_or_lt_or_gt_floor_min_dist_corner := int.add_one_le_of_lt z_eq_or_lt_or_gt_floor_min_dist_corner,
          have z_add_one_le_floor_min_dist_corner : (z : ℝ) + 1 ≤ (⌊vector.nth min_dist_corner i⌋ : ℝ) := by assumption_mod_cast,
          linarith,
          },
          {
          replace z_eq_or_lt_or_gt_floor_min_dist_corner : ⌊vector.nth min_dist_corner i⌋ < z := by linarith,
          replace z_eq_or_lt_or_gt_floor_min_dist_corner := int.add_one_le_of_lt z_eq_or_lt_or_gt_floor_min_dist_corner,
          have floor_min_dist_corner_add_one_le_z : (⌊vector.nth min_dist_corner i⌋ : ℝ) + 1 ≤ (z : ℝ) :=
            by assumption_mod_cast,
          linarith,
          },
          },
          },
          },
        end,
      split, exact point_on_line_i_x_where_min_dist_corner_should_be_corner_not_in_lattice,
      refl,
    end,
  have nat_abs_val : 
    ↑(⌊vector.nth corner i⌋ - ⌊vector.nth min_dist_corner i⌋).nat_abs = ⌊vector.nth min_dist_corner i⌋ - ⌊vector.nth corner i⌋ :=
    begin
      have nat_abs_possible_vals := int.nat_abs_eq (⌊vector.nth corner i⌋ - ⌊vector.nth min_dist_corner i⌋),
      have nat_abs_val_ge_zero := coe_nat_abs_ge_zero (⌊vector.nth corner i⌋ - ⌊vector.nth min_dist_corner i⌋),
      cases nat_abs_possible_vals,
      {
      rw ← nat_abs_possible_vals at nat_abs_val_ge_zero,
      have corner_le_min_dist_corner : vector.nth corner i ≤ min_dist_corner.nth i := by linarith,
      have floor_corner_le_floor_min_dist_corner := int.floor_mono corner_le_min_dist_corner,
      have floor_corner_sub_floor_min_dist_corner_eq_zero : int.floor(corner.nth i) - int.floor(min_dist_corner.nth i) = 0 := by linarith,
      have floor_min_dist_corner_sub_floor_corner_eq_zero : int.floor(min_dist_corner.nth i) - int.floor(corner.nth i) = 0 := by linarith,
      rw [floor_corner_sub_floor_min_dist_corner_eq_zero, floor_min_dist_corner_sub_floor_corner_eq_zero],
      have coe_goal := int.nat_abs_zero,
      assumption_mod_cast,
      },
      linarith,
    end,
  have nat_abs_val2 :
    ↑(int.floor(corner.nth i) - int.floor(point_on_line_i_x_where_min_dist_corner_should_be_corner.nth i)).nat_abs =
    int.floor(point_on_line_i_x_where_min_dist_corner_should_be_corner.nth i) - int.floor(corner.nth i) :=
    begin
      have nat_abs_possible_vals := 
        int.nat_abs_eq (int.floor(corner.nth i) - int.floor(point_on_line_i_x_where_min_dist_corner_should_be_corner.nth i)),
      have nat_abs_val_ge_zero := 
        coe_nat_abs_ge_zero (int.floor(corner.nth i) - int.floor(point_on_line_i_x_where_min_dist_corner_should_be_corner.nth i)),
      cases nat_abs_possible_vals,
      {
      rw ← nat_abs_possible_vals at nat_abs_val_ge_zero,
      have corner_le_min_dist_corner : vector.nth corner i ≤ min_dist_corner.nth i := by linarith,
      have floor_corner_le_floor_min_dist_corner := int.floor_mono corner_le_min_dist_corner,
      have floor_corner_add_a_le_point_on_line_i_x_where_min_dist_corner_should_be_add_one :
        ↑⌊vector.nth min_dist_corner i⌋ + a ≤ vector.nth point_on_line_i_x_where_min_dist_corner_should_be_corner i + 1 :=
        by linarith,
      have floor_mono_fact := int.floor_mono floor_corner_add_a_le_point_on_line_i_x_where_min_dist_corner_should_be_add_one,
      rw add_comm at floor_mono_fact,
      rw int.floor_add_int at floor_mono_fact,
      have floor_a_eq_zero : int.floor(a) = 0 :=
        begin
          rw int.floor_eq_iff,
          split, exact zero_le_a,
          simp, exact a_lt_one,
        end,
      rw floor_a_eq_zero at floor_mono_fact,
      rw zero_add at floor_mono_fact,
      have coe_floor_mono_fact :
        ⌊vector.nth min_dist_corner i⌋ ≤ ⌊vector.nth point_on_line_i_x_where_min_dist_corner_should_be_corner i + (1 : ℤ)⌋ :=
        by assumption_mod_cast,
      rw int.floor_add_int at coe_floor_mono_fact,
      have floor_mono_fact2 := int.floor_mono corner_add_one_le_min_dist_corner,
      have coe_floor_mono_fact2 : ⌊vector.nth corner i + (1 : ℤ)⌋ ≤ ⌊vector.nth min_dist_corner i⌋ := by assumption_mod_cast,
      rw int.floor_add_int at coe_floor_mono_fact2,
      linarith,
      },
      linarith,
    end,
  have dist_point_on_line_i_x_where_min_dist_should_be_corner_not_lt_min_dist_of_corners_not_in_lattice :
    ¬dist_point_on_line_i_x_where_min_dist_should_be_corner < min_dist_of_corners_not_in_lattice :=
    well_founded.not_lt_min
      nat.lt_wf dists_of_corners_not_in_lattice dists_of_corners_not_in_lattice_nonempty 
      dist_point_on_line_i_x_where_min_dist_corner_should_be_corner_in_dists_of_corners_not_in_lattice,
  replace dist_point_on_line_i_x_where_min_dist_should_be_corner_not_lt_min_dist_of_corners_not_in_lattice :
    ¬(dist_point_on_line_i_x_where_min_dist_should_be_corner : ℤ) < (min_dist_of_corners_not_in_lattice : ℤ) :=
    by assumption_mod_cast,
  dsimp[dist_point_on_line_i_x_where_min_dist_should_be_corner] at 
    dist_point_on_line_i_x_where_min_dist_should_be_corner_not_lt_min_dist_of_corners_not_in_lattice,
  rw ← min_dist_corner_has_min_dist at 
    dist_point_on_line_i_x_where_min_dist_should_be_corner_not_lt_min_dist_of_corners_not_in_lattice,
  rw [nat_abs_val, nat_abs_val2] at 
    dist_point_on_line_i_x_where_min_dist_should_be_corner_not_lt_min_dist_of_corners_not_in_lattice,
  have floor_min_dist_corner_le_floor_point_on_line_i_x_where_min_dist_corner_should_be_corner :
    ⌊vector.nth min_dist_corner i⌋ ≤ ⌊vector.nth point_on_line_i_x_where_min_dist_corner_should_be_corner i⌋ :=
    by linarith,
  have coe_floor_min_dist_corner_le_floor_point_on_line_i_x_where_min_dist_corner_should_be_corner :
    (⌊vector.nth min_dist_corner i⌋ : ℝ) ≤ (⌊vector.nth point_on_line_i_x_where_min_dist_corner_should_be_corner i⌋ : ℝ) :=
    by assumption_mod_cast,
  have floor_fact1 := int.floor_le (vector.nth point_on_line_i_x_where_min_dist_corner_should_be_corner i),
  have floor_fact2 := int.lt_floor_add_one (vector.nth min_dist_corner i),
  linarith,
  },
  {
  rename i_eq_coord i_ne_coord,
  rw if_neg i_ne_coord,
  rw cube at point_on_line_i_x_where_min_dist_corner_should_be_has_corner,
  simp at point_on_line_i_x_where_min_dist_corner_should_be_has_corner,
  rw in_cube at point_on_line_i_x_where_min_dist_corner_should_be_has_corner,
  simp at point_on_line_i_x_where_min_dist_corner_should_be_has_corner,
  replace point_on_line_i_x_where_min_dist_corner_should_be_has_corner :=
    point_on_line_i_x_where_min_dist_corner_should_be_has_corner coord,
  rw if_neg i_ne_coord at point_on_line_i_x_where_min_dist_corner_should_be_has_corner,
  exact point_on_line_i_x_where_min_dist_corner_should_be_has_corner,
  },
  },
  intro point_on_line_i_x_where_min_dist_corner_should_be_corner_eq_t1,
  have h : t1.nth i = t1.nth i := by refl,
  conv at h 
    begin
      to_lhs,
      rw t1_eq_min_dist_corner,
    end,
  rw ← point_on_line_i_x_where_min_dist_corner_should_be_corner_eq_t1 at h,
  rw cube at point_on_line_i_x_where_min_dist_corner_should_be_has_corner,
  simp at point_on_line_i_x_where_min_dist_corner_should_be_has_corner,
  rw in_cube at point_on_line_i_x_where_min_dist_corner_should_be_has_corner,
  simp at point_on_line_i_x_where_min_dist_corner_should_be_has_corner,
  replace point_on_line_i_x_where_min_dist_corner_should_be_has_corner := 
    point_on_line_i_x_where_min_dist_corner_should_be_has_corner i,
  simp at point_on_line_i_x_where_min_dist_corner_should_be_has_corner,
  rw ← h at point_on_line_i_x_where_min_dist_corner_should_be_has_corner,
  cases point_on_line_i_x_where_min_dist_corner_should_be_has_corner,
  linarith,
  },
  {
  rename t1_eq_min_dist_corner t1_ne_min_dist_corner,
  use min_dist_corner,
  split, exact min_dist_corner_in_T,
  split,
  {
  rw cube,
  simp,
  rw in_cube,
  simp,
  intro coord,
  by_cases i_eq_coord : i = coord, {rw i_eq_coord, simp,},
  rename i_eq_coord i_ne_coord,
  rw if_neg i_ne_coord,
  change cube min_dist_corner ∩ line_i i x ≠ ∅ at min_dist_corner_cube_intersects_line_i_x,
  rw [cube, line_i, set.inter_def, set.ne_empty_iff_nonempty, set.nonempty_def] at min_dist_corner_cube_intersects_line_i_x,
  cases min_dist_corner_cube_intersects_line_i_x with intersection_point min_dist_corner_cube_intersects_line_i_x,
  simp at min_dist_corner_cube_intersects_line_i_x,
  cases min_dist_corner_cube_intersects_line_i_x with intersection_point_in_cube intersection_point_on_line_i_x,
  replace intersection_point_on_line_i_x := intersection_point_on_line_i_x coord,
  cases intersection_point_on_line_i_x, {exfalso, exact i_ne_coord intersection_point_on_line_i_x,},
  rw in_cube at intersection_point_in_cube,
  replace intersection_point_in_cube := intersection_point_in_cube coord,
  rw ← intersection_point_on_line_i_x at intersection_point_in_cube,
  exact intersection_point_in_cube,
  },
  {
  intro min_dist_corner_eq_t1,
  symmetry' at min_dist_corner_eq_t1,
  exact t1_ne_min_dist_corner min_dist_corner_eq_t1,
  },
  },
  },
  {
  rename point_on_line_i_x_where_min_dist_corner_should_be_has_corner point_on_line_i_x_where_min_dist_corner_should_be_cornerless,
  /-
  Cannot just use point_on_line_i_x_where_min_dist_corner_should_be because there may be a corner that has the same floor distance
  as min_dist_corner but has a remainder less than a. Then that corner could be the unique corner that captures
  point_on_line_i_x_where_min_dist_corner_should_be. If that is the case, then we instead need to use 
  point_on_line_i_x_where_min_dist_corner_is because that point will be captured both by min_dist_corner and this other corner
  -/
  by_cases point_on_line_i_x_where_min_dist_corner_is_has_corner_besides_min_dist_corner :
    ∃ point_on_line_i_x_where_min_dist_corner_is_corner ∈ T,
    point_on_line_i_x_where_min_dist_corner_is ∈ cube point_on_line_i_x_where_min_dist_corner_is_corner ∧
    point_on_line_i_x_where_min_dist_corner_is_corner ≠ min_dist_corner,
  {
  have point_on_line_i_x_where_min_dist_corner_is_in_min_dist_corner : 
    point_on_line_i_x_where_min_dist_corner_is ∈ cube min_dist_corner :=
    begin
      rw cube,
      simp,
      rw in_cube,
      simp,
      intro coord,
      by_cases i_eq_coord : i = coord, {rw i_eq_coord, simp,},
      rename i_eq_coord i_ne_coord,
      rw if_neg i_ne_coord,
      change cube min_dist_corner ∩ line_i i x ≠ ∅ at min_dist_corner_cube_intersects_line_i_x,
      rw [cube, line_i, set.inter_def, set.ne_empty_iff_nonempty, set.nonempty_def] at min_dist_corner_cube_intersects_line_i_x,
      cases min_dist_corner_cube_intersects_line_i_x with intersection_point min_dist_corner_cube_intersects_line_i_x,
      simp at min_dist_corner_cube_intersects_line_i_x,
      cases min_dist_corner_cube_intersects_line_i_x with intersection_point_in_cube intersection_point_on_line_i_x,
      replace intersection_point_on_line_i_x := intersection_point_on_line_i_x coord,
      cases intersection_point_on_line_i_x, {exfalso, exact i_ne_coord intersection_point_on_line_i_x,},
      rw in_cube at intersection_point_in_cube,
      replace intersection_point_in_cube := intersection_point_in_cube coord,
      rw ← intersection_point_on_line_i_x at intersection_point_in_cube,
      exact intersection_point_in_cube,
    end,
  use point_on_line_i_x_where_min_dist_corner_is,
  intros t1 t1_in_T point_on_line_i_x_in_t1,
  cases point_on_line_i_x_where_min_dist_corner_is_has_corner_besides_min_dist_corner with 
    other_min_dist_corner point_on_line_i_x_where_min_dist_corner_is_has_corner_besides_min_dist_corner,
  cases point_on_line_i_x_where_min_dist_corner_is_has_corner_besides_min_dist_corner with
    other_min_dist_corner_in_T point_on_line_i_x_where_min_dist_corner_is_has_corner_besides_min_dist_corner,
  cases point_on_line_i_x_where_min_dist_corner_is_has_corner_besides_min_dist_corner with
    point_on_line_i_x_where_min_dist_corner_is_in_other_min_dist_corner other_min_dist_corner_ne_min_dist_corner,
  by_cases t1_eq_min_dist_corner : t1 = min_dist_corner,
  {
  use other_min_dist_corner,
  split, exact other_min_dist_corner_in_T,
  split, exact point_on_line_i_x_where_min_dist_corner_is_in_other_min_dist_corner,
  rw t1_eq_min_dist_corner,
  exact other_min_dist_corner_ne_min_dist_corner,
  },
  {
  rename t1_eq_min_dist_corner t1_ne_min_dist_corner,
  use min_dist_corner,
  split, exact min_dist_corner_in_T,
  split, exact point_on_line_i_x_where_min_dist_corner_is_in_min_dist_corner,
  intro min_dist_corner_eq_t1,
  symmetry' at min_dist_corner_eq_t1,
  exact t1_ne_min_dist_corner min_dist_corner_eq_t1,
  },
  },
  {
  exact tiling_lattice_structure_right_implication_helper_three_helper d T i x not_i_lattice corner corner_in_T t t_in_T_i_x
    corner_in_T_i_x corner_lt_t min_dist_corner min_dist_corner_gt_corner min_dist_corner_in_T 
    min_dist_corner_cube_intersects_line_i_x i' i_eq_i' corner_add_one_le_min_dist_corner zero_le_a a_lt_one t_not_a_mod_1 
    zero_le_b b_lt_one corner_not_b_mod_1 dists_of_corners_not_in_lattice_nonempty min_dist_corner_has_min_dist 
    min_dist_corner_not_a_mod_1 point_on_line_i_x_where_min_dist_corner_should_be_cornerless 
    point_on_line_i_x_where_min_dist_corner_is_has_corner_besides_min_dist_corner,
  },
  },
  },
end

lemma tiling_lattice_structure_right_implication_two_corners_not_congruent_mod_one_in_lattice_case
  (d : ℕ)
  (T : set (point d))
  (i : fin d)
  (x : point d)
  (not_i_lattice : ∀ (a : ℝ),
                     0 ≤ a →
                     a < 1 →
                     (∀ (t : vector ℝ d),
                        t ∈ T_i T i x →
                        (∃ (z : ℤ), t.nth i = ↑z + a)) →
                     (∃ (z_2 : ℤ),
                        ∀ (t_2 : vector ℝ d),
                          t_2 ∈ T_i T i x →
                          t_2.nth i = ↑z_2 + a →
                          (∃ (t_3 : vector ℝ d),
                             t_3 ∈ T_i T i x ∧
                               t_3.nth i = ↑z_2 + a ∧
                                 ¬t_3 = t_2)))
  (corner : point d)
  (corner_in_T : corner ∈ T)
  (t : vector ℝ d)
  (t_in_T_i_x : t ∈ T_i T i x)
  (corner_in_T_i_x : corner ∈ T_i T i x)
  (corner_lt_t : vector.nth corner i < t.nth i) :
  let a : ℝ := vector.nth corner i - ↑⌊vector.nth corner i⌋,
      b : ℝ := t.nth i - ↑⌊t.nth i⌋
  in 0 ≤ a →
     a < 1 →
     (∀ (z : ℤ), ¬t.nth i = ↑z + a) →
     0 ≤ b →
     b < 1 →
     (∀ (z : ℤ), ¬vector.nth corner i = ↑z + b) →
     (∃ (p : point d),
        ∀ (t1 : point d),
          t1 ∈ T →
          p ∈ cube t1 →
          (∃ (t2 : point d), t2 ∈ T ∧ p ∈ cube t2 ∧ ¬t2 = t1)) :=
begin
  intros a b zero_le_a a_lt_one t_not_a_mod_1 zero_le_b b_lt_one corner_not_b_mod_1,
  --Constructing the set of corners not equal to a mod 1 so I can take the
  --minimum of the set and base my argument on that point
  let corners_not_in_lattice := 
    {t ∈ T_i T i x | vector.nth t i > corner.nth i ∧ ∀ z : ℤ, vector.nth t i ≠ ↑z + a},
  --Set of natural number distances between corner and a corner in T_i_x that is not equal to a mod 1
  let dists_of_corners_not_in_lattice :=
    { dist : ℕ | ∃ t ∈ corners_not_in_lattice, 
                  dist = (int.floor(vector.nth corner i) - int.floor(vector.nth t i)).nat_abs },
  have dists_of_corners_not_in_lattice_nonempty : dists_of_corners_not_in_lattice.nonempty :=
    begin
      rw set.nonempty_def,
      use (int.floor(vector.nth corner i) - int.floor(vector.nth t i)).nat_abs,
      dsimp,
      use t,
      split,
      split,
      exact t_in_T_i_x,
      split,
      linarith,
      exact t_not_a_mod_1,
      refl,
    end,
  let min_dist_of_corners_not_in_lattice := 
    well_founded.min nat.lt_wf dists_of_corners_not_in_lattice dists_of_corners_not_in_lattice_nonempty,
  let corners_not_in_lattice_at_min_dist :=
    { t ∈ corners_not_in_lattice | 
        (int.floor(vector.nth corner i) - int.floor(vector.nth t i)).nat_abs = min_dist_of_corners_not_in_lattice
    },
  have set_of_corners_not_in_lattice_at_min_dist_nonempty : corners_not_in_lattice_at_min_dist.nonempty :=
    begin
      rw set.nonempty_def,
      have h : min_dist_of_corners_not_in_lattice ∈ dists_of_corners_not_in_lattice :=
        well_founded.min_mem nat.lt_wf dists_of_corners_not_in_lattice dists_of_corners_not_in_lattice_nonempty,
      dsimp at h,
      cases h with min_dist_corner h,
      use min_dist_corner,
      dsimp[corners_not_in_lattice_at_min_dist],
      change min_dist_corner ∈ corners_not_in_lattice ∧
        (⌊vector.nth corner i⌋ - ⌊min_dist_corner.nth i⌋).nat_abs = min_dist_of_corners_not_in_lattice,
      cases h with h_left h_1,
      cases h_left with h_2 h_3,
      split,
      dsimp[corners_not_in_lattice],
      split,
      exact h_2,
      exact h_3,
      symmetry,
      exact h_1,
    end,
  rw set.nonempty_def at set_of_corners_not_in_lattice_at_min_dist_nonempty,
  cases set_of_corners_not_in_lattice_at_min_dist_nonempty with min_dist_corner min_dist_corner_property,
  dsimp[corners_not_in_lattice_at_min_dist] at min_dist_corner_property,
  change 
    min_dist_corner ∈ corners_not_in_lattice ∧
    (⌊vector.nth corner i⌋ - ⌊min_dist_corner.nth i⌋).nat_abs = min_dist_of_corners_not_in_lattice
    at min_dist_corner_property,
  cases min_dist_corner_property with min_dist_corner_not_in_lattice min_dist_corner_has_min_dist,
  dsimp[corners_not_in_lattice] at min_dist_corner_not_in_lattice,
  change 
    min_dist_corner ∈ T_i T i x ∧ min_dist_corner.nth i > corner.nth i ∧
    ∀ z : ℤ, min_dist_corner.nth i ≠ ↑z + a 
    at min_dist_corner_not_in_lattice,
  cases min_dist_corner_not_in_lattice with min_dist_corner_in_T_i_x min_dist_corner_properties,
  cases min_dist_corner_properties with min_dist_corner_gt_corner min_dist_corner_not_a_mod_1,
  rw T_i at min_dist_corner_in_T_i_x,
  simp at min_dist_corner_in_T_i_x,
  cases min_dist_corner_in_T_i_x with min_dist_corner_in_T min_dist_corner_cube_intersects_line_i_x,
  replace min_dist_corner_not_a_mod_1 :=
    min_dist_corner_not_a_mod_1 (int.floor(vector.nth min_dist_corner i)),
  replace min_dist_corner_not_a_mod_1 := lt_or_gt_of_ne min_dist_corner_not_a_mod_1,
  cases min_dist_corner_not_a_mod_1, --Case on this to choose what to use on goal
  {
  let min_dist_corner_at_line_i_x :=
    vector.of_fn (λ j, if(j = i) then (vector.nth min_dist_corner j) else vector.nth x j),
  /-
  Before I use min_dist_corner_at_line_i_x I need to confirm whether there is a corner before 
  min_dist_corner. If there is, then min_dist_corner_at_line_i_x will be in both that and in min_dist_corner. But 
  if there isn't, I should use a point slightly before min_dist_corner that can't be covered by anything.
  -/
  by_cases exists_prev_corner : 
    ∃ prev_corner ∈ T_i T i x, (vector.nth min_dist_corner i) - (vector.nth prev_corner i) > 0 ∧
                                (vector.nth min_dist_corner i) - (vector.nth prev_corner i) < 1,
  {
  exact tiling_lattice_structure_right_implication_helper_one d T i x not_i_lattice corner corner_in_T t t_in_T_i_x
    corner_in_T_i_x corner_lt_t min_dist_corner min_dist_corner_gt_corner min_dist_corner_in_T
    min_dist_corner_cube_intersects_line_i_x exists_prev_corner zero_le_a a_lt_one t_not_a_mod_1 zero_le_b 
    b_lt_one corner_not_b_mod_1 dists_of_corners_not_in_lattice_nonempty min_dist_corner_has_min_dist 
    min_dist_corner_not_a_mod_1,
  },
  {
  rename exists_prev_corner prev_corner_doesn't_exist,
  /-
  coordinate_just_before_min_dist_corner is a coordinate that is not in the cube of min_dist_corner and cannot be
  in the cube of a corner before min_dist_corner (because prev_corner_doesn't_exist)

  coordinate_just_before_min_dist_corner is not in min_dist_corner because a must be strictly greater than 0 (as the
  remainder of min_dist_corner is strictly less than a) so coordinate_just_before_min_dist_corner is strictly less
  than the floor of min_dist_corner

  coordinate_just_before_min_dist_corner is not in a cube before min_dist_corner because the closest a cube can be
  before min_dist_corner is floor(min_dist_corner) - 2 + a (minus 2 rather than minus 1 because prev_corner_doesn't exist).
  When we add 1 to that to get the max that corner can capture, we get floor(min_dist_corner) - 1 + a which is strictly less
  than coordinate_just_before_min_dist_corner
  -/
  let coordinate_just_before_min_dist_corner : ℝ := ↑(int.floor(vector.nth min_dist_corner i)) + (a - 1)/2,
  let point_just_before_min_dist_corner : point d :=
    vector.of_fn (λ j : fin d, if(j = i) then coordinate_just_before_min_dist_corner else vector.nth x j),
  have coordinate_just_before_min_dist_corner_before_min_dist_corner :
    coordinate_just_before_min_dist_corner < vector.nth min_dist_corner i :=
    begin
      dsimp[coordinate_just_before_min_dist_corner],
      have a_minus_one_divided_by_two_lt_zero : (a-1)/2 < 0 := by linarith,
      have min_dist_corner_floor_le := int.floor_le (vector.nth min_dist_corner i),
      linarith,
    end,
  use point_just_before_min_dist_corner,
  intros t1 t1_in_T,
  rw imp_iff_not_or,
  left, --falsify point_just_before_min_dist_corner ∈ cube t1 (there is no t1 for which this is possible)
  rw cube,
  simp,
  rw in_cube,
  simp,
  simp at prev_corner_doesn't_exist,
  by_cases t1_in_T_i_x : t1 ∈ T_i T i x,
  {
  rename prev_corner_doesn't_exist no_prev_corner_exists,
  have prev_corner_doesn't_exist := no_prev_corner_exists t1,
  replace prev_corner_doesn't_exist := prev_corner_doesn't_exist t1_in_T_i_x,
  rw imp_iff_not_or at prev_corner_doesn't_exist,
  use i,
  simp,
  cases prev_corner_doesn't_exist,
  { intro t1_le_coordinate_just_before_min_dist_corner,
    linarith,
  },
  {
  intro t1_le_coordinate_just_before_min_dist_corner,
  --Need to use the min_dist_of_corners_not_in_lattice definition to show that t1 must have mod a (or be far below corner)
  --and that either way, this puts t1 even farther from min_dist_corner, which will imply the current goal
  by_cases t1_a_mod_1 : ∃ z : ℤ, vector.nth t1 i = z + a,
  {
  cases t1_a_mod_1 with floor_t1 t1_a_mod_1,
  have floor_t1_eq_floor_t1 : floor_t1 = int.floor(vector.nth t1 i) :=
    begin
      contrapose t1_a_mod_1,
      rename t1_a_mod_1 floor_t1_neq_floor_t1,
      intro t1_a_mod_1,
      have floor_t1_eq_floor_floor_t1_add_a : int.floor(vector.nth t1 i) = int.floor(↑floor_t1 + a) := floor_mono_eq t1_a_mod_1,
      rw int.floor_int_add floor_t1 a at floor_t1_eq_floor_floor_t1_add_a,
      have floor_a_eq_zero : int.floor a = 0 :=
        begin
          rw int.floor_eq_iff,
          split, exact zero_le_a,
          simp, exact a_lt_one,
        end,
      rw floor_a_eq_zero at floor_t1_eq_floor_floor_t1_add_a,
      simp at floor_t1_eq_floor_floor_t1_add_a,
      symmetry' at floor_t1_eq_floor_floor_t1_add_a,
      exact floor_t1_neq_floor_t1 floor_t1_eq_floor_floor_t1_add_a,
    end,
  replace t1_a_mod_1 : vector.nth t1 i = ↑(int.floor(vector.nth t1 i)) + a :=
    begin
      rw ← floor_t1_eq_floor_t1,
      exact t1_a_mod_1,
    end,
  have t1_one_plus_one_before_floor_min_dist_corner_minus_one_plus_a :
    vector.nth t1 i + 1 ≤ ↑(int.floor(vector.nth min_dist_corner i)) - 1 + a :=
    begin
      replace prev_corner_doesn't_exist := add_le_of_le_sub_left prev_corner_doesn't_exist,
      rw t1_a_mod_1 at prev_corner_doesn't_exist,
      let b := vector.nth min_dist_corner i - ↑(int.floor(vector.nth min_dist_corner i)),
      replace min_dist_corner_not_a_mod_1 := sub_left_lt_of_lt_add min_dist_corner_not_a_mod_1,
      change b < a at min_dist_corner_not_a_mod_1,
      have min_dist_corner_eq_floor_add_b : 
        vector.nth min_dist_corner i = ↑(int.floor(vector.nth min_dist_corner i)) + b :=
        begin
          dsimp only[b],
          linarith,
        end,
      rw min_dist_corner_eq_floor_add_b at prev_corner_doesn't_exist,
      have t1_more_than_one_less_than_min_dist_corner : ⌊vector.nth t1 i⌋ + 1 < ⌊vector.nth min_dist_corner i⌋ :=
        begin
          replace prev_corner_doesn't_exist : ↑⌊vector.nth t1 i⌋ + 1 ≤ ↑⌊vector.nth min_dist_corner i⌋ + (b - a) := by linarith,
          have b_sub_a_lt_zero : b - a < 0 := by linarith,
          replace prev_corner_doesn't_exist := lt_of_le_add_neg b_sub_a_lt_zero prev_corner_doesn't_exist,
          assumption_mod_cast,
        end,
      rw t1_a_mod_1,
      have floor_t1_add_2_leq_floor_min_dist_corner_with_coe : 
        ↑(int.floor(vector.nth t1 i)) + (2 : ℝ) ≤ ↑(int.floor(vector.nth min_dist_corner i)) :=
        begin
          have floor_t1_add_2_leq_floor_min_dist_corner : 
            int.floor(vector.nth t1 i) + 2 ≤ int.floor(vector.nth min_dist_corner i) := by linarith,
          assumption_mod_cast,
        end,
      linarith,
    end,
  have h : ↑⌊vector.nth min_dist_corner i⌋ - 1 + a ≤ coordinate_just_before_min_dist_corner :=
    begin
      change ↑⌊vector.nth min_dist_corner i⌋ - 1 + a ≤ ↑⌊vector.nth min_dist_corner i⌋ + (a-1)/2,
      linarith,
    end,
  linarith,
  },
  {
  exact tiling_lattice_structure_right_implication_helper_two d T i x not_i_lattice corner corner_in_T t t_in_T_i_x corner_in_T_i_x
    corner_lt_t min_dist_corner min_dist_corner_gt_corner min_dist_corner_in_T min_dist_corner_cube_intersects_line_i_x
    t1 t1_in_T no_prev_corner_exists t1_in_T_i_x prev_corner_doesn't_exist zero_le_a a_lt_one t_not_a_mod_1 zero_le_b b_lt_one 
    corner_not_b_mod_1 dists_of_corners_not_in_lattice_nonempty min_dist_corner_has_min_dist min_dist_corner_not_a_mod_1 
    coordinate_just_before_min_dist_corner_before_min_dist_corner t1_a_mod_1,
  },
  },
  },
  {
  rename t1_in_T_i_x t1_not_in_T_i_x,
  rw T_i at t1_not_in_T_i_x,
  simp at t1_not_in_T_i_x,
  replace t1_not_in_T_i_x := t1_not_in_T_i_x t1_in_T,
  --Figure out which coordinate prevents cube t1 from intersecting with line_i_x, then use that coordinate as coord for the goal
  rw cube at t1_not_in_T_i_x,
  rw line_i at t1_not_in_T_i_x,
  rw set.inter_def at t1_not_in_T_i_x,
  simp at t1_not_in_T_i_x,
  rw set.eq_empty_iff_forall_not_mem at t1_not_in_T_i_x,
  simp at t1_not_in_T_i_x,
  --apply t1_not_in_T_i_x to point_just_before_min_dist_corner to obtain the coordinate that I need to use for the current goal
  replace t1_not_in_T_i_x := t1_not_in_T_i_x point_just_before_min_dist_corner,
  --The hypothesis of t1_not_in_T_i_x must be false because the conclusion is clearly false
  rw imp_iff_not_or at t1_not_in_T_i_x,
  cases t1_not_in_T_i_x,
  {
  rw in_cube at t1_not_in_T_i_x,
  simp at t1_not_in_T_i_x,
  exact t1_not_in_T_i_x,
  },
  { --Derive a contradiction from t1_not_in_T_i_x
  cases t1_not_in_T_i_x with j t1_not_in_T_i_x,
  replace t1_not_in_T_i_x : i ≠ j ∧ vector.nth x j ≠ vector.nth point_just_before_min_dist_corner j :=
    begin
      split,
      intro i_eq_j,
      exact t1_not_in_T_i_x 
        (or.intro_left (vector.nth x j = vector.nth point_just_before_min_dist_corner j) i_eq_j),
      intro h,
      exact t1_not_in_T_i_x (or.intro_right (i = j) h),
    end,
  cases t1_not_in_T_i_x with i_neq_j x_neq_point_just_before_min_dist_corner_at_j,
  dsimp[point_just_before_min_dist_corner] at x_neq_point_just_before_min_dist_corner_at_j,
  simp at x_neq_point_just_before_min_dist_corner_at_j,
  symmetry' at i_neq_j,
  rw if_neg i_neq_j at x_neq_point_just_before_min_dist_corner_at_j,
  exfalso,
  exact x_neq_point_just_before_min_dist_corner_at_j (by refl),
  },
  },
  },
  },
  {
  exact tiling_lattice_structure_right_implication_helper_three d T i x not_i_lattice corner corner_in_T t t_in_T_i_x corner_in_T_i_x
    corner_lt_t min_dist_corner min_dist_corner_gt_corner min_dist_corner_in_T min_dist_corner_cube_intersects_line_i_x
    zero_le_a a_lt_one t_not_a_mod_1 zero_le_b b_lt_one corner_not_b_mod_1 dists_of_corners_not_in_lattice_nonempty  
    min_dist_corner_has_min_dist min_dist_corner_not_a_mod_1,
  },
end

lemma tiling_lattice_structure_right_implication_unique_corner_case :
  ∀ d : ℕ, ∀ T : set (point d), ∀ i : fin d, ∀ x : point d,
  ∀ not_i_lattice : 
    ∀ (a : ℝ), 0 ≤ a → a < 1 → (∀ (t : vector ℝ d), t ∈ T_i T i x → (∃ (z : ℤ), t.nth i = ↑z + a)) → 
    (∃ (z_2 : ℤ), ∀ (t_2 : vector ℝ d), t_2 ∈ T_i T i x → t_2.nth i = ↑z_2 + a → 
    (∃ (t_3 : vector ℝ d), t_3 ∈ T_i T i x ∧ t_3.nth i = ↑z_2 + a ∧ ¬t_3 = t_2)),
  ∀ corner : point d, ∀ corner_in_T : corner ∈ T, ∀ x_in_cube_corner : x ∈ cube corner,
  ∀ corner_unique : ∀ (alt_corner : point d), alt_corner ∈ T → x ∈ cube alt_corner → alt_corner = corner,
  ∃ (p : point d), ∀ (t1 : point d), t1 ∈ T → p ∈ cube t1 → (∃ (t2 : point d), t2 ∈ T ∧ p ∈ cube t2 ∧ ¬t2 = t1)
  :=
begin
  repeat{intro},
  let a := (vector.nth corner i) - ↑(int.floor(vector.nth corner i)),
  have a_ge_zero : a ≥ 0 :=
    begin
      change (vector.nth corner i) - ↑(int.floor(vector.nth corner i)) ≥ 0,
      rw ge_iff_le,
      rw le_sub,
      rw sub_zero,
      exact int.floor_le (vector.nth corner i),
    end,
  rw ge_iff_le at a_ge_zero,
  rename a_ge_zero zero_le_a,
  have a_lt_one : a < 1 :=
    begin
      change (vector.nth corner i) - ↑(int.floor(vector.nth corner i)) < 1,
      have : vector.nth corner i < ↑⌊vector.nth corner i⌋ + 1 := int.lt_floor_add_one (vector.nth corner i),
      linarith,
    end,
  have not_i_lattice_a := not_i_lattice a zero_le_a a_lt_one,
  by_cases not_i_lattice_a_hypothesis : (∀ (t : vector ℝ d), t ∈ T_i T i x → (∃ (z : ℤ), t.nth i = ↑z + a)),
  {
  replace not_i_lattice_a := not_i_lattice_a not_i_lattice_a_hypothesis,
  cases not_i_lattice_a with z not_i_lattice_a,
  let point_at_z_on_line_i_x :=
    vector.of_fn (λ j : fin d, if(j = i) then ↑z + a else x.nth j),
  use point_at_z_on_line_i_x,
  intros t1 t1_in_T point_at_z_on_line_i_x_in_t1,
  have t1_in_T_i_x : t1 ∈ T_i T i x :=
    begin
      rw T_i,
      simp,
      split, exact t1_in_T,
      change cube t1 ∩ line_i i x ≠ ∅,
      rw [set.ne_empty_iff_nonempty, set.nonempty_def],
      use point_at_z_on_line_i_x,
      rw set.inter_def,
      simp,
      split, exact point_at_z_on_line_i_x_in_t1,
      rw line_i,
      simp,
      intro,
      by_cases j_eq_i : j = i, {left, symmetry, exact j_eq_i},
      right,
      rw if_neg j_eq_i,
    end,
  have t1_a_mod_1 := not_i_lattice_a_hypothesis t1 t1_in_T_i_x,
  cases t1_a_mod_1 with z' t1_val,
  have z_eq_z' : z = z' :=
    begin
      rw cube at point_at_z_on_line_i_x_in_t1,
      simp at point_at_z_on_line_i_x_in_t1,
      rw in_cube at point_at_z_on_line_i_x_in_t1,
      simp at point_at_z_on_line_i_x_in_t1,
      replace point_at_z_on_line_i_x_in_t1 := point_at_z_on_line_i_x_in_t1 i,
      simp at point_at_z_on_line_i_x_in_t1,
      cases point_at_z_on_line_i_x_in_t1 with t1_le_z_add_a z_add_a_lt_t1_add_one,
      replace t1_le_z_add_a : t1.nth i ≤ ↑z + a := by linarith,
      replace z_add_a_lt_t1_add_one : ↑z + a < t1.nth i + 1 := by linarith,
      rw t1_val at t1_le_z_add_a,
      rw t1_val at z_add_a_lt_t1_add_one,
      have coe_z'_le_z : (z' : ℝ) ≤ (z : ℝ) := by linarith,
      have coe_z_lt_z'_add_one : (z : ℝ) < (z' : ℝ) + 1 := by linarith,
      have z'_le_z : z' ≤ z := by assumption_mod_cast,
      have z_lt_z'_add_one : z < z' + 1 := by assumption_mod_cast,
      omega,
    end,
  rw ← z_eq_z' at t1_val,
  replace not_i_lattice_a := not_i_lattice_a t1 t1_in_T_i_x t1_val,
  cases not_i_lattice_a with t2 t2_property,
  cases t2_property with t2_in_T_i_x t2_property,
  cases t2_property with t2_val t2_ne_t1,
  use t2,
  rw T_i at t2_in_T_i_x,
  change t2 ∈ T ∧ cube t2 ∩ line_i i x ≠ ∅ at t2_in_T_i_x,
  cases t2_in_T_i_x with t2_in_T t2_intersects_line_i_x,
  split, exact t2_in_T,
  split,
  {
  rw [cube, line_i, set.inter_def, set.ne_empty_iff_nonempty, set.nonempty_def] at t2_intersects_line_i_x,
  cases t2_intersects_line_i_x with intersection_point t2_intersects_line_i_x,
  simp at t2_intersects_line_i_x,
  cases t2_intersects_line_i_x with intersection_point_in_t2 intersection_point_on_line_i_x,
  rw cube,
  simp,
  rw in_cube,
  simp,
  intro coord,
  by_cases coord_eq_i : coord = i,
  {
  rw coord_eq_i,
  simp,
  rw t2_val,
  split, linarith, linarith,
  },
  {
  rename coord_eq_i coord_ne_i,
  rw if_neg coord_ne_i,
  rw in_cube at intersection_point_in_t2,
  replace intersection_point_in_t2 := intersection_point_in_t2 coord,
  replace intersection_point_on_line_i_x := intersection_point_on_line_i_x coord,
  cases intersection_point_on_line_i_x, 
  {
  exfalso, 
  symmetry' at intersection_point_on_line_i_x, 
  exact coord_ne_i intersection_point_on_line_i_x
  },
  {
  rw ← intersection_point_on_line_i_x at intersection_point_in_t2,
  exact intersection_point_in_t2,
  }
  },
  },
  {
  exact t2_ne_t1,
  },
  },
  {
  clear not_i_lattice_a,
  rename not_i_lattice_a_hypothesis not_i_lattice_a,
  simp at not_i_lattice_a,
  change
    ∃ (t : vector ℝ d), t ∈ T_i T i x ∧ ∀ (z : ℤ), ¬t.nth i = ↑z + a at not_i_lattice_a,
  cases not_i_lattice_a with t not_i_lattice_a,
  cases not_i_lattice_a with t_in_T_i_x t_not_a_mod_1,
  have corner_in_T_i_x : corner ∈ T_i T i x :=
    begin
      rw T_i,
      change corner ∈ T ∧ cube corner ∩ line_i i x ≠ ∅,
      split, exact corner_in_T,
      rw line_i,
      rw set.inter_def,
      rw set.ne_empty_iff_nonempty,
      rw set.nonempty_def,
      simp,
      use x,
      split, exact x_in_cube_corner,
      intro, right, refl,
    end,
  let b := (t.nth i) - ↑(int.floor(t.nth i)),
  have b_ge_zero : b ≥ 0 :=
    begin
      change (t.nth i) - ↑(int.floor(t.nth i)) ≥ 0,
      rw ge_iff_le,
      rw le_sub,
      rw sub_zero,
      exact int.floor_le (t.nth i),
    end,
  rw ge_iff_le at b_ge_zero,
  rename b_ge_zero zero_le_b,
  have b_lt_one : b < 1 :=
    begin
      change (t.nth i) - ↑(int.floor(t.nth i)) < 1,
      have : t.nth i < ↑⌊t.nth i⌋ + 1 := int.lt_floor_add_one (t.nth i),
      linarith,
    end,
  have corner_not_b_mod_1 : ∀ z : ℤ, ¬corner.nth i = ↑z + b :=
    begin
      intros z corner_b_mod_1,
      dsimp only[b] at corner_b_mod_1,
      have corner_val : corner.nth i = ↑(int.floor(corner.nth i)) + a := by {dsimp only[a], linarith,},
      rw corner_val at corner_b_mod_1,
      apply (t_not_a_mod_1 (⌊vector.nth corner i⌋ - z + ⌊t.nth i⌋)),
      have coe_goal : t.nth i = ↑⌊vector.nth corner i⌋ - ↑z + ↑⌊t.nth i⌋ + a := by linarith,
      assumption_mod_cast,
    end,
  by_cases corner_lt_t : corner.nth i < t.nth i,
  {
  exact tiling_lattice_structure_right_implication_two_corners_not_congruent_mod_one_in_lattice_case
    d T i x not_i_lattice corner corner_in_T t t_in_T_i_x
    corner_in_T_i_x corner_lt_t zero_le_a a_lt_one t_not_a_mod_1 zero_le_b b_lt_one
    corner_not_b_mod_1,
  },
  {
  have t_lt_corner : t.nth i < corner.nth i :=
    begin
      have t_le_corner : t.nth i ≤ corner.nth i := by linarith,
      have t_eq_corner_or_t_lt_corner := eq_or_lt_of_le t_le_corner,
      cases t_eq_corner_or_t_lt_corner,
      {
      exfalso,
      replace corner_not_b_mod_1 := corner_not_b_mod_1 (int.floor(t.nth i)),
      rw ← t_eq_corner_or_t_lt_corner at corner_not_b_mod_1,
      dsimp[b] at corner_not_b_mod_1,
      contrapose corner_not_b_mod_1,
      simp,
      },
      {
      exact t_eq_corner_or_t_lt_corner,
      },
    end,
  have t_in_T : t ∈ T :=
    begin
      rw T_i at t_in_T_i_x,
      change t ∈ T ∧ cube t ∩ line_i i x ≠ ∅ at t_in_T_i_x,
      cases t_in_T_i_x,
      exact t_in_T_i_x_left,
    end,
  exact tiling_lattice_structure_right_implication_two_corners_not_congruent_mod_one_in_lattice_case
    d T i x not_i_lattice t t_in_T corner corner_in_T_i_x t_in_T_i_x t_lt_corner zero_le_b b_lt_one
    corner_not_b_mod_1 zero_le_a a_lt_one t_not_a_mod_1,
  },
  },
end

lemma tiling_lattice_structure_right_implication :
  ∀ d : ℕ, ∀ T : set (point d), ∀ i : fin d, 
  is_tiling T → ∀ x : point d, is_i_lattice d (T_i T i x) i :=
begin
  intros _ _ _,
  contrapose,
  simp,
  intro,
  intro not_i_lattice,
  rw is_i_lattice at not_i_lattice,
  rw is_tiling,
  simp,
  change ∃ (p : point d), ∀ (t1 : point d), t1 ∈ T → p ∈ cube t1 → 
    (∃ (t2 : point d), t2 ∈ T ∧ p ∈ cube t2 ∧ ¬t2 = t1),
  simp at not_i_lattice,
  change ∀ (a : ℝ), 0 ≤ a → a < 1 → (∀ (t : vector ℝ d), t ∈ T_i T i x → 
    (∃ (z : ℤ), t.nth i = ↑z + a)) → 
    (∃ (z_2 : ℤ), ∀ (t_2 : vector ℝ d), t_2 ∈ T_i T i x → t_2.nth i = ↑z_2 + a → 
    (∃ (t_3 : vector ℝ d), t_3 ∈ T_i T i x ∧ t_3.nth i = ↑z_2 + a ∧ ¬t_3 = t_2)) at not_i_lattice,
  have try_to_find_x_corner := try_point_to_corner T x,
  cases try_to_find_x_corner,
  { --No corner case
  use x,
  intros t t_in_T x_in_cube_t,
  exfalso,
  exact try_to_find_x_corner t t_in_T x_in_cube_t,
  },
  { --Unique corner is the hard case (where I will need the mod 1 argument)
  cases try_to_find_x_corner with corner corner_prop,
  cases corner_prop with corner_in_T corner_prop,
  cases corner_prop with x_in_cube_corner corner_unique,
  exact tiling_lattice_structure_right_implication_unique_corner_case
    d T i x not_i_lattice corner corner_in_T x_in_cube_corner corner_unique,
  },
  { --Multiple corners case
  cases try_to_find_x_corner,
  let t1 := prod.fst try_to_find_x_corner_val,
  let t2 := prod.snd try_to_find_x_corner_val,
  change t1 ∈ T ∧ x ∈ cube t1 ∧ t2 ∈ T ∧ x ∈ cube t2 ∧ t1 ≠ t2 at try_to_find_x_corner_property,
  cases try_to_find_x_corner_property with t1_in_T try_to_find_x_corner_property,
  cases try_to_find_x_corner_property with x_in_cube_t1 try_to_find_x_corner_property,
  cases try_to_find_x_corner_property with t2_in_T try_to_find_x_corner_property,
  cases try_to_find_x_corner_property with x_in_cube_t2 t1_neq_t2,
  use x,
  intros t t_in_T x_in_cube_T,
  by_cases t_eq_t1 : t = t1,
  use t2,
  split,
  exact t2_in_T,
  split,
  exact x_in_cube_t2,
  rw t_eq_t1,
  intro t2_eq_t1,
  have t1_eq_t2 : t1 = t2,
  symmetry,
  exact t2_eq_t1,
  exact t1_neq_t2 t1_eq_t2,
  rename t_eq_t1 t_neq_t1,
  use t1,
  split,
  exact t1_in_T,
  split,
  exact x_in_cube_t1,
  intro t1_eq_t,
  have t_eq_t1 : t = t1,
  symmetry,
  exact t1_eq_t,
  exact t_neq_t1 t_eq_t1,
  },
end

theorem tiling_lattice_structure : 
  ∀ d : ℕ, ∀ T : set (point d), ∀ i : fin d, 
  is_tiling T ↔ ∀ x : point d, is_i_lattice d (T_i T i x) i :=
begin
  repeat {intro},
  split,
  apply tiling_lattice_structure_right_implication,
  apply tiling_lattice_structure_left_implication,
end

lemma cube_distance_lemma :
  ∀ d : ℕ, ∀ T : set (point d), ∀ H : is_tiling T,
  ∀ x : int_point d, ∀ i : fin d,
  ((int_point_to_corner H x).val).nth i + 1 = 
  ((point_to_corner H (add_vectors (int_point_to_point x) (unit_basis_vector i))).val).nth i :=
begin
  repeat{intro},
  let x' := int_point_to_point x,
  have T_i_x_is_i_lattice : is_i_lattice d (T_i T i x') i := by {rw tiling_lattice_structure d T i at H, exact H x',},
  rw is_i_lattice at T_i_x_is_i_lattice,
  cases T_i_x_is_i_lattice with a T_i_x_is_i_lattice,
  cases T_i_x_is_i_lattice with zero_le_a T_i_x_is_i_lattice,
  cases T_i_x_is_i_lattice with a_lt_one T_i_x_is_i_lattice,
  cases T_i_x_is_i_lattice with all_corners_mod_a all_ints_have_corner,
  let x_corner := (int_point_to_corner H x).val,
  have x_corner_def : (int_point_to_corner H x).val = x_corner := by refl,
  have x_corner_property := (int_point_to_corner H x).property,
  rw x_corner_def at x_corner_property,
  rw x_corner_def,
  cases x_corner_property with x_corner_in_T x_corner_property,
  cases x_corner_property with x_in_x_corner x_corner_unique,
  have x_corner_in_T_i_x : x_corner ∈ T_i T i x' :=
    begin
      rw T_i,
      simp,
      split, exact x_corner_in_T,
      change cube x_corner ∩ line_i i x' ≠ ∅,
      rw[line_i, set.inter_def, set.ne_empty_iff_nonempty, set.nonempty_def],
      use x',
      simp,
      dsimp[x'],
      exact x_in_x_corner,
    end,
  have x_corner_mod_a := all_corners_mod_a x_corner x_corner_in_T_i_x,
  cases x_corner_mod_a with floor_x_corner x_corner_mod_a,

  let x_add_unit := add_vectors (int_point_to_point x) (unit_basis_vector i),
  have x_add_unit_def : add_vectors (int_point_to_point x) (unit_basis_vector i) = x_add_unit := by refl,
  rw x_add_unit_def,
  let x_add_unit_corner := (point_to_corner H x_add_unit).val,
  have x_add_unit_corner_def : (point_to_corner H x_add_unit).val = x_add_unit_corner := by refl,
  have x_add_unit_corner_property := (point_to_corner H x_add_unit).property,
  rw x_add_unit_corner_def at x_add_unit_corner_property,
  rw x_add_unit_corner_def,
  cases x_add_unit_corner_property with x_add_unit_corner_in_T x_add_unit_corner_property,
  cases x_add_unit_corner_property with x_add_unit_in_x_add_unit_corner x_add_unit_corner_unique,
  have x_add_unit_corner_in_T_i_x : x_add_unit_corner ∈ T_i T i x' :=
    begin
      rw T_i,
      simp,
      split, exact x_add_unit_corner_in_T,
      change cube x_add_unit_corner ∩ line_i i x' ≠ ∅,
      rw[line_i, set.inter_def, set.ne_empty_iff_nonempty, set.nonempty_def],
      use x_add_unit,
      simp,
      dsimp[x'],
      split, exact x_add_unit_in_x_add_unit_corner,
      intro j,
      by_cases i_eq_j : i = j, {left, exact i_eq_j},
      rename i_eq_j i_ne_j,
      right,
      rw int_point_to_point,
      simp,
      rw ← x_add_unit_def,
      rw add_vectors,
      simp,
      rw int_point_to_point,
      simp,
      rw unit_basis_vector,
      simp,
      exact i_ne_j,
    end,
  have x_add_unit_corner_mod_a := all_corners_mod_a x_add_unit_corner x_add_unit_corner_in_T_i_x,
  cases x_add_unit_corner_mod_a with floor_x_add_unit_corner x_add_unit_corner_mod_a,
  rw cube at x_in_x_corner,
  simp at x_in_x_corner,
  rw in_cube at x_in_x_corner,
  replace x_in_x_corner := x_in_x_corner i,
  rw x_corner_mod_a at x_in_x_corner,
  cases x_in_x_corner with x_corner_le_x x_lt_x_corner_add_one,
  replace x_corner_le_x : ↑floor_x_corner + a ≤ x'.nth i := by linarith,
  replace x_lt_x_corner_add_one : x'.nth i < ↑floor_x_corner + a + 1 := by linarith,
  rw cube at x_add_unit_in_x_add_unit_corner,
  simp at x_add_unit_in_x_add_unit_corner,
  rw in_cube at x_add_unit_in_x_add_unit_corner,
  replace x_add_unit_in_x_add_unit_corner := x_add_unit_in_x_add_unit_corner i,
  dsimp[x_add_unit] at x_add_unit_in_x_add_unit_corner,
  rw add_vectors at x_add_unit_in_x_add_unit_corner,
  simp at x_add_unit_in_x_add_unit_corner,
  rw unit_basis_vector at x_add_unit_in_x_add_unit_corner,
  simp at x_add_unit_in_x_add_unit_corner,
  rw x_add_unit_corner_mod_a at x_add_unit_in_x_add_unit_corner,
  cases x_add_unit_in_x_add_unit_corner with x_add_unit_corner_le_x_add_one x_lt_x_add_unit_corner,
  change ↑floor_x_add_unit_corner + a ≤ vector.nth x' i + 1 at x_add_unit_corner_le_x_add_one,
  change vector.nth x' i < ↑floor_x_add_unit_corner + a at x_lt_x_add_unit_corner,
  have coe_floor_x_corner_lt_floor_x_add_unit_corner : (floor_x_corner : ℝ) < (floor_x_add_unit_corner : ℝ) := 
    by linarith,
  have coe_floor_x_add_unit_corner_lt_x_corner_add_two : (floor_x_add_unit_corner : ℝ) < ↑floor_x_corner + 2 := 
    by linarith,
  have floor_x_corner_lt_floor_x_add_unit_corner : floor_x_corner < floor_x_add_unit_corner := 
    by assumption_mod_cast,
  have coe_floor_x_add_unit_corner_lt_x_corner_add_two : floor_x_add_unit_corner < floor_x_corner + 2 := 
    by assumption_mod_cast,
  have floor_x_corner_add_one_eq_floor_x_add_unit_corner : floor_x_corner + 1 = floor_x_add_unit_corner := by omega,
  have coe_floor_x_corner_add_one_eq_floor_x_add_unit_corner : (floor_x_corner : ℝ) + 1 = ↑floor_x_add_unit_corner :=
    by assumption_mod_cast,
  rw [x_corner_mod_a, x_add_unit_corner_mod_a],
  linarith,
end

lemma faceshare_free_lemma_helper
  (d : ℕ) (T : set (point d)) (H : is_tiling T) (corner1 : point d) (corner1_in_T : corner1 ∈ T) (corner2 : point d) 
  (corner2_in_T : corner2 ∈ T) (i : fin d) (corners_faceshare : is_facesharing corner1 corner2)
  (corners_same_outside_of_i : ∀ (y : fin d), i = y ∨ vector.nth corner1 y = vector.nth corner2 y)
  (corners_differ_at_i : vector.nth corner1 i - vector.nth corner2 i = 1) :
  ∃ (x : int_point d) (i : fin d), 
    is_facesharing (int_point_to_corner H x).val
      (point_to_corner H (add_vectors (int_point_to_point x) (unit_basis_vector i))).val :=
begin
  let corner2_rounded_up : int_point d := vector.of_fn (λ j : fin d, int.ceil(corner2.nth j)),
  let corner1_rounded_up : int_point d := vector.of_fn (λ j : fin d, int.ceil(corner1.nth j)),
  use corner2_rounded_up,
  use i,
  let corner2' := (int_point_to_corner H corner2_rounded_up).val,
  have corner2'_def : (int_point_to_corner H corner2_rounded_up).val = corner2' := by refl,
  let corner2'_property := (int_point_to_corner H corner2_rounded_up).property,
  rw corner2'_def at corner2'_property,
  rw corner2'_def,
  cases corner2'_property with corner2'_in_T corner2'_property,
  cases corner2'_property with corner2_rounded_up_in_corner2' corner2'_unique,
  have corner2_rounded_up_in_corner2 : int_point_to_point corner2_rounded_up ∈ cube corner2 :=
    begin
      rw cube,
      simp,
      rw in_cube,
      intro coord,
      rw int_point_to_point,
      split, {simp, exact int.le_ceil (vector.nth corner2 coord),},
      simp, exact int.ceil_lt_add_one (vector.nth corner2 coord),
    end,
  have corner2_eq_corner2' : corner2 = corner2' := corner2'_unique corner2 corner2_in_T corner2_rounded_up_in_corner2,
  rw ← corner2_eq_corner2',
  let corner2_rounded_up_add_unit := (add_vectors (int_point_to_point corner2_rounded_up) (unit_basis_vector i)),
  have corner2_rounded_up_add_unit_def : 
    (add_vectors (int_point_to_point corner2_rounded_up) (unit_basis_vector i)) = corner2_rounded_up_add_unit := by refl,
  rw corner2_rounded_up_add_unit_def,
  let corner1' := (point_to_corner H corner2_rounded_up_add_unit).val,
  have corner1'_def : (point_to_corner H corner2_rounded_up_add_unit).val = corner1' := by refl,
  rw corner1'_def,
  let corner1'_property := (point_to_corner H corner2_rounded_up_add_unit).property,
  rw corner1'_def at corner1'_property,
  cases corner1'_property with corner1'_in_T corner1'_property,
  cases corner1'_property with corner2_rounded_up_add_unit_in_corner1' corner1'_unique,
  have corner2_rounded_up_add_unit_in_corner1 : corner2_rounded_up_add_unit ∈ cube corner1 :=
    begin
      rw cube,
      change in_cube corner1 corner2_rounded_up_add_unit,
      rw in_cube,
      intro coord,
      by_cases i_eq_coord : i = coord,
      { rw ← i_eq_coord,
        dsimp[corner2_rounded_up_add_unit],
        rw [add_vectors, int_point_to_point],
        dsimp[corner2_rounded_up],
        rw unit_basis_vector,
        simp,
        have corner2_le_ceil_corner2 := int.le_ceil (corner2.nth i),
        have corner2_ceil_lt_corner2_add_one := int.ceil_lt_add_one (corner2.nth i),
        split, linarith, linarith,
      },
      rename i_eq_coord i_ne_coord,
      dsimp[corner2_rounded_up_add_unit],
      rw [add_vectors, int_point_to_point],
      dsimp[corner2_rounded_up],
      rw unit_basis_vector,
      simp,
      rw if_neg i_ne_coord,
      simp,
      have corner1_eq_corner2_at_coord : corner1.nth coord = corner2.nth coord :=
        begin
          replace corners_same_outside_of_i := corners_same_outside_of_i coord,
          cases corners_same_outside_of_i, {exfalso, exact i_ne_coord corners_same_outside_of_i,},
          exact corners_same_outside_of_i,
        end,
      rw corner1_eq_corner2_at_coord,
      have corner2_le_ceil_corner2 := int.le_ceil (corner2.nth coord),
      have corner2_ceil_lt_corner2_add_one := int.ceil_lt_add_one (corner2.nth coord),
      split, linarith, linarith,
    end,
  have corner1_eq_corner1' := corner1'_unique corner1 corner1_in_T corner2_rounded_up_add_unit_in_corner1,
  rw ← corner1_eq_corner1',
  exact (is_facesharing_comm corners_faceshare),
end

lemma faceshare_free_lemma :
  ∀ d : ℕ, ∀ T : set (point d), ∀ H : is_tiling T, tiling_faceshare_free T ↔
  ∀ x : int_point d, ∀ i : fin d,
  ¬(is_facesharing (int_point_to_corner H x).val 
                   (point_to_corner H (add_vectors (int_point_to_point x) (unit_basis_vector i))).val)
  :=
begin
  repeat{intro},
  split,
  { intro T_faceshare_free,
    intros x i,
    rw tiling_faceshare_free at T_faceshare_free,
    let x_corner := (int_point_to_corner H x).val,
    have x_corner_def : (int_point_to_corner H x).val = x_corner := by refl,
    have x_corner_property := (int_point_to_corner H x).property,
    rw x_corner_def at x_corner_property,
    rw x_corner_def,
    cases x_corner_property with x_corner_in_T x_corner_property,
    let x_add_unit := add_vectors (int_point_to_point x) (unit_basis_vector i),
    have x_add_unit_def : add_vectors (int_point_to_point x) (unit_basis_vector i) = x_add_unit := by refl,
    rw x_add_unit_def,
    let x_add_unit_corner := (point_to_corner H x_add_unit).val,
    have x_add_unit_corner_def : (point_to_corner H x_add_unit).val = x_add_unit_corner := by refl,
    have x_add_unit_corner_property := (point_to_corner H x_add_unit).property,
    rw x_add_unit_corner_def at x_add_unit_corner_property,
    rw x_add_unit_corner_def,
    cases x_add_unit_corner_property with x_add_unit_corner_in_T x_add_unit_corner_property,
    exact T_faceshare_free x_corner x_corner_in_T x_add_unit_corner x_add_unit_corner_in_T,
  },
  contrapose,
  intro T_not_faceshare_free,
  simp,
  change ∃(x : int_point d) (i : fin d),
    is_facesharing ↑(int_point_to_corner H x) ↑(point_to_corner H (add_vectors (int_point_to_point x) (unit_basis_vector i))),
  rw tiling_faceshare_free at T_not_faceshare_free,
  simp at T_not_faceshare_free,
  cases T_not_faceshare_free with corner1 T_not_faceshare_free,
  cases T_not_faceshare_free with corner1_in_T T_not_faceshare_free,
  cases T_not_faceshare_free with corner2 T_not_faceshare_free,
  cases T_not_faceshare_free with corner2_in_T corners_faceshare,
  have corners_faceshare' := corners_faceshare,
  rw is_facesharing at corners_faceshare',
  cases corners_faceshare' with i corners_faceshare',
  cases corners_faceshare' with corners_differ_at_i corners_same_outside_of_i,
  cases corners_differ_at_i,
  exact faceshare_free_lemma_helper 
    d T H corner1 corner1_in_T corner2 corner2_in_T i corners_faceshare corners_same_outside_of_i corners_differ_at_i,
  replace corners_same_outside_of_i : ∀ (y : fin d), i = y ∨ vector.nth corner2 y = vector.nth corner1 y :=
    begin
      intro y,
      replace corners_same_outside_of_i := corners_same_outside_of_i y,
      cases corners_same_outside_of_i, {left, exact corners_same_outside_of_i},
      right, symmetry, exact corners_same_outside_of_i,
    end,
  replace corners_faceshare : is_facesharing corner2 corner1 := is_facesharing_comm corners_faceshare,
  exact faceshare_free_lemma_helper 
    d T H corner2 corner2_in_T corner1 corner1_in_T i corners_faceshare corners_same_outside_of_i corners_differ_at_i,
end

def shift_tiling {d : ℕ} (T : set (point d)) (i : fin d) (a : ℝ) (b : ℝ) : set (point d) :=
  { t : point d | t ∈ T ∧ ne_mod_one (t.nth i) a } ∪ 
  { t' : point d | ∃ t ∈ T, t' = add_vectors t (scaled_basis_vector b i) ∧ eq_mod_one (t.nth i) a }

lemma shifted_tiling_still_tiling
  (d : ℕ) (a b original_mod : ℝ) (T : set (point d)) (T_is_tiling : is_tiling T) (i : fin d) (x : point d)
  (T_i_x_is_i_lattice : 0 ≤ original_mod ∧ original_mod < 1 ∧
    (∀ (t : vector ℝ d), t ∈ T_i T i x → (∃ (z : ℤ), t.nth i = ↑z + original_mod)) ∧
     ∀ (y : ℤ), ∃ (t : vector ℝ d) (H : t ∈ T_i T i x), 
      t.nth i = ↑y + original_mod ∧ ∀ (t' : vector ℝ d), t' ∈ T_i T i x → t'.nth i = ↑y + original_mod → t' = t)
  (original_mod_eq_a_mod_one : eq_mod_one original_mod a) :
  let T' : set (point d) := shift_tiling T i a b
  in shift_tiling T i a b = T' →
     (∃ (a : ℝ), 0 ≤ a ∧ a < 1 ∧ (∀ (t : vector ℝ d), t ∈ T_i T' i x → (∃ (z : ℤ), t.nth i = ↑z + a)) ∧
          ∀ (y : ℤ), ∃ (t : vector ℝ d) (H : t ∈ T_i T' i x), 
            t.nth i = ↑y + a ∧ ∀ (t' : vector ℝ d), t' ∈ T_i T' i x → t'.nth i = ↑y + a → t' = t) :=
begin
  intros T' T'_def,
  rcases T_i_x_is_i_lattice with ⟨zero_le_original_mod, original_mod_lt_one, all_corners_original_mod, every_int_has_corner⟩,
  rw eq_mod_one at original_mod_eq_a_mod_one,
  rcases original_mod_eq_a_mod_one with ⟨b_floor, a_floor, y, zero_le_y, y_lt_one, original_mod_eq_b_floor_add_y, a_eq_y_mod_one⟩,
  have original_mod_eq_y : original_mod = y :=  
    begin
      have b_floor_eq_zero : (b_floor : ℝ) = 0 :=
        begin
          replace original_mod_eq_b_floor_add_y : original_mod = y + ↑b_floor := by linarith,
          have floor_mono_fact := floor_mono_eq original_mod_eq_b_floor_add_y,

          replace zero_le_original_mod : ↑(0 : ℤ) ≤ original_mod := by assumption_mod_cast,
          replace original_mod_lt_one : original_mod < ↑(0 : ℤ) + 1 :=
            begin
              have coe_goal : original_mod < 0 + 1 := by linarith,
              assumption_mod_cast,
            end,
          have floor_original_mod_val := floor_val zero_le_original_mod original_mod_lt_one,
          rw floor_original_mod_val at floor_mono_fact,

          have floor_add_int_fact := int.floor_add_int y b_floor,
          rw floor_add_int_fact at floor_mono_fact,

          replace zero_le_y : ↑(0 : ℤ) ≤ y := by assumption_mod_cast,
          replace y_lt_one : y < ↑(0 : ℤ) + 1 :=
            begin
              have coe_goal : y < 0 + 1 := by linarith,
              assumption_mod_cast,
            end,
          have floor_y_val := floor_val zero_le_y y_lt_one,
          rw floor_y_val at floor_mono_fact,
          have coe_goal : b_floor = 0 := by linarith,
          assumption_mod_cast,
        end,
      rw b_floor_eq_zero at original_mod_eq_b_floor_add_y,
      linarith,
    end,
  have a_eq_a_floor_add_original_mod : a = ↑a_floor + original_mod :=
    begin
      rw original_mod_eq_y,
      exact a_eq_y_mod_one,
    end,
  clear original_mod_eq_b_floor_add_y,
  clear a_eq_y_mod_one,
  clear original_mod_eq_y,
  clear y_lt_one,
  clear zero_le_y,
  clear y,
  clear b_floor,
  let floor_a_add_b := int.floor(a + b),
  let new_mod := a + b - ↑floor_a_add_b,
  have zero_le_new_mod : 0 ≤ new_mod :=
    begin
      have new_mod_le_a_add_b := int.floor_le (a+b),
      dsimp only[new_mod],
      linarith,
    end,
  have new_mod_lt_one : new_mod < 1 :=
    begin
      have a_add_b_lt_floor_a_add_b_add_one := int.lt_floor_add_one (a + b),
      dsimp only[new_mod],
      linarith,
    end,
  use new_mod,
  split, exact zero_le_new_mod,
  split, exact new_mod_lt_one,
  split,
  { intros t t_in_T'_i_x,
    rw T_i at t_in_T'_i_x,
    change t ∈ T' ∧ cube t ∩ line_i i x ≠ ∅ at t_in_T'_i_x,
    cases t_in_T'_i_x with t_in_T' t_intersects_line_i_x,
    dsimp[T'] at t_in_T',
    rw shift_tiling at t_in_T',
    simp at t_in_T',
    cases t_in_T',
    { --This case is impossible because we know that every corner in T_i_x is equal to a mod 1 (all_corners_original_mod)
      exfalso,
      change t ∈ T ∧ ne_mod_one (vector.nth t i) a at t_in_T',
      cases t_in_T' with t_in_T t_ne_a_mod_one,
      have t_in_T_i_x : t ∈ T_i T i x :=
        begin
          rw T_i,
          change t ∈ T ∧ cube t ∩ line_i i x ≠ ∅,
          split, exact t_in_T,
          exact t_intersects_line_i_x,
        end,
      have t_has_original_mod := all_corners_original_mod t t_in_T_i_x,
      cases t_has_original_mod with t_floor t_has_original_mod,
      rw ne_mod_one at t_ne_a_mod_one,
      rw eq_mod_one at t_ne_a_mod_one,
      simp at t_ne_a_mod_one,
      exact t_ne_a_mod_one t_floor a_floor original_mod zero_le_original_mod original_mod_lt_one t_has_original_mod 
        a_eq_a_floor_add_original_mod,
    },
    rename t t',
    rename t_intersects_line_i_x t'_intersects_line_i_x,
    rename t_in_T' t'_in_T',
    change ∃ (t : point d), t ∈ T ∧ t' = add_vectors t (scaled_basis_vector b i) ∧ eq_mod_one (vector.nth t i) a 
      at t'_in_T',
    cases t'_in_T' with t t'_in_T',
    cases t'_in_T' with t_in_T t'_in_T',
    cases t'_in_T' with t'_def t_eq_a_mod_one,
    rw [t'_def, add_vectors, scaled_basis_vector],
    simp,
    have t_intersects_line_i_x : cube t ∩ line_i i x ≠ ∅ :=
      begin
        rw [cube, line_i, set.inter_def, set.ne_empty_iff_nonempty, set.nonempty_def] at t'_intersects_line_i_x,
        simp at t'_intersects_line_i_x,
        cases t'_intersects_line_i_x with intersection_point t'_intersects_line_i_x,
        cases t'_intersects_line_i_x with intersection_point_in_t' intersection_point_on_line_i_x,
        let intersection_point_at_t : point d := 
          vector.of_fn (λ j : fin d, if(j = i) then t.nth i else intersection_point.nth j),
        rw [cube, line_i, set.inter_def, set.ne_empty_iff_nonempty, set.nonempty_def],
        simp,
        use intersection_point_at_t,
        split,
        { rw in_cube at intersection_point_in_t',
          rw in_cube,
          simp,
          intro coord,
          by_cases coord_eq_i : coord = i, {rw coord_eq_i, simp,},
          rename coord_eq_i coord_ne_i,
          rw if_neg coord_ne_i,
          replace intersection_point_in_t' := intersection_point_in_t' coord,
          rw [add_vectors, scaled_basis_vector] at t'_def,
          rw t'_def at intersection_point_in_t',
          simp at intersection_point_in_t',
          have i_ne_coord : i ≠ coord := by {intro i_eq_coord, symmetry' at i_eq_coord, exact coord_ne_i i_eq_coord,},
          rw if_neg i_ne_coord at intersection_point_in_t',
          simp at intersection_point_in_t',
          exact intersection_point_in_t',
        },
        intro j,
        by_cases i_eq_j : i = j, {left, exact i_eq_j,},
        rename i_eq_j i_ne_j,
        right,
        replace intersection_point_on_line_i_x := intersection_point_on_line_i_x j,
        cases intersection_point_on_line_i_x, {exfalso, exact i_ne_j intersection_point_on_line_i_x,},
        dsimp[intersection_point_at_t],
        have j_ne_i : j ≠ i := by {intro j_eq_i, symmetry' at j_eq_i, exact i_ne_j j_eq_i},
        simp,
        rw if_neg j_ne_i,
        exact intersection_point_on_line_i_x,
      end,
    have t_in_T_i_x : t ∈ T_i T i x :=
      begin
        rw T_i,
        simp,
        split, exact t_in_T,
        exact t_intersects_line_i_x,
      end,
    have t_original_mod := all_corners_original_mod t t_in_T_i_x,
    cases t_original_mod with t_floor t_original_mod,
    use (t_floor - a_floor + int.floor(a+b)),
    dsimp only[new_mod],
    rw t_original_mod,
    have original_mod_eq_a_sub_a_floor : original_mod = a - ↑a_floor := by linarith,
    rw original_mod_eq_a_sub_a_floor,
    simp only [int.cast_add, int.cast_sub],
    linarith,
  },
  intro z,
  let preshift_z := z - int.floor(b + original_mod),
  have preshift_z_has_corner_in_T := every_int_has_corner preshift_z,
  rcases preshift_z_has_corner_in_T with
    ⟨preshift_z_corner, preshift_z_corner_in_T_i_x, preshift_z_corner_original_mod, preshift_z_corner_unique⟩,
  have preshift_z_corner_in_T_i_x_copy := preshift_z_corner_in_T_i_x,
  rw T_i at preshift_z_corner_in_T_i_x_copy,
  simp at preshift_z_corner_in_T_i_x_copy,
  cases preshift_z_corner_in_T_i_x_copy with preshift_z_corner_in_T preshift_z_corner_intersects_line_i_x,
  let z_corner := add_vectors preshift_z_corner (scaled_basis_vector b i),
  have z_corner_in_T' : z_corner ∈ T' :=
    begin
      dsimp[T'],
      rw shift_tiling,
      simp,
      right,
      change ∃ (t : point d), t ∈ T ∧ z_corner = add_vectors t (scaled_basis_vector b i) ∧ eq_mod_one (vector.nth t i) a,
      use preshift_z_corner,
      split, exact preshift_z_corner_in_T,
      split, refl,
      rw eq_mod_one,
      use preshift_z,
      use a_floor,
      use original_mod,
      exact ⟨zero_le_original_mod, original_mod_lt_one, preshift_z_corner_original_mod, a_eq_a_floor_add_original_mod⟩,
    end,
  have z_corner_in_T'_i_x : z_corner ∈ T_i T' i x :=
    begin
      rw T_i,
      change z_corner ∈ T' ∧ cube z_corner ∩ line_i i x ≠ ∅,
      split, exact z_corner_in_T',
      change cube preshift_z_corner ∩ line_i i x ≠ ∅ at preshift_z_corner_intersects_line_i_x,
      rw [cube, line_i, set.inter_def, set.ne_empty_iff_nonempty, set.nonempty_def] 
        at preshift_z_corner_intersects_line_i_x,
      simp at preshift_z_corner_intersects_line_i_x,
      rcases preshift_z_corner_intersects_line_i_x with 
        ⟨intersection_point, intersection_point_in_preshift_z_corner, intersection_point_on_line_i_x⟩,
      rw [cube, line_i, set.inter_def, set.ne_empty_iff_nonempty, set.nonempty_def],
      simp,
      let intersection_point_at_z_corner := 
        vector.of_fn (λ j : fin d, if(i = j) then z_corner.nth i else intersection_point.nth j),
      use intersection_point_at_z_corner,
      split,
      { rw in_cube at intersection_point_in_preshift_z_corner,
        rw in_cube,
        simp,
        intro coord,
        replace intersection_point_in_preshift_z_corner := intersection_point_in_preshift_z_corner coord,
        by_cases i_eq_coord : i = coord, {rw i_eq_coord, simp,},
        rename i_eq_coord i_ne_coord,
        dsimp[z_corner],
        rw [scaled_basis_vector, add_vectors, if_neg i_ne_coord],
        simp,
        rw [if_neg i_ne_coord, add_zero],
        exact intersection_point_in_preshift_z_corner,
      },
      intro j,
      by_cases i_eq_j : i = j, {left, exact i_eq_j,},
      rename i_eq_j i_ne_j,
      right,
      replace intersection_point_on_line_i_x := intersection_point_on_line_i_x j,
      cases intersection_point_on_line_i_x, {exfalso, exact i_ne_j intersection_point_on_line_i_x,},
      dsimp[intersection_point_at_z_corner],
      simp,
      rw if_neg i_ne_j,
      exact intersection_point_on_line_i_x,
    end,
  use z_corner,
  use z_corner_in_T'_i_x,
  split,
  { dsimp only[z_corner],
    rw[scaled_basis_vector, add_vectors],
    simp,
    rw preshift_z_corner_original_mod,
    have original_mod_eq_a_sub_a_floor : original_mod = a - ↑a_floor := by linarith,
    dsimp only[new_mod],
    rw original_mod_eq_a_sub_a_floor,
    simp only [int.cast_sub],
    have floor_b_add_original_mod_add_a_floor_eq_floor_a_add_b : ⌊b + original_mod⌋ + a_floor = floor_a_add_b :=
      begin
        rw original_mod_eq_a_sub_a_floor,
        have b_add_a_sub_a_floor_eq_self : b + (a - ↑a_floor) = b + a + (↑(-a_floor)) :=
          begin
            have almost_goal :  b + (a - ↑a_floor) = b + a + (-↑a_floor) := by linarith,
            assumption_mod_cast,
          end,
        rw b_add_a_sub_a_floor_eq_self,
        have floor_add_int_fact := int.floor_add_int (b + a) (-a_floor),
        rw floor_add_int_fact,
        simp,
        dsimp only[floor_a_add_b],
        apply floor_mono_eq,
        rw add_comm,
      end,
    have coe_floor_b_add_original_mod_add_a_floor_eq_floor_a_add_b : 
      ↑⌊b + original_mod⌋ + (a_floor : ℝ) = (floor_a_add_b : ℝ) := by assumption_mod_cast,
    linarith,
  },
  intros t' t'_in_T'_i_x t'_val,
  rw T_i at t'_in_T'_i_x,
  simp at t'_in_T'_i_x,
  cases t'_in_T'_i_x with t'_in_T' t'_intersects_line_i_x,
  dsimp[T'] at t'_in_T',
  rw shift_tiling at t'_in_T',
  simp at t'_in_T',
  rcases t'_in_T' with ⟨t'_in_T, t'_ne_a_mod_one⟩ | ⟨t, t_in_T, t'_def, t_eq_a_mod_one⟩,
  { exfalso,
    have t'_in_T_i_x : t' ∈ T_i T i x := ⟨t'_in_T, t'_intersects_line_i_x⟩,
    have t'_original_mod := all_corners_original_mod t' t'_in_T_i_x,
    cases t'_original_mod with t'_floor t'_original_mod,
    rw [ne_mod_one, eq_mod_one] at t'_ne_a_mod_one,
    simp at t'_ne_a_mod_one,
    replace t'_ne_a_mod_one := 
      t'_ne_a_mod_one t'_floor a_floor original_mod zero_le_original_mod original_mod_lt_one t'_original_mod,
    exact t'_ne_a_mod_one a_eq_a_floor_add_original_mod,
  },
  dsimp[z_corner],
  rw t'_def,
  have t_eq_preshift_z_corner : t = preshift_z_corner :=
    begin
      have t_in_T_i_x : t ∈ T_i T i x :=
        begin
          rw T_i,
          split, exact t_in_T,
          simp,
          change cube t' ∩ line_i i x ≠ ∅ at t'_intersects_line_i_x,
          rw [cube, line_i, set.inter_def, set.ne_empty_iff_nonempty, set.nonempty_def] at t'_intersects_line_i_x,
          simp at t'_intersects_line_i_x,
          rcases t'_intersects_line_i_x with 
            ⟨t'_intersection_point, t'_intersection_point_in_t', t'_intersection_point_on_line_i_x⟩,
          change cube t ∩ line_i i x ≠ ∅,
          let intersection_point := vector.of_fn (λ j : fin d, if(i = j) then t.nth i else t'_intersection_point.nth j),
          rw [cube, line_i, set.inter_def, set.ne_empty_iff_nonempty, set.nonempty_def],
          simp,
          use intersection_point,
          split,
          { rw in_cube at t'_intersection_point_in_t',
            rw in_cube,
            simp,
            intro coord,
            by_cases i_eq_coord : i = coord, {rw i_eq_coord, simp,},
            rename i_eq_coord i_ne_coord,
            rw if_neg i_ne_coord,
            replace t'_intersection_point_in_t' := t'_intersection_point_in_t' coord,
            rw [t'_def, scaled_basis_vector, add_vectors] at t'_intersection_point_in_t',
            simp at t'_intersection_point_in_t',
            rw [if_neg i_ne_coord, add_zero] at t'_intersection_point_in_t',
            exact t'_intersection_point_in_t',
          },
          intro j,
          by_cases i_eq_j : i = j, {left, exact i_eq_j,},
          rename i_eq_j i_ne_j,
          dsimp[intersection_point],
          simp,
          rw if_neg i_ne_j,
          exact t'_intersection_point_on_line_i_x j,
        end,
      have t_val : t.nth i = ↑preshift_z + original_mod :=
        begin
          have t_val : t.nth i = z + a - ↑(int.floor(a + b)) :=
            begin
              rw [t'_def, scaled_basis_vector, add_vectors] at t'_val,
              simp at t'_val,
              dsimp only[new_mod, floor_a_add_b] at t'_val,
              linarith,
            end,
          have original_mod_def : original_mod = a - ↑a_floor := by linarith,
          rw [t_val, original_mod_def],
          dsimp[preshift_z],
          simp,
          have floor_a_add_b_eq_floor_b_add_original_mod_add_a_floor : int.floor(a+b) = int.floor(b + original_mod) + a_floor :=
            begin
              rw ← int.floor_add_int (b + original_mod) a_floor,
              apply floor_mono_eq,
              linarith,
            end,
          have coe_floor_a_add_b_eq_floor_b_add_original_mod_add_a_floor : 
            ↑(int.floor(a+b)) = ↑(int.floor(b + original_mod)) + (a_floor : ℝ) := by assumption_mod_cast,
          linarith,
        end,
      exact preshift_z_corner_unique t t_in_T_i_x t_val,
    end,
  rw t_eq_preshift_z_corner,
end

lemma shifting_preserves_faceshare_free (d : ℕ) (a b : ℝ) (T : set (point d)) (T_is_tiling : is_tiling T)
  (i : fin d) (T_is_i_lattice_everywhere : ∀ (x : point d), is_i_lattice d (T_i T i x) i) :
  let T' : set (point d) := shift_tiling T i a b
  in shift_tiling T i a b = T' →
     tiling_faceshare_free T →
     (∀ (t : point d), t ∈ T → ne_mod_one (vector.nth t i) (a + b)) →
     tiling_faceshare_free T' :=
begin
  intros T' T'_def T_faceshare_free no_corner_eq_a_add_b_mod_one,
  contrapose T_faceshare_free,
  rename T_faceshare_free T'_not_faceshare_free,
  rw tiling_faceshare_free at T'_not_faceshare_free,
  simp at T'_not_faceshare_free,
  rcases T'_not_faceshare_free with ⟨t1, t1_in_T', t2, t2_in_T', t1_t2_faceshare⟩,
  have t1_t2_faceshare_copy := t1_t2_faceshare,
  rw is_facesharing at t1_t2_faceshare_copy,
  rcases t1_t2_faceshare_copy with ⟨coord, t1_t2_diff_by_one_at_coord, t1_t2_eq_outside_coord⟩,
  have t1_eq_t2_mod_one : eq_mod_one (t1.nth i) (t2.nth i) :=
    begin
      by_cases coord_eq_i : coord = i,
      { rw eq_mod_one,
        use [int.floor(t1.nth coord), int.floor(t2.nth coord), t1.nth coord - ↑(int.floor(t1.nth coord))],
        have floor_le_fact := int.floor_le (t1.nth coord),
        have lt_floor_add_one_fact := int.lt_floor_add_one (t1.nth coord),
        split, linarith,
        split, linarith,
        rw coord_eq_i,
        split, linarith,
        rw coord_eq_i at t1_t2_diff_by_one_at_coord,
        cases t1_t2_diff_by_one_at_coord,
        { replace t1_t2_diff_by_one_at_coord : t1.nth i = t2.nth i + 1 := by linarith,
          have floor_t1_t2_diff_by_one_at_coord := floor_mono_eq t1_t2_diff_by_one_at_coord,
          replace floor_t1_t2_diff_by_one_at_coord : ⌊vector.nth t1 i⌋ = ⌊vector.nth t2 i + ↑(1 : ℤ)⌋ :=
            by assumption_mod_cast,
          rw int.floor_add_int at floor_t1_t2_diff_by_one_at_coord,
          replace floor_t1_t2_diff_by_one_at_coord : ↑⌊vector.nth t1 i⌋ = ↑⌊vector.nth t2 i⌋ + (1 : ℝ) :=
            by assumption_mod_cast,
          linarith,
        },
        replace t1_t2_diff_by_one_at_coord : t2.nth i = t1.nth i + 1 := by linarith,
        have floor_t1_t2_diff_by_one_at_coord := floor_mono_eq t1_t2_diff_by_one_at_coord,
        replace floor_t1_t2_diff_by_one_at_coord : ⌊vector.nth t2 i⌋ = ⌊vector.nth t1 i + ↑(1 : ℤ)⌋ :=
          by assumption_mod_cast,
        rw int.floor_add_int at floor_t1_t2_diff_by_one_at_coord,
        replace floor_t1_t2_diff_by_one_at_coord : ↑⌊vector.nth t2 i⌋ = ↑⌊vector.nth t1 i⌋ + (1 : ℝ) :=
          by assumption_mod_cast,
        linarith,
      },
      rename coord_eq_i coord_ne_i,
      replace t1_t2_eq_outside_coord := t1_t2_eq_outside_coord i,
      cases t1_t2_eq_outside_coord, {exfalso, exact coord_ne_i t1_t2_eq_outside_coord,},
      rw t1_t2_eq_outside_coord,
      exact eq_mod_one_reflexive (t2.nth i),
    end,
  by_cases t1_ne_a_add_b_mod_one : ne_mod_one (t1.nth i) (a+b),
  { --Neither t1 nor t2 have been shifted
    rw ne_mod_one at t1_ne_a_add_b_mod_one,
    have t1_in_T : t1 ∈ T :=
      begin
        dsimp[T'] at t1_in_T',
        rw shift_tiling at t1_in_T',
        simp at t1_in_T',
        rcases t1_in_T' with ⟨t1_in_T, _⟩ | ⟨preshift_t1, preshift_t1_in_T, preshift_t1_val, preshift_t1_eq_a_mod_one⟩, exact t1_in_T,
        exfalso, --This is impossible because t1_ne_a_add_b_mod_one
        have t1_val : t1.nth i = preshift_t1.nth i + b := by {rw [preshift_t1_val, scaled_basis_vector, add_vectors], simp,},
        have t1_eq_a_add_b_mod_one : eq_mod_one (preshift_t1.nth i + b) (a + b) := add_mod_eq_add_mod_right preshift_t1_eq_a_mod_one,
        rw ← t1_val at t1_eq_a_add_b_mod_one,
        exact t1_ne_a_add_b_mod_one t1_eq_a_add_b_mod_one,
      end,
    have t2_ne_a_add_b_mod_one : ¬eq_mod_one (t2.nth i) (a + b) :=
      begin
        intro t2_eq_a_add_b_mod_one,
        have t1_eq_a_add_b_mod_one := eq_mod_one_transitive t1_eq_t2_mod_one t2_eq_a_add_b_mod_one,
        exact t1_ne_a_add_b_mod_one t1_eq_a_add_b_mod_one,
      end,
    have t2_in_T : t2 ∈ T :=
      begin
        dsimp[T'] at t2_in_T',
        rw shift_tiling at t2_in_T',
        simp at t2_in_T',
        rcases t2_in_T' with ⟨t2_in_T, _⟩ | ⟨preshift_t2, preshift_t2_in_T, preshift_t2_val, preshift_t2_eq_a_mod_one⟩, exact t2_in_T,
        exfalso, --This is impossible because t2_ne_a_add_b_mod_one
        have t2_val : t2.nth i = preshift_t2.nth i + b := by {rw [preshift_t2_val, scaled_basis_vector, add_vectors], simp,},
        have t2_eq_a_add_b_mod_one : eq_mod_one (preshift_t2.nth i + b) (a + b) := add_mod_eq_add_mod_right preshift_t2_eq_a_mod_one,
        rw ← t2_val at t2_eq_a_add_b_mod_one,
        exact t2_ne_a_add_b_mod_one t2_eq_a_add_b_mod_one,
      end,
    rw tiling_faceshare_free,
    simp,
    use t1,
    split, exact t1_in_T,
    use t2,
    split, exact t2_in_T,
    exact t1_t2_faceshare,
  },
  --t1 and t2 must have been shifted (because of no_corner_eq_a_add_b_mod_one)
  rename t1_ne_a_add_b_mod_one t1_eq_a_add_b_mod_one,
  rw ne_mod_one at t1_eq_a_add_b_mod_one,
  simp at t1_eq_a_add_b_mod_one,
  have t2_eq_a_add_b_mod_one : eq_mod_one (t2.nth i) (a + b) :=
    begin
      replace t1_eq_t2_mod_one := eq_mod_one_symmetric t1_eq_t2_mod_one,
      exact eq_mod_one_transitive t1_eq_t2_mod_one t1_eq_a_add_b_mod_one,
    end,

  dsimp[T'] at t1_in_T',
  rw shift_tiling at t1_in_T',
  simp at t1_in_T',
  rcases t1_in_T' with ⟨t1_in_T, _⟩ | ⟨preshift_t1, preshift_t1_in_T, t1_val, preshift_t1_eq_a_mod_one⟩,
  { exfalso,
    replace no_corner_eq_a_add_b_mod_one := no_corner_eq_a_add_b_mod_one t1 t1_in_T,
    rw ne_mod_one at no_corner_eq_a_add_b_mod_one,
    exact no_corner_eq_a_add_b_mod_one t1_eq_a_add_b_mod_one,
  },
  have preshift_t1_val : ∀ j : fin d, preshift_t1.nth j = (add_vectors t1 (scaled_basis_vector (-b) i)).nth j :=
    begin
      intro j,
      by_cases i_eq_j : i = j,
      { rw [scaled_basis_vector, add_vectors, i_eq_j] at t1_val,
        simp at t1_val,
        rw [scaled_basis_vector, add_vectors, t1_val, i_eq_j],
        simp,
      },
      rename i_eq_j i_ne_j,
      rw [scaled_basis_vector, add_vectors] at t1_val,
      simp at t1_val,
      rw [scaled_basis_vector, add_vectors, t1_val],
      simp,
      rw if_neg i_ne_j,
      simp,
      intro i_eq_j,
      exfalso,
      exact i_ne_j i_eq_j,
    end,

  dsimp[T'] at t2_in_T',
  rw shift_tiling at t2_in_T',
  simp at t2_in_T',
  rcases t2_in_T' with ⟨t2_in_T, _⟩ | ⟨preshift_t2, preshift_t2_in_T, t2_val, preshift_t2_eq_a_mod_one⟩,
  { exfalso,
    replace no_corner_eq_a_add_b_mod_one := no_corner_eq_a_add_b_mod_one t2 t2_in_T,
    rw ne_mod_one at no_corner_eq_a_add_b_mod_one,
    exact no_corner_eq_a_add_b_mod_one t2_eq_a_add_b_mod_one,
  },
  have preshift_t2_val : ∀ j : fin d, preshift_t2.nth j = (add_vectors t2 (scaled_basis_vector (-b) i)).nth j :=
    begin
      intro j,
      by_cases i_eq_j : i = j,
      { rw [scaled_basis_vector, add_vectors, i_eq_j] at t2_val,
        simp at t2_val,
        rw [scaled_basis_vector, add_vectors, t2_val, i_eq_j],
        simp,
      },
      rename i_eq_j i_ne_j,
      rw [scaled_basis_vector, add_vectors] at t2_val,
      simp at t2_val,
      rw [scaled_basis_vector, add_vectors, t2_val],
      simp,
      rw if_neg i_ne_j,
      simp,
      intro i_eq_j,
      exfalso,
      exact i_ne_j i_eq_j,
    end,

  rw tiling_faceshare_free,
  simp,
  use preshift_t1,
  split, exact preshift_t1_in_T,
  use preshift_t2,
  split, exact preshift_t2_in_T,
  rw is_facesharing,
  use coord,
  split,
  { rw [preshift_t1_val, preshift_t2_val, scaled_basis_vector, add_vectors, add_vectors],
    simp,
    exact t1_t2_diff_by_one_at_coord,
  },
  intro y,
  rw [preshift_t1_val, preshift_t2_val, scaled_basis_vector, add_vectors, add_vectors],
  simp,
  replace t1_t2_eq_outside_coord := t1_t2_eq_outside_coord y,
  exact t1_t2_eq_outside_coord,
end

theorem replacement_lemma :
  ∀ d : ℕ, ∀ T : set (point d), ∀ T_is_tiling : is_tiling T, ∀ a : ℝ, ∀ b : ℝ, ∀ i : fin d,
  is_tiling (shift_tiling T i a b) ∧ 
  (tiling_faceshare_free T → (∀ t : point d, t ∈ T → ne_mod_one (t.nth i) (a + b)) → 
  tiling_faceshare_free (shift_tiling T i a b)) :=
  begin
    repeat{intro},
    have T_is_i_lattice_everywhere := tiling_lattice_structure_right_implication d T i T_is_tiling,
    let T' := shift_tiling T i a b,
    have T'_def : shift_tiling T i a b = T' := by refl,
    rw T'_def,
    split,
    { rw tiling_lattice_structure d T' i,
      intro x,
      replace T_is_i_lattice_everywhere := T_is_i_lattice_everywhere x,
      rw is_i_lattice,
      rw is_i_lattice at T_is_i_lattice_everywhere,
      cases T_is_i_lattice_everywhere with original_mod T_i_x_is_i_lattice,
      by_cases original_mod_eq_a_mod_one : eq_mod_one original_mod a,
      { exact shifted_tiling_still_tiling d a b original_mod T T_is_tiling i x T_i_x_is_i_lattice 
          original_mod_eq_a_mod_one T'_def, },
      rename original_mod_eq_a_mod_one original_mod_ne_a_mod_one,
      use original_mod,
      have T_i_x_eq_T'_i_x : T_i T i x = T_i T' i x :=
        begin
          rcases T_i_x_is_i_lattice with 
            ⟨zero_le_original_mod, original_mod_lt_one, all_original_corners_original_mod, all_ints_have_original_corner⟩,
          rw [T_i, T_i],
          ext t,
          simp,
          intro t_intersects_line_i_x,
          dsimp[T'],
          rw shift_tiling,
          simp,
          split,
          { intro t_in_T,
            left, split, exact t_in_T,
            have t_in_T_i_x : t ∈ T_i T i x :=
              begin
                rw T_i,
                simp,
                split, exact t_in_T,
                exact t_intersects_line_i_x,
              end,
            replace all_original_corners_original_mod := all_original_corners_original_mod t t_in_T_i_x,
            cases all_original_corners_original_mod with floor_t t_original_mod,
            have t_has_original_mod : eq_mod_one original_mod (t.nth i) :=
              begin
                rw eq_mod_one,
                use 0,
                use floor_t,
                use original_mod,
                split, exact zero_le_original_mod,
                split, exact original_mod_lt_one,
                split,
                {
                have original_mod_eq_zero_add_original_mod : original_mod = 0 + original_mod := by linarith,
                assumption_mod_cast,
                },
                exact t_original_mod,
              end,
            rw ne_mod_one,
            intro t_eq_a_mod_one,
            have original_mod_eq_a_mod_one := eq_mod_one_transitive t_has_original_mod t_eq_a_mod_one,
            exact original_mod_ne_a_mod_one original_mod_eq_a_mod_one,
          },
          contrapose,
          intro t_not_in_T,
          rw not_or_distrib,
          split,
          { rw not_and_distrib,
            left,
            exact t_not_in_T,
          },
          simp,
          intros unshifted_t unshifted_t_in_T t_def,
          have unshifted_t_intersects_line_i_x : ¬cube unshifted_t ∩ line_i i x = ∅ :=
            begin
              --unshifted_t has same non-i coordinates as t, so this should follows from t_intersects_line_i_x
              change cube t ∩ line_i i x ≠ ∅ at t_intersects_line_i_x,
              rw [cube, line_i, set.inter_def, set.ne_empty_iff_nonempty, set.nonempty_def] at t_intersects_line_i_x,
              cases t_intersects_line_i_x with t_intersection_point t_intersects_line_i_x,
              simp at t_intersects_line_i_x,
              cases t_intersects_line_i_x with t_intersection_point_in_t t_intersection_point_on_line_i_x,

              let unshifted_t_intersection_point : point d := 
                vector.of_fn (λ j : fin d, if(i = j) then unshifted_t.nth i else t_intersection_point.nth j),
              change cube unshifted_t ∩ line_i i x ≠ ∅,
              rw [cube, line_i, set.inter_def, set.ne_empty_iff_nonempty, set.nonempty_def],
              use unshifted_t_intersection_point,
              simp,
              split,
              { rw in_cube,
                simp,
                intro coord,
                by_cases i_eq_coord : i = coord, {rw i_eq_coord, simp,},
                rename i_eq_coord i_ne_coord,
                rw if_neg i_ne_coord,
                rw in_cube at t_intersection_point_in_t,
                replace t_intersection_point_in_t := t_intersection_point_in_t coord,
                have t_eq_unshifted_t_at_coord : t.nth coord = unshifted_t.nth coord :=
                  begin
                    rw [t_def, scaled_basis_vector, add_vectors],
                    simp,
                    intro i_eq_coord,
                    exfalso,
                    exact i_ne_coord i_eq_coord,
                  end,
                rw ← t_eq_unshifted_t_at_coord,
                exact t_intersection_point_in_t,
              },
              intro j,
              by_cases i_eq_j : i = j, {left, exact i_eq_j,},
              rename i_eq_j i_ne_j,
              right,
              rw if_neg i_ne_j,
              replace t_intersection_point_on_line_i_x := t_intersection_point_on_line_i_x j,
              cases t_intersection_point_on_line_i_x, {exfalso, exact i_ne_j t_intersection_point_on_line_i_x,},
              exact t_intersection_point_on_line_i_x,
            end,
          have unshifted_t_in_T_i_x : unshifted_t ∈ T_i T i x :=
            begin
              rw T_i,
              simp,
              split, exact unshifted_t_in_T,
              exact unshifted_t_intersects_line_i_x,
            end,
          replace all_original_corners_original_mod := 
            all_original_corners_original_mod unshifted_t unshifted_t_in_T_i_x,
          cases all_original_corners_original_mod with floor_unshifted_t unshifted_t_original_mod,
          have unshifted_t_has_original_mod : eq_mod_one original_mod (unshifted_t.nth i) :=
            begin
              rw eq_mod_one,
              use 0,
              use floor_unshifted_t,
              use original_mod,
              split, exact zero_le_original_mod,
              split, exact original_mod_lt_one,
              split,
              { have original_mod_eq_zero_add_original_mod : original_mod = 0 + original_mod := by linarith,
                assumption_mod_cast,
              },
              exact unshifted_t_original_mod,
            end,
          intro unshifted_t_has_mod_a,
          have original_mod_eq_a_mod_one := eq_mod_one_transitive unshifted_t_has_original_mod unshifted_t_has_mod_a,
          exact original_mod_ne_a_mod_one original_mod_eq_a_mod_one,
        end,
      rw ← T_i_x_eq_T'_i_x,
      exact T_i_x_is_i_lattice, 
    },
    exact shifting_preserves_faceshare_free d a b T T_is_tiling i T_is_i_lattice_everywhere T'_def,
  end