import s_discrete

open_locale classical

noncomputable def s_finset {s : ℕ} (s_ne_zero : s ≠ 0) : finset ℝ :=
begin
  let numerators : finset ℕ := finset.range s,
  let div_by_s_fn : ℕ ↪ ℝ :=
    begin
      let div_by_s_fn : ℕ → ℝ := λ numerator, ↑numerator / ↑s,
      have div_by_s_fn_injective : function.injective div_by_s_fn :=
        begin
          intros num1 num2 num1_div_by_s_eq_num2_div_by_s,
          dsimp[div_by_s_fn] at num1_div_by_s_eq_num2_div_by_s,
          have s_cast_ne_zero : (s : ℝ) ≠ 0 := by exact_mod_cast s_ne_zero,
          have mul_div_cancel_fact1 := mul_div_cancel' (num1 : ℝ) s_cast_ne_zero,
          have mul_div_cancel_fact2 := mul_div_cancel' (num2 : ℝ) s_cast_ne_zero,
          replace num1_div_by_s_eq_num2_div_by_s : (s : ℝ) * ((num1 : ℝ) / (s : ℝ)) = (s : ℝ) * ((num2 : ℝ) / (s : ℝ)) :=
            by rw num1_div_by_s_eq_num2_div_by_s,
          rw [mul_div_cancel_fact1, mul_div_cancel_fact2] at num1_div_by_s_eq_num2_div_by_s,
          exact_mod_cast num1_div_by_s_eq_num2_div_by_s,
        end,
      exact {to_fun := div_by_s_fn, inj' := div_by_s_fn_injective},
    end,
  exact finset.map div_by_s_fn numerators,
end

lemma s_finset_card {s : ℕ} (s_ne_zero : s ≠ 0) : (s_finset s_ne_zero).card = s :=
  by {rw s_finset, simp only [finset.card_range, finset.card_map],}

lemma s_finset_range {s : ℕ} {s_ne_zero : s ≠ 0} {a : ℝ} (a_in_s_finset : a ∈ s_finset s_ne_zero) : 0 ≤ a ∧ a < 1 :=
begin
  rw s_finset at a_in_s_finset,
  simp only [exists_prop, finset.mem_map, function.embedding.coe_fn_mk, finset.mem_range] at a_in_s_finset,
  rcases a_in_s_finset with ⟨a_num, a_num_lt_s, a_num_div_s_eq_a⟩,
  have zero_le_s : 0 ≤ s := nat.zero_le s,
  have cast_zero_le_s : (0 : ℝ) ≤ ↑s := by {exact_mod_cast zero_le_s},
  have cast_zero_lt_s : (0 : ℝ) < ↑s :=
    begin
      cases eq_or_lt_of_le cast_zero_le_s with zero_eq_s zero_lt_s,
      { exfalso,
        symmetry' at zero_eq_s,
        have s_eq_zero : s = 0 := by {exact_mod_cast zero_eq_s},
        exact s_ne_zero s_eq_zero,
      },
      exact zero_lt_s,
    end,
  have zero_le_a : 0 ≤ a :=
    begin
      have zero_le_a_num : 0 ≤ a_num := nat.zero_le a_num,
      have cast_zero_le_a_num : (0 : ℝ) ≤ ↑a_num := by {exact_mod_cast zero_le_a_num},
      rw ← a_num_div_s_eq_a,
      exact div_nonneg cast_zero_le_a_num cast_zero_le_s,
    end,
  have a_lt_one : a < 1 :=
    by {rw [← a_num_div_s_eq_a, div_lt_one cast_zero_lt_s], exact_mod_cast a_num_lt_s},
  exact ⟨zero_le_a, a_lt_one⟩,
end

lemma s_finset_distinct_mod_one {s : ℕ} {s_ne_zero : s ≠ 0} {a : ℝ} {b : ℝ} (a_ne_b : a ≠ b) (a_in_s_finset : a ∈ s_finset s_ne_zero)
  (b_in_s_finset : b ∈ s_finset s_ne_zero) : ne_mod_one a b :=
begin
  rcases s_finset_range a_in_s_finset with ⟨zero_le_a, a_lt_one⟩,
  rcases s_finset_range b_in_s_finset with ⟨zero_le_b, b_lt_one⟩,
  rintro ⟨a_floor, b_floor, y, zero_le_y, y_lt_one, a_eq_a_floor_add_y, b_eq_b_floor_add_y⟩,
  rcases eq_or_lt_or_gt a_floor b_floor with a_floor_eq_b_floor | a_floor_lt_b_floor | a_floor_gt_b_floor,
  { rw [a_floor_eq_b_floor, ← b_eq_b_floor_add_y] at a_eq_a_floor_add_y,
    exact a_ne_b a_eq_a_floor_add_y,
  },
  { have a_floor_add_one_le_b_floor := int.add_one_le_of_lt a_floor_lt_b_floor,
    have cast_a_floor_add_one_le_b_floor : (↑a_floor : ℝ) + 1 ≤ ↑b_floor := by {exact_mod_cast a_floor_add_one_le_b_floor},
    rw a_eq_a_floor_add_y at zero_le_a a_lt_one,
    rw b_eq_b_floor_add_y at zero_le_b b_lt_one,
    clear_except cast_a_floor_add_one_le_b_floor zero_le_a a_lt_one zero_le_b b_lt_one,
    linarith,
  },
  rw gt at a_floor_gt_b_floor,
  have b_floor_add_one_le_a_floor := int.add_one_le_of_lt a_floor_gt_b_floor,
  have cast_a_floor_add_one_le_b_floor : (↑b_floor : ℝ) + 1 ≤ ↑a_floor := by {exact_mod_cast b_floor_add_one_le_a_floor},
  rw a_eq_a_floor_add_y at zero_le_a a_lt_one,
  rw b_eq_b_floor_add_y at zero_le_b b_lt_one,
  clear_except cast_a_floor_add_one_le_b_floor zero_le_a a_lt_one zero_le_b b_lt_one,
  linarith,
end

lemma inductive_replacement_lemma_helper2 {d : ℕ} {s : ℕ} (s_ne_zero : s ≠ 0) (i : fin d) (T : set (point d)) 
  (T_is_tiling : is_tiling T) (T_faceshare_free : tiling_faceshare_free T) (T_is_periodic : is_periodic T_is_tiling)
  (coords_before_i_handled : ∀ p : point d, p ∈ T → ∀ j : fin d, j.val < i.val → 
    ∃ s_val ∈ s_finset s_ne_zero, eq_mod_one (vector.nth p j) s_val) : 
  ∀ coords_left : ℕ, ∀ coords : finset ℝ, ∀ goal_finset : finset ℝ, goal_finset ⊆ s_finset s_ne_zero →
  (∀ coord ∈ coords, ∀ s_val ∈ s_finset s_ne_zero, ne_mod_one coord s_val) →
  (∀ p ∈ T, ∀ goal_val ∈ goal_finset, ne_mod_one (vector.nth p i) goal_val) →
  coords_left = coords.card → coords.card ≤ goal_finset.card →
  ∃ T_shifted : set (point d), ∃ T_shifted_is_tiling : is_tiling T_shifted, tiling_faceshare_free T_shifted ∧ is_periodic T_shifted_is_tiling ∧
  (∀ p : point d, p ∈ T_shifted → ∀ j : fin d, j.val < i.val → ∃ s_val ∈ s_finset s_ne_zero, eq_mod_one (vector.nth p j) s_val) ∧
  (∀ p : point d, p ∈ T_shifted → (∀ coord ∈ coords, ne_mod_one (vector.nth p i) coord) 
    ∧ ((∃ goal_val ∈ goal_finset, eq_mod_one (vector.nth p i) goal_val) ∨ p ∈ T)) ∧
  (∀ p : point d, p ∈ T_shifted → ∀ j : fin d, j.val > i.val → ∃ p' ∈ T, vector.nth p j = vector.nth p' j) :=
begin
  intro coords_left,
  induction coords_left with coords_left_pred ih,
  { intros coords goal_finset goal_finset_subset_s_finset coords_inter_s_finset_empty T_disjoint_goal_finset coords_empty 
      coords_card_le_goal_finset_card,
    use [T, T_is_tiling, T_faceshare_free, T_is_periodic],
    split, exact coords_before_i_handled, --T_shifted_property_before_i
    split,
    { intros p p_in_T,--Prove T_shifted_property_at_i
      split,
      { intros coord coord_in_coords,
        exfalso, --Derive contradiction between coord_in_coords and coords_empty
        symmetry' at coords_empty,
        rw finset.card_eq_zero at coords_empty,
        rw coords_empty at coord_in_coords,
        exact finset.not_mem_empty coord coord_in_coords,
      },
      right, exact p_in_T,
    },
    intros p p_in_T j j_val_gt_i_val, --Prove T_shifted_property_after_i
    use [p, p_in_T],
  },
  intros coords goal_finset goal_finset_subset_s_finset coords_disjoint_s_fisnet T_disjoint_goal_finset coords_left_def 
    coords_card_le_goal_finset_card,
  let coords_list : list ℝ := finset.sort has_le.le coords,
  let goal_list : list ℝ := finset.sort has_le.le goal_finset,
  have coords_list_def : coords_list = finset.sort has_le.le coords := by refl,
  have goal_list_def : goal_list = finset.sort has_le.le goal_finset := by refl,
  cases finset.sort has_le.le coords with last_coord rest_coords,
  { exfalso, --coords_left_def says coords.card > 0, so it is impossible that coords_list = list.nil
    have coords_list_length_eq_coords_card : coords_list.length = coords.card := finset.length_sort real.has_le.le,
    rw [← coords_list_length_eq_coords_card, coords_list_def, list.length] at coords_left_def,
    exact nat.succ_ne_zero coords_left_pred coords_left_def,
  },
  cases finset.sort has_le.le goal_finset with last_goal rest_goal_list,
  { exfalso, --coords.card ≤ goal_finset.card and coords.card > 0, so it is impossible that goal_list = list.nil
    have goal_finset_card_eq_goal_list_length : goal_list.length = goal_finset.card := finset.length_sort real.has_le.le,
    rw [← goal_finset_card_eq_goal_list_length, goal_list_def, list.length, ← coords_left_def] at coords_card_le_goal_finset_card,
    exact nat.not_succ_le_zero coords_left_pred coords_card_le_goal_finset_card,
  },
  have last_goal_in_goal_finset : last_goal ∈ goal_finset :=
    begin
      rw ← finset.mem_sort real.has_le.le,
      change last_goal ∈ goal_list,
      rw goal_list_def,
      simp only [list.mem_cons_iff, true_or, eq_self_iff_true],
    end,
  have last_goal_in_s_finset := finset.mem_of_subset goal_finset_subset_s_finset last_goal_in_goal_finset,
  let rest_coords_finset : finset ℝ := rest_coords.to_finset,
  let rest_goal_finset : finset ℝ := rest_goal_list.to_finset,
  have rest_goal_finset_subset_goal_finset : rest_goal_finset ⊆ goal_finset := 
    begin
      dsimp[rest_goal_finset],
      rw finset.subset_iff,
      intros rest_goal_val rest_goal_val_in_rest_goal_finset,
      rw list.mem_to_finset at rest_goal_val_in_rest_goal_finset,
      rw ← finset.mem_sort real.has_le.le,
      change rest_goal_val ∈ goal_list,
      rw [goal_list_def, list.mem_cons_iff],
      right,
      exact rest_goal_val_in_rest_goal_finset,
    end,
  have rest_goal_finset_subset_s_finset : rest_goal_finset ⊆ s_finset s_ne_zero :=
    finset.subset.trans rest_goal_finset_subset_goal_finset goal_finset_subset_s_finset,
  have rest_coords_finset_subset_coords : rest_coords_finset ⊆ coords :=
    begin
      dsimp[rest_coords_finset],
      rw finset.subset_iff,
      intros coord coord_in_rest_coords,
      rw list.mem_to_finset at coord_in_rest_coords,
      rw ← finset.mem_sort real.has_le.le,
      change coord ∈ coords_list,
      rw [coords_list_def, list.mem_cons_iff],
      right,
      exact coord_in_rest_coords,
    end,
  have rest_coords_finset_disjoint_s_finset : 
    ∀ (coord : ℝ), coord ∈ rest_coords_finset → ∀ (s_val : ℝ), s_val ∈ s_finset s_ne_zero → ne_mod_one coord s_val := 
    begin
      intros coord coord_in_rest_coords_finset s_val s_val_in_s_finset,
      have coord_in_coords := finset.mem_of_subset rest_coords_finset_subset_coords coord_in_rest_coords_finset,
      exact coords_disjoint_s_fisnet coord coord_in_coords s_val s_val_in_s_finset,
    end,
  have rest_coords_nodup : rest_coords.nodup :=
    begin
      rw list.nodup,
      have coords_list_nodup : coords_list.nodup := finset.sort_nodup real.has_le.le coords,
      rw [list.nodup, coords_list_def, list.pairwise_cons] at coords_list_nodup,
      exact coords_list_nodup.2,
    end,
  have rest_coords_card : coords_left_pred = rest_coords_finset.card := 
    begin
      dsimp[rest_coords_finset],
      have coords_list_length : coords_list.length = rest_coords.length + 1 :=
        by {rw coords_list_def, exact list.length_cons last_coord rest_coords},
      have coords_list_length_eq_coords_card : coords_list.length = coords.card :=
        by {dsimp[coords_list], apply finset.length_sort},
      rw ← coords_left_def at coords_list_length_eq_coords_card,
      rw list.to_finset_card_of_nodup rest_coords_nodup,
      clear_except coords_list_length coords_list_length_eq_coords_card,
      omega,
    end,
  have T_disjoint_rest_goal_finset : 
    ∀ (p : vector ℝ d), p ∈ T → ∀ (goal_val : ℝ), goal_val ∈ rest_goal_finset → ne_mod_one (p.nth i) goal_val :=
    begin
      intros p p_in_T goal_val goal_val_in_rest_goal_finset,
      have goal_val_in_goal_finset := finset.mem_of_subset rest_goal_finset_subset_goal_finset goal_val_in_rest_goal_finset,
      exact T_disjoint_goal_finset p p_in_T goal_val goal_val_in_goal_finset,
    end,
  have rest_coords_card_le_rest_goal_finset_card : rest_coords_finset.card ≤ rest_goal_finset.card := 
    begin
      rw ← rest_coords_card,
      rw [← coords_left_def, nat.succ_eq_add_one] at coords_card_le_goal_finset_card,
      have coords_left_pred_le_goal_finset_card_sub_one : coords_left_pred ≤ goal_finset.card - 1 :=
        by {clear_except coords_card_le_goal_finset_card, omega},
      have goal_finset_card : goal_finset.card = rest_goal_finset.card + 1 :=
        begin
          rw ← finset.length_sort real.has_le.le,
          change goal_list.length = rest_goal_finset.card + 1,
          dsimp[rest_goal_finset],
          have rest_goal_list_nodup : rest_goal_list.nodup := 
            begin
              have goal_list_nodup : goal_list.nodup := finset.sort_nodup has_le.le goal_finset,
              rw [goal_list_def, list.nodup, list.pairwise_cons, ← list.nodup] at goal_list_nodup,
              exact goal_list_nodup.2,
            end,
          rw [goal_list_def, list.length_cons, list.to_finset_card_of_nodup rest_goal_list_nodup],
        end,
      rw goal_finset_card at coords_left_pred_le_goal_finset_card_sub_one,
      simp only [nat.add_succ_sub_one, add_zero] at coords_left_pred_le_goal_finset_card_sub_one,
      exact coords_left_pred_le_goal_finset_card_sub_one,
    end,
  rcases ih rest_coords_finset rest_goal_finset rest_goal_finset_subset_s_finset rest_coords_finset_disjoint_s_finset
    T_disjoint_rest_goal_finset rest_coords_card rest_coords_card_le_rest_goal_finset_card with
    ⟨T_shifted_prev, T_shifted_prev_is_tiling, T_shifted_prev_faceshare_free, T_shifted_prev_is_periodic, T_shifted_prev_property_before_i,
      T_shifted_prev_property_at_i, T_shifted_prev_property_after_i⟩,
  let T_shifted := shift_tiling T_shifted_prev i last_coord (last_goal - last_coord),
  rcases replacement_lemma d T_shifted_prev T_shifted_prev_is_tiling last_coord (last_goal - last_coord) i with
    ⟨T_shifted_is_tiling, T_shifted_prev_faceshare_free_implication⟩,
  use [T_shifted, T_shifted_is_tiling],
  have last_goal_not_in_T_shifted_prev : 
    (∀ (t : point d), t ∈ T_shifted_prev → ne_mod_one (vector.nth t i) (last_coord + (last_goal - last_coord))) :=
    begin
      intros t t_in_T_shifted_prev,
      simp only [add_sub_cancel'_right],
      rcases T_shifted_prev_property_at_i t t_in_T_shifted_prev with
        ⟨t_ne_mod_one_rest_coords, ⟨goal_val, goal_val_in_rest_goal_finset, t_eq_goal_val_mod_one⟩ | t_in_T⟩,
      { have goal_val_ne_last_goal : goal_val ≠ last_goal :=
          begin
            have goal_list_nodup : goal_list.nodup := finset.sort_nodup real.has_le.le goal_finset,
            rw [list.nodup, goal_list_def, list.pairwise_cons] at goal_list_nodup,
            rcases goal_list_nodup with ⟨last_goal_not_in_rest_goal_list, rest_goal_list_nodup⟩,
            dsimp[rest_goal_finset] at goal_val_in_rest_goal_finset,
            rw list.mem_to_finset at goal_val_in_rest_goal_finset,
            symmetry,
            exact last_goal_not_in_rest_goal_list goal_val goal_val_in_rest_goal_finset,
          end,
        have goal_val_in_s_finset : goal_val ∈ s_finset s_ne_zero := 
          finset.mem_of_subset rest_goal_finset_subset_s_finset goal_val_in_rest_goal_finset,
        have goal_val_ne_last_goal_mod_one := s_finset_distinct_mod_one goal_val_ne_last_goal goal_val_in_s_finset last_goal_in_s_finset,
        intro t_eq_last_goal_mod_one,
        replace t_eq_goal_val_mod_one := eq_mod_one_symmetric t_eq_goal_val_mod_one,
        exact goal_val_ne_last_goal_mod_one (eq_mod_one_transitive t_eq_goal_val_mod_one t_eq_last_goal_mod_one),
      },
      exact T_disjoint_goal_finset t t_in_T last_goal last_goal_in_goal_finset,
    end,
  have T_shifted_faceshare_free := T_shifted_prev_faceshare_free_implication T_shifted_prev_faceshare_free last_goal_not_in_T_shifted_prev,
  split, exact T_shifted_faceshare_free,
  split, 
  exact shifted_periodic_tiling_still_periodic T_shifted_prev_is_tiling T_shifted_prev_is_periodic i last_coord (last_goal - last_coord) T_shifted_is_tiling,
  split,
  { intros p p_in_T_shifted j j_val_lt_i_val, --Prove T_shifted_property_before_i
    dsimp[T_shifted] at p_in_T_shifted,
    rw shift_tiling at p_in_T_shifted,
    simp only [exists_prop, set.mem_union_eq, set.mem_set_of_eq] at p_in_T_shifted,
    rcases p_in_T_shifted with 
      ⟨p_in_T_shifted_prev, p_ne_last_coord_mod_one⟩ | ⟨p_prev, p_prev_in_T_shifted_prev, p_def, p_prev_eq_last_coord_mod_one⟩,
    exact T_shifted_prev_property_before_i p p_in_T_shifted_prev j j_val_lt_i_val,
    rw [scaled_basis_vector, add_vectors] at p_def,
    simp only [vector.nth_of_fn] at p_def,
    rw p_def,
    simp only [vector.nth_of_fn],
    have i_ne_j : i ≠ j :=
      by {intro i_eq_j, rw i_eq_j at j_val_lt_i_val, exact lt_irrefl j.val j_val_lt_i_val},
    rw [if_neg i_ne_j, add_zero],
    exact T_shifted_prev_property_before_i p_prev p_prev_in_T_shifted_prev j j_val_lt_i_val,
  },
  split,
  { intros p p_in_T_shifted, --Prove T_shifted_property_at_i
    dsimp[T_shifted] at p_in_T_shifted,
    rw shift_tiling at p_in_T_shifted,
    simp only [exists_prop, set.mem_union_eq, set.mem_set_of_eq] at p_in_T_shifted,
    rcases p_in_T_shifted with 
      ⟨p_in_T_shifted_prev, p_ne_last_coord_mod_one⟩ | ⟨p_prev, p_prev_in_T_shifted_prev, p_def, p_prev_eq_last_coord_mod_one⟩,
    { rcases T_shifted_prev_property_at_i p p_in_T_shifted_prev with ⟨p_ne_rest_coords_mod_one, T_shifted_second_property_at_i⟩,
      split,
      { intros coord coord_in_coords,
        by_cases coord_in_rest_coords_finset : coord ∈ rest_coords_finset,
        exact p_ne_rest_coords_mod_one coord coord_in_rest_coords_finset,
        rename coord_in_rest_coords_finset coord_not_in_rest_coords_finset,
        have coord_in_coords_list : coord ∈ coords_list := by {rw finset.mem_sort, exact coord_in_coords},
        rw [coords_list_def, list.mem_cons_eq] at coord_in_coords_list,
        cases coord_in_coords_list with coord_eq_last_coord coord_in_rest_coords,
        { rw coord_eq_last_coord,
          exact p_ne_last_coord_mod_one,
        },
        have coord_in_rest_coords_finset : coord ∈ rest_coords_finset := by {rw list.mem_to_finset, exact coord_in_rest_coords},
        exact p_ne_rest_coords_mod_one coord coord_in_rest_coords_finset,
      },
      rcases T_shifted_second_property_at_i with
        ⟨goal_val, goal_val_in_rest_goal_finset, p_eq_goal_val_mod_one⟩ | p_in_T,
      { left,
        have goal_val_in_goal_finset := finset.mem_of_subset rest_goal_finset_subset_goal_finset goal_val_in_rest_goal_finset,
        use [goal_val, goal_val_in_goal_finset, p_eq_goal_val_mod_one],
      },
      right,
      exact p_in_T,
    },
    split,
    { intros coord coord_in_coords p_eq_coord_mod_one,
      rw [p_def, scaled_basis_vector, add_vectors] at p_eq_coord_mod_one,
      simp only [if_true, eq_self_iff_true, vector.nth_of_fn] at p_eq_coord_mod_one,
      replace p_eq_coord_mod_one := subst_summand_eq_mod_one p_prev_eq_last_coord_mod_one p_eq_coord_mod_one,
      simp only [add_sub_cancel'_right] at p_eq_coord_mod_one,
      exact coords_disjoint_s_fisnet coord coord_in_coords last_goal last_goal_in_s_finset (eq_mod_one_symmetric p_eq_coord_mod_one),
    },
    left,
    use [last_goal, last_goal_in_goal_finset],
    rw [p_def, scaled_basis_vector, add_vectors],
    simp only [if_true, eq_self_iff_true, vector.nth_of_fn],
    apply subst_summand_eq_mod_one (eq_mod_one_symmetric p_prev_eq_last_coord_mod_one),
    simp only [add_sub_cancel'_right],
    exact eq_mod_one_reflexive last_goal,
  },
  intros p p_in_T_shifted j j_val_gt_i_val, --Prove T_shifted_property_after_i
  dsimp[T_shifted] at p_in_T_shifted,
  rw shift_tiling at p_in_T_shifted,
  simp only [exists_prop, set.mem_union_eq, set.mem_set_of_eq] at p_in_T_shifted,
  rcases p_in_T_shifted with 
    ⟨p_in_T_shifted_prev, p_ne_last_coord_mod_one⟩ | ⟨p_prev, p_prev_in_T_shifted_prev, p_def, p_prev_eq_last_coord_mod_one⟩,
  exact T_shifted_prev_property_after_i p p_in_T_shifted_prev j j_val_gt_i_val,
  rw [scaled_basis_vector, add_vectors] at p_def,
  simp only [vector.nth_of_fn] at p_def,
  rw p_def,
  simp only [vector.nth_of_fn],
  have i_ne_j : i ≠ j :=
    by {intro i_eq_j, rw i_eq_j at j_val_gt_i_val, exact gt_irrefl j.val j_val_gt_i_val},
  rw [if_neg i_ne_j, add_zero],
  exact T_shifted_prev_property_after_i p_prev p_prev_in_T_shifted_prev j j_val_gt_i_val,
end

lemma inductive_replacement_lemma_helper1 {d : ℕ} {s : ℕ} (d_ne_zero : d ≠ 0) (s_ne_zero : s ≠ 0) (i : fin d) (T : set (point d)) 
  (T_is_tiling : is_tiling T) (T_faceshare_free : tiling_faceshare_free T) (T_is_periodic : is_periodic T_is_tiling) (T_is_s_discrete : is_s_discrete s T) 
  (coords_before_i_handled : ∀ p : point d, p ∈ T → ∀ j : fin d, j.val < i.val → 
    ∃ s_val ∈ s_finset s_ne_zero, eq_mod_one (vector.nth p j) s_val) :
  ∃ T_shifted : set (point d), ∃ T_shifted_is_tiling : is_tiling T_shifted, tiling_faceshare_free T_shifted ∧ 
  is_periodic T_shifted_is_tiling ∧ is_s_discrete s T_shifted ∧
  ∀ p : point d, p ∈ T_shifted → ∀ j : fin d, j.val ≤ i.val → ∃ s_val ∈ s_finset s_ne_zero, eq_mod_one (vector.nth p j) s_val :=
begin
  rcases T_is_s_discrete i with ⟨coords, coords_card_le_s, ⟨coords_distinct_mod_one, T_is_s_discrete'⟩⟩,
  let goal_finset := {s_val ∈ s_finset s_ne_zero | ∀ coord ∈ coords, ne_mod_one coord s_val},
  let coords_inter_s_finset := {coord ∈ coords | ∃ s_val ∈ s_finset s_ne_zero, eq_mod_one coord s_val},
  have coords_inter_goal_subset_of_coords : coords_inter_s_finset ⊆ coords :=
    by {dsimp[coords_inter_s_finset], simp only [finset.filter_subset]},
  have goal_finset_subset_s_finset : goal_finset ⊆ s_finset s_ne_zero :=
    by {dsimp[goal_finset], apply finset.filter_subset},
  have coords_to_handle_disjoint_s_finset : 
    ∀ (coord : ℝ), coord ∈ coords \ coords_inter_s_finset → ∀ (s_val : ℝ), s_val ∈ s_finset s_ne_zero → ne_mod_one coord s_val :=
    begin
      intros coord coord_in_coords_remaining s_val s_val_in_s_finset,
      dsimp[coords_inter_s_finset, goal_finset] at coord_in_coords_remaining,
      simp only [not_exists, and_imp, not_and, finset.mem_sdiff, finset.mem_filter] at coord_in_coords_remaining,
      cases coord_in_coords_remaining with coord_in_coords coord_in_coords_imp,
      exact coord_in_coords_imp coord_in_coords s_val s_val_in_s_finset,
    end,
  have T_disjoint_goal_finset :
    ∀ (p : vector ℝ d), p ∈ T → ∀ (goal_val : ℝ), goal_val ∈ goal_finset → ne_mod_one (p.nth i) goal_val :=
    begin
      intros p p_in_T goal_val goal_val_in_goal_finset p_eq_goal_val_mod_one,
      dsimp[goal_finset] at goal_val_in_goal_finset,
      simp only [finset.mem_filter] at goal_val_in_goal_finset,
      cases goal_val_in_goal_finset with goal_val_in_s_finset goal_val_not_in_T,
      rcases T_is_s_discrete' p p_in_T with ⟨coord, coord_in_coords, p_eq_coord_mod_one⟩,
      replace p_eq_coord_mod_one := eq_mod_one_symmetric p_eq_coord_mod_one,
      have coord_eq_goal_val_mod_one := eq_mod_one_transitive p_eq_coord_mod_one p_eq_goal_val_mod_one,
      exact goal_val_not_in_T coord coord_in_coords coord_eq_goal_val_mod_one,
    end,
  have coords_to_handle_card_le_goal_finset_card : (coords \ coords_inter_s_finset).card ≤ goal_finset.card := 
    begin
      rw finset.card_sdiff,
      { simp only [tsub_le_iff_right],
        have goal_finset_card_add_coord_inter_s_card_eq_s_card : goal_finset.card + coords_inter_s_finset.card = (s_finset s_ne_zero).card :=
          begin
            let s_finset_filter_fn := (λ s_val : ℝ, ∀ (coord : ℝ), coord ∈ coords → ne_mod_one coord s_val),
            have s_finset_filter_fn_decidable : decidable_pred s_finset_filter_fn := 
              (λ s_val, classical.prop_decidable (s_finset_filter_fn s_val)),
            let s_finset_filter_fn_neg := (λ s_val : ℝ, ∃ coord ∈ coords, eq_mod_one coord s_val),
            have not_s_finset_filter_fn_neg_eq_f_finset_filter_fn_neg : not ∘ s_finset_filter_fn = s_finset_filter_fn_neg :=
              begin
                apply funext,
                intro s_val,
                dsimp[s_finset_filter_fn, s_finset_filter_fn_neg],
                simp only [exists_prop, eq_iff_iff, not_forall],
                split,
                { rintro ⟨coord, coord_in_coords, coord_eq_s_val_mod_one⟩,
                  use [coord, coord_in_coords],
                  rw [ne_mod_one, not_not] at coord_eq_s_val_mod_one,
                  exact coord_eq_s_val_mod_one,
                },
                rintro ⟨coord, coord_in_coords, coord_eq_s_val_mod_one⟩,
                use [coord, coord_in_coords],
              end,
            
            rw ← @finset.filter_card_add_filter_neg_card_eq_card ℝ (s_finset s_ne_zero) s_finset_filter_fn s_finset_filter_fn_decidable,
            have goal_finset_eq_s_finset_filtered : 
              goal_finset = @finset.filter ℝ s_finset_filter_fn s_finset_filter_fn_decidable (s_finset s_ne_zero) :=
              begin
                dsimp[goal_finset, s_finset_filter_fn],
                apply finset.filter_congr_decidable,
              end,
            rw goal_finset_eq_s_finset_filtered,
            simp only [add_right_inj],
            let f : ℝ → ℝ := 
              (λ coord : ℝ,
                begin
                  by_cases h : ∃ s_val ∈ s_finset s_ne_zero, eq_mod_one coord s_val,
                  exact classical.some h,
                  exact (-1 : ℝ),
                end
              ),
            convert_to coords_inter_s_finset.card = (finset.image f coords_inter_s_finset).card,
            { have finset_card_eq_self_card : ∀ s : finset ℝ, ∀ s' : finset ℝ, s = s' → s.card = s'.card :=
                by {intros s s' s_eq_s', rw s_eq_s'},
              apply finset_card_eq_self_card,
              apply finset.ext,
              intro s_val,
              split,
              { intro s_val_in_filtered_set,
                conv at s_val_in_filtered_set
                begin
                  find (not ∘ s_finset_filter_fn) {rw not_s_finset_filter_fn_neg_eq_f_finset_filter_fn_neg}
                end,
                dsimp[s_finset_filter_fn_neg] at s_val_in_filtered_set,
                simp only [exists_prop, finset.mem_filter] at s_val_in_filtered_set,
                rcases s_val_in_filtered_set with ⟨s_val_in_s_finset, ⟨coord, coord_in_coords, coord_eq_s_val_mod_one⟩⟩,
                rw finset.mem_image,
                use coord,
                split,
                { dsimp[coords_inter_s_finset],
                  simp only [exists_prop, finset.mem_filter],
                  use [coord_in_coords, s_val, s_val_in_s_finset, coord_eq_s_val_mod_one],
                },
                dsimp[f],
                have if_cond_true : ∃ (s_val : ℝ) (H : s_val ∈ s_finset s_ne_zero), eq_mod_one coord s_val := 
                  ⟨s_val, s_val_in_s_finset, coord_eq_s_val_mod_one⟩,
                convert_to classical.some if_cond_true = s_val, apply dif_pos,
                rcases classical.some_spec if_cond_true with ⟨classical_some_in_s_finset, coord_eq_classical_some_mod_one⟩,
                by_contra classical_some_ne_s_val,
                have classical_some_eq_s_val_mod_one : eq_mod_one (classical.some if_cond_true) s_val :=
                  eq_mod_one_transitive (eq_mod_one_symmetric coord_eq_classical_some_mod_one) coord_eq_s_val_mod_one,
                exact s_finset_distinct_mod_one classical_some_ne_s_val classical_some_in_s_finset s_val_in_s_finset
                  classical_some_eq_s_val_mod_one,
              },
              intro s_val_in_image,
              conv
              begin
                find (not ∘ s_finset_filter_fn) {rw not_s_finset_filter_fn_neg_eq_f_finset_filter_fn_neg}
              end,
              dsimp[s_finset_filter_fn_neg],
              simp only [exists_prop, finset.mem_filter],
              dsimp[f] at s_val_in_image,
              rw finset.mem_image at s_val_in_image,
              simp only [exists_prop] at s_val_in_image,
              rcases s_val_in_image with ⟨coord, coord_in_coords_inter_s_finset, classical_some_eq_s_val⟩,
              by_cases if_cond : ∃ (s_val : ℝ), s_val ∈ s_finset s_ne_zero ∧ eq_mod_one coord s_val,
              { rename if_cond if_cond_true,
                rw dif_pos if_cond_true at classical_some_eq_s_val,
                rcases classical.some_spec if_cond_true with ⟨classical_some_in_s_finset, coord_eq_classical_some_mod_one⟩,
                rw ← classical_some_eq_s_val,
                have coord_in_coords : coord ∈ coords := 
                  begin
                    dsimp[coords_inter_s_finset] at coord_in_coords_inter_s_finset,
                    rw finset.mem_filter at coord_in_coords_inter_s_finset,
                    cases coord_in_coords_inter_s_finset with coord_in_coords _,
                    exact coord_in_coords,
                  end,
                exact ⟨classical_some_in_s_finset, ⟨coord, coord_in_coords, coord_eq_classical_some_mod_one⟩⟩,
              },
              rename if_cond if_cond_false,
              exfalso, --Derive contradiction from if_cond_false
              dsimp[coords_inter_s_finset] at coord_in_coords_inter_s_finset,
              rw finset.mem_filter at coord_in_coords_inter_s_finset,
              cases coord_in_coords_inter_s_finset with _ if_cond_true,
              have if_cond_true' : ∃ s_val : ℝ, s_val ∈ s_finset s_ne_zero ∧ eq_mod_one coord s_val :=
                begin
                  rcases if_cond_true with ⟨s_val, s_val_in_s_finset, coord_eq_s_val_mod_one⟩,
                  use s_val,
                  exact ⟨s_val_in_s_finset, coord_eq_s_val_mod_one⟩,
                end,
              exact if_cond_false if_cond_true',
            },
            symmetry,
            rw finset.card_image_eq_iff_inj_on,
            rw set.inj_on,
            intros coord1 coord1_in_coords_inter_s_finset coord2 coord2_in_coords_inter_s_finset f_coord1_eq_f_coord2,
            rw finset.mem_coe at coord1_in_coords_inter_s_finset coord2_in_coords_inter_s_finset,
            dsimp[coords_inter_s_finset] at coord1_in_coords_inter_s_finset coord2_in_coords_inter_s_finset,
            simp only [exists_prop, finset.mem_filter] at coord1_in_coords_inter_s_finset coord2_in_coords_inter_s_finset,
            rcases coord1_in_coords_inter_s_finset with
              ⟨coord1_in_coords, ⟨coord1_s_val, coord1_s_val_in_s_finset, coord1_eq_coord1_s_val_mod_one⟩⟩,
            rcases coord2_in_coords_inter_s_finset with
              ⟨coord2_in_coords, ⟨coord2_s_val, coord2_s_val_in_s_finset, coord2_eq_coord2_s_val_mod_one⟩⟩,
            dsimp[f] at f_coord1_eq_f_coord2,
            have exists_s_val_eq_coord1_mod_one : ∃ (s_val : ℝ) (H : s_val ∈ s_finset s_ne_zero), eq_mod_one coord1 s_val :=
              ⟨coord1_s_val, coord1_s_val_in_s_finset, coord1_eq_coord1_s_val_mod_one⟩,
            have exists_s_val_eq_coord2_mod_one : ∃ (s_val : ℝ) (H : s_val ∈ s_finset s_ne_zero), eq_mod_one coord2 s_val :=
              ⟨coord2_s_val, coord2_s_val_in_s_finset, coord2_eq_coord2_s_val_mod_one⟩,
            rw [dif_pos exists_s_val_eq_coord1_mod_one, dif_pos exists_s_val_eq_coord2_mod_one] at f_coord1_eq_f_coord2,
            rcases classical.some_spec exists_s_val_eq_coord1_mod_one with
              ⟨classical_some1_in_s_finset, coord1_eq_classical_some1_mod_one⟩,
            rcases classical.some_spec exists_s_val_eq_coord2_mod_one with
              ⟨classical_some2_in_s_finset, coord2_eq_classical_some2_mod_one⟩, 
            rw f_coord1_eq_f_coord2 at coord1_eq_classical_some1_mod_one,
            have coord1_eq_coord2_mod_one : eq_mod_one coord1 coord2 :=
              eq_mod_one_transitive coord1_eq_classical_some1_mod_one (eq_mod_one_symmetric coord2_eq_classical_some2_mod_one),
            by_contra coord1_ne_coord2,
            exact coords_distinct_mod_one coord1 coord1_in_coords coord2 coord2_in_coords coord1_ne_coord2 coord1_eq_coord2_mod_one,
          end,
        rw [goal_finset_card_add_coord_inter_s_card_eq_s_card, s_finset_card s_ne_zero],
        exact coords_card_le_s,
      },
      apply finset.filter_subset,
    end,
  rcases inductive_replacement_lemma_helper2 s_ne_zero i T T_is_tiling T_faceshare_free T_is_periodic coords_before_i_handled 
    (coords \ coords_inter_s_finset).card (coords \ coords_inter_s_finset) goal_finset goal_finset_subset_s_finset
    coords_to_handle_disjoint_s_finset T_disjoint_goal_finset (by refl) coords_to_handle_card_le_goal_finset_card with
    ⟨T_shifted, T_shifted_is_tiling, T_shifted_faceshare_free, T_shifted_is_periodic, T_shifted_property_before_i, T_shifted_property_at_i, 
      T_shifted_property_after_i⟩,
  use [T_shifted, T_shifted_is_tiling],
  split, exact T_shifted_faceshare_free,
  split, exact T_shifted_is_periodic,
  split,
  { rw is_s_discrete,
    intro j,
    have j_eq_or_lt_or_gt_i := nat_eq_or_lt_or_gt j.val i.val,
    rcases j_eq_or_lt_or_gt_i with j_val_eq_i_val | j_val_lt_i_val | j_val_gt_i_val,
    { use s_finset s_ne_zero,
      split,
      { apply le_of_eq,
        exact s_finset_card s_ne_zero,
      },
      split,
      { intros coord1 coord1_in_s_finset coord2 coord2_in_s_finset coord1_ne_coord2,
        exact s_finset_distinct_mod_one coord1_ne_coord2 coord1_in_s_finset coord2_in_s_finset,
      },
      intros t t_in_T_shifted,
      have j_eq_i := fin.eq_of_veq j_val_eq_i_val,
      rw j_eq_i,
      cases T_shifted_property_at_i t t_in_T_shifted with coords_not_in_T_shifted T_shifted_has_goal,
      by_contra goal_false,
      cases T_shifted_has_goal with goal t_in_T,
      { simp only [not_exists, exists_prop, not_and] at goal_false,
        rcases goal with ⟨goal_val, goal_val_in_goal_finset, t_eq_goal_val_mod_one⟩,
        have goal_val_in_s_finset := finset.mem_of_subset goal_finset_subset_s_finset goal_val_in_goal_finset,
        exact goal_false goal_val goal_val_in_s_finset t_eq_goal_val_mod_one,
      },
      rcases T_is_s_discrete' t t_in_T with ⟨coord, coord_in_coords, t_eq_mod_one_coord⟩,
      have coord_in_coords_to_handle : coord ∈ coords \ coords_inter_s_finset :=
        begin
          dsimp[coords_inter_s_finset],
          simp only [not_exists, exists_prop, not_and, finset.mem_sdiff, finset.mem_filter],
          split, exact coord_in_coords,
          intros coord_in_coords goal_val goal_val_in_goal_finset coord_eq_goal_val_mod_one,
          have t_eq_goal_val_mod_one := eq_mod_one_transitive t_eq_mod_one_coord coord_eq_goal_val_mod_one,
          simp only [not_exists, exists_prop, not_and] at goal_false,
          exact goal_false goal_val goal_val_in_goal_finset t_eq_goal_val_mod_one,
        end,
      exact coords_not_in_T_shifted coord coord_in_coords_to_handle t_eq_mod_one_coord,
    },
    { use s_finset s_ne_zero,
      split,
      { apply le_of_eq,
        exact s_finset_card s_ne_zero,
      },
      split,
      { intros coord1 coord1_in_s_finset coord2 coord2_in_s_finset coord1_ne_coord2,
        exact s_finset_distinct_mod_one coord1_ne_coord2 coord1_in_s_finset coord2_in_s_finset,
      },
      intros t t_in_T_shifted,
      exact T_shifted_property_before_i t t_in_T_shifted j j_val_lt_i_val,
    },
    rcases T_is_s_discrete j with ⟨coords, coords_card_le_s, ⟨coords_distinct_mod_one, t_in_T_imp_t_j_in_coords⟩⟩,
    use [coords, coords_card_le_s],
    split, exact coords_distinct_mod_one,
    intros t t_in_T_shifted,
    rcases T_shifted_property_after_i t t_in_T_shifted j j_val_gt_i_val with ⟨t', t'_in_T, t_eq_t'_at_j⟩,
    rw t_eq_t'_at_j,
    exact t_in_T_imp_t_j_in_coords t' t'_in_T,
  },
  intros p p_in_T_shifted j j_val_le_i,
  cases lt_or_eq_of_le j_val_le_i with j_val_lt_i_val j_val_eq_i_val, 
  exact T_shifted_property_before_i p p_in_T_shifted j j_val_lt_i_val,
  have j_eq_i : j = i := fin.eq_of_veq j_val_eq_i_val,
  rw j_eq_i,
  replace T_shifted_property_at_i := T_shifted_property_at_i p p_in_T_shifted,
  cases T_shifted_property_at_i with T_shifted_shifts_all_bad_coords T_shifted_coords_all_in_goal_finset,
  by_contra p_coord_not_in_goal_finset, --Derive contradiction between p_coord_not_in_goal_finset and T_shifted_property_at_i
  cases T_shifted_coords_all_in_goal_finset with T_shifted_coords_all_in_goal_finset p_in_T,
  { rcases T_shifted_coords_all_in_goal_finset with ⟨goal_val, goal_val_in_goal_finset, p_eq_goal_val_mod_one⟩,
    simp only [not_exists, exists_prop, not_and] at p_coord_not_in_goal_finset,
    have goal_val_in_s_finset := finset.mem_of_subset goal_finset_subset_s_finset goal_val_in_goal_finset,
    exact p_coord_not_in_goal_finset goal_val goal_val_in_s_finset p_eq_goal_val_mod_one,
  },
  have p_i_in_coords : ∃ coord ∈ coords, eq_mod_one (vector.nth p i) coord := T_is_s_discrete' p p_in_T,
  rcases p_i_in_coords with ⟨coord, coord_in_coords, p_i_eq_coords_mod_one⟩,
  by_cases coord_in_goal_finset : coord ∈ goal_finset,
  { simp only [not_exists, exists_prop, not_and] at p_coord_not_in_goal_finset,
    have coord_in_s_finset := finset.mem_of_subset goal_finset_subset_s_finset coord_in_goal_finset,
    exact p_coord_not_in_goal_finset coord coord_in_s_finset p_i_eq_coords_mod_one,
  },
  rename coord_in_goal_finset coord_not_in_goal_finset,
  have coord_in_coords_to_handle : coord ∈ coords \ coords_inter_s_finset :=
    begin
      dsimp[coords_inter_s_finset],
      simp only [not_exists, exists_prop, not_and, finset.mem_sdiff, finset.mem_filter],
      split, exact coord_in_coords,
      intros coord_in_coords goal_val goal_val_in_goal_finset coord_eq_goal_val_mod_one,
      have p_eq_goal_val_mod_one := eq_mod_one_transitive p_i_eq_coords_mod_one coord_eq_goal_val_mod_one,
      simp only [not_exists, exists_prop, not_and] at p_coord_not_in_goal_finset,
      exact p_coord_not_in_goal_finset goal_val goal_val_in_goal_finset p_eq_goal_val_mod_one,
    end,
  exact T_shifted_shifts_all_bad_coords coord coord_in_coords_to_handle p_i_eq_coords_mod_one,
end

lemma inductive_replacement_lemma {d : ℕ} {s : ℕ} (d_ne_zero : d ≠ 0) (s_ne_zero : s ≠ 0) (T : set (point d)) 
  (T_is_tiling : is_tiling T) (T_faceshare_free : tiling_faceshare_free T) (T_is_periodic: is_periodic T_is_tiling) (T_is_s_discrete : is_s_discrete s T) :
  ∃ T_shifted : set (point d), ∃ T_shifted_is_tiling : is_tiling T_shifted, tiling_faceshare_free T_shifted ∧ is_periodic T_shifted_is_tiling ∧
  (∀ i : fin d, ∀ p : point d, p ∈ T_shifted → ∃ s_val ∈ s_finset s_ne_zero, eq_mod_one (vector.nth p i) s_val) :=
begin
  let d_sub_one : fin d := ⟨d - 1, nat.pred_lt d_ne_zero⟩,
  have inductive_replacement_lemma_helper_fact : ∀ i : fin d, i.val < d → 
    ∃ T_shifted : set (point d), ∃ T_shifted_is_tiling : is_tiling T_shifted, tiling_faceshare_free T_shifted ∧ 
    is_periodic T_shifted_is_tiling ∧ is_s_discrete s T_shifted ∧
    ∀ p : point d, p ∈ T_shifted → ∀ j : fin d, j.val ≤ i.val → ∃ s_val ∈ s_finset s_ne_zero, eq_mod_one (vector.nth p j) s_val :=
    begin
      intro i,
      induction i.val,
      { intro zero_lt_d,
        have coords_before_zero_handled : ∀ p : point d, p ∈ T → ∀ j : fin d, j.val < 0 → 
          ∃ s_val ∈ s_finset s_ne_zero, eq_mod_one (vector.nth p j) s_val :=
          by {intros p p_in_T j j_lt_zero, exfalso, clear_except j_lt_zero, linarith,},
        exact inductive_replacement_lemma_helper1 d_ne_zero s_ne_zero ⟨0, zero_lt_d⟩ T T_is_tiling T_faceshare_free
          T_is_periodic T_is_s_discrete coords_before_zero_handled,
      },
      intro n_succ_lt_d,
      have n_lt_d : n < d := nat.lt_of_succ_lt n_succ_lt_d,
      rcases ih n_lt_d with
        ⟨T_shifted_prev, T_shifted_prev_is_tiling, T_shifted_prev_faceshare_free, T_shifted_prev_is_periodic, T_shifted_prev_s_discrete, 
        T_shifted_prev_coord_property⟩,
      have coords_before_n_succ_handled : 
        ∀ p : point d, p ∈ T_shifted_prev → ∀ j : fin d, j.val < n.succ → ∃ s_val ∈ s_finset s_ne_zero, eq_mod_one (vector.nth p j) s_val :=
        begin
          intros p p_in_T_shifted_prev j j_lt_n_succ,
          have j_le_n := nat.le_of_lt_succ j_lt_n_succ,
          exact T_shifted_prev_coord_property p p_in_T_shifted_prev j j_le_n,
        end,
      exact inductive_replacement_lemma_helper1 d_ne_zero s_ne_zero ⟨n.succ, n_succ_lt_d⟩ T_shifted_prev T_shifted_prev_is_tiling
        T_shifted_prev_faceshare_free T_shifted_prev_is_periodic T_shifted_prev_s_discrete coords_before_n_succ_handled,
    end,
  rcases inductive_replacement_lemma_helper_fact d_sub_one (nat.pred_lt d_ne_zero) with
    ⟨T_shifted, T_shifted_is_tiling, T_shifted_faceshare_free, T_shifted_is_periodic, T_shifted_s_discrete, T_shifted_only_uses_goal_coordinates⟩,
  use [T_shifted, T_shifted_is_tiling, T_shifted_faceshare_free, T_shifted_is_periodic],
  intros i p p_in_T_shifted,
  have i_val_le_d_sub_one_val : i.val ≤ d_sub_one.val :=
    begin
      have i_val_lt_d := i.property,
      dsimp only[d_sub_one],
      exact nat.le_pred_of_lt i_val_lt_d,
    end,
  exact T_shifted_only_uses_goal_coordinates p p_in_T_shifted i i_val_le_d_sub_one_val,
end

lemma goal_clique_with_info_map_fn_yields_fin_double_s_vector {d s : ℕ} (d_ne_zero : d ≠ 0) (s_ne_zero : s ≠ 0) (T : set (point d)) (T_is_tiling : is_tiling T)
  (T_faceshare_free : tiling_faceshare_free T) (T_is_periodic : is_periodic T_is_tiling) (T_is_s_discrete : is_s_discrete s T) (T_shifted : set (point d))
  (T_shifted_is_tiling : is_tiling T_shifted) (T_shifted_faceshare_free : tiling_faceshare_free T_shifted)
  (T_shifted_contains_only_s_points : 
    ∀ (i : fin d) (p : point d), p ∈ T_shifted → (∃ (s_val : ℝ) (H : s_val ∈ s_finset s_ne_zero), eq_mod_one (vector.nth p i) s_val))
  (core_points_finset : 
    finset {p : point d // ∀ (j : fin d), (j.val < d → vector.nth p j = 0 ∨ vector.nth p j = 1) ∧ (j.val ≥ d → vector.nth p j = 0)})
  (core_points_finset_card : core_points_finset.card = 2 ^ d)
  (core_points_finset_property : 
    ∀ (p : point d) (h : ∀ (j : fin d), (j.val < d → vector.nth p j = 0 ∨ vector.nth p j = 1) ∧ (j.val ≥ d → vector.nth p j = 0)),
      (⟨p, h⟩ : {p : point d // ∀ (j : fin d), (j.val < d → vector.nth p j = 0 ∨ vector.nth p j = 1) ∧ (j.val ≥ d → vector.nth p j = 0)}) ∈ core_points_finset)
  (p : {p : point d // ∀ (j : fin d), (j.val < d → vector.nth p j = 0 ∨ vector.nth p j = 1) ∧ (j.val ≥ d → vector.nth p j = 0)}) :
  ∃ fin_double_s_vector : vector (fin (2*s)) d, ∀ i : fin d, ↑(fin_double_s_vector.nth i).val = ↑s * (((point_to_corner T_shifted_is_tiling p).val).nth i) + s - 1 :=
begin
  let p_corner := (point_to_corner T_shifted_is_tiling ↑p).val,
  have p_corner_def : p_corner = (point_to_corner T_shifted_is_tiling ↑p).val := by refl,
  have p_corner_property := (point_to_corner T_shifted_is_tiling ↑p).property,
  rw ← p_corner_def at p_corner_property,
  rw ← p_corner_def,
  rcases p_corner_property with ⟨p_corner_in_T_shifted, p_in_p_corner, p_corner_unique⟩,
  rw cube at p_in_p_corner,
  simp only [set.mem_set_of_eq] at p_in_p_corner,
  rw in_cube at p_in_p_corner,
  have each_coord_is_nat : ∀ i : fin d, ∃ n : ℕ, ↑n = ↑s * vector.nth p_corner i + ↑s - 1 :=
    begin
      intro i,
      rcases T_shifted_contains_only_s_points i p_corner p_corner_in_T_shifted with ⟨s_val, s_val_in_s_finset, p_corner_eq_s_val_mod_one⟩,
      rcases s_finset_range s_val_in_s_finset with ⟨zero_le_s_val, s_val_lt_one⟩,
      replace p_in_p_corner := p_in_p_corner i,
      rcases p_in_p_corner with ⟨p_corner_le_p, p_lt_p_corner_add_one⟩,
      cases p.property i with p_property unnecessary,
      clear unnecessary,
      cases p_property i.property with p_eq_zero p_eq_one,
      { simp only [subtype.val_eq_coe] at p_eq_zero,
        rw p_eq_zero at p_corner_le_p p_lt_p_corner_add_one,
        rcases p_corner_eq_s_val_mod_one with ⟨p_corner_floor, zero, y, zero_le_y, y_lt_one, p_corner_def, s_val_def⟩,
        have zero_eq_zero : zero = 0 :=
          begin
            rw s_val_def at zero_le_s_val s_val_lt_one,
            clear_except zero_le_s_val s_val_lt_one zero_le_y y_lt_one,
            rcases eq_or_lt_or_gt zero 0 with zero_eq_zero | zero_lt_zero | zero_gt_zero,
            exact zero_eq_zero,
            { have zero_le_neg_one : zero ≤ -1 := by omega,
              have cast_zero_le_neg_one : ↑zero ≤ (-1 : ℝ) := by exact_mod_cast zero_le_neg_one,
              linarith,
            },
            have zero_ge_one : zero ≥ 1 := by omega,
            have cast_zero_ge_one : ↑zero ≥ (1 : ℝ) := by exact_mod_cast zero_ge_one,
            linarith,
          end,
        have cast_zero_eq_zero : ↑zero = (0 : ℝ) := by exact_mod_cast zero_eq_zero,
        rw [cast_zero_eq_zero, zero_add] at s_val_def,
        rw ← s_val_def at p_corner_def,
        by_cases s_val_eq_zero : s_val = 0,
        { rw [s_val_eq_zero, add_zero] at p_corner_def,
          use  s * int.to_nat(p_corner_floor) + s - 1,
          have zero_le_p_corner_floor : 0 ≤ p_corner_floor :=
            begin
              clear_except p_corner_def p_lt_p_corner_add_one p_corner_le_p,
              rw p_corner_def at p_lt_p_corner_add_one p_corner_le_p,
              have h1 : p_corner_floor ≤ 0 := by exact_mod_cast p_corner_le_p,
              have h2 : 0 < p_corner_floor + 1 := by exact_mod_cast p_lt_p_corner_add_one,
              omega,
            end,
          have p_corner_floor_to_nat_eq_self : ↑p_corner_floor.to_nat = p_corner_floor := int.to_nat_of_nonneg zero_le_p_corner_floor,
          have cast_p_corner_floor_to_nat_eq_self : ↑p_corner_floor.to_nat = (↑p_corner_floor : ℝ) := 
            by exact_mod_cast p_corner_floor_to_nat_eq_self,
          have one_le_s : 1 ≤ s := 
            begin
              rcases nat_eq_or_lt_or_gt s 0 with s_eq_zero | s_lt_zero | s_gt_zero,
              { exfalso,
                exact s_ne_zero s_eq_zero,
              },
              { exfalso,
                exact nat.not_lt_zero s s_lt_zero,
              },
              clear_except s_gt_zero,
              have zero_lt_s : 0 < s := by linarith,
              omega,
            end,
          rw [nat.add_sub_assoc one_le_s, nat.cast_add (s * p_corner_floor.to_nat) (s - 1), nat.cast_sub one_le_s, nat.cast_mul,
            cast_p_corner_floor_to_nat_eq_self, p_corner_def, ← add_sub_assoc, nat.cast_one],
        },
        rename s_val_eq_zero s_val_ne_zero,
        rcases s_finset_range s_val_in_s_finset with ⟨zero_le_s_val, s_val_lt_one⟩,
        rw s_finset at s_val_in_s_finset,
        simp only [exists_prop, finset.mem_map, function.embedding.coe_fn_mk, finset.mem_range] at s_val_in_s_finset,
        rcases s_val_in_s_finset with ⟨s_val_num, s_val_num_lt_s, s_val_num_div_s_eq_s_val⟩,
        use s_val_num - 1,
        rcases nat_eq_or_lt_or_gt s_val_num 0 with s_val_num_eq_zero | s_val_num_lt_zero | s_val_num_gt_zero,
        { exfalso,
          rw s_val_num_eq_zero at s_val_num_div_s_eq_s_val,
          simp only [zero_div, nat.cast_zero] at s_val_num_div_s_eq_s_val,
          symmetry' at s_val_num_div_s_eq_s_val,
          exact s_val_ne_zero s_val_num_div_s_eq_s_val,
        },
        { exfalso,
          clear_except s_val_num_lt_zero,
          linarith,
        },
        have one_le_s_val_num : 1 ≤ s_val_num := by {clear_except s_val_num_gt_zero, omega},
        have cast_s_ne_zero : ↑s ≠ (0 : ℝ) := by exact_mod_cast s_ne_zero,
        have p_corner_floor_eq_neg_one : p_corner_floor = -1 :=
          begin
            rcases eq_or_lt_or_gt p_corner_floor (-1) with p_corner_floor_eq_neg_one | p_corner_floor_lt_neg_one | p_corner_floor_gt_neg_one,
            exact p_corner_floor_eq_neg_one,
            { have p_corner_floor_le_neg_two : p_corner_floor ≤ -2 := by {clear_except p_corner_floor_lt_neg_one, omega},
              have cast_p_corner_floor_le_neg_two : ↑p_corner_floor ≤ (-2 : ℝ) := by exact_mod_cast p_corner_floor_le_neg_two,
              linarith,
            },
            have zero_le_p_corner_floor : 0 ≤ p_corner_floor := by {clear_except p_corner_floor_gt_neg_one, omega},
            have cast_zero_le_p_corner_floor : (0 : ℝ) ≤ ↑p_corner_floor := by exact_mod_cast zero_le_p_corner_floor,
            have zero_ne_s_val : 0 ≠ s_val := by {intro zero_eq_s_val, symmetry' at zero_eq_s_val, exact s_val_ne_zero zero_eq_s_val},
            have zero_lt_s_val : 0 < s_val := lt_of_le_of_ne zero_le_s_val zero_ne_s_val,
            linarith,
          end,
        have cast_p_corner_floor_eq_neg_one : ↑p_corner_floor = (-1 : ℝ) := by exact_mod_cast p_corner_floor_eq_neg_one,
        rw ← s_val_num_div_s_eq_s_val at p_corner_def,
        rw [nat.cast_sub one_le_s_val_num, p_corner_def, mul_add, mul_div_of_ne_zero ↑s_val_num cast_s_ne_zero, cast_p_corner_floor_eq_neg_one],
        simp only [nat.cast_one, mul_neg, mul_one, neg_add_cancel_comm],
      },
      simp only [subtype.val_eq_coe] at p_eq_one,
      rw p_eq_one at p_corner_le_p p_lt_p_corner_add_one,
      rcases p_corner_eq_s_val_mod_one with ⟨p_corner_floor, zero, y, zero_le_y, y_lt_one, p_corner_def, s_val_def⟩,
       have zero_eq_zero : zero = 0 :=
        begin
          rw s_val_def at zero_le_s_val s_val_lt_one,
          clear_except zero_le_s_val s_val_lt_one zero_le_y y_lt_one,
          rcases eq_or_lt_or_gt zero 0 with zero_eq_zero | zero_lt_zero | zero_gt_zero,
          exact zero_eq_zero,
          { have zero_le_neg_one : zero ≤ -1 := by omega,
            have cast_zero_le_neg_one : ↑zero ≤ (-1 : ℝ) := by exact_mod_cast zero_le_neg_one,
            linarith,
          },
          have zero_ge_one : zero ≥ 1 := by omega,
          have cast_zero_ge_one : ↑zero ≥ (1 : ℝ) := by exact_mod_cast zero_ge_one,
          linarith,
        end,
      have cast_zero_eq_zero : ↑zero = (0 : ℝ) := by exact_mod_cast zero_eq_zero,
      rw [cast_zero_eq_zero, zero_add] at s_val_def,
      rw ← s_val_def at p_corner_def,
      by_cases s_val_eq_zero : s_val = 0,
      { rw [s_val_eq_zero, add_zero] at p_corner_def,
        use s * int.to_nat(p_corner_floor) + s - 1,
        have one_le_p_corner_floor : 1 ≤ p_corner_floor :=
          begin
            clear_except p_corner_def p_lt_p_corner_add_one,
            rw p_corner_def at p_lt_p_corner_add_one,
            have h : 1 < p_corner_floor + 1 := by exact_mod_cast p_lt_p_corner_add_one,
            omega,
          end,
        have zero_le_p_corner_floor : 0 ≤ p_corner_floor := by linarith,
        have p_corner_floor_to_nat_eq_self : ↑p_corner_floor.to_nat = p_corner_floor := int.to_nat_of_nonneg zero_le_p_corner_floor,
        have cast_p_corner_floor_to_nat_eq_self : ↑p_corner_floor.to_nat = (↑p_corner_floor : ℝ) := 
          by exact_mod_cast p_corner_floor_to_nat_eq_self,
        have one_le_s : 1 ≤ s := 
          begin
            rcases nat_eq_or_lt_or_gt s 0 with s_eq_zero | s_lt_zero | s_gt_zero,
            { exfalso,
              exact s_ne_zero s_eq_zero,
            },
            { exfalso,
              exact nat.not_lt_zero s s_lt_zero,
            },
            clear_except s_gt_zero,
            have zero_lt_s : 0 < s := by linarith,
            omega,
          end,
        rw [nat.add_sub_assoc one_le_s, nat.cast_add (s * p_corner_floor.to_nat) (s - 1), nat.cast_sub one_le_s, nat.cast_mul,
          cast_p_corner_floor_to_nat_eq_self, p_corner_def, ← add_sub_assoc, nat.cast_one],
      },
      rename s_val_eq_zero s_val_ne_zero,
      rcases s_finset_range s_val_in_s_finset with ⟨zero_le_s_val, s_val_lt_one⟩,
      rw s_finset at s_val_in_s_finset,
      simp only [exists_prop, finset.mem_map, function.embedding.coe_fn_mk, finset.mem_range] at s_val_in_s_finset,
      rcases s_val_in_s_finset with ⟨s_val_num, s_val_num_lt_s, s_val_num_div_s_eq_s_val⟩,
      use ↑s_val_num + ↑s - 1,
      rcases nat_eq_or_lt_or_gt s_val_num 0 with s_val_num_eq_zero | s_val_num_lt_zero | s_val_num_gt_zero,
      { exfalso,
        rw s_val_num_eq_zero at s_val_num_div_s_eq_s_val,
        simp only [zero_div, nat.cast_zero] at s_val_num_div_s_eq_s_val,
        symmetry' at s_val_num_div_s_eq_s_val,
        exact s_val_ne_zero s_val_num_div_s_eq_s_val,
      },
      { exfalso,
        clear_except s_val_num_lt_zero,
        linarith,
      },
      have one_le_s_val_num : 1 ≤ s_val_num := by {clear_except s_val_num_gt_zero, omega},
      have one_le_s_add_s_val_num : 1 ≤ ↑s_val_num + ↑s := by linarith,
      have cast_s_ne_zero : ↑s ≠ (0 : ℝ) := by exact_mod_cast s_ne_zero,
      have p_corner_floor_eq_zero : p_corner_floor = 0 :=
        begin
          rcases eq_or_lt_or_gt p_corner_floor 0 with p_corner_floor_eq_zero | p_corner_floor_lt_zero | p_corner_floor_gt_zero,
          exact p_corner_floor_eq_zero,
          { have p_corner_floor_le_neg_one : p_corner_floor ≤ -1 := by {clear_except p_corner_floor_lt_zero, omega},
            have cast_p_corner_floor_le_neg_one : ↑p_corner_floor ≤ (-1 : ℝ) := by exact_mod_cast p_corner_floor_le_neg_one,
            linarith,
          },
          have one_le_p_corner_floor : 1 ≤ p_corner_floor := by {clear_except p_corner_floor_gt_zero, omega},
          have cast_one_le_p_corner_floor : (1 : ℝ) ≤ ↑p_corner_floor := by exact_mod_cast one_le_p_corner_floor,
          have zero_ne_s_val : 0 ≠ s_val := by {intro zero_eq_s_val, symmetry' at zero_eq_s_val, exact s_val_ne_zero zero_eq_s_val},
          have zero_lt_s_val : 0 < s_val := lt_of_le_of_ne zero_le_s_val zero_ne_s_val,
          linarith,
        end,
      have cast_p_corner_floor_eq_zero : ↑p_corner_floor = (0 : ℝ) := by exact_mod_cast p_corner_floor_eq_zero,
      rw ← s_val_num_div_s_eq_s_val at p_corner_def,
      rw [nat.cast_sub one_le_s_add_s_val_num, p_corner_def, mul_add, mul_div_of_ne_zero ↑s_val_num cast_s_ne_zero, cast_p_corner_floor_eq_zero],
      simp only [nat.cast_id, nat.cast_add, zero_add, nat.cast_one, mul_zero],
    end,
  have each_coord_lt_double_s : ∀ i : fin d, classical.some (each_coord_is_nat i) < 2 * s :=
    begin
      intro i,
      have cast_goal : ↑(classical.some (each_coord_is_nat i)) < (2 : ℝ) * ↑s :=
        begin
          rw classical.some_spec (each_coord_is_nat i),
          replace p_in_p_corner := p_in_p_corner i,
          rcases p_in_p_corner with ⟨p_corner_le_p, p_lt_p_corner_add_one⟩,
          have p_le_one : vector.nth (↑p : point d) i ≤ (1 : ℝ) :=
            begin
              cases p.property i with p_property unneeded,
              simp only [subtype.val_eq_coe] at p_property,
              cases p_property i.property with p_eq_zero p_eq_one,
              { rw p_eq_zero,
                linarith,
              },
              rw p_eq_one,
            end,
          have p_corner_le_one : vector.nth p_corner i ≤ 1 := by linarith,
          have zero_le_p : (0 : ℝ) ≤ vector.nth (↑p : point d) i :=
            begin
              cases p.property i with p_property unneeded,
              simp only [subtype.val_eq_coe] at p_property,
              cases p_property i.property with p_eq_zero p_eq_one,
              rw p_eq_zero,
              rw p_eq_one,
              linarith,
            end,
          have neg_one_le_p_corner : -1 ≤ vector.nth p_corner i := by linarith,
          have zero_le_cast_s : (0 : ℝ) ≤ ↑s := by exact_mod_cast (zero_le s),
          have goal_sans_sub_one : ↑s * vector.nth p_corner i + ↑s ≤ 2 * ↑s :=
            begin
              rw mul_comm (2 : ℝ) ↑s,
              convert_to ↑s * vector.nth p_corner i + ↑s * 1 ≤ ↑s * 2, rw mul_one,
              rw ← mul_add,
              apply mul_le_mul, exact le_refl ↑s, linarith, linarith, exact zero_le_cast_s,
            end,
          clear_except goal_sans_sub_one,
          linarith,
        end,
      exact_mod_cast cast_goal,
    end,
  use vector.of_fn (λ i, ⟨classical.some (each_coord_is_nat i), each_coord_lt_double_s i⟩),
  intro i,
  simp only [vector.nth_of_fn],
  rw classical.some_spec (each_coord_is_nat i),
end

noncomputable def build_goal_clique_with_info_map_fn {d s : ℕ} (d_ne_zero : d ≠ 0) (s_ne_zero : s ≠ 0) (T : set (point d)) (T_is_tiling : is_tiling T)
  (T_faceshare_free : tiling_faceshare_free T) (T_is_periodic : is_periodic T_is_tiling) (T_is_s_discrete : is_s_discrete s T) (T_shifted : set (point d))
  (T_shifted_is_tiling : is_tiling T_shifted) (T_shifted_faceshare_free : tiling_faceshare_free T_shifted)
  (T_shifted_contains_only_s_points : 
    ∀ (i : fin d) (p : point d), p ∈ T_shifted → (∃ (s_val : ℝ) (H : s_val ∈ s_finset s_ne_zero), eq_mod_one (vector.nth p i) s_val))
  (core_points_finset : 
    finset {p : point d // ∀ (j : fin d), (j.val < d → vector.nth p j = 0 ∨ vector.nth p j = 1) ∧ (j.val ≥ d → vector.nth p j = 0)})
  (core_points_finset_card : core_points_finset.card = 2 ^ d)
  (core_points_finset_property : 
    ∀ (p : point d) (h : ∀ (j : fin d), (j.val < d → vector.nth p j = 0 ∨ vector.nth p j = 1) ∧ (j.val ≥ d → vector.nth p j = 0)),
      (⟨p, h⟩ : {p : point d // ∀ (j : fin d), (j.val < d → vector.nth p j = 0 ∨ vector.nth p j = 1) ∧ (j.val ≥ d → vector.nth p j = 0)}) ∈ core_points_finset) : 
  {p : point d // ∀ (j : fin d), (j.val < d → vector.nth p j = 0 ∨ vector.nth p j = 1) ∧ (j.val ≥ d → vector.nth p j = 0)} →
  {v : vector (fin (2*s)) d // ∃ p : point d, is_core_point p ∧ ∃ p_corner ∈ T_shifted, 
    p ∈ cube p_corner ∧ (∀ alt_corner : point d, alt_corner ∈ T_shifted → p ∈ cube alt_corner → alt_corner = p_corner) ∧
    (∀ i : fin d, ↑s * (vector.nth p_corner i) + ↑s - 1 = (vector.nth v i).val)} :=
begin
  intro p,
  use classical.some 
    (goal_clique_with_info_map_fn_yields_fin_double_s_vector d_ne_zero s_ne_zero T T_is_tiling T_faceshare_free T_is_periodic T_is_s_discrete T_shifted
      T_shifted_is_tiling T_shifted_faceshare_free T_shifted_contains_only_s_points core_points_finset core_points_finset_card
      core_points_finset_property p),
  let res := classical.some 
    (goal_clique_with_info_map_fn_yields_fin_double_s_vector d_ne_zero s_ne_zero T T_is_tiling T_faceshare_free T_is_periodic T_is_s_discrete T_shifted
      T_shifted_is_tiling T_shifted_faceshare_free T_shifted_contains_only_s_points core_points_finset core_points_finset_card
      core_points_finset_property p),
  have res_def : res = classical.some 
    (goal_clique_with_info_map_fn_yields_fin_double_s_vector d_ne_zero s_ne_zero T T_is_tiling T_faceshare_free T_is_periodic T_is_s_discrete T_shifted
      T_shifted_is_tiling T_shifted_faceshare_free T_shifted_contains_only_s_points core_points_finset core_points_finset_card
      core_points_finset_property p) := by refl,
  rw ← res_def,
  have res_property := classical.some_spec
    (goal_clique_with_info_map_fn_yields_fin_double_s_vector d_ne_zero s_ne_zero T T_is_tiling T_faceshare_free T_is_periodic T_is_s_discrete T_shifted
      T_shifted_is_tiling T_shifted_faceshare_free T_shifted_contains_only_s_points core_points_finset core_points_finset_card
      core_points_finset_property p),
  rw ← res_def at res_property,
  let p_corner := (point_to_corner T_shifted_is_tiling p).val,
  have p_corner_def : p_corner = (point_to_corner T_shifted_is_tiling p).val := by refl,
  have p_corner_property := (point_to_corner T_shifted_is_tiling p).property,
  rw ← p_corner_def at p_corner_property,
  rcases p_corner_property with ⟨p_corner_in_T_shifted, p_in_p_corner, p_corner_unique⟩,
  use [p.val, (λ i, (and.elim_left (p.property i)) i.property), p_corner, p_corner_in_T_shifted, p_in_p_corner, p_corner_unique],
  intro i,
  symmetry,
  exact res_property i,
end

lemma periodic_tiling_implies_clique_helper {d s : ℕ} (d_ne_zero : d ≠ 0) (s_ne_zero : s ≠ 0) (T : set (point d)) (T_is_tiling : is_tiling T)
  (T_faceshare_free : tiling_faceshare_free T) (T_is_periodic : is_periodic T_is_tiling) (T_is_s_discrete : is_s_discrete s T)
  (T_shifted : set (point d)) (T_shifted_is_tiling : is_tiling T_shifted) (T_shifted_faceshare_free : tiling_faceshare_free T_shifted)
  (T_shifted_is_periodic : is_periodic T_shifted_is_tiling)
  (T_shifted_contains_only_s_points : 
    ∀ (i : fin d) (p : point d), p ∈ T_shifted → (∃ (s_val : ℝ) (H : s_val ∈ s_finset s_ne_zero), eq_mod_one (vector.nth p i) s_val))
  (core_points_finset : 
    finset {p : point d // ∀ (j : fin d), (j.val < d → vector.nth p j = 0 ∨ vector.nth p j = 1) ∧ (j.val ≥ d → vector.nth p j = 0)})
  (core_points_finset_card : core_points_finset.card = 2 ^ d)
  (core_points_finset_property : 
    ∀ (p : point d) (h : ∀ (j : fin d), (j.val < d → vector.nth p j = 0 ∨ vector.nth p j = 1) ∧ (j.val ≥ d → vector.nth p j = 0)),
    (⟨p, h⟩ : {p : point d // ∀ (j : fin d), (j.val < d → vector.nth p j = 0 ∨ vector.nth p j = 1) ∧ (j.val ≥ d → vector.nth p j = 0)}) 
    ∈ core_points_finset)
  (goal_clique_with_info_map : 
    {p : point d // ∀ (j : fin d), (j.val < d → vector.nth p j = 0 ∨ vector.nth p j = 1) ∧ (j.val ≥ d → vector.nth p j = 0)} ↪
    {v : vector (fin (2*s)) d // ∃ (p : point d), is_core_point p ∧ ∃ (p_corner : point d) (H : p_corner ∈ T_shifted), p ∈ cube p_corner ∧
      (∀ (alt_corner : point d), alt_corner ∈ T_shifted → p ∈ cube alt_corner → alt_corner = p_corner) ∧
      ∀ (i : fin d), ↑s * vector.nth p_corner i + ↑s - 1 = ↑((v.nth i).val)})
  (v1 v2 : vector (fin (2 * s)) d) (v1_ne_v2 : v1 ≠ v2) (v1' : vector (fin (2 * s)) d) (core_point1 : point d)
  (core_point1_is_core_point : is_core_point core_point1) (core_point1_corner : point d)
  (core_point1_corner_in_T_shifted : core_point1_corner ∈ T_shifted) (core_point1_in_core_point1_corner : core_point1 ∈ cube core_point1_corner)
  (core_point1_corner_unique : 
    ∀ (alt_corner : point d), alt_corner ∈ T_shifted → core_point1 ∈ cube alt_corner → alt_corner = core_point1_corner)
  (v2' : vector (fin (2 * s)) d) (core_point2 : point d) (core_point2_is_core_point : is_core_point core_point2) (core_point2_corner : point d)
  (core_point2_corner_in_T_shifted : core_point2_corner ∈ T_shifted) (core_point2_in_core_point2_corner : core_point2 ∈ cube core_point2_corner)
  (core_point2_corner_unique : ∀ (alt_corner : point d), alt_corner ∈ T_shifted → core_point2 ∈ cube alt_corner → alt_corner = core_point2_corner)
  (v2_def : v2' = v2) (v1_def : v1' = v1)
  (core_point1_corner_v1'_relationship : ∀ (i : fin d), ↑s * vector.nth core_point1_corner i + ↑s - 1 = ↑(↑(v1.nth i) : ℕ))
  (core_point2_corner_v2'_relationship : ∀ (i : fin d), ↑s * vector.nth core_point2_corner i + ↑s - 1 = ↑(↑(v2.nth i) : ℕ))
  (v1_not_adj_v2 : 
    (∀ (x : fin d), ↑(v1.nth x) = ↑(v2.nth x) + s → ∀ (x_1 : fin d), ¬v1.nth x_1 = v2.nth x_1 → x = x_1) ∧ 
    ∀ (x : fin d), ↑(v2.nth x) = ↑(v1.nth x) + s → ∀ (x_1 : fin d), ¬v2.nth x_1 = v1.nth x_1 → x = x_1)
  (v1_not_adj_v2_hyp_false : ¬∃ (i : fin d), ↑(v1.nth i) = ↑(v2.nth i) + s ∨ ↑(v2.nth i) = ↑(v1.nth i) + s) :
  let goal_clique_with_info : finset
        {v : vector (fin (2*s)) d // ∃ (p : point d),
           is_core_point p ∧
             ∃ (p_corner : point d) (H : p_corner ∈ T_shifted),
               p ∈ cube p_corner ∧
                 (∀ (alt_corner : point d),
                      alt_corner ∈ T_shifted →
                      p ∈ cube alt_corner → alt_corner = p_corner) ∧
                   ∀ (i : fin d),
                     ↑s * vector.nth p_corner i + ↑s - 1 =
                       ↑((v.nth i).val)} :=
        finset.map goal_clique_with_info_map core_points_finset
  in false :=
begin
  intros goal_clique_with_info,
  simp only [not_exists] at v1_not_adj_v2_hyp_false,
  have core_point1_corner_ne_core_point2_corner_add_or_sub_1 :
    ∀ i : fin d, core_point1_corner.nth i ≠ core_point2_corner.nth i + 1 ∧ core_point2_corner.nth i ≠ core_point1_corner.nth i + 1 :=
    begin
      intro i,
      replace v1_not_adj_v2_hyp_false := v1_not_adj_v2_hyp_false i,
      rw not_or_distrib at v1_not_adj_v2_hyp_false,
      cases v1_not_adj_v2_hyp_false with v1_ne_v2_add_s v2_ne_v1_add_s,
      replace core_point1_corner_v1'_relationship := core_point1_corner_v1'_relationship i,
      replace core_point2_corner_v2'_relationship := core_point2_corner_v2'_relationship i,
      have real_v1_ne_v2_add_s : (↑(↑(v1.nth i) : ℕ) : ℝ) ≠ (↑(↑(v2.nth i) : ℕ) : ℝ) + ↑s := by exact_mod_cast v1_ne_v2_add_s,
      have real_v2_ne_v1_add_s : (↑(↑(v2.nth i) : ℕ) : ℝ) ≠ (↑(↑(v1.nth i) : ℕ) : ℝ) + ↑s := by exact_mod_cast v2_ne_v1_add_s,
      rw [← core_point1_corner_v1'_relationship, ← core_point2_corner_v2'_relationship, add_sub_assoc, add_sub_assoc,
        add_comm (↑s * vector.nth core_point1_corner i) (↑s - 1), 
        add_comm (↑s * vector.nth core_point2_corner i) (↑s - 1),
        add_assoc] at real_v1_ne_v2_add_s real_v2_ne_v1_add_s,
      simp only [ne.def, add_right_inj] at real_v1_ne_v2_add_s real_v2_ne_v1_add_s,
      have rw1 : ↑s * vector.nth core_point1_corner i + ↑s = ↑s * vector.nth core_point1_corner i + ↑s * (1 : ℝ) := by rw mul_one,
      have rw2 : ↑s * vector.nth core_point2_corner i + ↑s = ↑s * vector.nth core_point2_corner i + ↑s * (1 : ℝ) := by rw mul_one,
      rw rw1 at real_v2_ne_v1_add_s,
      rw rw2 at real_v1_ne_v2_add_s,
      rw ← mul_add at real_v1_ne_v2_add_s real_v2_ne_v1_add_s,
      simp only [mul_eq_mul_left_iff, nat.cast_eq_zero] at real_v1_ne_v2_add_s real_v2_ne_v1_add_s,
      rw not_or_distrib at real_v1_ne_v2_add_s real_v2_ne_v1_add_s,
      exact ⟨real_v1_ne_v2_add_s.1, real_v2_ne_v1_add_s.1⟩,
    end,
  let z : int_point d := vector.of_fn
    (λ i, if(core_point1_corner.nth i < core_point2_corner.nth i + 1 ∧ core_point2_corner.nth i < core_point1_corner.nth i + 1) then 0
          else if(core_point2_corner.nth i >= core_point1_corner.nth i + 1) then 1
          else -1),
  let int_core_point1 : int_point d := vector.of_fn (λ i, if(core_point1.nth i = 0) then 0 else 1),
  have int_point_to_point_int_core_point1_eq_core_point1 : int_point_to_point int_core_point1 = core_point1 :=
    begin
      apply vector.ext,
      intro i,
      rw int_point_to_point,
      dsimp only[int_core_point1],
      simp only [vector.nth_of_fn],
      cases core_point1_is_core_point i with core_point1_eq_zero core_point1_eq_one,
      rw [if_pos core_point1_eq_zero, core_point1_eq_zero], refl,
      have core_point1_ne_zero : core_point1.nth i ≠ 0 := by {rw core_point1_eq_one, norm_num},
      rw [if_neg core_point1_ne_zero, core_point1_eq_one],
      norm_num,
    end,
  replace T_shifted_is_periodic := T_shifted_is_periodic int_core_point1 z,
  let core_point1_add_double_z_corner := (int_point_to_corner T_shifted_is_tiling (add_int_vectors int_core_point1 (double_int_vector z))).val,
  have core_point1_add_double_z_corner_def : 
    core_point1_add_double_z_corner = (int_point_to_corner T_shifted_is_tiling (add_int_vectors int_core_point1 (double_int_vector z))).val := by refl,
  have core_point1_add_double_z_corner_property := (int_point_to_corner T_shifted_is_tiling (add_int_vectors int_core_point1 (double_int_vector z))).property,
  rw ← core_point1_add_double_z_corner_def at core_point1_add_double_z_corner_property,
  rcases core_point1_add_double_z_corner_property with 
    ⟨core_point1_add_double_z_corner_in_T_shifted, core_point1_add_double_z_in_core_point1_add_double_z_corner, core_point1_add_double_z_corner_unique⟩,
  let shared_point : point d := vector.of_fn 
    (λ i, if(core_point2_corner.nth i >= core_point1_add_double_z_corner.nth i) then core_point2_corner.nth i else core_point1_add_double_z_corner.nth i),
  rcases T_shifted_is_tiling shared_point with ⟨unique_corner, unique_corner_in_T_shifted, shared_point_in_unique_corner, unique_corner_unique⟩,
  have shared_point_in_core_point1_add_double_z_corner : shared_point ∈ cube core_point1_add_double_z_corner :=
    begin
      rw cube,
      simp only [set.mem_set_of_eq],
      rw in_cube,
      simp only [vector.nth_of_fn, ge_iff_le, not_exists],
      intro i,
      replace core_point1_corner_ne_core_point2_corner_add_or_sub_1 := core_point1_corner_ne_core_point2_corner_add_or_sub_1 i,
      split,
      { by_cases h : vector.nth core_point1_add_double_z_corner i ≤ vector.nth core_point2_corner i,
        { rw if_pos h,
          exact h,
        },
        rw if_neg h,
      },
      by_cases h : vector.nth core_point1_add_double_z_corner i ≤ vector.nth core_point2_corner i,
      { rw if_pos h,
        have int_core_point1_corner_eq_core_point1_corner : ↑(int_point_to_corner T_shifted_is_tiling int_core_point1) = core_point1_corner :=
          begin
            rw ← subtype.val_eq_coe,
            rcases (int_point_to_corner T_shifted_is_tiling int_core_point1).property with
              ⟨int_core_point1_corner_in_T_shifted, int_core_point1_in_int_core_point1_corner, int_core_point1_corner_unique⟩,
            conv at int_core_point1_in_int_core_point1_corner
            begin
              find (int_point_to_point int_core_point1) {rw int_point_to_point_int_core_point1_eq_core_point1},
            end,
            exact core_point1_corner_unique (int_point_to_corner T_shifted_is_tiling int_core_point1).val int_core_point1_corner_in_T_shifted
              int_core_point1_in_int_core_point1_corner,
          end,
        rw [core_point1_add_double_z_corner_def, T_shifted_is_periodic, double_int_vector, add_vectors],
        conv
        begin
          find (int_point_to_point _) {rw int_point_to_point},
        end,
        simp only [subtype.val_eq_coe, vector.nth_of_fn, ge_iff_le, mul_ite, mul_zero, mul_one, mul_neg],
        by_cases z_eq_zero : vector.nth core_point1_corner i < vector.nth core_point2_corner i + 1 ∧ vector.nth core_point2_corner i < vector.nth core_point1_corner i + 1,
        { rw [if_pos z_eq_zero, int.cast_zero, add_zero, int_core_point1_corner_eq_core_point1_corner],
          exact z_eq_zero.2,
        },
        rename z_eq_zero z_ne_zero,
        rw cube at core_point1_in_core_point1_corner core_point2_in_core_point2_corner,
        simp only [set.mem_set_of_eq] at core_point1_in_core_point1_corner core_point2_in_core_point2_corner,
        rw in_cube at core_point1_in_core_point1_corner core_point2_in_core_point2_corner,
        replace core_point1_in_core_point1_corner := core_point1_in_core_point1_corner i,
        replace core_point2_in_core_point2_corner := core_point2_in_core_point2_corner i,
        by_cases z_eq_one : vector.nth core_point2_corner i ≥ vector.nth core_point1_corner i + 1,
        { rw [if_neg z_ne_zero, if_pos z_eq_one, int.cast_bit0, int.cast_one, int_core_point1_corner_eq_core_point1_corner],
          have core_point2_le_one := le_one_of_is_core_point i core_point2_is_core_point,
          have core_point1_ge_zero := ge_zero_of_is_core_point i core_point1_is_core_point,
          linarith,
        },
        rename z_eq_one z_ne_one,
        rw [if_neg z_ne_zero, if_neg z_ne_one, int.cast_neg, int.cast_bit0, int.cast_one, int_core_point1_corner_eq_core_point1_corner],
        rw [not_and_distrib, not_lt, not_lt] at z_ne_zero,
        cases z_ne_zero with core_point2_corner_add_one_le_core_point1_corner core_point1_corner_add_one_le_core_point2_corner,
        { cases lt_or_eq_of_le core_point2_corner_add_one_le_core_point1_corner with goal core_point2_corner_add_one_eq_core_point1_corner,
          linarith,
          exfalso,
          symmetry' at core_point2_corner_add_one_eq_core_point1_corner,
          exact core_point1_corner_ne_core_point2_corner_add_or_sub_1.1 core_point2_corner_add_one_eq_core_point1_corner,
        },
        linarith,
      },
      rw if_neg h,
      norm_num,
    end,
  have core_point1_add_double_z_corner_eq_unique_corner := 
    unique_corner_unique core_point1_add_double_z_corner core_point1_add_double_z_corner_in_T_shifted shared_point_in_core_point1_add_double_z_corner,
  have shared_point_in_core_point2_corner : shared_point ∈ cube core_point2_corner :=
    begin
      rw cube,
      simp only [set.mem_set_of_eq],
      rw in_cube,
      simp only [vector.nth_of_fn, ge_iff_le, not_exists],
      intro i,
      replace core_point1_corner_ne_core_point2_corner_add_or_sub_1 := core_point1_corner_ne_core_point2_corner_add_or_sub_1 i,
      split,
      { by_cases h : vector.nth core_point1_add_double_z_corner i ≤ vector.nth core_point2_corner i,
        rw if_pos h,
        rw if_neg h,
        simp only [not_le] at h,
        exact le_of_lt h,
      },
      by_cases h : vector.nth core_point1_add_double_z_corner i ≤ vector.nth core_point2_corner i,
      { rw if_pos h,
        norm_num,
      },
      rw if_neg h,
      have int_core_point1_corner_eq_core_point1_corner : ↑(int_point_to_corner T_shifted_is_tiling int_core_point1) = core_point1_corner :=
        begin
          rw ← subtype.val_eq_coe,
          rcases (int_point_to_corner T_shifted_is_tiling int_core_point1).property with
            ⟨int_core_point1_corner_in_T_shifted, int_core_point1_in_int_core_point1_corner, int_core_point1_corner_unique⟩,
          conv at int_core_point1_in_int_core_point1_corner
          begin
            find (int_point_to_point int_core_point1) {rw int_point_to_point_int_core_point1_eq_core_point1},
          end,
          exact core_point1_corner_unique (int_point_to_corner T_shifted_is_tiling int_core_point1).val int_core_point1_corner_in_T_shifted
            int_core_point1_in_int_core_point1_corner,
        end,
      rw [core_point1_add_double_z_corner_def, T_shifted_is_periodic, double_int_vector, add_vectors],
      conv
      begin
        find (int_point_to_point _) {rw int_point_to_point},
      end,
      simp only [subtype.val_eq_coe, vector.nth_of_fn, ge_iff_le, mul_ite, mul_zero, mul_one, mul_neg],
      by_cases z_eq_zero : vector.nth core_point1_corner i < vector.nth core_point2_corner i + 1 ∧ vector.nth core_point2_corner i < vector.nth core_point1_corner i + 1,
      { rw [if_pos z_eq_zero, int.cast_zero, add_zero, int_core_point1_corner_eq_core_point1_corner],
        exact z_eq_zero.1,
      },
      rename z_eq_zero z_ne_zero,
      rw cube at core_point1_in_core_point1_corner core_point2_in_core_point2_corner,
      simp only [set.mem_set_of_eq] at core_point1_in_core_point1_corner core_point2_in_core_point2_corner,
      rw in_cube at core_point1_in_core_point1_corner core_point2_in_core_point2_corner,
      replace core_point1_in_core_point1_corner := core_point1_in_core_point1_corner i,
      replace core_point2_in_core_point2_corner := core_point2_in_core_point2_corner i,
      by_cases z_eq_one : vector.nth core_point2_corner i ≥ vector.nth core_point1_corner i + 1,
      { rw [if_neg z_ne_zero, if_pos z_eq_one, int.cast_bit0, int.cast_one, int_core_point1_corner_eq_core_point1_corner],
        rw [not_and_distrib, not_lt, not_lt] at z_ne_zero,
        cases z_ne_zero with core_point2_corner_add_one_le_core_point1_corner core_point1_corner_add_one_le_core_point2_corner,
        linarith,
        cases lt_or_eq_of_le core_point1_corner_add_one_le_core_point2_corner with goal core_point1_corner_add_one_eq_core_point2_corner,
        linarith,
        exfalso,
        symmetry' at core_point1_corner_add_one_eq_core_point2_corner,
        exact core_point1_corner_ne_core_point2_corner_add_or_sub_1.2 core_point1_corner_add_one_eq_core_point2_corner,
      },
      rename z_eq_one z_ne_one,
      rw [if_neg z_ne_zero, if_neg z_ne_one, int.cast_neg, int.cast_bit0, int.cast_one, int_core_point1_corner_eq_core_point1_corner],
      have core_point2_ge_zero := ge_zero_of_is_core_point i core_point2_is_core_point,
      have core_point2_le_one := le_one_of_is_core_point i core_point1_is_core_point,
      linarith,
    end,
  have core_point2_corner_eq_unique_corner := 
    unique_corner_unique core_point2_corner core_point2_corner_in_T_shifted shared_point_in_core_point2_corner,
  have core_point2_corner_eq_core_point1_add_double_z_corner : core_point2_corner = core_point1_add_double_z_corner :=
    by rw [core_point1_add_double_z_corner_eq_unique_corner, core_point2_corner_eq_unique_corner],
  by_cases core_point1_eq_core_point2 : core_point1 = core_point2,
  { have v1_eq_v2 : v1 = v2 :=
      begin
        apply vector.ext,
        intro i,
        have cast_cast_goal : (↑(↑(v1.nth i) : ℕ) : ℝ) = (↑(↑(v2.nth i) : ℕ) : ℝ) :=
          begin
            rw [← core_point1_corner_v1'_relationship i, ← core_point2_corner_v2'_relationship i],
            simp only [sub_left_inj, add_left_inj, mul_eq_mul_left_iff, nat.cast_eq_zero],
            left,
            rw core_point1_eq_core_point2 at core_point1_in_core_point1_corner,
            rw core_point2_corner_unique core_point1_corner core_point1_corner_in_T_shifted core_point1_in_core_point1_corner,
          end,
        have cast_goal : (↑(v1.nth i) : ℕ) = (↑(v2.nth i) : ℕ) := by exact_mod_cast cast_cast_goal,
        apply fin.eq_of_veq,
        simp only [fin.val_eq_coe],
        exact_mod_cast cast_goal,
      end,
    exact v1_ne_v2 v1_eq_v2,
  },
  have core_point1_ne_core_point2 : ∃ i : fin d, core_point1.nth i ≠ core_point2.nth i :=
    begin
      by_contra h,
      simp only [not_exists_not] at h,
      exact core_point1_eq_core_point2 (vector.ext h),
    end,
  cases core_point1_ne_core_point2 with i core_point1_ne_core_point2,
  replace core_point1_is_core_point := core_point1_is_core_point i,
  replace core_point2_is_core_point := core_point2_is_core_point i,
  rw cube at core_point1_in_core_point1_corner core_point2_in_core_point2_corner core_point1_add_double_z_in_core_point1_add_double_z_corner,
  simp only [set.mem_set_of_eq] at core_point1_in_core_point1_corner core_point2_in_core_point2_corner core_point1_add_double_z_in_core_point1_add_double_z_corner,
  rw in_cube at core_point1_in_core_point1_corner core_point2_in_core_point2_corner core_point1_add_double_z_in_core_point1_add_double_z_corner,
  replace core_point1_in_core_point1_corner := core_point1_in_core_point1_corner i,
  replace core_point2_in_core_point2_corner := core_point2_in_core_point2_corner i,
  replace core_point1_add_double_z_in_core_point1_add_double_z_corner := core_point1_add_double_z_in_core_point1_add_double_z_corner i,
  cases core_point1_in_core_point1_corner with core_point1_corner_le_core_point1 core_point1_lt_core_point1_corner_add_one,
  cases core_point2_in_core_point2_corner with core_point2_corner_le_core_point2 core_point2_lt_core_point2_corner_add_one,
  rw [int_point_to_point, add_int_vectors, double_int_vector] at core_point1_add_double_z_in_core_point1_add_double_z_corner,
  simp only [vector.nth_of_fn, ge_iff_le, mul_ite, mul_zero, mul_one, mul_neg, int.cast_add] at core_point1_add_double_z_in_core_point1_add_double_z_corner,
  cases core_point1_is_core_point with core_point1_eq_zero core_point1_eq_one,
  { cases core_point2_is_core_point with core_point2_eq_zero core_point2_eq_one,
    { rw [core_point1_eq_zero, core_point2_eq_zero] at core_point1_ne_core_point2,
      exact core_point1_ne_core_point2 (by refl),
    },
    rw if_pos core_point1_eq_zero at core_point1_add_double_z_in_core_point1_add_double_z_corner,
    simp only [int.cast_zero, zero_add] at core_point1_add_double_z_in_core_point1_add_double_z_corner,
    rw ← core_point2_corner_eq_core_point1_add_double_z_corner at core_point1_add_double_z_in_core_point1_add_double_z_corner,
    by_cases h1 : vector.nth core_point1_corner i < vector.nth core_point2_corner i + 1 ∧ vector.nth core_point2_corner i < vector.nth core_point1_corner i + 1,
    { rw if_pos h1 at core_point1_add_double_z_in_core_point1_add_double_z_corner,
      simp only [int.cast_zero] at core_point1_add_double_z_in_core_point1_add_double_z_corner,
      linarith,
    },
    rw if_neg h1 at core_point1_add_double_z_in_core_point1_add_double_z_corner,
    by_cases h2 : vector.nth core_point1_corner i + 1 ≤ vector.nth core_point2_corner i,
    { rw if_pos h2 at core_point1_add_double_z_in_core_point1_add_double_z_corner,
      simp only [int.cast_bit0, int.cast_one] at core_point1_add_double_z_in_core_point1_add_double_z_corner,
      linarith,
    },
    rw if_neg h2 at core_point1_add_double_z_in_core_point1_add_double_z_corner,
    simp only [int.cast_neg, int.cast_bit0, int.cast_one] at core_point1_add_double_z_in_core_point1_add_double_z_corner,
    linarith,
  },
  cases core_point2_is_core_point with core_point2_eq_zero core_point2_eq_one,
  { have core_point1_ne_zero : core_point1.nth i ≠ 0 := by {rw core_point1_eq_one, norm_num},
    rw if_neg core_point1_ne_zero at core_point1_add_double_z_in_core_point1_add_double_z_corner,
    simp only [int.cast_one] at core_point1_add_double_z_in_core_point1_add_double_z_corner,
    rw ← core_point2_corner_eq_core_point1_add_double_z_corner at core_point1_add_double_z_in_core_point1_add_double_z_corner,
    by_cases h1 : vector.nth core_point1_corner i < vector.nth core_point2_corner i + 1 ∧ vector.nth core_point2_corner i < vector.nth core_point1_corner i + 1,
    { rw if_pos h1 at core_point1_add_double_z_in_core_point1_add_double_z_corner,
      simp only [int.cast_zero, add_zero, lt_add_iff_pos_left] at core_point1_add_double_z_in_core_point1_add_double_z_corner,
      linarith,
    },
    rw if_neg h1 at core_point1_add_double_z_in_core_point1_add_double_z_corner,
    by_cases h2 : vector.nth core_point1_corner i + 1 ≤ vector.nth core_point2_corner i,
    { rw if_pos h2 at core_point1_add_double_z_in_core_point1_add_double_z_corner,
      simp only [int.cast_bit0, int.cast_one] at core_point1_add_double_z_in_core_point1_add_double_z_corner,
      linarith,
    },
    rw if_neg h2 at core_point1_add_double_z_in_core_point1_add_double_z_corner,
    simp only [int.cast_neg, int.cast_bit0, int.cast_one, le_add_neg_iff_add_le, add_neg_lt_iff_le_add'] at core_point1_add_double_z_in_core_point1_add_double_z_corner,
    linarith,
  },
  rw [core_point1_eq_one, core_point2_eq_one] at core_point1_ne_core_point2,
  exact core_point1_ne_core_point2 (by refl),
end

theorem periodic_tiling_implies_clique {d : ℕ} {s : ℕ} (d_ne_zero : d ≠ 0) (s_ne_zero : s ≠ 0) :
  (∃ (T : set (point d)) (T_is_tiling : is_tiling T), tiling_faceshare_free T ∧ is_periodic T_is_tiling ∧ is_s_discrete s T) →
  has_clique (Keller_graph d s) (2 ^ d) :=
begin
  rintro ⟨T, T_is_tiling, T_faceshare_free, T_is_periodic, T_is_s_discrete⟩,
  rcases inductive_replacement_lemma d_ne_zero s_ne_zero T T_is_tiling T_faceshare_free T_is_periodic T_is_s_discrete with
    ⟨T_shifted, T_shifted_is_tiling, T_shifted_faceshare_free, T_shifted_is_periodic, T_shifted_contains_only_s_points⟩,
  have core_points_finset := build_core_points_finset ⟨d, lt_add_one d⟩,
  rcases core_points_finset with ⟨core_points_finset, core_points_finset_card, core_points_finset_property⟩,
  have goal_clique_with_info_map :
    {p : point d // ∀ (j : fin d), (j.val < d → vector.nth p j = 0 ∨ vector.nth p j = 1) ∧ (j.val ≥ d → vector.nth p j = 0)} ↪
    {v : vector (fin (2*s)) d // ∃ p : point d, is_core_point p ∧ ∃ p_corner ∈ T_shifted, 
      p ∈ cube p_corner ∧ (∀ alt_corner : point d, alt_corner ∈ T_shifted → p ∈ cube alt_corner → alt_corner = p_corner) ∧
      (∀ i : fin d, ↑s * (vector.nth p_corner i) + ↑s - 1 = (vector.nth v i).val)} :=
    begin
      let goal_clique_with_info_map_fn :
        {p : point d // ∀ (j : fin d), (j.val < d → vector.nth p j = 0 ∨ vector.nth p j = 1) ∧ (j.val ≥ d → vector.nth p j = 0)} →
        {v : vector (fin (2*s)) d // ∃ p : point d, is_core_point p ∧ ∃ p_corner ∈ T_shifted, 
          p ∈ cube p_corner ∧ (∀ alt_corner : point d, alt_corner ∈ T_shifted → p ∈ cube alt_corner → alt_corner = p_corner) ∧
          (∀ i : fin d, ↑s * (vector.nth p_corner i) + ↑s - 1 = (vector.nth v i).val)} :=
        build_goal_clique_with_info_map_fn d_ne_zero s_ne_zero T T_is_tiling T_faceshare_free T_is_periodic T_is_s_discrete T_shifted
          T_shifted_is_tiling T_shifted_faceshare_free T_shifted_contains_only_s_points core_points_finset core_points_finset_card
          core_points_finset_property,
      have goal_clique_with_info_map_fn_injective : function.injective goal_clique_with_info_map_fn :=
        begin
          rw function.injective,
          intros p1 p2 mapped_p1_eq_mapped_p2,
          dsimp[goal_clique_with_info_map_fn] at mapped_p1_eq_mapped_p2,
          rw build_goal_clique_with_info_map_fn at mapped_p1_eq_mapped_p2,
          simp only [subtype.val_eq_coe] at mapped_p1_eq_mapped_p2,
          let mapped_p1_statement :=
            goal_clique_with_info_map_fn_yields_fin_double_s_vector d_ne_zero s_ne_zero T T_is_tiling T_faceshare_free T_is_periodic T_is_s_discrete T_shifted
              T_shifted_is_tiling T_shifted_faceshare_free T_shifted_contains_only_s_points core_points_finset core_points_finset_card
              core_points_finset_property p1,
          let mapped_p2_statement :=
            goal_clique_with_info_map_fn_yields_fin_double_s_vector d_ne_zero s_ne_zero T T_is_tiling T_faceshare_free T_is_periodic T_is_s_discrete T_shifted
              T_shifted_is_tiling T_shifted_faceshare_free T_shifted_contains_only_s_points core_points_finset core_points_finset_card
              core_points_finset_property p2,
          change classical.some mapped_p1_statement = classical.some mapped_p2_statement at mapped_p1_eq_mapped_p2,
          let mapped_p1 := classical.some mapped_p1_statement,
          have mapped_p1_def : mapped_p1 = classical.some mapped_p1_statement := by refl,
          have mapped_p1_property := classical.some_spec mapped_p1_statement,
          rw ← mapped_p1_def at mapped_p1_property,
          let mapped_p2 := classical.some mapped_p2_statement,
          have mapped_p2_def : mapped_p2 = classical.some mapped_p2_statement := by refl,
          have mapped_p2_property := classical.some_spec mapped_p2_statement,
          rw ← mapped_p2_def at mapped_p2_property,
          rw [← mapped_p1_def, ← mapped_p2_def] at mapped_p1_eq_mapped_p2,
          let p1_corner := (point_to_corner T_shifted_is_tiling ↑p1).val,
          have p1_corner_def : p1_corner = (point_to_corner T_shifted_is_tiling ↑p1).val := by refl,
          have p1_corner_property := (point_to_corner T_shifted_is_tiling ↑p1).property,
          rw ← p1_corner_def at p1_corner_property,
          rcases p1_corner_property with ⟨p1_corner_in_T_shifted, p1_in_p1_corner, p1_corner_unique⟩,
          let p2_corner := (point_to_corner T_shifted_is_tiling ↑p2).val,
          have p2_corner_def : p2_corner = (point_to_corner T_shifted_is_tiling ↑p2).val := by refl,
          have p2_corner_property := (point_to_corner T_shifted_is_tiling ↑p2).property,
          rw ← p2_corner_def at p2_corner_property,
          rcases p2_corner_property with ⟨p2_corner_in_T_shifted, p2_in_p2_corner, p2_corner_unique⟩,
          have p1_corner_eq_p2_corner : p1_corner = p2_corner :=
            begin
              apply vector.ext,
              intro i,
              replace mapped_p1_property := mapped_p1_property i,
              replace mapped_p2_property := mapped_p2_property i,
              rw mapped_p1_eq_mapped_p2 at mapped_p1_property,
              rw [mapped_p1_property, ← p1_corner_def, ← p2_corner_def] at mapped_p2_property,
              simp only [add_left_inj, mul_eq_mul_left_iff, nat.cast_eq_zero, sub_left_inj, subtype.val_eq_coe] at mapped_p2_property,
              cases mapped_p2_property with goal s_eq_zero, exact goal,
              exfalso,
              exact s_ne_zero s_eq_zero,
            end,
          apply subtype.ext,
          apply vector.ext,
          intro i,
          by_contra p1_ne_p2_at_i,
          rcases p1.property i with ⟨p1_is_core_point, unneeded1⟩,
          rcases p2.property i with ⟨p2_is_core_point, unneeded2⟩,
          clear unneeded1 unneeded2,
          simp only [subtype.val_eq_coe] at p1_is_core_point p2_is_core_point,
          replace p1_is_core_point := p1_is_core_point i.property,
          replace p2_is_core_point := p2_is_core_point i.property,
          rw cube at p1_in_p1_corner p2_in_p2_corner,
          simp only [set.mem_set_of_eq] at p1_in_p1_corner p2_in_p2_corner,
          rw in_cube at p1_in_p1_corner p2_in_p2_corner,
          replace p1_in_p1_corner := p1_in_p1_corner i,
          replace p2_in_p2_corner := p2_in_p2_corner i,
          rw p1_corner_eq_p2_corner at p1_in_p1_corner,
          cases p1_in_p1_corner with p1_corner_le_p1 p1_lt_p1_corner_add_one,
          cases p2_in_p2_corner with p2_corner_le_p2 p2_lt_p2_corner_add_one,
          cases p1_is_core_point with p1_eq_zero p1_eq_one,
          { cases p2_is_core_point with p2_eq_zero p2_eq_one,
            { rw [p1_eq_zero, p2_eq_zero] at p1_ne_p2_at_i,
              exact p1_ne_p2_at_i (by refl),
            },
            rw p1_eq_zero at p1_corner_le_p1 p1_lt_p1_corner_add_one,
            rw p2_eq_one at p2_corner_le_p2 p2_lt_p2_corner_add_one,
            linarith,
          },
          cases p2_is_core_point with p2_eq_zero p2_eq_one,
          { rw p1_eq_one at p1_corner_le_p1 p1_lt_p1_corner_add_one,
            rw p2_eq_zero at p2_corner_le_p2 p2_lt_p2_corner_add_one,
            linarith,
          },
          rw [p1_eq_one, p2_eq_one] at p1_ne_p2_at_i,
          exact p1_ne_p2_at_i (by refl),
        end,
      exact {to_fun := goal_clique_with_info_map_fn, inj' := goal_clique_with_info_map_fn_injective},
    end,
  let goal_clique_with_info := finset.map goal_clique_with_info_map core_points_finset,
  have goal_clique_with_info_card : goal_clique_with_info.card = core_points_finset.card := finset.card_map goal_clique_with_info_map,
  rw core_points_finset_card at goal_clique_with_info_card,
  simp only [] at goal_clique_with_info_card,
  let remove_info_map :
    {v : vector (fin (2*s)) d // ∃ p : point d, is_core_point p ∧ ∃ p_corner ∈ T_shifted, 
      p ∈ cube p_corner ∧ (∀ alt_corner : point d, alt_corner ∈ T_shifted → p ∈ cube alt_corner → alt_corner = p_corner) ∧
      (∀ i : fin d, ↑s * (vector.nth p_corner i) + ↑s - 1 = (vector.nth v i).val)} ↪ vector (fin (2*s)) d :=
    begin
      let remove_info_map_fn :
        {v : vector (fin (2*s)) d // ∃ p : point d, is_core_point p ∧ ∃ p_corner ∈ T_shifted, 
          p ∈ cube p_corner ∧ (∀ alt_corner : point d, alt_corner ∈ T_shifted → p ∈ cube alt_corner → alt_corner = p_corner) ∧
          (∀ i : fin d, ↑s * (vector.nth p_corner i) + ↑s - 1 = (vector.nth v i).val)} → vector (fin (2*s)) d :=
        λ v, v,
      have remove_info_map_fn_injective : function.injective remove_info_map_fn :=
        by {rw function.injective, dsimp[remove_info_map_fn], simp},
      exact {to_fun := remove_info_map_fn, inj' := remove_info_map_fn_injective},
    end,
  let goal_clique := finset.map remove_info_map goal_clique_with_info,
  have goal_clique_card : goal_clique.card = goal_clique_with_info.card := finset.card_map remove_info_map,
  rw goal_clique_with_info_card at goal_clique_card,
  use [goal_clique, goal_clique_card],
  intros v1 v2 v1_in_goal_clique v2_in_goal_clique v1_ne_v2,
  rw Keller_graph,
  simp only [simple_graph.from_rel_adj, fin.val_eq_coe, exists_and_distrib_left, ne.def],
  split, exact v1_ne_v2,
  dsimp[goal_clique] at v1_in_goal_clique v2_in_goal_clique,
  rw finset.mem_map at v1_in_goal_clique v2_in_goal_clique,
  simp only [exists_prop, fin.val_eq_coe, finset.mem_map, ge_iff_le, subtype.exists] at v1_in_goal_clique v2_in_goal_clique,
  rcases v1_in_goal_clique with 
    ⟨v1', ⟨core_point1, core_point1_is_core_point, ⟨core_point1_corner, core_point1_corner_in_T_shifted, 
    core_point1_in_core_point1_corner, core_point1_corner_unique, core_point1_corner_v1'_relationship⟩⟩, redundant, v1_def⟩,
  clear redundant,
  rcases v2_in_goal_clique with 
    ⟨v2', ⟨core_point2, core_point2_is_core_point, ⟨core_point2_corner, core_point2_corner_in_T_shifted, 
    core_point2_in_core_point2_corner, core_point2_corner_unique, core_point2_corner_v2'_relationship⟩⟩, redundant, v2_def⟩,
  clear redundant,
  dsimp[remove_info_map] at v1_def v2_def,
  rw v1_def at core_point1_corner_v1'_relationship,
  rw v2_def at core_point2_corner_v2'_relationship,
  by_contra v1_not_adj_v2,
  rw not_or_distrib at v1_not_adj_v2,
  simp only [not_exists, not_and, not_not] at v1_not_adj_v2,
  by_cases v1_not_adj_v2_hyp : ∃ i : fin d, ↑(v1.nth i) = ↑(v2.nth i) + s ∨ ↑(v2.nth i) = ↑(v1.nth i) + s,
  { replace T_shifted_faceshare_free := T_shifted_faceshare_free core_point1_corner core_point1_corner_in_T_shifted
      core_point2_corner core_point2_corner_in_T_shifted,
    rw is_facesharing at T_shifted_faceshare_free,
    simp only [not_exists, not_and, not_forall] at T_shifted_faceshare_free,
    rcases v1_not_adj_v2_hyp with ⟨i, v1_eq_v2_add_s | v2_eq_v1_add_s⟩,
    { replace v1_not_adj_v2 := (and.elim_left v1_not_adj_v2) i v1_eq_v2_add_s,
      have core_point_corners_off_by_one : vector.nth core_point1_corner i - vector.nth core_point2_corner i = 1 :=
        begin
          replace core_point1_corner_v1'_relationship := core_point1_corner_v1'_relationship i,
          replace core_point2_corner_v2'_relationship := core_point2_corner_v2'_relationship i,
          rw v1_eq_v2_add_s at core_point1_corner_v1'_relationship,
          rw fin.coe_eq_val at core_point1_corner_v1'_relationship core_point2_corner_v2'_relationship,
          replace core_point1_corner_v1'_relationship : 
            ↑s * vector.nth core_point1_corner i + ↑s - (1 : ℝ) = ↑((v2.nth i).val) + ↑s := 
            by exact_mod_cast core_point1_corner_v1'_relationship,
          rw ← core_point2_corner_v2'_relationship at core_point1_corner_v1'_relationship,
          clear_except core_point1_corner_v1'_relationship s_ne_zero,
          rw add_comm (↑s * vector.nth core_point2_corner i + ↑s - 1) ↑s at core_point1_corner_v1'_relationship,
          rw [sub_eq_add_neg, sub_eq_add_neg, add_assoc (↑s * vector.nth core_point2_corner i) ↑s (-1), ← add_assoc,
            add_assoc (↑s * vector.nth core_point1_corner i) ↑s (-1)] at core_point1_corner_v1'_relationship,
          simp only [add_left_inj] at core_point1_corner_v1'_relationship,
          have s_times_goal : ↑s * vector.nth core_point1_corner i - ↑s * vector.nth core_point2_corner i = ↑s := by linarith,
          rw ← mul_sub_left_distrib at s_times_goal,
          have s_times_goal_div_s : ↑s * (vector.nth core_point1_corner i - vector.nth core_point2_corner i) / ↑s = ↑s / ↑s :=
            by rw s_times_goal,
          have cast_s_ne_zero : ↑s ≠ (0 : ℝ) := by exact_mod_cast s_ne_zero,
          rw [mul_div_cancel_left (vector.nth core_point1_corner i - vector.nth core_point2_corner i) cast_s_ne_zero, 
            div_self cast_s_ne_zero] at s_times_goal_div_s,
          exact s_times_goal_div_s,
        end,
      replace T_shifted_faceshare_free := T_shifted_faceshare_free i (or.inl core_point_corners_off_by_one),
      rcases T_shifted_faceshare_free with ⟨j, i_ne_j_and_core_point1_eq_core_point2_at_j⟩,
      rw not_or_distrib at i_ne_j_and_core_point1_eq_core_point2_at_j,
      cases i_ne_j_and_core_point1_eq_core_point2_at_j with i_ne_j core_point1_corner_ne_core_point2_corner_at_j,
      have v1_ne_v2_at_j : v1.nth j ≠ v2.nth j :=
        begin
          replace core_point1_corner_v1'_relationship := core_point1_corner_v1'_relationship j,
          replace core_point2_corner_v2'_relationship := core_point2_corner_v2'_relationship j,
          intro v1_eq_v2_at_j,
          rcases real_eq_or_lt_or_gt (core_point1_corner.nth j) (core_point2_corner.nth j) with
            core_point1_corner_eq_core_point2_corner | core_point1_corner_lt_core_point2_corner |
            core_point1_corner_gt_core_point2_corner,
          exact core_point1_corner_ne_core_point2_corner_at_j core_point1_corner_eq_core_point2_corner,
          { rw [v1_eq_v2_at_j, ← core_point2_corner_v2'_relationship] at core_point1_corner_v1'_relationship,
            simp only [add_left_inj, mul_eq_mul_left_iff, nat.cast_eq_zero, sub_left_inj] at core_point1_corner_v1'_relationship,
            cases core_point1_corner_v1'_relationship with core_point1_corner_eq_core_point2_corner s_eq_zero,
            { rw core_point1_corner_eq_core_point2_corner at core_point1_corner_lt_core_point2_corner,
              exact lt_irrefl (vector.nth core_point2_corner j) core_point1_corner_lt_core_point2_corner,
            },
            exact s_ne_zero s_eq_zero,
          },
          rw [v1_eq_v2_at_j, ← core_point2_corner_v2'_relationship] at core_point1_corner_v1'_relationship,
          simp only [add_left_inj, mul_eq_mul_left_iff, nat.cast_eq_zero, sub_left_inj] at core_point1_corner_v1'_relationship,
          cases core_point1_corner_v1'_relationship with core_point1_corner_eq_core_point2_corner s_eq_zero,
          { rw core_point1_corner_eq_core_point2_corner at core_point1_corner_gt_core_point2_corner,
            exact gt_irrefl (vector.nth core_point2_corner j) core_point1_corner_gt_core_point2_corner,
          },
          exact s_ne_zero s_eq_zero,
        end,
      exact i_ne_j (v1_not_adj_v2 j v1_ne_v2_at_j),
    }, --Next case is symmetrical to the above case
    replace v1_not_adj_v2 := (and.elim_right v1_not_adj_v2) i v2_eq_v1_add_s,
    have core_point_corners_off_by_one : vector.nth core_point2_corner i - vector.nth core_point1_corner i = 1 :=
      begin
        replace core_point1_corner_v1'_relationship := core_point1_corner_v1'_relationship i,
        replace core_point2_corner_v2'_relationship := core_point2_corner_v2'_relationship i,
        rw v2_eq_v1_add_s at core_point2_corner_v2'_relationship,
        rw fin.coe_eq_val at core_point1_corner_v1'_relationship core_point2_corner_v2'_relationship,
        replace core_point2_corner_v2'_relationship : 
          ↑s * vector.nth core_point2_corner i + ↑s - (1 : ℝ) = ↑((v1.nth i).val) + ↑s := 
          by exact_mod_cast core_point2_corner_v2'_relationship,
        rw ← core_point1_corner_v1'_relationship at core_point2_corner_v2'_relationship,
        clear_except core_point2_corner_v2'_relationship s_ne_zero,
        rw add_comm (↑s * vector.nth core_point1_corner i + ↑s - 1) ↑s at core_point2_corner_v2'_relationship,
        rw [sub_eq_add_neg, sub_eq_add_neg, add_assoc (↑s * vector.nth core_point1_corner i) ↑s (-1), ← add_assoc,
          add_assoc (↑s * vector.nth core_point2_corner i) ↑s (-1)] at core_point2_corner_v2'_relationship,
        simp only [add_left_inj] at core_point2_corner_v2'_relationship,
        have s_times_goal : ↑s * vector.nth core_point2_corner i - ↑s * vector.nth core_point1_corner i = ↑s := by linarith,
        rw ← mul_sub_left_distrib at s_times_goal,
        have s_times_goal_div_s : ↑s * (vector.nth core_point2_corner i - vector.nth core_point1_corner i) / ↑s = ↑s / ↑s :=
          by rw s_times_goal,
        have cast_s_ne_zero : ↑s ≠ (0 : ℝ) := by exact_mod_cast s_ne_zero,
        rw [mul_div_cancel_left (vector.nth core_point2_corner i - vector.nth core_point1_corner i) cast_s_ne_zero, 
          div_self cast_s_ne_zero] at s_times_goal_div_s,
        exact s_times_goal_div_s,
      end,
    replace T_shifted_faceshare_free := T_shifted_faceshare_free i (or.inr core_point_corners_off_by_one),
    rcases T_shifted_faceshare_free with ⟨j, i_ne_j_and_core_point1_eq_core_point2_at_j⟩,
    rw not_or_distrib at i_ne_j_and_core_point1_eq_core_point2_at_j,
    cases i_ne_j_and_core_point1_eq_core_point2_at_j with i_ne_j core_point1_corner_ne_core_point2_corner_at_j,
    have v2_ne_v1_at_j : v2.nth j ≠ v1.nth j :=
      begin
        replace core_point1_corner_v1'_relationship := core_point1_corner_v1'_relationship j,
        replace core_point2_corner_v2'_relationship := core_point2_corner_v2'_relationship j,
        intro v2_eq_v1_at_j,
        rcases real_eq_or_lt_or_gt (core_point1_corner.nth j) (core_point2_corner.nth j) with
          core_point1_corner_eq_core_point2_corner | core_point1_corner_lt_core_point2_corner |
          core_point1_corner_gt_core_point2_corner,
        exact core_point1_corner_ne_core_point2_corner_at_j core_point1_corner_eq_core_point2_corner,
        { rw [← v2_eq_v1_at_j, ← core_point2_corner_v2'_relationship] at core_point1_corner_v1'_relationship,
          simp only [add_left_inj, mul_eq_mul_left_iff, nat.cast_eq_zero, sub_left_inj] at core_point1_corner_v1'_relationship,
          cases core_point1_corner_v1'_relationship with core_point1_corner_eq_core_point2_corner s_eq_zero,
          { rw core_point1_corner_eq_core_point2_corner at core_point1_corner_lt_core_point2_corner,
            exact lt_irrefl (vector.nth core_point2_corner j) core_point1_corner_lt_core_point2_corner,
          },
          exact s_ne_zero s_eq_zero,
        },
        rw [← v2_eq_v1_at_j, ← core_point2_corner_v2'_relationship] at core_point1_corner_v1'_relationship,
        simp only [add_left_inj, mul_eq_mul_left_iff, nat.cast_eq_zero, sub_left_inj] at core_point1_corner_v1'_relationship,
        cases core_point1_corner_v1'_relationship with core_point1_corner_eq_core_point2_corner s_eq_zero,
        { rw core_point1_corner_eq_core_point2_corner at core_point1_corner_gt_core_point2_corner,
          exact gt_irrefl (vector.nth core_point2_corner j) core_point1_corner_gt_core_point2_corner,
        },
        exact s_ne_zero s_eq_zero,
      end,
    exact i_ne_j (v1_not_adj_v2 j v2_ne_v1_at_j),
  },
  rename v1_not_adj_v2_hyp v1_not_adj_v2_hyp_false,
  clear' remove_info_map goal_clique goal_clique_card goal_clique_with_info_card,
  exact periodic_tiling_implies_clique_helper d_ne_zero s_ne_zero T T_is_tiling T_faceshare_free T_is_periodic T_is_s_discrete T_shifted
    T_shifted_is_tiling T_shifted_faceshare_free T_shifted_is_periodic T_shifted_contains_only_s_points core_points_finset core_points_finset_card
    core_points_finset_property goal_clique_with_info_map v1 v2 v1_ne_v2 v1' core_point1 core_point1_is_core_point core_point1_corner
    core_point1_corner_in_T_shifted core_point1_in_core_point1_corner core_point1_corner_unique v2' core_point2 core_point2_is_core_point
    core_point2_corner core_point2_corner_in_T_shifted core_point2_in_core_point2_corner core_point2_corner_unique v2_def v1_def
    core_point1_corner_v1'_relationship core_point2_corner_v2'_relationship v1_not_adj_v2 v1_not_adj_v2_hyp_false,
end

lemma clique_nonexistence_implies_Keller_conjecture {d : ℕ} (d_gt_zero : d > 0) :
  ¬has_clique (Keller_graph d (2^(d-1))) (2^d) → Keller_conjecture d :=
begin
  intro h,
  apply periodic_reduction d d_gt_zero,
  contrapose h,
  rw not_not,
  rw periodic_Keller_conjecture at h,
  simp only [not_forall, not_not, exists_prop, exists_and_distrib_right] at h,
  rcases h with ⟨T, ⟨T_is_tiling, T_is_periodic⟩, T_faceshare_free⟩,
  have T_is_s_discrete := s_discrete_upper_bound d T T_is_tiling d_gt_zero T_is_periodic,
  have d_ne_zero : d ≠ 0 := by linarith,
  have two_to_the_d_sub_one_ne_zero : 2^(d - 1) ≠ 0 :=
    begin
      have two_to_the_d_sub_one_pos : 2^(d - 1) > 0 := by norm_num,
      linarith,
    end,
  apply periodic_tiling_implies_clique d_ne_zero two_to_the_d_sub_one_ne_zero,
  use [T, T_is_tiling, T_faceshare_free, T_is_periodic, T_is_s_discrete],
end