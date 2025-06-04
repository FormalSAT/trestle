import no_clique_implies_keller

def cubelet {d : ℕ} (s : ℕ) (corner : point d) : set (point d) := 
  { p | ∀ i : fin d, corner.nth i ≤ p.nth i ∧ p.nth i < corner.nth i + (1 / (↑s : ℝ)) }

def cubelets_equivalent {d : ℕ} (s : ℕ) (corner1 : point d) (corner2 : point d) : Prop :=
  ∃ x : int_point d, corner1 = add_vectors corner2 (int_point_to_point(double_int_vector x))

def valid_core_cubelet_coord {s : ℕ} (s_ne_zero : s ≠ 0) (coord_val : ℝ) : Prop := 
  ∃ s_val ∈ (s_finset s_ne_zero), coord_val = s_val ∨ coord_val = s_val + 1

lemma zero_le_of_valid_core_cubelet_coord {s : ℕ} {s_ne_zero : s ≠ 0} {coord_val : ℝ} :
  valid_core_cubelet_coord s_ne_zero coord_val → 0 ≤ coord_val :=
begin
  rw valid_core_cubelet_coord,
  rintro ⟨s_val, s_val_in_s_finset, coord_val_eq_s_val | coord_val_eq_s_val_add_one⟩,
  { rw coord_val_eq_s_val,
    exact (s_finset_range s_val_in_s_finset).1,
  },
  have h := (s_finset_range s_val_in_s_finset).1,
  linarith,
end

lemma lt_two_of_valid_core_cubelet_coord {s : ℕ} {s_ne_zero : s ≠ 0} {coord_val : ℝ} :
  valid_core_cubelet_coord s_ne_zero coord_val → coord_val < 2 :=
begin
  rw valid_core_cubelet_coord,
  rintro ⟨s_val, s_val_in_s_finset, coord_val_eq_s_val | coord_val_eq_s_val_add_one⟩,
  { have h := (s_finset_range s_val_in_s_finset).2,
    linarith,
  },
  have h := (s_finset_range s_val_in_s_finset).2,
  linarith,
end

def valid_core_cubelet {d s : ℕ} (s_ne_zero : s ≠ 0) (p : point d) : Prop := 
  ∀ i : fin d, valid_core_cubelet_coord s_ne_zero (p.nth i)

--A function that takes an arbitrary point and returns the unique cubelet it belongs to
noncomputable def get_cubelet {d : ℕ} (s : ℕ) (p : point d) : point d := vector.of_fn (λ i, (int.floor ((p.nth i) * s)) / (↑s : ℝ))
--A function that takes an arbitrary point and returns the unique core cubelet that is equivalent to the cubelet it belongs to
noncomputable def get_core_cubelet {d : ℕ} (s : ℕ) (p : point d) : point d := vector.of_fn (λ i, (int.mod (int.floor ((p.nth i) * s)) (2 * s)) / (↑s : ℝ))

lemma all_points_in_cubelets {d s : ℕ} (zero_lt_s : 0 < s) : ∀ p : point d, p ∈ (cubelet s (get_cubelet s p)) :=
begin
  intro p,
  rw [cubelet, get_cubelet],
  simp only [vector.nth_of_fn, one_div, set.mem_set_of_eq],
  intro i,
  have cast_zero_lt_s : (0 : ℝ) < ↑s := by exact_mod_cast zero_lt_s,
  split,
  { rw div_le_iff cast_zero_lt_s,
    exact int.floor_le (vector.nth p i * ↑s),
  },
  rw [← one_div, ← add_div, lt_div_iff cast_zero_lt_s],
  exact int.lt_floor_add_one (vector.nth p i * ↑s),
end

lemma get_core_cubelet_returns_valid_core_cubelet {d s : ℕ} (s_ne_zero : s ≠ 0) : 
  ∀ p : point d, valid_core_cubelet s_ne_zero (get_core_cubelet s p) :=
begin
  intros p i,
  rw [get_core_cubelet, valid_core_cubelet_coord],
  simp only [vector.nth_of_fn, exists_prop],
  have cast_s_ne_zero : ↑s ≠ (0 : ℝ) := by exact_mod_cast s_ne_zero,
  have two_ne_zero : 2 ≠ 0 := (ne.ite_ne_left_iff s_ne_zero).mp (ne.symm s_ne_zero),
  have double_s_ne_zero : 2 * s ≠ 0 := mul_ne_zero two_ne_zero s_ne_zero,
  have cast_double_s_ne_zero : (2 : ℤ) * ↑s ≠ 0 := by exact_mod_cast double_s_ne_zero,
  by_cases mod_val_lt_s : (⌊vector.nth p i * ↑s⌋.mod (2 * ↑s)).nat_abs < s,
  { use (⌊vector.nth p i * ↑s⌋.mod (2 * ↑s)) / s,
    split,
    { rw s_finset,
      simp only [finset.mem_map, finset.mem_range, function.embedding.coe_fn_mk, exists_prop],
      use [(⌊vector.nth p i * ↑s⌋.mod (2 * ↑s)).nat_abs, mod_val_lt_s],
      rw div_eq_div_iff cast_s_ne_zero cast_s_ne_zero,
      simp only [mul_eq_mul_right_iff, nat.cast_eq_zero],
      left,
      exact_mod_cast (int.nat_abs_of_nonneg (int.mod_nonneg ⌊vector.nth p i * ↑s⌋ cast_double_s_ne_zero)),
    },
    left,
    refl,
  },
  rename mod_val_lt_s mod_val_ge_s,
  simp only [not_lt] at mod_val_ge_s,
  use (⌊vector.nth p i * ↑s⌋.mod (2 * ↑s) - s) / s,
  split,
  { rw s_finset,
    simp only [finset.mem_map, finset.mem_range, function.embedding.coe_fn_mk, exists_prop],
    have mod_val_lt_double_s : ↑(⌊vector.nth p i * ↑s⌋ % (2 * ↑s)).nat_abs < (2 : ℤ) * s :=
      begin
        have double_s_pos : 0 < 2 * s := ne.bot_lt double_s_ne_zero,
        have cast_double_s_pos : 0 < (2 : ℤ) * s := by exact_mod_cast double_s_pos,
        rw int.nat_abs_of_nonneg (int.mod_nonneg (⌊vector.nth p i * ↑s⌋) cast_double_s_ne_zero),
        exact int.mod_lt_of_pos (⌊vector.nth p i * ↑s⌋) cast_double_s_pos,
      end,
    have mod_val_sub_s_lt_s : ((⌊vector.nth p i * ↑s⌋ % (2 * ↑s)).nat_abs - s) < s :=
      begin
        have h : (⌊vector.nth p i * ↑s⌋ % (2 * ↑s)).nat_abs < 2 * s := by exact_mod_cast mod_val_lt_double_s,
        linarith,
      end,
    use [(⌊vector.nth p i * ↑s⌋ % (2 * ↑s)).nat_abs - s, mod_val_sub_s_lt_s],
    have nums_eq : (↑((⌊vector.nth p i * ↑s⌋ % (2 * ↑s)).nat_abs - s) : ℝ) = (↑(⌊vector.nth p i * ↑s⌋.mod (2 * ↑s)) - ↑s) :=
      begin
        change (↑((⌊vector.nth p i * ↑s⌋.mod (2 * ↑s)).nat_abs - s) : ℝ) = (↑(⌊vector.nth p i * ↑s⌋.mod (2 * ↑s)) - ↑s),
        rw [nat.cast_sub mod_val_ge_s, sub_left_inj],
        have cast_goal : (↑((⌊vector.nth p i * ↑s⌋.mod (2 * ↑s)).nat_abs) : ℤ) = (⌊vector.nth p i * ↑s⌋.mod (2 * ↑s)) :=
          begin
            rw int.nat_abs_of_nonneg,
            exact int.mod_nonneg (⌊vector.nth p i * ↑s⌋) cast_double_s_ne_zero,
          end,
        exact_mod_cast cast_goal,
      end,
    rw nums_eq,
  },
  right,
  rw [sub_div, div_self cast_s_ne_zero],
  norm_num,
end

lemma point_core_cubelet_equiv_point_cubelet {d s : ℕ} (s_ne_zero : s ≠ 0) :
  ∀ p : point d, cubelets_equivalent s (get_core_cubelet s p) (get_cubelet s p) :=
begin
  intro p,
  have cast_s_ne_zero : ↑s ≠ (0 : ℝ) := by exact_mod_cast s_ne_zero,
  have int_s_ne_zero : ↑s ≠ (0 : ℤ) := by exact_mod_cast s_ne_zero,
  rw [get_cubelet, get_core_cubelet, cubelets_equivalent],
  have x_exists : ∃ x : int_point d, ∀ i : fin d, (↑(⌊vector.nth p i * ↑s⌋.mod (2 * ↑s)) / ↑s - ↑⌊vector.nth p i * ↑s⌋ / (↑s : ℝ)) / 2 = ↑(x.nth i) :=
    begin
      change ∃ x : int_point d, ∀ i : fin d, (↑(⌊vector.nth p i * ↑s⌋ % (2 * ↑s)) / ↑s - ↑⌊vector.nth p i * ↑s⌋ / (↑s : ℝ)) / 2 = ↑(x.nth i),
      use vector.of_fn (λ i, -(int.floor(p.nth i * s) / (2 * ↑s))),
      intro i,
      simp only [vector.nth_of_fn, int.cast_neg],
      rw [div_sub_div_same, div_div_eq_div_mul, mul_comm (↑s : ℝ) 2, int.mod_def],
      simp only [int.cast_sub, int.cast_mul, int.cast_bit0, int.cast_one, int.cast_coe_nat, sub_sub_cancel_left],
      rw [neg_div, neg_inj, mul_comm, mul_div_cancel],
      simp only [ne.def, mul_eq_zero, bit0_eq_zero, one_ne_zero, nat.cast_eq_zero, false_or],
      exact s_ne_zero,
    end,
  cases x_exists with x x_property,
  use x,
  rw [double_int_vector, int_point_to_point, add_vectors],
  apply vector.ext,
  intro i,
  simp only [vector.nth_of_fn, int.cast_mul, int.cast_bit0, int.cast_one],
  have goal_rw : ↑(⌊vector.nth p i * ↑s⌋.mod (2 * ↑s)) / (↑s : ℝ) - (↑⌊vector.nth p i * ↑s⌋ / ↑s) = 2 * ↑(vector.nth x i) :=
    begin
      rw ← x_property i,
      linarith,
    end,
  linarith,
end

--build_core_cubelets_finset d is the finset of cardinality (2*s)^d that contains all valid core cubelets
noncomputable def build_core_cubelets_finset {d s : ℕ} (s_ne_zero : s ≠ 0) (n : fin (d + 1)) :
  {res : finset ({p : point d // ∀ i : fin d, (i.val < n.val → valid_core_cubelet_coord s_ne_zero (p.nth i)) ∧ (i.val ≥ n.val → p.nth i = 0)}) //
    res.card = (2*s)^n.val ∧
    (∀ p : point d, (∀ i : fin d, i.val ≥ n.val → p.nth i = 0) → ∃ cubelet ∈ res, cubelets_equivalent s (cubelet : point d) (get_cubelet s p)) ∧
    --The above condition works a little bit differently from what I wrote for build_core_points_finset. The idea is that when n is d, then this
    --line states that for all points p, there is a cubelet in res that is equivalent to p's cubelet. So for every valid cubelet, res contains
    --an equivalent cubelet
    ∀ p : point d, ∀ h : (∀ i : fin d, (i.val < n.val → valid_core_cubelet_coord s_ne_zero (p.nth i)) ∧ (i.val ≥ n.val → p.nth i = 0)),
    (⟨p, h⟩ : {p : point d // ∀ i : fin d, (i.val < n.val → valid_core_cubelet_coord s_ne_zero (p.nth i)) ∧ (i.val ≥ n.val → p.nth i = 0)}) ∈ res
  }
  :=
begin
  cases n with n_val n_property,
  induction n_val with m ih,
  { let res_elem : {p : point d // ∀ i : fin d, (i.val < 0 → valid_core_cubelet_coord s_ne_zero (p.nth i)) ∧ (i.val ≥ 0 → p.nth i = 0)} :=
      begin
        use (vector.of_fn (λ i, 0)),
        intro i,
        split,
        { intro i_lt_zero,
          exfalso,
          linarith,
        },
        intro i_ge_zero,
        simp only [vector.nth_of_fn],
      end,
    let res : finset {p : point d // ∀ i : fin d, (i.val < 0 → valid_core_cubelet_coord s_ne_zero (p.nth i)) ∧ (i.val ≥ 0 → p.nth i = 0)} := { res_elem },
    use res,
    simp only [finset.card_singleton, pow_zero, eq_self_iff_true, ge_iff_le, zero_le, forall_true_left, finset.mem_singleton,
      exists_prop, subtype.exists, nat.not_lt_zero, forall_false_left, true_and, subtype.mk_eq_mk, subtype.coe_mk],
    split,
    { intros p p_eq_zero_everywhere,
      use (vector.of_fn (λ i, 0)),
      simp only [vector.nth_of_fn, eq_self_iff_true, implies_true_iff, true_and],
      use (vector.of_fn (λ i, 0)),
      apply vector.ext,
      intro i,
      rw [double_int_vector, int_point_to_point, get_cubelet, add_vectors],
      simp only [vector.nth_of_fn, mul_zero, int.cast_zero, add_zero, p_eq_zero_everywhere i, zero_mul, int.floor_zero, int.cast_zero, zero_div],
    },
    intros p p_eq_zero_everywhere,
    apply vector.ext,
    intro i,
    simp only [vector.nth_of_fn],
    exact p_eq_zero_everywhere i,
  },
  have m_lt_d : m < d := by {rw nat.succ_eq_add_one at n_property, linarith},
  rcases ih (nat.lt_of_succ_lt n_property) with ⟨prev_res, prev_res_card, prev_res_covers_points, valid_core_cubelets_in_prev_res⟩,
  let next_level_map : fin (2*s) →
    {p : point d // ∀ (i : fin d), (i.val < m → valid_core_cubelet_coord s_ne_zero (vector.nth p i)) ∧ (i.val ≥ m → vector.nth p i = 0)} ↪
    {p : point d // ∀ (i : fin d), (i.val < m + 1 → valid_core_cubelet_coord s_ne_zero (vector.nth p i)) ∧ (i.val ≥ m + 1 → vector.nth p i = 0)} :=
    begin
      intro t,
      let next_level_map_fn :
        {p : point d // ∀ (i : fin d), (i.val < m → valid_core_cubelet_coord s_ne_zero (vector.nth p i)) ∧ (i.val ≥ m → vector.nth p i = 0)} →
        {p : point d // ∀ (i : fin d), (i.val < m + 1 → valid_core_cubelet_coord s_ne_zero (vector.nth p i)) ∧ (i.val ≥ m + 1 → vector.nth p i = 0)} := λ p,
        begin
          use (vector.of_fn (λ j : fin d, if(j.val = m) then ↑t / ↑s else p.val.nth j)),
          intro i,
          split,
          { intro i_val_lt_m_add_one,
            simp only [coe_coe, subtype.val_eq_coe, vector.nth_of_fn],
            by_cases i_eq_m : ↑i = m,
            { rw if_pos i_eq_m,
              by_cases t_lt_s : ↑t < s,
              { have t_div_s_in_s_finset : (↑(↑t : ℕ) : ℝ) / (↑s : ℝ) ∈ s_finset s_ne_zero :=
                  begin
                    rw s_finset,
                    simp only [finset.mem_map, finset.mem_range, function.embedding.coe_fn_mk, exists_prop],
                    use ↑t,
                    exact ⟨t_lt_s, rfl⟩,
                  end,
                use [(↑(↑t : ℕ) : ℝ) / (↑s : ℝ), t_div_s_in_s_finset],
                left,
                refl,
              },
              rename t_lt_s t_ge_s,
              simp only [not_lt] at t_ge_s,
              have t_div_s_sub_one_in_s_finset : (↑(↑t : ℕ) : ℝ) / (↑s : ℝ) - 1 ∈ s_finset s_ne_zero :=
                begin
                  rw s_finset,
                  simp only [finset.mem_map, finset.mem_range, function.embedding.coe_fn_mk, exists_prop],
                  use ↑t - s,
                  split,
                  { have t_lt_double_s := t.property,
                    simp only [fin.val_eq_coe] at t_lt_double_s,
                    linarith,
                  },
                  rw [nat.cast_sub t_ge_s, sub_div, div_self],
                  exact_mod_cast s_ne_zero,
                end,
              use [(↑(↑t : ℕ) : ℝ) / (↑s : ℝ) - 1, t_div_s_sub_one_in_s_finset],
              right,
              norm_num,
            },
            rename i_eq_m i_ne_m,
            rw if_neg i_ne_m,
            rw ← fin.val_eq_coe at i_ne_m,
            have i_le_m : i.val ≤ m := by linarith,
            exact (p.property i).1 (lt_of_le_of_ne i_le_m i_ne_m),
          },
          intro i_ge_m_add_one,
          simp only [coe_coe, subtype.val_eq_coe, vector.nth_of_fn],
          simp only [fin.val_eq_coe, ge_iff_le] at i_ge_m_add_one,
          have i_ne_m : ↑i ≠ m := by linarith,
          have i_ge_m : ↑i ≥ m := by linarith,
          rw ← fin.val_eq_coe at i_ge_m,
          rw if_neg i_ne_m,
          exact (p.property i).2 i_ge_m,
        end,
      have next_level_map_fn_injective : function.injective next_level_map_fn :=
        begin
          intros p1 p2 p1_output_eq_p2_output,
          apply subtype.ext,
          apply vector.ext,
          intro i,
          have p1_output_eq_p2_output_at_i : (next_level_map_fn p1).val.nth i = (next_level_map_fn p2).val.nth i := by rw p1_output_eq_p2_output,
          dsimp only[next_level_map_fn] at p1_output_eq_p2_output_at_i,
          simp only [coe_coe, subtype.val_eq_coe, vector.nth_of_fn] at p1_output_eq_p2_output_at_i,
          rcases lt_or_ge i.val m with i_lt_m | i_ge_m,
          { have i_ne_m : i.val ≠ m := ne_of_lt i_lt_m,
            rw fin.val_eq_coe at i_ne_m,
            rw [if_neg i_ne_m, if_neg i_ne_m] at p1_output_eq_p2_output_at_i,
            exact p1_output_eq_p2_output_at_i,
          },
          rw [← subtype.val_eq_coe, ← subtype.val_eq_coe, (p1.property i).2 i_ge_m, (p2.property i).2 i_ge_m],
        end,
      exact {to_fun := next_level_map_fn, inj' := next_level_map_fn_injective},
    end,
  let next_level_res_part := λ i, finset.map (next_level_map i) prev_res,
  have next_level_res_parts_disjoint : ∀ i : fin (2*s), i ∈ (finset.fin_range (2*s)) → ∀ j : fin (2 * s), j ∈ (finset.fin_range (2 * s)) → i ≠ j → 
    disjoint (next_level_res_part i) (next_level_res_part j) :=
    begin
      intros i i_in_fin_range j j_in_fin_range i_ne_j,
      rw finset.disjoint_iff_ne,
      intros a a_in_part_i b b_in_part_j a_eq_b,
      dsimp only[next_level_res_part] at a_in_part_i b_in_part_j,
      rw finset.mem_map at a_in_part_i b_in_part_j,
      rcases a_in_part_i with ⟨a_premap, a_premap_in_prev_res, map_a_premap_eq_a⟩,
      rcases b_in_part_j with ⟨b_premap, b_premap_in_prev_res, map_b_premap_eq_b⟩,
      dsimp only[next_level_map] at map_a_premap_eq_a map_b_premap_eq_b,
      simp only [coe_coe, subtype.val_eq_coe, function.embedding.coe_fn_mk] at map_a_premap_eq_a map_b_premap_eq_b,
      have a_eq_b_at_m : a.val.nth ⟨m, m_lt_d⟩ = b.val.nth ⟨m, m_lt_d⟩ := by {rw a_eq_b},
      rw [← map_a_premap_eq_a, ← map_b_premap_eq_b] at a_eq_b_at_m,
      simp only [vector.nth_of_fn, fin.coe_mk, eq_self_iff_true, if_true] at a_eq_b_at_m,
      have cast_s_ne_zero : ↑s ≠ (0 : ℝ) := by exact_mod_cast s_ne_zero,
      rw div_eq_div_iff cast_s_ne_zero cast_s_ne_zero at a_eq_b_at_m,
      simp only [mul_eq_mul_right_iff, nat.cast_inj, nat.cast_eq_zero] at a_eq_b_at_m,
      replace a_eq_b_at_m := or.resolve_right a_eq_b_at_m s_ne_zero,
      rw [← fin.val_eq_coe, ← fin.val_eq_coe] at a_eq_b_at_m,
      exact i_ne_j (fin.eq_of_veq a_eq_b_at_m),
    end,
  let res := finset.bUnion (finset.fin_range (2*s)) next_level_res_part,
  have res_card := finset.card_bUnion next_level_res_parts_disjoint,
  simp only [finset.card_map, finset.sum_const, finset.fin_range_card, nsmul_eq_mul, nat.cast_id] at res_card,
  conv at res_card
  begin
    to_rhs,
    find (2*s) {rw ← pow_one (2 * s)},
  end,
  rw [prev_res_card, ← pow_add] at res_card,
  conv at res_card
  begin
    to_rhs,
    find (1 + m) {rw [add_comm, ← nat.succ_eq_add_one]},
  end,
  use [res, res_card],
  split,
  { intros p p_property,
    let p' : point d := vector.of_fn (λ i, if(i.val = m) then 0 else p.nth i),
    have p'_property : ∀ i : fin d, i.val ≥ m → p'.nth i = 0 :=
      begin
        intros i i_ge_m,
        rw [ge_iff_le, le_iff_eq_or_lt] at i_ge_m,
        dsimp only[p'],
        simp only [fin.val_eq_coe, vector.nth_of_fn, ite_eq_left_iff],
        intro i_ne_m,
        cases i_ge_m with m_eq_i m_lt_i,
        { symmetry' at m_eq_i,
          simp only [fin.val_eq_coe] at m_eq_i,
          exfalso,
          exact i_ne_m m_eq_i,
        },
        have i_ge_m_succ : i.val ≥ m + 1 := by linarith,
        rw ← nat.succ_eq_add_one at i_ge_m_succ,
        exact p_property i i_ge_m_succ,
      end,
    rcases prev_res_covers_points p' p'_property with ⟨p'_core_cubelet, p'_core_cubelet_in_prev_res, p'_core_cubelet_covers_p'⟩,
    let p_core_cubelet := get_core_cubelet s p,
    have p_core_cubelet_def : p_core_cubelet = get_core_cubelet s p := by refl,
    have p_core_cubelet_valid := get_core_cubelet_returns_valid_core_cubelet s_ne_zero p,
    have p_core_cubelet_covers_p := point_core_cubelet_equiv_point_cubelet s_ne_zero p,
    rw ← p_core_cubelet_def at p_core_cubelet_valid p_core_cubelet_covers_p,
    have p_core_cubelet_almost_eq_p'_core_cubelet : ∀ i : fin d, i.val ≠ m → p_core_cubelet.nth i = p'_core_cubelet.val.nth i :=
      begin
        intros i i_ne_m,
        rw cubelets_equivalent at p_core_cubelet_covers_p p'_core_cubelet_covers_p',
        rcases p_core_cubelet_covers_p with ⟨x, p_core_cubelet_eq_p_cubelet_add_double_x⟩,
        rcases p'_core_cubelet_covers_p' with ⟨x', p'_core_cubelet_eq_p'_cubelet_add_double_x'⟩,
        replace p_core_cubelet_valid := p_core_cubelet_valid i,
        have p'_core_cubelet_property := p'_core_cubelet.property i,
        have zero_le_p_core_cubelet := zero_le_of_valid_core_cubelet_coord p_core_cubelet_valid,
        have p_core_cubelet_lt_two := lt_two_of_valid_core_cubelet_coord p_core_cubelet_valid,
        cases lt_or_gt_of_ne i_ne_m with i_lt_m i_gt_m,
        { replace p'_core_cubelet_property := (p'_core_cubelet_property).1 i_lt_m,
          have zero_le_p'_core_cubelet := zero_le_of_valid_core_cubelet_coord p'_core_cubelet_property,
          have p'_core_cubelet_lt_two := lt_two_of_valid_core_cubelet_coord p'_core_cubelet_property,
          rw [double_int_vector, int_point_to_point, get_cubelet, add_vectors] at
            p_core_cubelet_eq_p_cubelet_add_double_x p'_core_cubelet_eq_p'_cubelet_add_double_x',
          simp only [vector.nth_of_fn, fin.val_eq_coe, ite_mul, zero_mul, int.cast_mul, int.cast_bit0, int.cast_one] 
            at p_core_cubelet_eq_p_cubelet_add_double_x p'_core_cubelet_eq_p'_cubelet_add_double_x',
          simp only [subtype.val_eq_coe],
          rw[p_core_cubelet_eq_p_cubelet_add_double_x, p'_core_cubelet_eq_p'_cubelet_add_double_x'],
          simp only [vector.nth_of_fn],
          simp only [fin.val_eq_coe, ne.def] at i_ne_m,
          rw if_neg i_ne_m,
          simp only [add_right_inj, mul_eq_mul_left_iff, int.cast_inj, bit0_eq_zero, one_ne_zero, or_false],
          simp only [subtype.val_eq_coe] at zero_le_p'_core_cubelet p'_core_cubelet_lt_two,
          rw p'_core_cubelet_eq_p'_cubelet_add_double_x' at zero_le_p'_core_cubelet p'_core_cubelet_lt_two,
          rw p_core_cubelet_eq_p_cubelet_add_double_x at zero_le_p_core_cubelet p_core_cubelet_lt_two,
          simp only [vector.nth_of_fn] at zero_le_p'_core_cubelet p'_core_cubelet_lt_two zero_le_p_core_cubelet p_core_cubelet_lt_two,
          rw if_neg i_ne_m at zero_le_p'_core_cubelet p'_core_cubelet_lt_two,
          rcases eq_or_lt_or_gt (x.nth i) (x'.nth i) with x_eq_x' | x_lt_x' | x_gt_x',
          exact x_eq_x',
          { exfalso,
            have x_le_x'_sub_one : x.nth i ≤ x'.nth i - 1 := by linarith,
            have cast_x_le_x'_sub_one : ↑(x.nth i) ≤ ↑(x'.nth i) - (1 : ℝ) := by exact_mod_cast x_le_x'_sub_one,
            linarith,
          },
          exfalso,
          have x_ge_x'_add_one : x.nth i ≥ x'.nth i + 1 := by linarith,
          have cast_x_ge_x'_add_one : ↑(x.nth i) ≥ ↑(x'.nth i) + (1 : ℝ) := by exact_mod_cast x_ge_x'_add_one,
          linarith,
        },
        have i_ge_m : i.val ≥ m := by linarith,
        have i_ge_m_add_one : i.val ≥ m + 1 := by linarith,
        rw ← nat.succ_eq_add_one at i_ge_m_add_one,
        rw [double_int_vector, int_point_to_point, get_cubelet, add_vectors] at p_core_cubelet_eq_p_cubelet_add_double_x,
        simp only [vector.nth_of_fn, int.cast_mul, int.cast_bit0, int.cast_one] at p_core_cubelet_eq_p_cubelet_add_double_x,
        rw p_core_cubelet_eq_p_cubelet_add_double_x,
        simp only [vector.nth_of_fn, subtype.val_eq_coe],
        simp only [subtype.val_eq_coe] at p'_core_cubelet_property,
        rw [p_property i i_ge_m_add_one, p'_core_cubelet_property.2 i_ge_m],
        simp only [zero_mul, int.floor_zero, int.cast_zero, zero_div, zero_add, mul_eq_zero, bit0_eq_zero, one_ne_zero, int.cast_eq_zero, false_or],
        rw p_core_cubelet_eq_p_cubelet_add_double_x at zero_le_p_core_cubelet p_core_cubelet_lt_two,
        simp only [vector.nth_of_fn] at zero_le_p_core_cubelet p_core_cubelet_lt_two,
        rw p_property i i_ge_m_add_one at zero_le_p_core_cubelet p_core_cubelet_lt_two,
        simp only [zero_mul, int.floor_zero, int.cast_zero, zero_div, zero_add, zero_le_mul_left, zero_lt_bit0, zero_lt_one,
          int.cast_nonneg] at zero_le_p_core_cubelet p_core_cubelet_lt_two,
        cases le_or_gt (x.nth i) 0 with x_le_zero x_gt_zero, linarith,
        have x_ge_one : x.nth i ≥ 1 := by linarith,
        have cast_x_ge_one : ↑(x.nth i) ≥ (1 : ℝ) := by exact_mod_cast x_ge_one,
        exfalso,
        linarith,
      end,
    have p_core_cubelet_property : ∀ (i : fin d), 
      (i.val < m.succ → valid_core_cubelet_coord s_ne_zero (vector.nth p_core_cubelet i)) ∧ (i.val ≥ m.succ → vector.nth p_core_cubelet i = 0) :=
      begin
        intro i,
        replace p_core_cubelet_valid := p_core_cubelet_valid i,
        split,
        { intro i_lt_m,
          exact p_core_cubelet_valid,
        },
        intro i_ge_m_succ,
        rw nat.succ_eq_add_one at i_ge_m_succ,
        have i_ne_m : i.val ≠ m := by linarith,
        have i_ge_m : i.val ≥ m := by linarith,
        rw [p_core_cubelet_almost_eq_p'_core_cubelet i i_ne_m, (p'_core_cubelet.property i).2 i_ge_m],
      end,
    use [p_core_cubelet, p_core_cubelet_property],
    split,
    { dsimp only[res],
      rw finset.mem_bUnion,
      rcases (p_core_cubelet_property ⟨m, m_lt_d⟩).1 (nat.lt_succ_self m) with
        ⟨s_val, s_val_in_s_finset, p_core_cubelet_eq_s_val | p_core_cubelet_eq_s_val_add_one⟩,
      { rw s_finset at s_val_in_s_finset,
        simp only [finset.mem_map, finset.mem_range, function.embedding.coe_fn_mk, exists_prop] at s_val_in_s_finset,
        rcases s_val_in_s_finset with ⟨s_val_num, s_val_num_lt_s, s_val_num_div_s_eq_s_val⟩,
        have s_val_num_lt_double_s : s_val_num < 2 * s := by linarith,
        use ⟨s_val_num, s_val_num_lt_double_s⟩,
        simp only [finset.mem_fin_range, finset.mem_map, coe_coe, function.embedding.coe_fn_mk,
          exists_prop, subtype.exists, subtype.coe_mk, exists_and_distrib_right, true_and],
        use p'_core_cubelet,
        split,
        { simp only [subtype.coe_eta, exists_prop],
          exact ⟨p'_core_cubelet.property, p'_core_cubelet_in_prev_res⟩,
        },
        apply vector.ext,
        intro i,
        simp only [fin.val_eq_coe, vector.nth_of_fn],
        by_cases i_eq_m : ↑i = m,
        { rw [if_pos i_eq_m, s_val_num_div_s_eq_s_val, ← p_core_cubelet_eq_s_val],
          conv
          begin
            find (m) {rw ← i_eq_m},
          end,
          simp only [fin.eta],
        },
        rename i_eq_m i_ne_m,
        rw if_neg i_ne_m,
        symmetry,
        rw ← fin.val_eq_coe at i_ne_m,
        exact p_core_cubelet_almost_eq_p'_core_cubelet i i_ne_m,
      },
      rw s_finset at s_val_in_s_finset,
      simp only [finset.mem_map, finset.mem_range, function.embedding.coe_fn_mk, exists_prop] at s_val_in_s_finset,
      rcases s_val_in_s_finset with ⟨s_val_num, s_val_num_lt_s, s_val_num_div_s_eq_s_val⟩,
      have s_val_num_add_s_lt_double_s : s_val_num + s < 2 * s := by linarith,
      use ⟨s_val_num + s, s_val_num_add_s_lt_double_s⟩,
      simp only [finset.mem_fin_range, finset.mem_map, coe_coe, nat.cast_add, subtype.val_eq_coe,
        function.embedding.coe_fn_mk, exists_prop, subtype.exists, subtype.coe_mk, exists_and_distrib_right, true_and],
      use p'_core_cubelet,
      split,
      { simp only [subtype.coe_eta, exists_prop],
        exact ⟨p'_core_cubelet.property, p'_core_cubelet_in_prev_res⟩,
      },
      apply vector.ext,
      intro i,
      simp only [vector.nth_of_fn],
      by_cases i_eq_m : ↑i = m,
      { rw [if_pos i_eq_m, add_div, div_self ((by exact_mod_cast s_ne_zero) : ↑s ≠ (0 : ℝ)), s_val_num_div_s_eq_s_val, ← p_core_cubelet_eq_s_val_add_one],
        conv
        begin
          find (m) {rw ← i_eq_m},
        end,
        simp only [fin.eta],
      },
      rename i_eq_m i_ne_m,
      rw if_neg i_ne_m,
      symmetry,
      rw ← fin.val_eq_coe at i_ne_m,
      exact p_core_cubelet_almost_eq_p'_core_cubelet i i_ne_m,
    },
    exact p_core_cubelet_covers_p,
  },
  intros p p_property,
  dsimp only[res],
  rw finset.mem_bUnion,
  let p' : point d := vector.of_fn (λ i, if(i.val = m) then 0 else p.nth i),
  have p'_property : ∀ (i : fin d), (i.val < m → valid_core_cubelet_coord s_ne_zero (vector.nth p' i)) ∧ (m ≤ i.val → vector.nth p' i = 0) :=
    begin
      intro i,
      dsimp only[p'],
      simp only [fin.val_eq_coe, vector.nth_of_fn, ite_eq_left_iff],
      split,
      { intro i_lt_m,
        have i_ne_m : ↑i ≠ m := ne_of_lt i_lt_m,
        have i_lt_m_add_one : ↑i < m + 1 := by linarith,
        rw [← fin.val_eq_coe, ← nat.succ_eq_add_one] at i_lt_m_add_one,
        rw if_neg i_ne_m,
        exact (p_property i).1 i_lt_m_add_one,
      },
      intros m_le_i i_ne_m,
      have m_ne_i : m ≠ ↑i := by {intro m_eq_i, symmetry' at m_eq_i, exact i_ne_m m_eq_i},
      have m_lt_i := lt_of_le_of_ne m_le_i m_ne_i,
      have i_ge_m_succ : ↑i ≥ m + 1 := by linarith,
      rw [← fin.val_eq_coe, ← nat.succ_eq_add_one] at i_ge_m_succ,
      exact (p_property i).2 i_ge_m_succ,
    end,
  rcases (p_property ⟨m, m_lt_d⟩).1 (nat.lt_succ_self m) with ⟨s_val, s_val_in_s_finset, p_eq_s_val | p_eq_s_val_add_one⟩,
  { rw s_finset at s_val_in_s_finset,
    simp only [finset.mem_map, finset.mem_range, function.embedding.coe_fn_mk, exists_prop] at s_val_in_s_finset,
    rcases s_val_in_s_finset with ⟨s_val_num, s_val_num_lt_s, s_val_num_div_s_eq_s_val⟩,
    have s_val_num_lt_double_s : s_val_num < 2 * s := by linarith,
    use ⟨s_val_num, s_val_num_lt_double_s⟩,
    simp only [ge_iff_le, finset.mem_fin_range, finset.mem_map, coe_coe, subtype.val_eq_coe, function.embedding.coe_fn_mk,
      exists_prop, subtype.exists, subtype.coe_mk, exists_and_distrib_right, true_and],
    use p',
    split, use [p'_property, valid_core_cubelets_in_prev_res p' p'_property],
    apply vector.ext,
    intro i,
    simp only [vector.nth_of_fn, fin.val_eq_coe],
    by_cases i_eq_m : ↑i = m,
    { rw [if_pos i_eq_m, s_val_num_div_s_eq_s_val, ← p_eq_s_val],
      conv
      begin
        find (m) {rw ← i_eq_m},
      end,
      simp only [fin.eta],
    },
    rename i_eq_m i_ne_m,
    rw [if_neg i_ne_m, if_neg i_ne_m],
  },
  rw s_finset at s_val_in_s_finset,
  simp only [finset.mem_map, finset.mem_range, function.embedding.coe_fn_mk, exists_prop] at s_val_in_s_finset,
  rcases s_val_in_s_finset with ⟨s_val_num, s_val_num_lt_s, s_val_num_div_s_eq_s_val⟩,
  have s_val_num_add_s_lt_double_s : s_val_num + s < 2 * s := by linarith,
  use ⟨s_val_num + s, s_val_num_add_s_lt_double_s⟩,
  simp only [ge_iff_le, finset.mem_fin_range, finset.mem_map, coe_coe, nat.cast_add, subtype.val_eq_coe,
    function.embedding.coe_fn_mk, exists_prop, subtype.exists, subtype.coe_mk, exists_and_distrib_right, true_and],
  use p',
  split, use [p'_property, valid_core_cubelets_in_prev_res p' p'_property],
  apply vector.ext,
  intro i,
  simp only [vector.nth_of_fn, fin.val_eq_coe],
  by_cases i_eq_m : ↑i = m,
  { rw [if_pos i_eq_m, add_div, div_self ((by exact_mod_cast s_ne_zero) : ↑s ≠ (0 : ℝ)), s_val_num_div_s_eq_s_val, ← p_eq_s_val_add_one],
    conv
    begin
      find (m) {rw ← i_eq_m},
    end,
    simp only [fin.eta],
  },
  rename i_eq_m i_ne_m,
  rw [if_neg i_ne_m, if_neg i_ne_m],
end

--We say that a cube coveres a cubelet if the cubelet is entirely within the cube, or the cubelet could entirely be within the cube if we translated
--it by an even integer vector
def cube_covers_cubelet {d : ℕ} (s : ℕ) (cube_corner : point d) (cubelet_corner : point d) : Prop := 
  ∃ x : int_point d, (cubelet s cubelet_corner) ⊆ (cube (add_vectors cube_corner (int_point_to_point (double_int_vector x))))

lemma cubes_cover_all_equivalent_cubelets {d : ℕ} (s : ℕ) (cube_corner : point d) (c1 : point d) (c2 : point d) :
  cubelets_equivalent s c1 c2 → cube_covers_cubelet s cube_corner c1 → cube_covers_cubelet s cube_corner c2 :=
begin
  rintros ⟨x, c1_eq_c2_add_double_x⟩ ⟨y, c1_cubelet_in_cube_corner_add_double_y⟩,
  rw cube_covers_cubelet,
  use (add_int_vectors y (vector.of_fn (λ i, -(x.nth i)))),
  rw [add_int_vectors, double_int_vector, int_point_to_point, add_vectors, cube],
  rw set.subset_def,
  intros p p_in_c2_cubelet,
  simp only [vector.nth_of_fn, int.cast_mul, int.cast_bit0, int.cast_one, int.cast_add, int.cast_neg, set.mem_set_of_eq],
  rw in_cube,
  simp only [vector.nth_of_fn, ge_iff_le, not_exists],
  intro i,
  rw [set.subset_def, c1_eq_c2_add_double_x, double_int_vector, double_int_vector, int_point_to_point, int_point_to_point, add_vectors, add_vectors,
    cubelet, cube] at c1_cubelet_in_cube_corner_add_double_y,
  simp only [vector.nth_of_fn, int.cast_mul, int.cast_bit0, int.cast_one, set.mem_set_of_eq] at c1_cubelet_in_cube_corner_add_double_y,
  rw cubelet at p_in_c2_cubelet,
  simp only [set.mem_set_of_eq] at p_in_c2_cubelet,
  let p_add_double_x : point d := vector.of_fn (λ i, (p.nth i) + 2 * (x.nth i)),
  have p_add_double_x_property : (∀ (i : fin d),
    vector.nth c2 i + 2 * ↑(vector.nth x i) ≤ vector.nth p_add_double_x i ∧ vector.nth p_add_double_x i < vector.nth c2 i + 2 * ↑(vector.nth x i) + 1 / ↑s) :=
    begin
      intro i,
      dsimp only[p_add_double_x],
      simp only [vector.nth_of_fn, add_le_add_iff_right],
      replace p_in_c2_cubelet := p_in_c2_cubelet i,
      cases p_in_c2_cubelet with h1 h2,
      split, linarith,
      linarith,
    end,
  replace c1_cubelet_in_cube_corner_add_double_y := c1_cubelet_in_cube_corner_add_double_y p_add_double_x p_add_double_x_property,
  rw in_cube at c1_cubelet_in_cube_corner_add_double_y,
  simp only [vector.nth_of_fn, ge_iff_le, not_exists] at c1_cubelet_in_cube_corner_add_double_y,
  replace c1_cubelet_in_cube_corner_add_double_y := c1_cubelet_in_cube_corner_add_double_y i,
  cases c1_cubelet_in_cube_corner_add_double_y with h1 h2,
  split, linarith,
  linarith,
end

noncomputable def vertex_to_cube_corner {d s : ℕ} : vector (fin (2 * s)) d → point d := λ v, vector.of_fn (λ i, (v.nth i).val / s)

noncomputable def build_core_cubelets_covered_by_cube_next_level_map {d s : ℕ} (m : ℕ) (s_ne_zero : s ≠ 0) (cast_s_ne_zero : ↑s ≠ (0 : ℝ))
  (cast_double_s_ne_zero : 2 * ↑s ≠ (0 : ℤ)) (cast_zero_le_double_s : (0 : ℤ) ≤ 2 * ↑s) (v : vector (fin (2 * s)) d) (n_property : m.succ < d + 1)
  (m_lt_d_add_one : m < d + 1) (m_add_one_lt_d_add_one : m + 1 < d + 1) (m_lt_d : m < d) :
  let cube_corner : point d := vertex_to_cube_corner v 
  in fin s →
  {p : point d // ∀ (i : fin d), (i.val < m → valid_core_cubelet_coord s_ne_zero (p.nth i)) ∧ (i.val ≥ m → p.nth i = vector.nth cube_corner i)} ↪
  {p : point d // ∀ (i : fin d), (i.val < m.succ → valid_core_cubelet_coord s_ne_zero (p.nth i)) ∧ (i.val ≥ m.succ → p.nth i = vector.nth cube_corner i)} :=
begin
  intros cube_corner t,
  let next_level_map_fn :
    {p // ∀ (i : fin d), (i.val < m → valid_core_cubelet_coord s_ne_zero (vector.nth p i)) ∧ (i.val ≥ m → vector.nth p i = vector.nth cube_corner i)} →
    {p // ∀ (i : fin d),
      (i.val < m.succ → valid_core_cubelet_coord s_ne_zero (vector.nth p i)) ∧ (i.val ≥ m.succ → vector.nth p i = vector.nth cube_corner i)} := λ p,
    begin
      use (vector.of_fn (λ j : fin d, if(j.val = m) then (int.mod (v.nth j + t) (2 * s)) / s else p.val.nth j)),
      intro i,
      simp only [coe_coe, vector.nth_of_fn, ge_iff_le],
      split,
      { intro i_lt_m_succ,
        by_cases i_eq_m : i.val = m,
        { rw [if_pos i_eq_m, valid_core_cubelet_coord],
          by_cases num_lt_s : (int.mod (v.nth i + t) (2 * s)) < s,
          { use ↑(int.mod (v.nth i + t) (2 * s)) / (↑s : ℝ),
            split,
            { rw s_finset,
              simp only [coe_coe, finset.mem_map, finset.mem_range, function.embedding.coe_fn_mk, exists_prop],
              use (int.mod (v.nth i + t) (2 * s)).nat_abs,
              split,
              { have cast_goal : ↑(int.mod (↑(v.nth i) + (↑t : ℕ)) (2 * ↑s)).nat_abs < (↑s : ℤ) :=
                  begin
                    change ↑((↑(v.nth i) + (↑t : ℕ)) % (2 * ↑s) : ℤ).nat_abs < (↑s : ℤ),
                    rw int.nat_abs_of_nonneg (int.mod_nonneg (↑(v.nth i) + (↑t : ℕ)) cast_double_s_ne_zero),
                    exact num_lt_s,
                  end,
                exact_mod_cast cast_goal,
              },
              refl,
            },
            left,
            refl,
          },
          rename num_lt_s num_ge_s,
          simp only [coe_coe, not_lt] at num_ge_s,
          use ↑(int.mod (v.nth i + t) (2 * s)) / (↑s : ℝ) - 1,
          split,
          { rw s_finset,
            simp only [coe_coe, finset.mem_map, finset.mem_range, function.embedding.coe_fn_mk, exists_prop],
            use (int.mod (v.nth i + t) (2 * s) - s).nat_abs,
            split,
            { have mod_sub_s_nonneg : 0 ≤ (int.mod (↑(v.nth i) + ↑t) (2 * ↑s)) - (↑s : ℤ) :=
                by {simp only [coe_coe, sub_nonneg], exact num_ge_s},
              have cast_goal : ↑(((int.mod (↑(v.nth i) + ↑t) (2 * ↑s)) - ↑s).nat_abs) < (↑s : ℤ) :=
                begin
                  rw int.nat_abs_of_nonneg mod_sub_s_nonneg,
                  simp only [coe_coe],
                  have mod_lt_double_s := int.mod_lt (↑(↑(v.nth i) : ℕ) + (↑(↑t : ℕ) : ℤ)) cast_double_s_ne_zero,
                  rw abs_of_nonneg cast_zero_le_double_s at mod_lt_double_s,
                  change (↑(↑(v.nth i) : ℕ) + (↑(↑t : ℕ) : ℤ)) % ((2 : ℤ) * ↑s) - (↑s : ℤ) < ↑s,
                  linarith,
                end,
              exact_mod_cast cast_goal,
            },
            norm_num,
            have lhs_rw : (↑((int.mod (↑(↑(v.nth i) : ℕ) + (↑(↑t : ℕ) : ℤ)) (2 * ↑s) - ↑s).nat_abs) : ℝ) =
              ↑(↑((int.mod (↑(↑(v.nth i) : ℕ) + (↑(↑t : ℕ) : ℤ)) (2 * ↑s) - ↑s).nat_abs) : ℤ) := by refl,
            have mod_sub_s_nonneg : (0 : ℤ) ≤ int.mod (↑(↑(v.nth i) : ℕ) + (↑(↑t : ℕ) : ℤ)) (2 * ↑s) - ↑s := by linarith,
            rw [lhs_rw, int.nat_abs_of_nonneg mod_sub_s_nonneg, int.cast_sub, sub_div],
            simp only [int.cast_coe_nat, sub_right_inj],
            exact div_self cast_s_ne_zero,
          },
          right,
          norm_num,
        },
        rename i_eq_m i_ne_m,
        rw if_neg i_ne_m,
        rw nat.succ_eq_add_one at i_lt_m_succ,
        have i_le_m : i.val ≤ m := by linarith,
        have i_lt_m : i.val < m := lt_of_le_of_ne i_le_m i_ne_m,
        exact (p.property i).1 i_lt_m,
      },
      intro m_succ_le_i,
      rw nat.succ_eq_add_one at m_succ_le_i,
      have i_ne_m : i.val ≠ m := by linarith,
      have i_ge_m : i.val ≥ m := by linarith,
      rw if_neg i_ne_m,
      exact (p.property i).2 i_ge_m,
    end,
  have next_level_map_fn_injective : function.injective next_level_map_fn :=
    begin
      intros p1 p2 p1_output_eq_p2_output,
      apply subtype.ext,
      apply vector.ext,
      intro i,
      replace p1_output_eq_p2_output : (next_level_map_fn p1).val.nth i = (next_level_map_fn p2).val.nth i :=
        by rw p1_output_eq_p2_output,
      dsimp only[next_level_map_fn] at p1_output_eq_p2_output,
      simp only [coe_coe, vector.nth_of_fn] at p1_output_eq_p2_output,
      by_cases i_eq_m : i.val = m,
      { have i_ge_m : i.val ≥ m := ge_of_eq i_eq_m,
        rw [← subtype.val_eq_coe, ← subtype.val_eq_coe, (p1.property i).2 i_ge_m, (p2.property i).2 i_ge_m],
      },
      rename i_eq_m i_ne_m,
      rw [if_neg i_ne_m, if_neg i_ne_m] at p1_output_eq_p2_output,
      exact p1_output_eq_p2_output,
    end,
  exact {to_fun := next_level_map_fn, inj' := next_level_map_fn_injective},
end

noncomputable def build_core_cubelets_covered_by_cube {d s : ℕ} (s_ne_zero : s ≠ 0) (v : vector (fin (2 * s)) d) (n : fin (d + 1)) :
  {cubelets_covered : finset 
    ({p : point d // ∀ i : fin d, (i.val < n.val → valid_core_cubelet_coord s_ne_zero (p.nth i)) ∧ (i.val ≥ n.val → p.nth i = (vertex_to_cube_corner v).nth i)}) //
     cubelets_covered.card = s^n.val ∧ ∀ cubelet_corner ∈ cubelets_covered, cube_covers_cubelet s (vertex_to_cube_corner v) (cubelet_corner : point d)
  } :=
begin
  let cube_corner := vertex_to_cube_corner v,
  have zero_ne_s : 0 ≠ s := by {intro zero_eq_s, symmetry' at zero_eq_s, exact s_ne_zero zero_eq_s},
  have zero_lt_s : 0 < s := lt_of_le_of_ne (nat.zero_le s) zero_ne_s,
  have one_le_s : 1 ≤ s := by linarith,
  have double_s_ne_zero : 2 * s ≠ 0 := by linarith,
  have zero_le_double_s : 0 ≤ 2 * s := by linarith,
  have int_s_ne_zero : ↑s ≠ (0 : ℤ) := by exact_mod_cast s_ne_zero,
  have cast_s_nonneg : (0 : ℝ) ≤ ↑s := by exact_mod_cast (nat.zero_le s),
  have cast_s_ne_zero : ↑s ≠ (0 : ℝ) := by exact_mod_cast s_ne_zero,
  have cast_zero_lt_s : (0 : ℝ) < ↑s := by exact_mod_cast zero_lt_s,
  have cast_one_le_s : (1 : ℝ) ≤ ↑s := by exact_mod_cast one_le_s,
  have cast_double_s_ne_zero: 2 * ↑s ≠ (0 : ℤ) := by exact_mod_cast double_s_ne_zero,
  have cast_zero_ne_double_s : (0 : ℤ) ≠ 2 * ↑s := by {intro zero_eq_double_s, symmetry' at zero_eq_double_s, exact cast_double_s_ne_zero zero_eq_double_s},
  have cast_zero_le_double_s : (0 : ℤ) ≤ 2 * ↑s := by exact_mod_cast zero_le_double_s,
  have cast_zero_lt_double_s := lt_of_le_of_ne cast_zero_le_double_s cast_zero_ne_double_s,
  cases n with n_val n_property,
  simp only [fin.val_eq_coe, ge_iff_le, subtype.forall, subtype.coe_mk],
  induction n_val with m ih,
  { norm_num,
    let res : finset {p // ∀ (i : fin d), (i.val < 0 → valid_core_cubelet_coord s_ne_zero (vector.nth p i)) ∧ (i.val ≥ 0 → vector.nth p i = cube_corner.nth i)} :=
      begin
        let res_elem : {p // ∀ (i : fin d), (i.val < 0 → valid_core_cubelet_coord s_ne_zero (vector.nth p i)) ∧ (i.val ≥ 0 → vector.nth p i = cube_corner.nth i)} :=
          begin
            use cube_corner,
            intro j,
            split, {intro j_lt_zero, exfalso, linarith},
            intro j_ge_zero,
            refl,
          end,
        exact {res_elem},
      end,
    use res,
    split, by {rw finset.card_eq_one, use cube_corner},
    intros p h p_in_res,
    use [vector.of_fn (λ i, 0)],
    rw [double_int_vector, int_point_to_point, add_vectors, cube, set.subset_def, cubelet],
    simp only [set.mem_set_of_eq, vector.nth_of_fn, mul_zero, int.cast_zero, add_zero, vector.of_fn_nth],
    intros x x_property,
    rw in_cube,
    intro i,
    cases x_property i with p_le_x x_lt_p_add_one_div_s,
    rw h i at p_le_x x_lt_p_add_one_div_s,
    split, exact p_le_x,
    have one_div_s_lt_one : 1 / (↑s : ℝ) ≤ 1 := by {rw div_le_one cast_zero_lt_s, exact cast_one_le_s},
    linarith,
  },
  have m_lt_d_add_one : m < d + 1 := by {rw nat.succ_eq_add_one at n_property, linarith},
  have m_add_one_lt_d_add_one : m + 1 < d + 1 := by {rw nat.succ_eq_add_one at n_property, exact n_property},
  have m_lt_d : m < d := by linarith,
  rcases ih m_lt_d_add_one with ⟨prev_cubelets_covered, prev_cubelets_covered_card, prev_cubelets_covered_property⟩,
  let next_level_map : fin s →
    {p // ∀ (i : fin d), (i.val < m → valid_core_cubelet_coord s_ne_zero (vector.nth p i)) ∧ (i.val ≥ m → vector.nth p i = vector.nth cube_corner i)} ↪
    {p // ∀ (i : fin d), 
      (i.val < m.succ → valid_core_cubelet_coord s_ne_zero (vector.nth p i)) ∧ (i.val ≥ m.succ → vector.nth p i = vector.nth cube_corner i)} := 
    λ i, build_core_cubelets_covered_by_cube_next_level_map m s_ne_zero cast_s_ne_zero cast_double_s_ne_zero cast_zero_le_double_s 
      v n_property m_lt_d_add_one m_add_one_lt_d_add_one m_lt_d i,
  let next_level_res_part := λ i, finset.map (next_level_map i) prev_cubelets_covered,
  have next_level_res_parts_disjoint : ∀ i : fin s, i ∈ (finset.fin_range s) → ∀ j : fin s, j ∈ (finset.fin_range s) → i ≠ j → 
    disjoint (next_level_res_part i) (next_level_res_part j) :=
    begin
      intros i i_in_range_s j j_in_range_s i_ne_j,
      rw finset.disjoint_iff_ne,
      intros a a_in_part_i b b_in_part_j a_eq_b,
      have a_eq_b_at_m : a.val.nth ⟨m, m_lt_d⟩ = b.val.nth ⟨m, m_lt_d⟩ := by rw a_eq_b,
      dsimp only[next_level_res_part, next_level_map] at a_in_part_i b_in_part_j,
      rw build_core_cubelets_covered_by_cube_next_level_map at a_in_part_i b_in_part_j,
      simp only [ge_iff_le, coe_coe, subtype.val_eq_coe, subtype.coe_mk, finset.mem_map, function.embedding.coe_fn_mk, exists_prop,
        subtype.exists] at a_in_part_i b_in_part_j,
      rcases a_in_part_i with ⟨a', a'_property, a'_in_prev_cubelets_covered, a_def⟩,
      rcases b_in_part_j with ⟨b', b'_property, b'_in_prev_cubelets_covered, b_def⟩,
      rw [← a_def, ← b_def] at a_eq_b_at_m,
      simp only [vector.nth_of_fn, fin.coe_mk, eq_self_iff_true, if_true] at a_eq_b_at_m,
      rw [div_eq_div_iff cast_s_ne_zero cast_s_ne_zero, mul_eq_mul_right_iff] at a_eq_b_at_m,
      replace a_eq_b_at_m := or.resolve_right a_eq_b_at_m cast_s_ne_zero,
      change ↑((↑(↑(v.nth ⟨m, m_lt_d⟩) : ℕ) + (↑(↑i : ℕ) : ℤ)) % (2 * ↑s)) = ↑((↑(↑(v.nth ⟨m, m_lt_d⟩) : ℕ) + (↑(↑j : ℕ) : ℤ)) % (2 * ↑s)) at a_eq_b_at_m,
      rw [int.cast_inj, int.mod_eq_mod_iff_mod_sub_eq_zero] at a_eq_b_at_m,
      simp only [add_sub_add_left_eq_sub, euclidean_domain.mod_eq_zero] at a_eq_b_at_m,
      cases a_eq_b_at_m with x i_sub_j_eq_double_s_x,
      have zero_le_i := nat.zero_le ↑i,
      have cast_zero_le_i : (0 : ℤ) ≤ ↑(↑i : ℕ) := by exact_mod_cast zero_le_i,
      have zero_le_j := nat.zero_le ↑j,
      have cast_zero_le_j : (0 : ℤ) ≤ ↑(↑j : ℕ) := by exact_mod_cast zero_le_j,
      have i_lt_s : ↑i < s := by {have h := i.property, rw fin.val_eq_coe at h, exact h},
      have cast_i_lt_s : ↑(↑i : ℕ) < (↑s : ℤ) := by exact_mod_cast i_lt_s,
      have j_lt_s : ↑j < s := by {have h := j.property, rw fin.val_eq_coe at h, exact h},
      have cast_j_lt_s : ↑(↑j : ℕ) < (↑s : ℤ) := by exact_mod_cast j_lt_s,
      rcases eq_or_lt_or_gt x 0 with x_eq_zero | x_lt_zero | x_gt_zero,
      { rw [x_eq_zero, mul_zero] at i_sub_j_eq_double_s_x,
        have cast_i_eq_j := eq_of_sub_eq_zero i_sub_j_eq_double_s_x,
        rw [int.coe_nat_inj', ← fin.val_eq_coe, ← fin.val_eq_coe] at cast_i_eq_j,
        exact i_ne_j (fin.eq_of_veq cast_i_eq_j),
      },
      { have x_le_neg_one : x ≤ -1 := by linarith,
        have h : (↑(↑i : ℕ) : ℤ) - ↑(↑j : ℕ) ≤ -2 * ↑s :=
          begin
            rw i_sub_j_eq_double_s_x,
            simp only [neg_mul],
            rw [neg_eq_neg_one_mul, mul_comm (-(1 : ℤ))],
            exact mul_le_mul_of_nonneg_left x_le_neg_one cast_zero_le_double_s,
          end,
        linarith,
      },
      have x_ge_one : x ≥ 1 := by linarith,
      have h : (↑(↑i : ℕ) : ℤ) - ↑(↑j : ℕ) ≥ 2 * ↑s :=
        begin
          rw [i_sub_j_eq_double_s_x, ge_iff_le, le_mul_iff_one_le_right cast_zero_lt_double_s],
          linarith,
        end,
      linarith,
    end,
  let cubelets_covered := finset.bUnion (finset.fin_range s) next_level_res_part,
  have cubelets_covered_card := finset.card_bUnion next_level_res_parts_disjoint,
  simp only [finset.card_map, finset.sum_const, finset.fin_range_card, nsmul_eq_mul, nat.cast_id] at cubelets_covered_card,
  conv at cubelets_covered_card
  begin
    to_rhs,
    find s {rw ← pow_one s},
  end,
  rw [prev_cubelets_covered_card, ← pow_add] at cubelets_covered_card,
  conv at cubelets_covered_card
  begin
    to_rhs,
    find (1 + m) {rw [add_comm, ← nat.succ_eq_add_one]},
  end,
  use [cubelets_covered, cubelets_covered_card],
  intros p p_property p_in_cubelets_covered,
  dsimp only[cubelets_covered] at p_in_cubelets_covered,
  change (⟨p, p_property⟩ : 
    {p // ∀ (i : fin d), (i.val < m.succ → valid_core_cubelet_coord s_ne_zero (vector.nth p i)) ∧ 
                         (i.val ≥ m.succ → vector.nth p i = vector.nth (vertex_to_cube_corner v) i)})
    ∈ finset.bUnion (finset.fin_range s) next_level_res_part at p_in_cubelets_covered,
  rw finset.mem_bUnion at p_in_cubelets_covered,
  rcases p_in_cubelets_covered with ⟨a, a_in_range_s, p_in_next_level_res_part_a⟩,
  dsimp only[next_level_res_part] at p_in_next_level_res_part_a,
  rw finset.mem_map at p_in_next_level_res_part_a,
  rcases p_in_next_level_res_part_a with ⟨p_prev, p_prev_in_prev_cubelets_covered, p_def⟩,
  have p_prev_val_in_prev_cubelets_covered : 
    (⟨p_prev.val, p_prev.property⟩ : 
    {p : point d // ∀ (i : fin d), (i.val < m → valid_core_cubelet_coord s_ne_zero (p.nth i)) ∧
    (i.val ≥ m → p.nth i = vector.nth cube_corner i)}) ∈ prev_cubelets_covered :=
    begin
      convert_to p_prev ∈ prev_cubelets_covered,
      { apply subtype.ext,
        refl,
      },
      exact p_prev_in_prev_cubelets_covered,
    end,
  rcases prev_cubelets_covered_property p_prev.val p_prev.property p_prev_val_in_prev_cubelets_covered with ⟨x, p_prev_cubelet_covered⟩,
  let offset_val_at_i : fin d → ℤ := λ i, if((v.nth i).val + a.val < 2 * s) then 0 else -1,
  use vector.of_fn (λ i, if (i.val = m) then offset_val_at_i i else x.nth i),
  rw [double_int_vector, int_point_to_point, vertex_to_cube_corner, add_vectors, cube, cubelet, set.subset_def],
  simp only [set.mem_set_of_eq, fin.val_eq_coe, vector.nth_of_fn, int.cast_mul, int.cast_bit0, int.cast_one],
  intros point_in_p_cubelet point_in_p_cubelet_property,
  rw in_cube,
  simp only [vector.nth_of_fn, ge_iff_le, not_exists],
  intro i,
  by_cases i_eq_m : ↑i = m,
  { rw if_pos i_eq_m,
    replace point_in_p_cubelet_property := point_in_p_cubelet_property i,
    dsimp only[next_level_map] at p_def,
    rw build_core_cubelets_covered_by_cube_next_level_map at p_def,
    simp only [coe_coe, subtype.val_eq_coe, function.embedding.coe_fn_mk] at p_def,
    rw ← p_def at point_in_p_cubelet_property,
    simp only [vector.nth_of_fn] at point_in_p_cubelet_property,
    rw if_pos i_eq_m at point_in_p_cubelet_property,
    have h1 : ↑(↑(v.nth i) : ℕ) / (↑s : ℝ) + (2 : ℝ) * ↑(offset_val_at_i i) ≤ ↑((↑(↑(v.nth i) : ℕ) + (↑(↑a : ℕ) : ℤ)).mod (2 * ↑s)) / (↑s : ℝ) :=
      begin
        dsimp only[offset_val_at_i],
        by_cases v_add_a_lt_double_s : (v.nth i).val + a.val < 2 * s,
        { rw if_pos v_add_a_lt_double_s,
          rw [fin.val_eq_coe, fin.val_eq_coe] at v_add_a_lt_double_s,
          have cast_v_add_a_lt_double_s : ↑(↑(v.nth i) : ℕ) + ↑(↑a : ℕ) < (2 : ℤ) * ↑s := by exact_mod_cast v_add_a_lt_double_s,
          have zero_le_v_add_a : (0 : ℤ) ≤ ↑(↑(v.nth i) : ℕ) + ↑(↑a : ℕ) := by exact_mod_cast (nat.zero_le (↑(v.nth i) + ↑a)),
          simp only [int.cast_zero, mul_zero, add_zero],
          change ↑(↑(v.nth i) : ℕ) / (↑s : ℝ) ≤ ↑((↑(↑(v.nth i) : ℕ) + (↑(↑a : ℕ) : ℤ)) % (2 * ↑s)) / ↑s,
          rw [int.mod_eq_of_lt zero_le_v_add_a cast_v_add_a_lt_double_s, int.cast_add, int.cast_coe_nat, add_div],
          simp only [int.cast_coe_nat, le_add_iff_nonneg_right],
          exact div_nonneg (by exact_mod_cast (nat.zero_le (↑a : ℕ)) : 0 ≤ (↑(↑a : ℕ) : ℝ)) cast_s_nonneg,
        },
        rename v_add_a_lt_double_s v_add_a_ge_double_s,
        rw if_neg v_add_a_ge_double_s,
        simp only [int.cast_neg, int.cast_one, mul_neg, mul_one, add_neg_le_iff_le_add'],
        rw [← mul_div_cancel (2 : ℝ) cast_s_ne_zero, div_add_div_same, div_le_div_iff cast_zero_lt_s cast_zero_lt_s, mul_le_mul_right cast_zero_lt_s],
        change ↑(↑(v.nth i) : ℕ) ≤ (2 : ℝ) * ↑s + ↑((↑(↑(v.nth i) : ℕ) + (↑(↑a : ℕ) : ℤ)) % (2 * ↑s)),
        rw ← @int.add_mul_mod_self (↑(↑(v.nth i) : ℕ) + (↑(↑a : ℕ) : ℤ)) (-1) (2 * (↑s : ℤ)),
        simp only [neg_mul, one_mul],
        have zero_le_mod_val : (0 : ℤ) ≤ ↑(↑(v.nth i) : ℕ) + (↑(↑a : ℕ) : ℤ) + -(2 * ↑s) :=
          begin
            simp only [fin.val_eq_coe, not_lt] at v_add_a_ge_double_s,
            have cast_double_s_le_v_add_a : (2 : ℤ) * ↑s ≤ ↑(↑(v.nth i) : ℕ) + ↑(↑a : ℕ) := by exact_mod_cast v_add_a_ge_double_s,
            linarith,
          end,
        have mod_val_lt_double_s : ↑(↑(v.nth i) : ℕ) + (↑(↑a : ℕ) : ℤ) + -(2 * ↑s) < (2 : ℤ) * ↑s :=
          begin
            simp only [add_neg_lt_iff_le_add'],
            have v_le_double_s : ↑(v.nth i) < 2 * s := (v.nth i).property,
            have cast_ve_le_double_s : ↑(↑(v.nth i) : ℕ) < (2 : ℤ) * ↑s := by exact_mod_cast v_le_double_s,
            have a_lt_s : ↑a < s := a.property,
            have a_lt_double_s : ↑a < 2 * s := by linarith,
            have cast_a_lt_double_s : ↑(↑a : ℕ) < (2 : ℤ) * ↑s := by exact_mod_cast a_lt_double_s,
            exact add_lt_add cast_ve_le_double_s cast_a_lt_double_s,
          end,
        rw int.mod_eq_of_lt zero_le_mod_val mod_val_lt_double_s,
        simp only [int.cast_add, int.cast_coe_nat, int.cast_neg, int.cast_mul, int.cast_bit0, int.cast_one, add_neg_cancel_comm_assoc,
          le_add_iff_nonneg_right, nat.cast_nonneg],
      end,
    have h2 : ↑((↑(↑(v.nth i) : ℕ) + (↑(↑a : ℕ) : ℤ)).mod (2 * ↑s)) / (↑s : ℝ) + 1 / ↑s ≤ ↑(↑(v.nth i) : ℕ) / (↑s : ℝ) + (2 : ℝ) * ↑(offset_val_at_i i) + (1 : ℝ) :=
      begin
        dsimp only[offset_val_at_i],
        by_cases v_add_a_lt_double_s : (v.nth i).val + a.val < 2 * s,
        { rw if_pos v_add_a_lt_double_s,
          rw [fin.val_eq_coe, fin.val_eq_coe] at v_add_a_lt_double_s,
          have cast_v_add_a_lt_double_s : ↑(↑(v.nth i) : ℕ) + ↑(↑a : ℕ) < (2 : ℤ) * ↑s := by exact_mod_cast v_add_a_lt_double_s,
          have zero_le_v_add_a : (0 : ℤ) ≤ ↑(↑(v.nth i) : ℕ) + ↑(↑a : ℕ) := by exact_mod_cast (nat.zero_le (↑(v.nth i) + ↑a)),
          simp only [int.cast_zero, mul_zero, add_zero],
          change ↑((↑(↑(v.nth i) : ℕ) + (↑(↑a : ℕ) : ℤ)) % (2 * ↑s)) / (↑s : ℝ) + 1 / ↑s ≤ ↑(↑(v.nth i) : ℕ) / (↑s : ℝ) + 1,
          rw [int.mod_eq_of_lt zero_le_v_add_a cast_v_add_a_lt_double_s, int.cast_add, int.cast_coe_nat, add_div, add_assoc, div_add_div_same],
          simp only [int.cast_coe_nat, add_le_add_iff_left],
          rw [div_le_iff cast_zero_lt_s, one_mul],
          have a_lt_s : ↑a < s := a.property,
          have a_add_one_le_s : ↑a + 1 ≤ s := by linarith,
          exact_mod_cast a_add_one_le_s,
        },
        rename v_add_a_lt_double_s v_add_a_ge_double_s,
        rw if_neg v_add_a_ge_double_s,
        simp only [int.cast_neg, int.cast_one, mul_neg, mul_one],
        change ↑((↑(↑(v.nth i) : ℕ) + (↑(↑a : ℕ) : ℤ)) % (2 * ↑s)) / (↑s : ℝ) + 1 / ↑s ≤ ↑(↑(v.nth i) : ℕ) / (↑s : ℝ) + -2 + 1,
        rw ← @int.add_mul_mod_self (↑(↑(v.nth i) : ℕ) + (↑(↑a : ℕ) : ℤ)) (-1) (2 * (↑s : ℤ)),
        simp only [neg_mul, one_mul],
        have zero_le_mod_val : (0 : ℤ) ≤ ↑(↑(v.nth i) : ℕ) + (↑(↑a : ℕ) : ℤ) + -(2 * ↑s) :=
          begin
            simp only [fin.val_eq_coe, not_lt] at v_add_a_ge_double_s,
            have cast_double_s_le_v_add_a : (2 : ℤ) * ↑s ≤ ↑(↑(v.nth i) : ℕ) + ↑(↑a : ℕ) := by exact_mod_cast v_add_a_ge_double_s,
            linarith,
          end,
        have mod_val_lt_double_s : ↑(↑(v.nth i) : ℕ) + (↑(↑a : ℕ) : ℤ) + -(2 * ↑s) < (2 : ℤ) * ↑s :=
          begin
            simp only [add_neg_lt_iff_le_add'],
            have v_le_double_s : ↑(v.nth i) < 2 * s := (v.nth i).property,
            have cast_ve_le_double_s : ↑(↑(v.nth i) : ℕ) < (2 : ℤ) * ↑s := by exact_mod_cast v_le_double_s,
            have a_lt_s : ↑a < s := a.property,
            have a_lt_double_s : ↑a < 2 * s := by linarith,
            have cast_a_lt_double_s : ↑(↑a : ℕ) < (2 : ℤ) * ↑s := by exact_mod_cast a_lt_double_s,
            exact add_lt_add cast_ve_le_double_s cast_a_lt_double_s,
          end,
        rw int.mod_eq_of_lt zero_le_mod_val mod_val_lt_double_s,
        simp only [int.cast_add, int.cast_coe_nat, int.cast_neg, int.cast_mul, int.cast_bit0, int.cast_one],
        rw [add_div, ← neg_mul, mul_div_cancel (-2) cast_s_ne_zero, add_div, add_assoc, add_assoc, add_assoc],
        apply add_le_add (le_refl ((↑(↑(v.nth i) : ℕ) : ℝ) / (↑s : ℝ))),
        rw [← add_assoc, add_comm (↑(↑a : ℕ) / (↑s : ℝ)) (-2), add_assoc],
        apply add_le_add (le_refl (-2 : ℝ)),
        rw [← add_div, div_le_one cast_zero_lt_s],
        have a_lt_s : ↑a < s := a.property,
        have a_add_one_le_s : ↑a + 1 ≤ s := by linarith,
        exact_mod_cast a_add_one_le_s,
      end,
    cases point_in_p_cubelet_property with h3 h4,
    split, linarith, --Follows from h1 and h3
    linarith, --Follows from h2 and h4
  },
  rename i_eq_m i_ne_m,
  rw if_neg i_ne_m,
  rw [double_int_vector, int_point_to_point, vertex_to_cube_corner, add_vectors, cube, cubelet, set.subset_def] at p_prev_cubelet_covered,
  simp only [subtype.val_eq_coe, set.mem_set_of_eq, fin.val_eq_coe, vector.nth_of_fn, int.cast_mul, int.cast_bit0, int.cast_one] at p_prev_cubelet_covered,
  let point_in_p_cubelet' := vector.of_fn (λ i, if(↑i = m) then cube_corner.nth i else point_in_p_cubelet.nth i),
  have point_in_p_cubelet'_in_p_prev : 
    (∀ (i : fin d), p_prev.val.nth i ≤ vector.nth point_in_p_cubelet' i ∧ vector.nth point_in_p_cubelet' i < p_prev.val.nth i + 1 / ↑s) :=
    begin
      intro i,
      replace point_in_p_cubelet_property := point_in_p_cubelet_property i,
      dsimp only[point_in_p_cubelet'],
      simp only [subtype.val_eq_coe, vector.nth_of_fn],
      by_cases i_eq_m : ↑i = m,
      { rw [if_pos i_eq_m, ← subtype.val_eq_coe],
        have i_ge_m : i.val ≥ m := by {rw ← fin.val_eq_coe at i_eq_m, linarith},
        rw (p_prev.property i).2 i_ge_m,
        split, refl,
        norm_num,
        rw one_div_pos,
        exact cast_zero_lt_s,
      },
      rename i_eq_m i_ne_m,
      rw if_neg i_ne_m,
      dsimp only[next_level_map] at p_def,
      rw build_core_cubelets_covered_by_cube_next_level_map at p_def,
      simp only [coe_coe, subtype.val_eq_coe, function.embedding.coe_fn_mk] at p_def,
      have p_prev_eq_p_at_i : p_prev.val.nth i = p.nth i :=
        begin
          rw ← p_def,
          simp only [subtype.val_eq_coe, vector.nth_of_fn],
          rw if_neg i_ne_m,
        end,
      rw ← p_prev_eq_p_at_i at point_in_p_cubelet_property,
      exact point_in_p_cubelet_property,
    end,
  replace p_prev_cubelet_covered := p_prev_cubelet_covered point_in_p_cubelet' point_in_p_cubelet'_in_p_prev,
  rw in_cube at p_prev_cubelet_covered,
  simp only [vector.nth_of_fn, ge_iff_le, not_exists] at p_prev_cubelet_covered,
  replace p_prev_cubelet_covered := p_prev_cubelet_covered i,
  rw [if_neg i_ne_m] at p_prev_cubelet_covered,
  exact p_prev_cubelet_covered,
end

noncomputable def core_cubelets_covered_by_cube {d s : ℕ} (s_ne_zero : s ≠ 0) (v : vector (fin (2 * s)) d) :
  {cubelets_covered : finset ({cubelet_corner : point d // valid_core_cubelet s_ne_zero cubelet_corner}) //
     cubelets_covered.card = s^d ∧ ∀ cubelet_corner ∈ cubelets_covered, cube_covers_cubelet s (vertex_to_cube_corner v) (cubelet_corner : point d)
  } :=
begin
  have d_lt_d_add_one := lt_add_one d,
  let cube_corner := vertex_to_cube_corner v,
  let cubelets_covered_premap := (build_core_cubelets_covered_by_cube s_ne_zero v ⟨d, lt_add_one d⟩).val,
  rcases (build_core_cubelets_covered_by_cube s_ne_zero v ⟨d, lt_add_one d⟩).property with
    ⟨cubelets_covered_premap_card, cubelets_covered_premap_property⟩,
  let cast_map :
    {p : point d // ∀ i : fin d, (i.val < d → valid_core_cubelet_coord s_ne_zero (p.nth i)) ∧ (i.val ≥ d → p.nth i = cube_corner.nth i)} ↪
    {p : point d // valid_core_cubelet s_ne_zero p} :=
    begin
      let cast_map_fn :
        {p : point d // ∀ i : fin d, (i.val < d → valid_core_cubelet_coord s_ne_zero (p.nth i)) ∧ (i.val ≥ d → p.nth i = cube_corner.nth i)} →
        {p : point d // valid_core_cubelet s_ne_zero p} := λ p, ⟨p.val, λ i, (p.property i).1 i.property⟩,
      have cast_map_fn_injective : function.injective cast_map_fn :=
        begin
          rw function.injective,
          intros p1 p2 p1_output_eq_p2_output,
          dsimp[cast_map_fn] at p1_output_eq_p2_output,
          simp only at p1_output_eq_p2_output,
          refine subtype.eq _,
          simp only [subtype.val_eq_coe],
          exact p1_output_eq_p2_output,
        end,
      exact {to_fun := cast_map_fn, inj' := cast_map_fn_injective},
    end,
  let cubelets_covered := finset.map cast_map cubelets_covered_premap,
  have cubelets_covered_card : cubelets_covered.card = cubelets_covered_premap.card := finset.card_map cast_map,
  rw cubelets_covered_premap_card at cubelets_covered_card,
  use [cubelets_covered, cubelets_covered_card],
  intros cubelet_corner cubelet_corner_in_cubelets_covered,
  dsimp only[cubelets_covered] at cubelet_corner_in_cubelets_covered,
  simp only [ge_iff_le, subtype.val_eq_coe, subtype.coe_mk, finset.mem_map, function.embedding.coe_fn_mk, exists_prop,
    subtype.exists] at cubelet_corner_in_cubelets_covered,
  rcases cubelet_corner_in_cubelets_covered with ⟨a, a_property, a_in_cubelets_covered_premap, a_eq_cubelet_corner⟩,
  rw ← a_eq_cubelet_corner,
  exact cubelets_covered_premap_property ⟨a, a_property⟩ a_in_cubelets_covered_premap,
end

noncomputable def build_core_cubelets_covered_by_any_cube_finset {d s : ℕ} (s_ne_zero : s ≠ 0) 
  (clique : finset (vector (fin (2 * s)) d)) (clique_card : clique.card = 2 ^ d) 
  (all_vectors_adj_in_clique : ∀ (v1 v2 : vector (fin (2 * s)) d), v1 ∈ clique → v2 ∈ clique → v1 ≠ v2 → (Keller_graph d s).adj v1 v2):
  let T : set (point d) := { p | ∃ u ∈ clique, ∃ x : int_point d, ∀ i : fin d, p.nth i = (↑(u.nth i) : ℝ) / s + 2 * (x.nth i) } in
  {cubelets_covered : finset ({cubelet_corner : point d // valid_core_cubelet s_ne_zero cubelet_corner}) //
    cubelets_covered.card = (2*s)^d ∧
    ∀ cubelet_corner ∈ cubelets_covered, ∃ cube_corner ∈ T, cube_covers_cubelet s cube_corner (cubelet_corner : point d)
  } :=
begin
  intro T,
  have cast_s_ne_zero : ↑s ≠ (0 : ℝ) := by exact_mod_cast s_ne_zero,
  have zero_ne_s : 0 ≠ s := by {intro zero_eq_s, symmetry' at zero_eq_s, exact s_ne_zero zero_eq_s},
  have zero_lt_s : 0 < s := lt_of_le_of_ne (nat.zero_le s) zero_ne_s,
  let core_cubelets_covered_by_cube_fn : vector (fin (2 * s)) d → finset ({cubelet_corner : point d // valid_core_cubelet s_ne_zero cubelet_corner}) :=
    λ v, (core_cubelets_covered_by_cube s_ne_zero v).val,
  use finset.bUnion clique core_cubelets_covered_by_cube_fn,
  split,
  { have h : ∀ v1 : vector (fin (2 * s)) d, v1 ∈ clique → ∀ v2 : vector (fin (2 * s)) d, v2 ∈ clique → v1 ≠ v2 → 
      disjoint (core_cubelets_covered_by_cube_fn v1) (core_cubelets_covered_by_cube_fn v2) :=
      begin
        intros v1 v1_in_clique v2 v2_in_clique v1_ne_v2,
        dsimp only[core_cubelets_covered_by_cube_fn],
        rw finset.disjoint_iff_ne,
        intros a a_covered_by_v1 b b_covered_by_v2 a_eq_b,
        have v1_property := (core_cubelets_covered_by_cube s_ne_zero v1).property.2 a a_covered_by_v1,
        have v2_property := (core_cubelets_covered_by_cube s_ne_zero v2).property.2 b b_covered_by_v2,
        rcases v1_property with ⟨x1, a_cubelet_in_v1_add_double_x1_cube⟩,
        rcases v2_property with ⟨x2, b_cubelet_in_v2_add_double_x2_cube⟩,
        dsimp only[vertex_to_cube_corner] at a_cubelet_in_v1_add_double_x1_cube b_cubelet_in_v2_add_double_x2_cube,
        rw [double_int_vector, int_point_to_point, add_vectors, cube] at a_cubelet_in_v1_add_double_x1_cube b_cubelet_in_v2_add_double_x2_cube,
        simp only [vector.nth_of_fn, int.cast_mul, int.cast_bit0, int.cast_one] at a_cubelet_in_v1_add_double_x1_cube b_cubelet_in_v2_add_double_x2_cube,
        rw set.subset_def at a_cubelet_in_v1_add_double_x1_cube b_cubelet_in_v2_add_double_x2_cube,
        have b_in_cubelet_a : ↑b ∈ cubelet s (↑a : point d) :=
          begin
            rw [← a_eq_b, cubelet],
            simp only [one_div, set.mem_set_of_eq, le_refl, le_add_iff_nonneg_right, inv_nonneg, nat.cast_nonneg, and_self, implies_true_iff],
            intro i,
            simp only [lt_add_iff_pos_right, inv_pos, nat.cast_pos, true_and],
            exact zero_lt_s,
          end,
        have b_in_cubelet_b : ↑b ∈ cubelet s (↑b : point d) :=
          begin
            rw cubelet,
            simp only [one_div, set.mem_set_of_eq, le_refl, le_add_iff_nonneg_right, inv_nonneg, nat.cast_nonneg, and_self, implies_true_iff],
            intro i,
            simp only [lt_add_iff_pos_right, inv_pos, nat.cast_pos, true_and],
            exact zero_lt_s,
          end,
        replace a_cubelet_in_v1_add_double_x1_cube := a_cubelet_in_v1_add_double_x1_cube (↑b) b_in_cubelet_a,
        replace b_cubelet_in_v2_add_double_x2_cube := b_cubelet_in_v2_add_double_x2_cube (↑b) b_in_cubelet_b,
        simp only [fin.val_eq_coe, set.mem_set_of_eq] at a_cubelet_in_v1_add_double_x1_cube b_cubelet_in_v2_add_double_x2_cube,
        rw in_cube at a_cubelet_in_v1_add_double_x1_cube b_cubelet_in_v2_add_double_x2_cube,
        simp only [vector.nth_of_fn, ge_iff_le, not_exists] at a_cubelet_in_v1_add_double_x1_cube b_cubelet_in_v2_add_double_x2_cube,
        have v1_adj_v2 := all_vectors_adj_in_clique v1 v2 v1_in_clique v2_in_clique v1_ne_v2,
        rw Keller_graph at v1_adj_v2,
        simp only [fin.val_eq_coe, ne.def, exists_and_distrib_left, simple_graph.from_rel_adj] at v1_adj_v2,
        rcases v1_adj_v2 with ⟨v1_ne_v2, ⟨i, v1_eq_v2_add_s_at_i, j, v1_ne_v2_at_j, i_ne_j⟩ | ⟨i, v2_eq_v1_add_s_at_i, j, v2_ne_v1_at_j, i_ne_j⟩⟩,
        { replace a_cubelet_in_v1_add_double_x1_cube := a_cubelet_in_v1_add_double_x1_cube i,
          replace b_cubelet_in_v2_add_double_x2_cube := b_cubelet_in_v2_add_double_x2_cube i,
          rw v1_eq_v2_add_s_at_i at a_cubelet_in_v1_add_double_x1_cube,
          cases a_cubelet_in_v1_add_double_x1_cube with h1 h2,
          cases b_cubelet_in_v2_add_double_x2_cube with h3 h4,
          rcases le_or_gt (x2.nth i) (x1.nth i) with x2_le_x1 | x2_gt_x1,
          { --h1 and h4 form a contradiction
            have cast_x2_le_x1 : (↑(x2.nth i) : ℝ) ≤ ↑(x1.nth i) := by exact_mod_cast x2_le_x1,
            rw [nat.cast_add, add_div, div_self cast_s_ne_zero] at h1,
            linarith,
          },
          --h2 and h3 form a contradiction
          have x2_ge_x1_add_one : x2.nth i ≥ x1.nth i + 1 := by linarith,
          have cast_x2_ge_x1_add_one : ↑(x2.nth i) ≥ ↑(x1.nth i) + (1 : ℝ) := by exact_mod_cast x2_ge_x1_add_one,
          rw [nat.cast_add, add_div, div_self cast_s_ne_zero] at h2,
          linarith,
        },
        replace a_cubelet_in_v1_add_double_x1_cube := a_cubelet_in_v1_add_double_x1_cube i,
        replace b_cubelet_in_v2_add_double_x2_cube := b_cubelet_in_v2_add_double_x2_cube i,
        rw v2_eq_v1_add_s_at_i at b_cubelet_in_v2_add_double_x2_cube,
        cases a_cubelet_in_v1_add_double_x1_cube with h1 h2,
        cases b_cubelet_in_v2_add_double_x2_cube with h3 h4,
        rcases le_or_gt (x1.nth i) (x2.nth i) with x1_le_x2 | x1_gt_x2,
        { --h2 and h3 form a contradiction
          have cast_x1_le_x2 : (↑(x1.nth i) : ℝ) ≤ ↑(x2.nth i) := by exact_mod_cast x1_le_x2,
          rw [nat.cast_add, add_div, div_self cast_s_ne_zero] at h3,
          linarith,
        },
        --h1 and h4 form a contradiction
        have x1_gt_x2_add_one : x1.nth i ≥ x2.nth i + 1 := by linarith,
        have cast_x1_gt_x2_add_one : ↑(x1.nth i) ≥ ↑(x2.nth i) + (1 : ℝ) := by exact_mod_cast x1_gt_x2_add_one,
        rw [nat.cast_add, add_div, div_self cast_s_ne_zero] at h4,
        linarith,
      end,
    rw finset.card_bUnion h,
    simp only,
    have core_cubelets_covered_by_cube_card : ∀ u : vector (fin (2*s)) d, (core_cubelets_covered_by_cube_fn u).card = s^d :=
      begin
        intro u,
        dsimp only[core_cubelets_covered_by_cube_fn],
        exact ((core_cubelets_covered_by_cube s_ne_zero u).property).1,
      end,
    conv
    begin
      find ((core_cubelets_covered_by_cube_fn _).card) {rw core_cubelets_covered_by_cube_card}
    end,
    simp only [finset.sum_const, nsmul_eq_mul, nat.cast_id],
    rw [clique_card, ← mul_pow],
  },
  intros cubelet_corner cubelet_corner_in_cubelets_covered,
  rw finset.mem_bUnion at cubelet_corner_in_cubelets_covered,
  rcases cubelet_corner_in_cubelets_covered with ⟨v, v_in_clique, cubelet_corner_covered_by_v⟩,
  use vertex_to_cube_corner v,
  split,
  { dsimp only[T],
    simp only [coe_coe, exists_prop, set.mem_set_of_eq, vector.nth_of_fn, fin.val_eq_coe],
    use [v, v_in_clique, vector.of_fn (λ i, 0)],
    intro i,
    rw vertex_to_cube_corner,
    simp only [fin.val_eq_coe, vector.nth_of_fn, int.cast_zero, mul_zero, add_zero],
  },
  dsimp only[core_cubelets_covered_by_cube_fn] at cubelet_corner_covered_by_v,
  exact ((core_cubelets_covered_by_cube s_ne_zero v).property).2 cubelet_corner cubelet_corner_covered_by_v,
end

lemma tiling_from_clique_covers_all_points {d s : ℕ} (s_ne_zero : s ≠ 0) (clique : finset (vector (fin (2 * s)) d)) (clique_card : clique.card = 2 ^ d)
  (all_vectors_adj_in_clique : ∀ (v1 v2 : vector (fin (2 * s)) d), v1 ∈ clique → v2 ∈ clique → v1 ≠ v2 → (Keller_graph d s).adj v1 v2) (p : point d) :
  let T : set (point d) := { p | ∃ u ∈ clique, ∃ x : int_point d, ∀ i : fin d, p.nth i = (↑(u.nth i) : ℝ) / s + 2 * (x.nth i) }
  in (∀ (t : point d), t ∈ T → p ∉ cube t) → false :=
begin
  intros T p_has_no_corner,
  rcases build_core_cubelets_covered_by_any_cube_finset s_ne_zero clique clique_card all_vectors_adj_in_clique with 
    ⟨core_cubelets_covered_by_any_cube_finset, core_cubelets_covered_by_any_cube_finset_card, core_cubelets_covered_by_any_cube_finset_property⟩,
  have d_lt_d_add_one : d < d + 1 := by norm_num,
  rcases build_core_cubelets_finset (s_ne_zero : s ≠ 0) ⟨d, d_lt_d_add_one⟩ with
    ⟨core_cubelets_finset, core_cubelets_finset_card, core_cubelets_finset_covers_all_points, all_core_cubelets_in_core_cubelets_finset⟩,
  have p_satisfies_trivial_property : ∀ i : fin d, i.val ≥ d → p.nth i = 0 :=
    by {intros i i_ge_d, exfalso, have := i.property, linarith},
  rcases core_cubelets_finset_covers_all_points p p_satisfies_trivial_property with 
    ⟨p_core_cubelet, ⟨p_core_cubelet_in_core_cubelets_finset, p_core_cubelet_equivalent_to_p_cubelet⟩⟩,
  have p_core_cubelet_is_valid_core_cubelet : valid_core_cubelet s_ne_zero (p_core_cubelet : point d) :=
    λ i, and.left(p_core_cubelet.property i) i.property,
  let p_core_cubelet_as_valid_core_cublet : {cubelet_corner // valid_core_cubelet s_ne_zero cubelet_corner} :=
    ⟨(p_core_cubelet : point d), p_core_cubelet_is_valid_core_cubelet⟩,
  have p_core_cubelet_as_valid_core_cublet_in_core_cubelets_covered_by_any_cube_finset :
    p_core_cubelet_as_valid_core_cublet ∈ core_cubelets_covered_by_any_cube_finset :=
    begin
      let id : Π (a : {cubelet_corner : point d // valid_core_cubelet s_ne_zero cubelet_corner}), a ∈ core_cubelets_covered_by_any_cube_finset →
        {p : point d // ∀ (i : fin d), (i.val < d → valid_core_cubelet_coord s_ne_zero (vector.nth p i)) ∧ (i.val ≥ d → vector.nth p i = 0)} :=
        begin
          intros a a_in_core_cubelets_covered_by_any_cube_finset,
          use a.val,
          intro i,
          split,
          { intro i_lt_d,
            exact a.property i,
          },
          intro i_ge_d,
          have i_lt_d := i.property,
          exfalso,
          linarith,
        end,
      have h_id : ∀ (a : {cubelet_corner : point d // valid_core_cubelet s_ne_zero cubelet_corner}) (ha : a ∈ core_cubelets_covered_by_any_cube_finset),
        id a ha ∈ core_cubelets_finset :=
        begin
          intros a ha,
          have h : ∀ (i : fin d), (i.val < d → valid_core_cubelet_coord s_ne_zero (vector.nth (a : point d) i)) ∧ (i.val ≥ d → vector.nth (a : point d) i = 0) :=
            begin
              intro i,
              rw ← subtype.val_eq_coe,
              split,
              { intro i_lt_d,
                exact a.property i,
              },
              intro i_ge_d,
              have i_lt_d := i.property,
              exfalso,
              linarith,
            end,
          exact all_core_cubelets_in_core_cubelets_finset (a : point d) h,
        end,
      have id_inj : ∀ (a1 a2 : {cubelet_corner : point d // valid_core_cubelet s_ne_zero cubelet_corner}) (ha1 : a1 ∈ core_cubelets_covered_by_any_cube_finset)
        (ha2 : a2 ∈ core_cubelets_covered_by_any_cube_finset), id a1 ha1 = id a2 ha2 → a1 = a2 :=
        begin
          intros a1 a2 ha1 ha2 ids_eq,
          dsimp only[id] at ids_eq,
          simp only at ids_eq,
          exact subtype.ext ids_eq,
        end,
      have card_constraint : core_cubelets_finset.card ≤ core_cubelets_covered_by_any_cube_finset.card :=
        by {rw [core_cubelets_finset_card, core_cubelets_covered_by_any_cube_finset_card]},
      let p_core_cubelet' : {p : point d // ∀ (i : fin d), (i.val < d → valid_core_cubelet_coord s_ne_zero (vector.nth p i)) ∧ (i.val ≥ d → vector.nth p i = 0)} :=
        begin
          use (p_core_cubelet : point d),
          intro i,
          split,
          { intro i_lt_d,
            exact p_core_cubelet_is_valid_core_cubelet i,
          },
          intro i_ge_d,
          exfalso,
          have h := i.property,
          linarith,
        end,
      have p_core_cubelet'_in_core_cubelets_finset : p_core_cubelet' ∈ core_cubelets_finset :=
        begin
          dsimp only[p_core_cubelet'],
          convert_to p_core_cubelet ∈ core_cubelets_finset,
          simp only [subtype.coe_eta],
          exact p_core_cubelet_in_core_cubelets_finset,
        end,
      rcases finset.surj_on_of_inj_on_of_card_le id h_id id_inj card_constraint p_core_cubelet' p_core_cubelet'_in_core_cubelets_finset with
        ⟨p_core_cubelet_pre_id, p_core_cubelet_pre_id_in_core_cubelets_covered_by_any_cube_finset, p_core_cubelet'_eq_p_core_cubelet_pre_id⟩,
      convert_to p_core_cubelet_pre_id ∈ core_cubelets_covered_by_any_cube_finset,
      { dsimp only[id] at p_core_cubelet'_eq_p_core_cubelet_pre_id,
        rw subtype.ext_iff at p_core_cubelet'_eq_p_core_cubelet_pre_id,
        simp only [subtype.coe_mk] at p_core_cubelet'_eq_p_core_cubelet_pre_id,
        dsimp only[p_core_cubelet_as_valid_core_cublet],
        apply subtype.ext,
        simp only [subtype.coe_mk],
        exact p_core_cubelet'_eq_p_core_cubelet_pre_id,
      },
      exact p_core_cubelet_pre_id_in_core_cubelets_covered_by_any_cube_finset,
    end,
  rcases core_cubelets_covered_by_any_cube_finset_property p_core_cubelet_as_valid_core_cublet 
    p_core_cubelet_as_valid_core_cublet_in_core_cubelets_covered_by_any_cube_finset with
    ⟨p_core_cube, p_core_cube_in_T, p_core_cube_covers_p_core_cubelet⟩,
  dsimp only[p_core_cubelet_as_valid_core_cublet] at p_core_cube_covers_p_core_cubelet,
  simp only [subtype.coe_mk] at p_core_cube_covers_p_core_cubelet,
  have p_core_cube_covers_p_cubelet := cubes_cover_all_equivalent_cubelets s p_core_cube (p_core_cubelet : point d) (get_cubelet s p) 
    p_core_cubelet_equivalent_to_p_cubelet p_core_cube_covers_p_core_cubelet,
  rw cube_covers_cubelet at p_core_cube_covers_p_cubelet,
  rcases p_core_cube_covers_p_cubelet with ⟨x, p_core_cube_covers_p_cubelet⟩,
  have p_core_cube_add_double_x_in_T : (add_vectors p_core_cube (int_point_to_point (double_int_vector x))) ∈ T :=
    begin
      rcases p_core_cube_in_T with ⟨u, u_in_clique, a, p_core_cube_def⟩,
      use [u, u_in_clique, add_int_vectors a x],
      intro i,
      rw [double_int_vector, int_point_to_point, add_int_vectors, add_vectors],
      simp only [vector.nth_of_fn, int.cast_mul, int.cast_bit0, int.cast_one, coe_coe, int.cast_add],
      rw [p_core_cube_def i, mul_add, add_assoc],
      norm_num,
    end,
  have zero_lt_s : 0 < s := ne.bot_lt s_ne_zero,
  have p_in_p_core_cube_add_double_x : p ∈ cube (add_vectors p_core_cube (int_point_to_point (double_int_vector x))) :=
    set.mem_of_subset_of_mem p_core_cube_covers_p_cubelet (all_points_in_cubelets zero_lt_s p),
  exact p_has_no_corner (add_vectors p_core_cube (int_point_to_point (double_int_vector x))) p_core_cube_add_double_x_in_T p_in_p_core_cube_add_double_x,
end

lemma tiling_from_clique_is_tiling {d s : ℕ} (s_ne_zero : s ≠ 0) (clique : finset (vector (fin (2 * s)) d)) (clique_card : clique.card = 2 ^ d)
  (all_vectors_adj_in_clique : ∀ (v1 v2 : vector (fin (2 * s)) d), v1 ∈ clique → v2 ∈ clique → v1 ≠ v2 → (Keller_graph d s).adj v1 v2) :
  let T : set (point d) := { p | ∃ u ∈ clique, ∃ x : int_point d, ∀ i : fin d, p.nth i = (↑(u.nth i) : ℝ) / s + 2 * (x.nth i) }
  in is_tiling T :=
begin
  intros T p,
  have p_corner_possibilities := try_point_to_corner T p,
  rcases p_corner_possibilities with p_has_no_corner | ⟨p_corner, p_corner_in_T, p_in_p_corner, p_corner_unique⟩| 
    ⟨p_corners, p_corners_fst_in_T, p_in_p_corners_fst, p_corners_snd_in_T, p_in_p_corners_snd, p_corners_fst_ne_p_corners_snd⟩,
  { --p is not in any cube in T
    exfalso,
    exact tiling_from_clique_covers_all_points s_ne_zero clique clique_card all_vectors_adj_in_clique p p_has_no_corner,
  },
  { --p is in exactly one cube in T
    use [p_corner, p_corner_in_T, p_in_p_corner, p_corner_unique],
  },
  --p is in multiple distinct cubes in T
  exfalso,
  dsimp only[T] at p_corners_fst_in_T p_corners_snd_in_T,
  simp only [coe_coe, exists_prop, set.mem_set_of_eq] at p_corners_fst_in_T p_corners_snd_in_T,
  rcases p_corners_fst_in_T with ⟨u1, u1_in_clique, x1, p_corners_fst_eq_u1_div_s_add_double_x1⟩,
  rcases p_corners_snd_in_T with ⟨u2, u2_in_clique, x2, p_corners_snd_eq_u2_div_s_add_double_x2⟩,
  by_cases u1_eq_u2 : u1 = u2,
  { have u1_eq_u2_everywhere : ∀ i : fin d, u1.nth i = u2.nth i := by {intro i, rw u1_eq_u2},
    by_cases x1_eq_x2_everywhere : ∀ i : fin d, x1.nth i = x2.nth i,
    { have p_corners_fst_ne_p_corners_snd : ∃ i : fin d, p_corners.fst.nth i ≠ p_corners.snd.nth i :=
        by {by_contra h, simp only [not_exists_not] at h, exact p_corners_fst_ne_p_corners_snd (vector.ext h)},
      rcases p_corners_fst_ne_p_corners_snd with ⟨i, p_corners_fst_ne_p_corners_snd_at_i⟩,
      rw [p_corners_fst_eq_u1_div_s_add_double_x1 i, p_corners_snd_eq_u2_div_s_add_double_x2 i, u1_eq_u2_everywhere i,
        x1_eq_x2_everywhere i] at p_corners_fst_ne_p_corners_snd_at_i,
      exact p_corners_fst_ne_p_corners_snd_at_i (by refl),
    },
    rename x1_eq_x2_everywhere x1_ne_x2,
    simp only [not_forall] at x1_ne_x2,
    rcases x1_ne_x2 with ⟨i, x1_ne_x2_at_i⟩,
    rw cube at p_in_p_corners_fst p_in_p_corners_snd,
    simp only [set.mem_set_of_eq] at p_in_p_corners_fst p_in_p_corners_snd,
    rw in_cube at p_in_p_corners_fst p_in_p_corners_snd,
    replace p_in_p_corners_fst := p_in_p_corners_fst i,
    replace p_in_p_corners_snd := p_in_p_corners_snd i,
    rw [p_corners_fst_eq_u1_div_s_add_double_x1 i, u1_eq_u2_everywhere i] at p_in_p_corners_fst,
    rw p_corners_snd_eq_u2_div_s_add_double_x2 i at p_in_p_corners_snd,
    rcases eq_or_lt_or_gt (x1.nth i) (x2.nth i) with x1_eq_x2_at_i | x1_lt_x2_at_i | x1_gt_x2_at_i,
    { exfalso,
      exact x1_ne_x2_at_i x1_eq_x2_at_i,
    },
    { have x1_le_x2_sub_one : x1.nth i ≤ x2.nth i - 1 := by linarith,
      have coe_x1_le_x2_sub_one : ↑(x1.nth i) ≤ ↑(x2.nth i) - (1 : ℝ) := by exact_mod_cast x1_le_x2_sub_one,
      linarith,
    },
    have x1_ge_x2_add_one : x1.nth i ≥ x2.nth i + 1 := by linarith,
    have coe_x1_ge_x2_add_one : ↑(x1.nth i) ≥ ↑(x2.nth i) + (1 : ℝ) := by exact_mod_cast x1_ge_x2_add_one,
    linarith,
  },
  rename u1_eq_u2 u1_ne_u2,
  have p_in_p_corners_fst_inter_p_corners_snd : p ∈ cube p_corners.fst ∩ cube p_corners.snd :=
    by {rw [set.inter_def, set.mem_set_of_eq], exact ⟨p_in_p_corners_fst, p_in_p_corners_snd⟩},
  have u1_adj_u2 := all_vectors_adj_in_clique u1 u2 u1_in_clique u2_in_clique u1_ne_u2,
  rw Keller_graph at u1_adj_u2,
  simp only [fin.val_eq_coe, ne.def, exists_and_distrib_left, simple_graph.from_rel_adj] at u1_adj_u2,
  have cast_s_ne_zero : ↑s ≠ (0 : ℝ) := by exact_mod_cast s_ne_zero,
  rcases u1_adj_u2 with ⟨u1_ne_u2, ⟨i, u1_eq_u2_add_s_at_i, j, u1_ne_u2_at_j, i_ne_j⟩ | ⟨i, u2_eq_u1_add_s_at_i, j, u1_ne_u2_at_j, i_ne_j⟩⟩,
  { rcases eq_or_lt_or_gt (x1.nth i) (x2.nth i) with x1_eq_x2_at_i | x1_lt_x2_at_i | x1_gt_x2_at_i,
    { have p_corners_fst_sub_p_corners_snd_ge_one : ∃ i : fin d, p_corners.fst.nth i - p_corners.snd.nth i ≥ 1 ∨ p_corners.snd.nth i - p_corners.fst.nth i ≥ 1 :=
        begin
          use i,
          left,
          rw [p_corners_fst_eq_u1_div_s_add_double_x1 i, p_corners_snd_eq_u2_div_s_add_double_x2 i, x1_eq_x2_at_i, u1_eq_u2_add_s_at_i],
          simp only [nat.cast_add, add_sub_add_right_eq_sub, ge_iff_le],
          rw [add_div, add_tsub_cancel_left, div_self cast_s_ne_zero],
        end,
      rw cube_intersection_lemma_right_implication d p_corners.fst p_corners.snd p_corners_fst_sub_p_corners_snd_ge_one at p_in_p_corners_fst_inter_p_corners_snd,
      exact set.not_mem_empty p p_in_p_corners_fst_inter_p_corners_snd,
    },
    { have x1_le_x2_sub_one : x1.nth i ≤ x2.nth i - 1 := by linarith,
      have cast_x1_le_x2_sub_one : ↑(x1.nth i) ≤ ↑(x2.nth i) - (1 : ℝ) := by exact_mod_cast x1_le_x2_sub_one,
      have p_corners_snd_sub_p_corners_fst_ge_one : ∃ i : fin d, p_corners.fst.nth i - p_corners.snd.nth i ≥ 1 ∨ p_corners.snd.nth i - p_corners.fst.nth i ≥ 1 :=
        begin
          use i,
          right,
          rw [p_corners_fst_eq_u1_div_s_add_double_x1 i, p_corners_snd_eq_u2_div_s_add_double_x2 i, u1_eq_u2_add_s_at_i, nat.cast_add, add_div,
            ge_iff_le, sub_eq_add_neg, neg_add, neg_add_rev, add_comm (-(↑s / (↑s : ℝ))) (-(↑↑(u2.nth i) / (↑s : ℝ))), ← add_assoc, ← add_assoc,
            add_assoc (↑↑(u2.nth i) / (↑s : ℝ)) ((2 : ℝ) * ↑(vector.nth x2 i)) (-(↑↑(u2.nth i) / (↑s : ℝ))), 
            add_comm ((2 : ℝ) * ↑(vector.nth x2 i)) (-(↑↑(u2.nth i) / (↑s : ℝ))), ← add_assoc, add_neg_self, zero_add, div_self cast_s_ne_zero],
          linarith,
        end,
      rw cube_intersection_lemma_right_implication d p_corners.fst p_corners.snd p_corners_snd_sub_p_corners_fst_ge_one at p_in_p_corners_fst_inter_p_corners_snd,
      exact set.not_mem_empty p p_in_p_corners_fst_inter_p_corners_snd,
    },
    have x1_ge_x2_add_one : x1.nth i ≥ x2.nth i + 1 := by linarith,
    have cast_x1_ge_x2_add_one : ↑(x1.nth i) ≥ ↑(x2.nth i) + (1 : ℝ) := by exact_mod_cast x1_ge_x2_add_one,
    have p_corners_fst_sub_p_corners_snd_ge_one : ∃ i : fin d, p_corners.fst.nth i - p_corners.snd.nth i ≥ 1 ∨ p_corners.snd.nth i - p_corners.fst.nth i ≥ 1 :=
      begin
        use i,
        left,
        rw [p_corners_fst_eq_u1_div_s_add_double_x1 i, p_corners_snd_eq_u2_div_s_add_double_x2 i, u1_eq_u2_add_s_at_i, nat.cast_add, add_div,
          ge_iff_le, sub_eq_add_neg, neg_add, ← add_assoc, add_assoc (↑↑(u2.nth i) / ↑s + ↑s / (↑s : ℝ)) ((2 : ℝ) * ↑(vector.nth x1 i)) (-(↑↑(u2.nth i) / (↑s : ℝ))),
          add_comm ((2 : ℝ) * ↑(vector.nth x1 i)) (-(↑↑(u2.nth i) / (↑s : ℝ))), ← add_assoc,
          add_assoc (↑↑(u2.nth i) / (↑s : ℝ)) (↑s / (↑s : ℝ)) (-(↑↑(u2.nth i) / (↑s : ℝ))), add_comm (↑s / (↑s : ℝ)) (-(↑↑(u2.nth i) / (↑s : ℝ))), ← add_assoc,
          add_neg_self, zero_add, div_self cast_s_ne_zero],
        linarith,
      end,
    rw cube_intersection_lemma_right_implication d p_corners.fst p_corners.snd p_corners_fst_sub_p_corners_snd_ge_one at p_in_p_corners_fst_inter_p_corners_snd,
    exact set.not_mem_empty p p_in_p_corners_fst_inter_p_corners_snd,
  },
  --Basically symmetric to the above case
  rcases eq_or_lt_or_gt (x1.nth i) (x2.nth i) with x1_eq_x2_at_i | x1_lt_x2_at_i | x1_gt_x2_at_i,
  { have p_corners_snd_sub_p_corners_fst_ge_one : ∃ i : fin d, p_corners.fst.nth i - p_corners.snd.nth i ≥ 1 ∨ p_corners.snd.nth i - p_corners.fst.nth i ≥ 1 :=
    begin
      use i,
      right,
      rw [p_corners_fst_eq_u1_div_s_add_double_x1 i, p_corners_snd_eq_u2_div_s_add_double_x2 i, x1_eq_x2_at_i, u2_eq_u1_add_s_at_i],
      simp only [nat.cast_add, add_sub_add_right_eq_sub, ge_iff_le],
      rw [add_div, add_tsub_cancel_left, div_self cast_s_ne_zero],
    end,
    rw cube_intersection_lemma_right_implication d p_corners.fst p_corners.snd p_corners_snd_sub_p_corners_fst_ge_one at p_in_p_corners_fst_inter_p_corners_snd,
    exact set.not_mem_empty p p_in_p_corners_fst_inter_p_corners_snd,
  },
  { have x1_le_x2_sub_one : x1.nth i ≤ x2.nth i - 1 := by linarith,
    have cast_x1_le_x2_sub_one : ↑(x1.nth i) ≤ ↑(x2.nth i) - (1 : ℝ) := by exact_mod_cast x1_le_x2_sub_one,
    have p_corners_snd_sub_p_corners_fst_ge_one : ∃ i : fin d, p_corners.fst.nth i - p_corners.snd.nth i ≥ 1 ∨ p_corners.snd.nth i - p_corners.fst.nth i ≥ 1 :=
      begin
        use i,
        right,
        rw [p_corners_fst_eq_u1_div_s_add_double_x1 i, p_corners_snd_eq_u2_div_s_add_double_x2 i, u2_eq_u1_add_s_at_i, nat.cast_add, add_div,
          ge_iff_le, sub_eq_add_neg, neg_add, ← add_assoc, add_assoc (↑↑(u1.nth i) / ↑s + ↑s / (↑s : ℝ)), add_comm ((2 : ℝ) * ↑(vector.nth x2 i)),
          ← add_assoc, add_assoc (↑↑(u1.nth i) / (↑s : ℝ)), add_comm (↑s / (↑s : ℝ)), ← add_assoc, add_neg_self, zero_add, div_self cast_s_ne_zero],
        linarith,
      end,
    rw cube_intersection_lemma_right_implication d p_corners.fst p_corners.snd p_corners_snd_sub_p_corners_fst_ge_one at p_in_p_corners_fst_inter_p_corners_snd,
    exact set.not_mem_empty p p_in_p_corners_fst_inter_p_corners_snd,
  },
  have x1_ge_x2_add_one : x1.nth i ≥ x2.nth i + 1 := by linarith,
  have cast_x1_ge_x2_add_one : ↑(x1.nth i) ≥ ↑(x2.nth i) + (1 : ℝ) := by exact_mod_cast x1_ge_x2_add_one,
  have p_corners_fst_sub_p_corners_snd_ge_one : ∃ i : fin d, p_corners.fst.nth i - p_corners.snd.nth i ≥ 1 ∨ p_corners.snd.nth i - p_corners.fst.nth i ≥ 1 :=
    begin
      use i,
      left,
      rw [p_corners_fst_eq_u1_div_s_add_double_x1 i, p_corners_snd_eq_u2_div_s_add_double_x2 i, u2_eq_u1_add_s_at_i, nat.cast_add, add_div,
        ge_iff_le, sub_eq_add_neg, neg_add, neg_add_rev, ← add_assoc, ← add_assoc, add_assoc (↑↑(u1.nth i) / ↑s + (2 : ℝ) * ↑(vector.nth x1 i)),
        add_comm (-(↑s / (↑s : ℝ))), ← add_assoc, add_assoc (↑↑(u1.nth i) / (↑s : ℝ)), add_comm ((2 : ℝ) * ↑(vector.nth x1 i)), ← add_assoc,
        add_neg_self, zero_add, div_self cast_s_ne_zero],
      linarith,
    end,
  rw cube_intersection_lemma_right_implication d p_corners.fst p_corners.snd p_corners_fst_sub_p_corners_snd_ge_one at p_in_p_corners_fst_inter_p_corners_snd,
  exact set.not_mem_empty p p_in_p_corners_fst_inter_p_corners_snd,
end

lemma zero_le_graph_vertex {d s : ℕ} (u : vector (fin (2 * s)) d) (i : fin d) : (0 : ℕ) ≤ ↑(u.nth i) := by {apply zero_le}
lemma graph_vertex_le_double_s {d s : ℕ} (u : vector (fin (2 * s)) d) (i : fin d) : ↑(u.nth i) < (2 : ℕ) * s :=
  by {rw ← fin.val_eq_coe, exact (u.nth i).property}

lemma tiling_from_clique_faceshare_free {d s : ℕ} (s_ne_zero : s ≠ 0) (clique : finset (vector (fin (2 * s)) d)) (clique_card : clique.card = 2 ^ d)
  (all_vectors_adj_in_clique : ∀ (v1 v2 : vector (fin (2 * s)) d), v1 ∈ clique → v2 ∈ clique → v1 ≠ v2 → (Keller_graph d s).adj v1 v2) :
  let T : set (point d) := { p | ∃ u ∈ clique, ∃ x : int_point d, ∀ i : fin d, p.nth i = (↑(u.nth i) : ℝ) / s + 2 * (x.nth i) }
  in tiling_faceshare_free T :=
begin
  intros T corner1 corner1_in_T corner2 corner2_in_T corner1_faceshares_corner2,
  dsimp only[T] at corner1_in_T corner2_in_T,
  simp only [coe_coe, exists_prop, set.mem_set_of_eq] at corner1_in_T corner2_in_T,
  rcases corner1_in_T with ⟨u1, u1_in_clique, x1, corner1_eq_u1_div_s_add_double_x1⟩,
  rcases corner2_in_T with ⟨u2, u2_in_clique, x2, corner2_eq_u2_div_s_add_double_x2⟩,
  by_cases u1_eq_u2_everywhere : ∀ i : fin d, u1.nth i = u2.nth i,
  { rcases corner1_faceshares_corner2 with ⟨i, corner1_diff_corner2_eq_one, corner1_eq_corner2_outside_of_i⟩,
    replace corner1_eq_u1_div_s_add_double_x1 := corner1_eq_u1_div_s_add_double_x1 i,
    replace corner2_eq_u2_div_s_add_double_x2 := corner2_eq_u2_div_s_add_double_x2 i,
    rw [corner1_eq_u1_div_s_add_double_x1, corner2_eq_u2_div_s_add_double_x2, u1_eq_u2_everywhere i, add_sub_add_left_eq_sub, add_sub_add_left_eq_sub,
      ← mul_sub, ← mul_sub] at corner1_diff_corner2_eq_one,
    rcases corner1_diff_corner2_eq_one with corner1_sub_corner2_eq_one | corner2_sub_corner1_eq_one,
    { have cast_corner1_sub_corner2_eq_one : 2 * ((vector.nth x1 i) - (vector.nth x2 i)) = 1 := by exact_mod_cast corner1_sub_corner2_eq_one,
      have zero_le_two : 0 ≤ (2 : ℤ) := by norm_num,
      have two_eq_one := int.eq_one_of_mul_eq_one_right zero_le_two cast_corner1_sub_corner2_eq_one,
      linarith,
    },
    have cast_corner2_sub_corner1_eq_one : 2 * ((vector.nth x2 i) - (vector.nth x1 i)) = 1 := by exact_mod_cast corner2_sub_corner1_eq_one,
    have zero_le_two : 0 ≤ (2 : ℤ) := by norm_num,
    have two_eq_one := int.eq_one_of_mul_eq_one_right zero_le_two cast_corner2_sub_corner1_eq_one,
    linarith,
  },
  rename u1_eq_u2_everywhere u1_ne_u2,
  have cast_s_ne_zero : ↑s ≠ (0 : ℝ) := by exact_mod_cast s_ne_zero,
  have zero_lt_cast_s : (0 : ℝ) < ↑s :=
    begin
      cases lt_or_eq_of_le (zero_le s),
      exact_mod_cast h,
      exfalso,
      symmetry' at h,
      exact s_ne_zero h,
    end,
  replace u1_ne_u2 : u1 ≠ u2 := 
    by {intro u1_eq_u2, rw u1_eq_u2 at u1_ne_u2, contrapose u1_ne_u2, simp only [eq_self_iff_true, implies_true_iff, not_true, not_false_iff]},
  have u1_adj_u2 := all_vectors_adj_in_clique u1 u2 u1_in_clique u2_in_clique u1_ne_u2,
  rw Keller_graph at u1_adj_u2,
  simp only [fin.val_eq_coe, ne.def, exists_and_distrib_left, simple_graph.from_rel_adj] at u1_adj_u2,
  rcases u1_adj_u2 with ⟨u1_ne_u2, ⟨i, u1_eq_u2_add_s_at_i, j, u1_ne_u2_at_j, i_ne_j⟩ | ⟨i, u2_eq_u1_add_s_at_i, j, u2_ne_u1_at_j, i_ne_j⟩⟩,
  { have corner1_ne_corner2_at_i : corner1.nth i ≠ corner2.nth i :=
      begin
        have cast_rw : (↑(↑(u2.nth i) + s) : ℝ) = ↑(↑(u2.nth i) : ℕ) + (↑s : ℝ) := (↑(vector.nth u2 i) : ℕ).cast_add s,
        rw [corner1_eq_u1_div_s_add_double_x1 i, corner2_eq_u2_div_s_add_double_x2 i, u1_eq_u2_add_s_at_i, cast_rw, add_div, div_self cast_s_ne_zero],
        rcases eq_or_lt_or_gt (x1.nth i) (x2.nth i) with x1_eq_x2_at_i | x1_lt_x2_at_i | x1_gt_x2_at_i,
        { rw x1_eq_x2_at_i,
          norm_num,
        },
        { have x1_le_x2_sub_one : x1.nth i ≤ x2.nth i - 1 := by linarith,
          have cast_x1_le_x2_sub_one : ↑(x1.nth i) ≤ ↑(x2.nth i) - (1 : ℝ) := by exact_mod_cast x1_le_x2_sub_one,
          linarith,
        },
        have x1_ge_x2_add_one : x1.nth i ≥ x2.nth i + 1 := by linarith,
        have cast_x1_ge_x2_add_one : ↑(x1.nth i) ≥ ↑(x2.nth i) + (1 : ℝ) := by exact_mod_cast x1_ge_x2_add_one,
        linarith,
      end,
    have corner1_ne_corner2_at_j : corner1.nth j ≠ corner2.nth j :=
      begin
        rw [corner1_eq_u1_div_s_add_double_x1 j, corner2_eq_u2_div_s_add_double_x2 j],
        have zero_le_u1 : (0 : ℝ) ≤ ↑(↑(u1.nth j) : ℕ) := by exact_mod_cast (zero_le_graph_vertex u1 j),
        have u1_le_double_s : ↑(↑(u1.nth j) : ℕ) < (2 : ℝ) * s := by exact_mod_cast (graph_vertex_le_double_s u1 j),
        have zero_le_u2 : (0 : ℝ) ≤ ↑(↑(u2.nth j) : ℕ) := by exact_mod_cast (zero_le_graph_vertex u2 j),
        have u2_le_double_s : ↑(↑(u2.nth j) : ℕ) < (2 : ℝ) * s := by exact_mod_cast (graph_vertex_le_double_s u2 j),
        rcases eq_or_lt_or_gt (x1.nth j) (x2.nth j) with x1_eq_x2_at_j | x1_lt_x2_at_j | x1_gt_x2_at_j,
        { rw x1_eq_x2_at_j,
          simp only [ne.def, add_left_inj],
          rw div_eq_div_iff cast_s_ne_zero cast_s_ne_zero,
          simp only [mul_eq_mul_right_iff, nat.cast_inj, nat.cast_eq_zero],
          rw not_or_distrib,
          split,
          { rw [fin.coe_eq_val, fin.coe_eq_val],
            intro u1_val_eq_u2_val,
            exact u1_ne_u2_at_j (fin.eq_of_veq u1_val_eq_u2_val),
          },
          exact s_ne_zero,
        },
        { have x1_le_x2_sub_one : x1.nth j ≤ x2.nth j - 1 := by linarith,
          have cast_x1_le_x2_sub_one : ↑(x1.nth j) ≤ ↑(x2.nth j) - (1 : ℝ) := by exact_mod_cast x1_le_x2_sub_one,
          have u1_div_s_lt_u2_div_s_add_two : ↑(↑(u1.nth j) : ℕ) / (↑s : ℝ) < ↑(↑(u2.nth j) : ℕ) / (↑s : ℝ) + 2 :=
            begin
              have lhs_lt_two : (↑(↑(u1.nth j) : ℕ) : ℝ) / ↑s < 2 :=
                by {rw div_lt_iff zero_lt_cast_s, exact u1_le_double_s},
              have two_le_rhs : 2 ≤ (↑(↑(u2.nth j) : ℕ) : ℝ) / ↑s + 2 :=
                begin
                  simp only [le_add_iff_nonneg_left],
                  rw [le_div_iff zero_lt_cast_s, zero_mul],
                  exact zero_le_u2,
                end,
              linarith,
            end,
          linarith,
        },
        have x1_ge_x2_add_one : x1.nth j ≥ x2.nth j + 1 := by linarith,
        have cast_x1_ge_x2_add_one : ↑(x1.nth j) ≥ ↑(x2.nth j) + (1 : ℝ) := by exact_mod_cast x1_ge_x2_add_one,
        have u1_div_s_lt_u2_div_s_add_two : ↑(↑(u2.nth j) : ℕ) / (↑s : ℝ) < ↑(↑(u1.nth j) : ℕ) / (↑s : ℝ) + 2 :=
          begin
            have lhs_lt_two : (↑(↑(u2.nth j) : ℕ) : ℝ) / ↑s < 2 :=
              by {rw div_lt_iff zero_lt_cast_s, exact u2_le_double_s},
            have two_le_rhs : 2 ≤ (↑(↑(u1.nth j) : ℕ) : ℝ) / ↑s + 2 :=
              begin
                simp only [le_add_iff_nonneg_left],
                rw [le_div_iff zero_lt_cast_s, zero_mul],
                exact zero_le_u1,
              end,
            linarith,
          end,
        linarith,
      end,
    rcases corner1_faceshares_corner2 with ⟨k, irrelevant, corner1_eq_corner2_outside_of_k⟩,
    by_cases k_eq_i : k = i,
    { cases corner1_eq_corner2_outside_of_k j with k_eq_j corner1_eq_corner2_at_j,
      { rw [← k_eq_i, ← k_eq_j] at i_ne_j,
        exact i_ne_j (by refl),
      },
      exact corner1_ne_corner2_at_j corner1_eq_corner2_at_j,
    },
    rename k_eq_i k_ne_i,
    cases corner1_eq_corner2_outside_of_k i with k_eq_i corner1_eq_corner2_at_i,
    exact k_ne_i k_eq_i,
    exact corner1_ne_corner2_at_i corner1_eq_corner2_at_i,
  },
  have corner1_ne_corner2_at_i : corner1.nth i ≠ corner2.nth i :=
    begin
      have cast_rw : (↑(↑(u1.nth i) + s) : ℝ) = ↑(↑(u1.nth i) : ℕ) + (↑s : ℝ) := (↑(vector.nth u1 i) : ℕ).cast_add s,
      rw [corner1_eq_u1_div_s_add_double_x1 i, corner2_eq_u2_div_s_add_double_x2 i, u2_eq_u1_add_s_at_i, cast_rw, add_div, div_self cast_s_ne_zero],
      rcases eq_or_lt_or_gt (x1.nth i) (x2.nth i) with x1_eq_x2_at_i | x1_lt_x2_at_i | x1_gt_x2_at_i,
      { rw x1_eq_x2_at_i,
        norm_num,
      },
      { have x1_le_x2_sub_one : x1.nth i ≤ x2.nth i - 1 := by linarith,
        have cast_x1_le_x2_sub_one : ↑(x1.nth i) ≤ ↑(x2.nth i) - (1 : ℝ) := by exact_mod_cast x1_le_x2_sub_one,
        linarith,
      },
      have x1_ge_x2_add_one : x1.nth i ≥ x2.nth i + 1 := by linarith,
      have cast_x1_ge_x2_add_one : ↑(x1.nth i) ≥ ↑(x2.nth i) + (1 : ℝ) := by exact_mod_cast x1_ge_x2_add_one,
      linarith,
    end,
  have corner1_ne_corner2_at_j : corner1.nth j ≠ corner2.nth j :=
    begin
      rw [corner1_eq_u1_div_s_add_double_x1 j, corner2_eq_u2_div_s_add_double_x2 j],
      have zero_le_u1 : (0 : ℝ) ≤ ↑(↑(u1.nth j) : ℕ) := by exact_mod_cast (zero_le_graph_vertex u1 j),
      have u1_le_double_s : ↑(↑(u1.nth j) : ℕ) < (2 : ℝ) * s := by exact_mod_cast (graph_vertex_le_double_s u1 j),
      have zero_le_u2 : (0 : ℝ) ≤ ↑(↑(u2.nth j) : ℕ) := by exact_mod_cast (zero_le_graph_vertex u2 j),
      have u2_le_double_s : ↑(↑(u2.nth j) : ℕ) < (2 : ℝ) * s := by exact_mod_cast (graph_vertex_le_double_s u2 j),
      rcases eq_or_lt_or_gt (x1.nth j) (x2.nth j) with x1_eq_x2_at_j | x1_lt_x2_at_j | x1_gt_x2_at_j,
      { rw x1_eq_x2_at_j,
        simp only [ne.def, add_left_inj],
        rw div_eq_div_iff cast_s_ne_zero cast_s_ne_zero,
        simp only [mul_eq_mul_right_iff, nat.cast_inj, nat.cast_eq_zero],
        rw not_or_distrib,
        split,
        { rw [fin.coe_eq_val, fin.coe_eq_val],
          intro u1_val_eq_u2_val,
          symmetry' at u1_val_eq_u2_val,
          exact u2_ne_u1_at_j (fin.eq_of_veq u1_val_eq_u2_val),
        },
        exact s_ne_zero,
      },
      { have x1_le_x2_sub_one : x1.nth j ≤ x2.nth j - 1 := by linarith,
        have cast_x1_le_x2_sub_one : ↑(x1.nth j) ≤ ↑(x2.nth j) - (1 : ℝ) := by exact_mod_cast x1_le_x2_sub_one,
        have u1_div_s_lt_u2_div_s_add_two : ↑(↑(u1.nth j) : ℕ) / (↑s : ℝ) < ↑(↑(u2.nth j) : ℕ) / (↑s : ℝ) + 2 :=
          begin
            have lhs_lt_two : (↑(↑(u1.nth j) : ℕ) : ℝ) / ↑s < 2 :=
              by {rw div_lt_iff zero_lt_cast_s, exact u1_le_double_s},
            have two_le_rhs : 2 ≤ (↑(↑(u2.nth j) : ℕ) : ℝ) / ↑s + 2 :=
              begin
                simp only [le_add_iff_nonneg_left],
                rw [le_div_iff zero_lt_cast_s, zero_mul],
                exact zero_le_u2,
              end,
            linarith,
          end,
        linarith,
      },
      have x1_ge_x2_add_one : x1.nth j ≥ x2.nth j + 1 := by linarith,
      have cast_x1_ge_x2_add_one : ↑(x1.nth j) ≥ ↑(x2.nth j) + (1 : ℝ) := by exact_mod_cast x1_ge_x2_add_one,
      have u1_div_s_lt_u2_div_s_add_two : ↑(↑(u2.nth j) : ℕ) / (↑s : ℝ) < ↑(↑(u1.nth j) : ℕ) / (↑s : ℝ) + 2 :=
        begin
          have lhs_lt_two : (↑(↑(u2.nth j) : ℕ) : ℝ) / ↑s < 2 :=
            by {rw div_lt_iff zero_lt_cast_s, exact u2_le_double_s},
          have two_le_rhs : 2 ≤ (↑(↑(u1.nth j) : ℕ) : ℝ) / ↑s + 2 :=
            begin
              simp only [le_add_iff_nonneg_left],
              rw [le_div_iff zero_lt_cast_s, zero_mul],
              exact zero_le_u1,
            end,
          linarith,
        end,
      linarith,
    end,
  rcases corner1_faceshares_corner2 with ⟨k, irrelevant, corner1_eq_corner2_outside_of_k⟩,
  by_cases k_eq_i : k = i,
  { cases corner1_eq_corner2_outside_of_k j with k_eq_j corner1_eq_corner2_at_j,
    { rw [← k_eq_i, ← k_eq_j] at i_ne_j,
      exact i_ne_j (by refl),
    },
    exact corner1_ne_corner2_at_j corner1_eq_corner2_at_j,
  },
  rename k_eq_i k_ne_i,
  cases corner1_eq_corner2_outside_of_k i with k_eq_i corner1_eq_corner2_at_i,
  exact k_ne_i k_eq_i,
  exact corner1_ne_corner2_at_i corner1_eq_corner2_at_i,
end

theorem clique_implies_tiling {d s : ℕ} (s_ne_zero : s ≠ 0) :
  has_clique (Keller_graph d s) (2 ^ d) →
  (∃ (T : set (point d)), is_tiling T ∧ tiling_faceshare_free T) :=
begin
  rintro ⟨clique, clique_card, all_vectors_adj_in_clique⟩,
  let T : set (point d) := { p | ∃ u ∈ clique, ∃ x : int_point d, ∀ i : fin d, p.nth i = (↑(u.nth i) : ℝ) / s + 2 * (x.nth i) },
  use [T, tiling_from_clique_is_tiling s_ne_zero clique clique_card all_vectors_adj_in_clique, 
    tiling_from_clique_faceshare_free s_ne_zero clique clique_card all_vectors_adj_in_clique],
end

theorem clique_existence_refutes_Keller_conjecture {d s : ℕ} (s_ne_zero : s ≠ 0) :
  has_clique (Keller_graph d s) (2^d) → ¬Keller_conjecture d :=
begin
  rw Keller_conjecture,
  simp only [not_forall, not_not, exists_prop],
  exact clique_implies_tiling s_ne_zero,
end

theorem Keller_conjecture_false : ¬Keller_conjecture 8 :=
  clique_existence_refutes_Keller_conjecture (of_to_bool_ff rfl : (2 : ℕ) ≠ 0) G_8_2_has_clique