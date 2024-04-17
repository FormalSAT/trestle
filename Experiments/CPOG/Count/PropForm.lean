/-
Copyright (c) 2023 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Ring
import ProofChecker.Data.Pog

open Finset

/-
This is the counting function for partitioned formulas, also known as POGs. The main theorem,
to be proved below, is that this really does count the number of models.
-/

namespace PropForm

def countModels (nVars : Nat) : PropForm ν → Nat
  | tr         => 2^nVars
  | fls        => 0
  | var _      => 2^(nVars - 1)
  | neg φ      => 2^nVars - φ.countModels nVars
  | disj φ ψ   => φ.countModels nVars + ψ.countModels nVars
  | conj φ ψ   => φ.countModels nVars * ψ.countModels nVars / 2^nVars
  | impl _ _   => 0
  | biImpl _ _ => 0

def ringEval {R : Type} [CommRing R] (weight : ν → R) : PropForm ν → R
  | tr         => 1
  | fls        => 0
  | var x      => weight x
  | neg φ      => 1 - φ.ringEval weight
  | disj φ ψ   => φ.ringEval weight + ψ.ringEval weight
  | conj φ ψ   => φ.ringEval weight * ψ.ringEval weight
  | impl _ _   => 0
  | biImpl _ _ => 0

end PropForm

/-
Propositional assignments and their restrictions to finsets.
-/

namespace PropAssignment

def defined_on (v : PropAssignment ν) (s : Finset ν) : Prop := ∀ ⦃x⦄, x ∉ s → v x = false

theorem eq_false_of_defined_on {v : PropAssignment ν} {s : Finset ν} {x : ν}
    (h : v.defined_on s) (h' : ¬ x ∈ s) : v x = false := h h'

theorem defined_on_mono {v : PropAssignment ν} {s t : Finset ν} (h : s ⊆ t) :
    v.defined_on s → v.defined_on t :=
  fun h' _ hnnt => h' fun hns => hnnt (h hns)

variable [DecidableEq ν]

def restrict (v : PropAssignment ν) (s : Finset ν) : PropAssignment ν := fun x => if x ∈ s then v x else false

@[simp] theorem defined_on_restrict (v : PropAssignment ν) (s : Finset ν) :
    (v.restrict s).defined_on s := by intro n hns; rw [restrict, if_neg hns]

@[simp] theorem restrict_pos (v : PropAssignment ν) {x : ν} {s : Finset ν} (h : x ∈ s) :
    v.restrict s x = v x := by simp [restrict, h]

end PropAssignment

namespace PropForm

variable [DecidableEq ν]

theorem eval_restrict_vars (φ : PropForm ν) (v : PropAssignment ν) :
    φ.eval (v.restrict φ.vars) = φ.eval v :=
  eval_ext fun _ hx => v.restrict_pos hx

end PropForm

namespace Finset

variable [DecidableEq ν]

/-- The characteristic funbction of `s`. -/
def toPropAssignment (s : Finset ν) : PropAssignment ν := fun x => if x ∈ s then true else false

theorem toPropAssignment_eq_true {x : ν} (s : Finset ν) :
    s.toPropAssignment x = true ↔ x ∈ s := by
  rw [toPropAssignment]; split <;> simp_all

theorem toPropAssignment_eq_false {x : ν} (s : Finset ν) :
    s.toPropAssignment x = false ↔ x ∉ s := by
  simp [←toPropAssignment_eq_true]

theorem injective_toPropAssignment : Function.Injective (@toPropAssignment ν _) := by
  intro s1 s2 heq
  ext x
  have := congr_fun heq x
  rw [←s1.toPropAssignment_eq_true, this, s2.toPropAssignment_eq_true]

end Finset

/-
Models of a propositional formula over a set of variables.

Note: we don't intend to use this theory computationally, so we use classical logic to declare
decidable equality on `PropAssignment ν`.
-/

variable [DecidableEq ν]

noncomputable instance : DecidableEq (PropAssignment ν) := fun _ _ => Classical.propDecidable _

namespace Finset

noncomputable def assignments (s : Finset ν) : Finset (PropAssignment ν) :=
  s.powerset.image toPropAssignment

@[simp] theorem mem_assignments (s : Finset ν) (v : PropAssignment ν) :
    v ∈ assignments s ↔ v.defined_on s := by
  simp only [assignments, mem_image, mem_powerset]
  constructor
  . rintro ⟨t, ht1, rfl⟩ x hx
    rw [toPropAssignment_eq_false]
    intro h; exact hx (ht1 h)
  . intro h
    use s.filter (v . = true)
    simp only [filter_subset, true_and]
    ext x
    simp only [toPropAssignment, mem_filter]
    by_cases hx : x ∈ s
    . cases (v x) <;> simp [hx]
    . simp [hx, h hx]

theorem InjOn_set_assignments (s : Finset ν) (hxs : x ∉ s) (b : Bool) :
    Set.InjOn (PropAssignment.set . x b) (assignments s) := by
  intro v1 hv1 v2 hv2 heq
  simp only [mem_coe, mem_assignments] at hv1 hv2
  ext x'
  have := congr_fun heq x'; dsimp at this
  by_cases h : x' = x
  . rw [h, hv1 hxs, hv2 hxs]
  . rwa [PropAssignment.set_get_of_ne _ _ (Ne.symm h),
      PropAssignment.set_get_of_ne _ _ (Ne.symm h)] at this

theorem assignments_empty : assignments (∅ : Finset ν) = {fun _ => false} := by
  ext τ; simp only [mem_assignments, PropAssignment.defined_on, not_mem_empty, not_false_iff,
    forall_true_left, mem_singleton]
  constructor
  . intro h; ext x; simp [h]
  . intro h; simp [h]

theorem card_assignments (s : Finset ν) : card (assignments s) = 2^(card s) := by
  rw [assignments, card_image_of_injective _ injective_toPropAssignment, card_powerset]

end Finset

def PropAssignment.cond (s : Finset ν) (p : PropAssignment ν × PropAssignment ν) :
    PropAssignment ν :=
  fun x => if x ∈ s then p.1 x else p.2 x

namespace PropForm

/-- Models of a propositional formula on a set of variables -/
noncomputable def models (φ : PropForm ν) (s : Finset ν) := s.assignments.filter (φ.eval .)

@[simp] theorem mem_models {φ : PropForm ν} {s : Finset ν} (v : PropAssignment ν) :
    v ∈ φ.models s ↔ v.defined_on s ∧ φ.eval v = true :=
  by rw [models, mem_filter, mem_assignments]

theorem models_tr (s : Finset ν) : tr.models s = assignments s := by
  simp [models]

theorem models_fls (s : Finset ν) : fls.models s = (∅ : Finset (PropAssignment ν)) := by
  ext τ; simp

theorem models_disj {φ ψ : PropForm ν} (s : Finset ν) :
    (φ.disj ψ).models s = (φ.models s) ∪ (ψ.models s) := by
  ext v; simp [mem_models, eval, and_or_left]

theorem models_Disjoint {φ ψ : PropForm ν} (s : Finset ν) (h : ∀ v, ¬ (φ.eval v ∧ ψ.eval v))  :
    Disjoint (φ.models s) (ψ.models s) := by
  rw [disjoint_iff_ne]
  rintro v hv1 _ hv2 rfl
  apply h v
  rw [mem_models] at hv1 hv2
  rw [hv1.2, hv2.2]; simp

theorem models_var {x : ν} {s : Finset ν} (hxs : x ∈ s) :
    (var x).models s = (assignments (s.erase x)).image (PropAssignment.set . x true) := by
    ext v; simp only [mem_models, eval, mem_image]
    constructor
    . intro ⟨hvdef, hvx⟩
      use v.set x false
      constructor
      . rw [mem_assignments]
        intro x' hx'
        rw [mem_erase, not_and] at hx'
        by_cases h : x' = x
        . rw [h, PropAssignment.set_get]
        . rw [PropAssignment.set_get_of_ne _ _ (Ne.symm h), hvdef (hx' h)]
      . rw [PropAssignment.set_set, ←hvx, PropAssignment.set_same]
    . rintro ⟨v', hv', rfl⟩
      rw [mem_assignments] at hv'
      constructor
      . intro x' hx'
        have h1 : x' ≠ x := by rintro rfl; contradiction
        have h2 : x' ∉ erase s x := by rw [mem_erase, not_and_or]; right; exact hx'
        rw [PropAssignment.set_get_of_ne _ _ (Ne.symm h1), hv' h2]
      . simp

theorem models_neg (φ : PropForm ν) (s : Finset ν) :
  φ.neg.models s ∪ φ.models s = assignments s := by
    ext v; simp only [mem_assignments, mem_union, mem_models, eval, Bool.bnot_eq_to_not_eq,
      Bool.not_eq_true]
    rw [←and_or_left]; cases (eval v φ) <;> simp

theorem models_neg_Disjoint (φ : PropForm ν) (s : Finset ν) :
    Disjoint (φ.neg.models s) (φ.models s) := by
  rw [disjoint_iff_ne]
  rintro v hv1 _ hv2 rfl
  rw [mem_models] at hv2
  rw [mem_models, eval, hv2.2] at hv1
  simp at hv1

theorem models_conj {φ ψ: PropForm ν} (hdisj : φ.vars ∩ ψ.vars = ∅) :
  (φ.conj ψ).models ((φ.conj ψ).vars) =
    ((φ.models φ.vars).product (ψ.models ψ.vars)).image (PropAssignment.cond φ.vars) := by
  symm; ext v
  simp only [mem_image, mem_product, mem_models, Prod.exists, eval, Bool.and_eq_true,
    PropAssignment.cond, vars]
  constructor
  . rintro ⟨v1, v2, ⟨⟨_, heval1⟩, ⟨hdef2, heval2⟩⟩, rfl⟩
    constructor
    . intro x hx
      rw [mem_union, not_or] at hx
      dsimp; rw [if_neg hx.1, hdef2 hx.2]
    . constructor
      . rw [←heval1]; apply eval_ext
        intro x hx; rw [if_pos hx]
      . rw [←heval2]; apply eval_ext
        intro x hx
        simp only [eq_empty_iff_forall_not_mem, mem_inter, not_and'] at hdisj
        have hx' : x ∉ φ.vars := hdisj _ hx
        rw [if_neg hx']
  . intro ⟨hdef, heval1, heval2⟩
    use fun x => if x ∈ φ.vars then v x else false
    use fun x => if x ∈ ψ.vars then v x else false
    dsimp
    constructor
    . constructor
      . constructor
        . intro x hx; dsimp; rw [if_neg hx]
        . rw [←heval1]
          apply eval_ext; intro x hx; rw [if_pos hx]
      . constructor
        . intro x hx; dsimp; rw [if_neg hx]
        . rw [←heval2]
          apply eval_ext; intro x hx; rw [if_pos hx]
    . ext x
      have := @hdef x
      split <;> simp_all

theorem InjOn_cond (φ ψ : PropForm ν) {s t : Finset ν} (hdisj : s ∩ t = ∅) :
  Set.InjOn (PropAssignment.cond s) <| (φ.models s).product (ψ.models t) := by
    intro ⟨p11, p12⟩ hp1 ⟨p21, p22⟩ hp2
    simp only [coe_product, Set.mem_prod, mem_coe, mem_models] at hp1 hp2
    simp only [PropAssignment.cond]
    dsimp; intro h
    rw [Prod.mk.injEq]
    constructor
    . ext x
      have := congr_fun h x
      by_cases h' : x ∈ s <;> simp_all
      rw [hp1.1.1 h', hp2.1.1 h']
    . ext x
      have := congr_fun h x
      by_cases h' : x ∈ s <;> simp_all
      simp only [eq_empty_iff_forall_not_mem, mem_inter, not_and] at hdisj
      rw [hp1.2.1 (hdisj _ h'), hp2.2.1 (hdisj _ h')]

theorem models_insert {φ : PropForm ν} {a : ν} {s : Finset ν} (h : φ.vars ⊆ s) (ha : a ∉ s) :
    φ.models (insert a s) = φ.models s ∪ (φ.models s).image (fun τ => τ.set a true) := by
  ext τ
  simp only [mem_models, mem_union, mem_image]
  constructor
  . intro ⟨hdef, heq⟩
    by_cases h' : τ a = true
    . right
      use (τ.set a false)
      constructor
      . constructor
        . intro x xns
          by_cases hx : x = a
          . rw [hx, PropAssignment.set_get]
          . rw [PropAssignment.set_get_of_ne _ _ (Ne.symm hx)]
            apply hdef; simp [xns, hx]
        . rw [eval_set_of_not_mem_vars, heq]
          intro h''; exact ha (h h'')
      . rw [PropAssignment.set_set, ←h', PropAssignment.set_same]
    . left; rw [Bool.not_eq_true] at h'
      constructor
      . intro x xns
        by_cases hx : x = a
        . rw [hx, h']
        . apply hdef; simp [xns, hx]
      . exact heq
  . rintro (⟨hdef, heq⟩ | ⟨τ', ⟨hdef, heval⟩, rfl⟩)
    . exact ⟨PropAssignment.defined_on_mono (Finset.subset_insert _ _) hdef, heq⟩
    . constructor
      . intro x xnas
        rw [mem_insert, not_or] at xnas
        rw [PropAssignment.set_get_of_ne _ _ (Ne.symm xnas.1)]
        exact hdef xnas.2
      . rw [←heval]
        apply eval_ext
        intro x hx
        rw [PropAssignment.set_get_of_ne]
        contrapose! ha; rw [ha]
        exact h hx

theorem models_insert_Disjoint {φ : PropForm ν} {a : ν} {s : Finset ν} (ha : a ∉ s) :
    Disjoint (φ.models s) ((φ.models s).image (fun τ => τ.set a true)) := by
  rw [disjoint_iff_ne]
  rintro τ hτ1 _ hτ2 rfl
  simp only [mem_image, mem_models] at hτ1 hτ2
  rcases hτ2 with ⟨τ', ⟨⟨_, _⟩, rfl⟩⟩
  have := hτ1.1
  specialize this ha
  rw [PropAssignment.set_get] at this
  contradiction

/-
Theorems about cardinality.
-/

@[simp] theorem card_models_tr (s : Finset ν) : card ((tr : PropForm ν).models s) = 2^(card s) := by
  simp [models_tr, card_assignments]

@[simp] theorem card_models_fls (s : Finset ν) : card ((fls : PropForm ν).models s) = 0 := by
  simp [models_fls, card_assignments]

@[simp] theorem card_models_var {x : ν} {s : Finset ν} (hxs : x ∈ s) :
    card ((var x).models s) = 2^(card s - 1) := by
  rw [models_var hxs,
    card_image_of_injOn (Finset.InjOn_set_assignments _ (Finset.not_mem_erase _ _) _),
    card_assignments, card_erase_of_mem hxs]

@[simp] theorem card_models_disj_disjoint {φ ψ : PropForm ν} (s : Finset ν)
      (h : ∀ v, ¬ (φ.eval v ∧ ψ.eval v)) :
    card ((φ.disj ψ).models s) = card (φ.models s) + card (ψ.models s) := by
  rw [models_disj, card_disjoint_union (models_Disjoint _ h)]

@[simp] theorem card_models_neg (φ : PropForm ν) (s : Finset ν) :
    card (φ.neg.models s) = 2^(card s) - card (φ.models s) := by
  symm; apply Nat.sub_eq_of_eq_add
  rw [←card_disjoint_union (models_neg_Disjoint _ _), models_neg, card_assignments]

theorem card_models_vars {φ : PropForm ν} {s : Finset ν} (h : φ.vars ⊆ s) :
    card (φ.models s) = card (φ.models φ.vars) * 2^(card s - card φ.vars) := by
  let f (p : PropAssignment ν × Finset ν) : PropAssignment ν :=
    fun x => if x ∈ φ.vars then p.1 x else p.2.toPropAssignment x
  have h1 : ((φ.models φ.vars).product (s \ φ.vars).powerset).image f = φ.models s := by
    ext v; simp only [mem_image, mem_product, mem_models, mem_powerset, Prod.exists]
    constructor
    { rintro ⟨v, t, ⟨⟨_, hevalv⟩, hh⟩, rfl⟩
      constructor
      . intro x hxns
        have : x ∉ φ.vars := fun h' => hxns (h h')
        dsimp; rw [if_neg this, toPropAssignment_eq_false]
        intro h'; apply hxns; exact subset_sdiff.mp hh |>.1 h'
      . rw [←hevalv]
        apply eval_ext
        intro x hx
        rw [if_pos hx] }
    intro ⟨hvdef, hevalv⟩
    use v.restrict φ.vars, (s \ φ.vars).filter (fun x => v x)
    constructor
    . constructor
      . constructor
        . simp
        . rw [eval_restrict_vars, hevalv]
      . apply filter_subset
    . ext x; dsimp; split
      . next h => rw [v.restrict_pos h]
      . next hmem =>
          unfold Finset.toPropAssignment
          by_cases hxs : x ∈ s <;> split <;> simp_all [@hvdef x]
  have h2 : Set.InjOn f <| (φ.models φ.vars).product (s \ φ.vars).powerset := by
    intro ⟨v1, t1⟩ h21 ⟨v2, t2⟩ h22 h23
    simp only [Set.mem_prod, mem_product, mem_coe, mem_models, Set.mem_preimage, mem_powerset,
      and_imp, subset_sdiff, Prod.forall, Prod.mk.injEq] at h21 h22 h23 |-
    constructor
    . ext x
      by_cases hx : x ∈ φ.vars
      . have := congr_fun h23 x
        simp [hx] at this; exact this
      . rw [h21.1.1 hx, h22.1.1 hx]
    . ext x
      simp at h21
      by_cases hx : x ∈ φ.vars
      . rw [eq_false (disjoint_right.mp h21.2.2 hx), eq_false (disjoint_right.mp h22.2.2 hx)]
      . have := congr_fun h23 x
        simp [hx] at this
        rw [←toPropAssignment_eq_true, this, toPropAssignment_eq_true]
  rw [←h1, card_image_of_injOn h2, card_product, card_powerset, card_sdiff h]

theorem card_models_conj_aux {φ ψ: PropForm ν} (hdisj : φ.vars ∩ ψ.vars = ∅) :
    card ((φ.conj ψ).models (φ.conj ψ).vars) =
      card (φ.models φ.vars) * card (ψ.models ψ.vars) := by
  rw [models_conj hdisj, card_image_of_injOn (InjOn_cond _ _ hdisj), card_product]

@[simp] theorem card_models_conj {φ ψ : PropForm ν} {s : Finset ν}
      (hsub : φ.vars ∪ ψ.vars ⊆ s) (hdisj : vars φ ∩ vars ψ = ∅) :
    card ((φ.conj ψ).models s) = card (φ.models s) * card (ψ.models s) / 2^(card s):= by
  symm; apply Nat.div_eq_of_eq_mul_left
  . apply pow_pos; apply zero_lt_two
  have hφ := union_subset_left hsub
  have hψ := union_subset_right hsub
  have card_un := card_disjoint_union (disjoint_iff_inter_eq_empty.mpr hdisj)
  have aux : card (vars ψ) ≤ card s - card (vars φ) := by
    apply Nat.le_sub_of_add_le
    rw [add_comm, ←card_un]
    exact card_le_of_subset hsub
  have : (φ.conj ψ).vars ⊆ s := by rw [vars, union_subset_iff]; exact ⟨hφ, hψ⟩
  rw [card_models_vars hφ, card_models_vars hψ, card_models_vars this, card_models_conj_aux hdisj]
  rw [mul_right_comm]; simp only [mul_assoc, ←pow_add]
  rw [←Nat.sub_add_comm (card_le_of_subset hψ)]
  rw [Nat.add_sub_assoc aux, add_comm (card s)]
  rw [vars, card_un, tsub_tsub]

/-
The main theorem.
-/

theorem countModels_eq_card_models {φ : PropForm ν} {s : Finset ν}
      (hvars : φ.vars ⊆ s) (hdec : φ.partitioned) :
    φ.countModels s.card = card (φ.models s) := by
  induction φ
  case var x      =>
    rw [vars, singleton_subset_iff] at hvars
    rw [countModels, card_models_var hvars]
  case tr         => simp [countModels]
  case fls        => simp [countModels]
  case neg φ ih   =>
    rw [vars] at hvars
    rw [partitioned] at hdec
    rw [countModels, card_models_neg φ, ih hvars hdec]
  case conj φ ψ ihφ ihψ =>
    rw [vars] at hvars
    have hφ := union_subset_left hvars
    have hψ := union_subset_right hvars
    rw [partitioned] at hdec
    rw [countModels, card_models_conj hvars hdec.2.2, ihφ hφ hdec.1, ihψ hψ hdec.2.1]
  case disj φ ψ ihφ ihψ =>
    rw [vars, union_subset_iff] at hvars
    rw [partitioned] at hdec
    rw [countModels, card_models_disj_disjoint s hdec.2.2, ihφ hvars.1 hdec.1, ihψ hvars.2 hdec.2.1]
  case impl  _    => rw [partitioned] at hdec; contradiction
  case biImpl _ _ => rw [partitioned] at hdec; contradiction

end PropForm

/-
Weighted models
-/

namespace PropForm

variable {R : Type} [CommRing R]

open BigOperators

noncomputable def weightSum (weight : ν → R) (φ : PropForm ν) (s : Finset ν) : R :=
  ∑ τ in φ.models s, ∏ x in s, if τ x then weight x else 1 - weight x

theorem injective_models_set {φ : PropForm ν} {a : ν} {s : Finset ν} {b : Bool} (h' : a ∉ s) :
  ∀ x ∈ models φ s, ∀ y ∈ models φ s,
      PropAssignment.set x a b = PropAssignment.set y a b → x = y := by
  simp only [mem_models]
  intro τ1 ⟨τ1def, _⟩ τ2 ⟨τ2def, _⟩ heq
  ext x
  have := congr_fun heq x
  by_cases h : a = x
  . rw [←h, τ1def h', τ2def h']
  . simp [PropAssignment.set_get_of_ne _ _ h] at this
    exact this

theorem weightSum_insert (weight : ν → R) {φ : PropForm ν} {a : ν} {s : Finset ν}
      (h : φ.vars ⊆ s) (h' : a ∉ s) :
    weightSum weight φ (insert a s) = weightSum weight φ s := by
  rw [weightSum, models_insert h h', Finset.sum_union (models_insert_Disjoint h')]
  rw [Finset.sum_image (injective_models_set h'), ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro τ hτ; rw [mem_models] at hτ
  rw [Finset.prod_insert h', Finset.prod_insert h']; dsimp
  have : τ a ≠ true := by rw [hτ.1 h']; simp
  rw [if_neg this, PropAssignment.set_get, if_pos rfl]
  have : ∀ x, x = (1 - weight a) * x + weight a * x :=
    by intro x; rw [←add_mul, sub_add_cancel, one_mul]
  symm; trans; apply this
  apply congr_arg; apply congr_arg; apply Finset.prod_congr rfl
  intro x xs; rw [PropAssignment.set_get_of_ne]; rintro rfl; exact h' xs

theorem weightSum_of_vars_subset (weight : ν → R) {φ : PropForm ν} {s : Finset ν}
    (h : φ.vars ⊆ s) : weightSum weight φ s = weightSum weight φ φ.vars := by
  suffices : ∀ t, φ.vars ∩ t = ∅ → weightSum weight φ φ.vars = weightSum weight φ (φ.vars ∪ t)
  . specialize this (s \ φ.vars) (Finset.inter_sdiff_self _ _)
    rw [this, Finset.union_sdiff_of_subset h]
  intro t
  induction t using Finset.induction
  . next => simp
  . next a t anint ih =>
    intro hdisj
    rw [weightSum, Finset.union_insert, weightSum_insert, ←ih]; rfl
    . rw [←subset_empty, ←hdisj]; apply inter_subset_inter_left
      apply subset_insert
    . apply subset_union_left
    rw [mem_union, not_or]
    refine ⟨?_, anint⟩
    intro ha
    apply not_mem_empty a
    rw [←hdisj, mem_inter]
    exact ⟨ha, mem_insert_self _ _⟩

theorem ringEval_eq_weightSum (weight : ν → R) {φ : PropForm ν} (hdec : φ.partitioned) :
    φ.ringEval weight = φ.weightSum weight φ.vars := by
  have weightSum_tr : weightSum weight tr (vars tr) = 1 := by
    rw [weightSum, models_tr, vars, assignments_empty, sum_singleton, prod_empty]
  induction φ
  case var x      =>
    rw [ringEval, weightSum, vars, models_var (mem_singleton_self x), erase_singleton,
         assignments_empty, image_singleton, sum_singleton, prod_singleton,
         PropAssignment.set_get, if_pos rfl]
  case tr         =>
    rw [ringEval, weightSum_tr]
  case fls        =>
    rw [ringEval, weightSum, models_fls, sum_empty]
  case neg φ ih   =>
    rw [partitioned] at hdec
    rw [ringEval, ih hdec, sub_eq_iff_eq_add, vars, weightSum, weightSum,
        ←sum_union (models_neg_Disjoint _ _), models_neg, ←models_tr, ←weightSum,
        weightSum_of_vars_subset, weightSum_tr]
    simp [vars]
  case conj φ ψ ihφ ihψ =>
    rw [partitioned] at hdec
    have hDisj : Disjoint φ.vars ψ.vars := by
      rw [disjoint_iff_inter_eq_empty]; exact hdec.2.2
    rw [ringEval, weightSum, models_conj hdec.2.2, ihφ hdec.1, ihψ hdec.2.1,
        sum_image (InjOn_cond _ _ hdec.2.2), sum_product, weightSum, mul_comm,
        mul_sum]
    apply sum_congr rfl
    intros τ _
    rw [mul_comm, weightSum, mul_sum]
    apply sum_congr rfl
    intros τ' _
    rw [vars, prod_union hDisj]
    apply congr; apply congr_arg
    . apply prod_congr rfl
      intros x hx; simp [hx, PropAssignment.cond]
    . apply prod_congr rfl
      intros x hx
      have hx' : x ∉ φ.vars := by
        intro h
        apply not_mem_empty x
        rw [←hdec.2.2, mem_inter]
        exact ⟨h, hx⟩
      simp [hx', PropAssignment.cond]
  case disj φ ψ ihφ ihψ =>
    rw [partitioned] at hdec
    have h1 : vars φ ⊆ vars (φ.disj ψ) := subset_union_left _ _
    have h2 : vars ψ ⊆ vars (φ.disj ψ) := subset_union_right _ _
    rw [ringEval, ihφ hdec.1, ihψ hdec.2.1, ←weightSum_of_vars_subset _ h1,
      ←weightSum_of_vars_subset _ h2]
    unfold weightSum
    rw [models_disj, sum_union (models_Disjoint _ hdec.2.2)]
  case impl  _    => rw [partitioned] at hdec; contradiction
  case biImpl _ _ => rw [partitioned] at hdec; contradiction

end PropForm

