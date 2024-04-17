/-
Copyright (c) 2022 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/
import Std.Data.List.Lemmas
import Std.Data.Array.Lemmas
import Std.Tactic.ShowTerm

import Mathlib.Data.List.Perm

import ProofChecker.Model.ToMathlib
import ProofChecker.Data.HashMap.Basic
import ProofChecker.Data.HashMap.WF

namespace HashMap
open Std (AssocList)
variable [BEq α] [Hashable α] [LawfulHashable α] [PartialEquivBEq α]

namespace Imp
open List

-- NOTE(WN): These would ideally be solved by a congruence-closure-for-PERs tactic
-- See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Rewriting.20congruent.20relations
-- Same for proofs about List.Perm
private theorem beq_nonsense_1 {a b c : α} : a != b → a == c → b != c :=
  fun h₁ h₂ => Bool.bne_iff_not_beq.mpr fun h₃ =>
    Bool.bne_iff_not_beq.mp h₁ (PartialEquivBEq.trans h₂ (PartialEquivBEq.symm h₃))

private theorem beq_nonsense_2 {a b c : α} : a == b → b == c → ¬(c != a) :=
  fun h₁ h₂ h₃ => Bool.bne_iff_not_beq.mp (bne_symm h₃) (PartialEquivBEq.trans h₁ h₂)

private theorem beq_nonsense_3 {a b c : α} : a != b → c == b  → c != a :=
  fun h₁ h₂ => bne_symm (beq_nonsense_1 (bne_symm h₁) (PartialEquivBEq.symm h₂))

namespace Buckets

/-- The contents of any given bucket are pairwise `bne`. -/
theorem Pairwise_bne_bucket (bkts : Buckets α β) (H : bkts.WF) (h : i < bkts.val.size) :
    Pairwise (·.1 != ·.1) bkts.val[i].toList := by
  have := H.distinct bkts.val[i] (Array.getElem_mem_data _ _)
  exact Pairwise.imp Bool.bne_iff_not_beq.mpr this

/-- Reformulation of `Pairwise_bne_bucket` for use with `List.foo_of_unique`. -/
theorem Pairwise_bne_bucket' (bkts : Buckets α β) (H : bkts.WF) (h : i < bkts.val.size) (a : α) :
    Pairwise (fun p q => p.1 == a → q.1 != a) bkts.val[i].toList :=
  Pairwise.imp beq_nonsense_1 (Pairwise_bne_bucket bkts H h)

/-! ## Main abstraction using `toListModel` -/

/-- It is a bit easier to reason about `foldl (append)` than `foldl (foldl)`, so we use this
(less efficient) variant of `toList` as the mathematical model. -/
def toListModel (bkts : Buckets α β) : List (α × β) :=
  -- Note(WN): the implementation is  `bkts.foldl` rather than `bkts.data.foldl` because we need
  -- to reason about array indices in some of the theorems.
  bkts.val.foldl (init := []) (fun acc bkt => acc ++ bkt.toList)

attribute [local simp] foldl_cons_fn foldl_append_fn

theorem toListModel_eq (bkts : Buckets α β) : bkts.toListModel = bkts.val.data.bind (·.toList) := by
  simp [toListModel, Array.foldl_eq_foldl_data]

theorem mem_toListModel_iff_mem_bucket (bkts : Buckets α β) (H : bkts.WF) (ab : α × β) :
    haveI := mkIdx (hash ab.fst) bkts.property
    ab ∈ bkts.toListModel ↔ ab ∈ (bkts.val[this.1.toNat]'this.2).toList := by
  have : ab ∈ bkts.toListModel ↔ ∃ bkt ∈ bkts.val.data, ab ∈ bkt.toList := by
    simp [toListModel_eq, mem_bind]
  rw [this]
  clear this
  apply Iff.intro
  . intro ⟨bkt, hBkt, hMem⟩
    have ⟨i, hGetI⟩ := Array.get_of_mem_data hBkt
    simp only [getElem_fin] at hGetI
    suffices (mkIdx (hash ab.fst) bkts.property).val.toNat = i by
      simp [Array.ugetElem_eq_getElem, this, hGetI, hMem]
    unfold Imp.mkIdx
    dsimp
    exact H.hash_self i.val i.isLt ab (hGetI ▸ hMem)
  . intro h
    refine ⟨_, Array.getElem_mem_data _ _, h⟩

/-- The map does not store duplicate (by `beq`) keys. -/
theorem Pairwise_bne_toListModel (bkts : Buckets α β) (H : bkts.WF) :
    bkts.toListModel.Pairwise (·.1 != ·.1) := by
  unfold toListModel
  refine Array.foldl_induction
    (motive := fun i (acc : List (α × β)) =>
      -- The acc has the desired property
      acc.Pairwise (·.1 != ·.1)
      -- All not-yet-accumulated buckets are pairwise disjoint with the acc
      ∧ ∀ j, i ≤ j → (_ : j < bkts.val.size) →
        ∀ p ∈ acc, ∀ r ∈ bkts.val[j].toList, p.1 != r.1)
    ?h0 ?hf |>.left
  case h0 => exact ⟨Pairwise.nil, fun.⟩
  case hf =>
    intro i acc h
    refine ⟨pairwise_append.mpr ⟨h.left, ?bkt, ?accbkt⟩, ?accbkts⟩
    case bkt => apply Pairwise_bne_bucket bkts H
    case accbkt =>
      intro a hA b hB
      exact h.right i.val (Nat.le_refl _) i.isLt a hA b hB
    case accbkts =>
      intro j hGe hLt p hP r hR
      cases mem_append.mp hP
      case inl hP => exact h.right j (Nat.le_of_succ_le hGe) hLt p hP r hR
      case inr hP =>
        -- Main proof 2: distinct buckets store bne keys
        refine Bool.bne_iff_not_beq.mpr fun h => ?_
        have hHashEq := LawfulHashable.hash_eq h
        have hGt := Nat.lt_of_succ_le hGe
        have hHashP := H.hash_self i (Nat.lt_trans hGt hLt) _ hP
        have hHashR := H.hash_self j hLt _ hR
        dsimp at hHashP hHashR
        have : i.val = j := by
          rw [hHashEq] at hHashP
          exact .trans hHashP.symm hHashR
        exact Nat.ne_of_lt hGt this

/-- Reformulation of `Pairwise_bne_toListModel` for use with `List.foo_of_unique`. -/
-- TODO: rm in favor of below
theorem Pairwise_bne_toListModel' (bkts : Buckets α β) (H : bkts.WF) (a : α) :
    bkts.toListModel.Pairwise (fun p q => p.1 == a → q.1 != a) :=
  Pairwise.imp beq_nonsense_1 (Pairwise_bne_toListModel bkts H)

theorem unique_toListModel (bkts : Buckets α β) (H : bkts.WF) (a : α) :
    bkts.toListModel.unique (·.1 == a) :=
  Pairwise.imp
    (fun h h₁ h₂ => Bool.bne_iff_not_beq.mp (h h₁) h₂)
    (Pairwise_bne_toListModel' bkts H a)

@[simp]
theorem toListModel_mk (size : Nat) (h : size.isPowerOfTwo) :
    (Buckets.mk (α := α) (β := β) size h).toListModel = [] := by
  simp only [Buckets.mk, toListModel_eq, mkArray_data]
  clear h
  induction size <;> simp [*]

theorem exists_of_toListModel_update (bkts : Buckets α β) (i d h) :
    ∃ l₁ l₂, bkts.toListModel = l₁ ++ bkts.1[i.toNat].toList ++ l₂
      ∧ (bkts.update i d h).toListModel = l₁ ++ d.toList ++ l₂ := by
  have ⟨bs₁, bs₂, hTgt, _, hUpd⟩ := bkts.exists_of_update i d h
  refine ⟨bs₁.bind (·.toList), bs₂.bind (·.toList), ?_, ?_⟩
  . simp [toListModel_eq, hTgt]
  . simp [toListModel_eq, hUpd]

theorem exists_of_toListModel_update_WF (bkts : Buckets α β) (H : bkts.WF) (i d h) :
    ∃ l₁ l₂, bkts.toListModel = l₁ ++ bkts.1[i.toNat].toList ++ l₂
      ∧ (bkts.update i d h).toListModel = l₁ ++ d.toList ++ l₂
      ∧ ∀ ab ∈ l₁, ((hash ab.fst).toUSize % bkts.val.size) < i := by
  have ⟨bs₁, bs₂, hTgt, hLen, hUpd⟩ := bkts.exists_of_update i d h
  refine ⟨bs₁.bind (·.toList), bs₂.bind (·.toList), ?_, ?_, ?_⟩
  . simp [toListModel_eq, hTgt]
  . simp [toListModel_eq, hUpd]
  . intro ab hMem
    have ⟨bkt, hBkt, hAb⟩ := mem_bind.mp hMem
    clear hMem
    have ⟨⟨j, hJ⟩, hEq⟩ := get_of_mem hBkt
    have hJ' : j < bkts.val.size := by
      apply Nat.lt_trans hJ
      simp [Array.size, hTgt, Nat.lt_add_of_pos_right (Nat.succ_pos _)]
    have : ab ∈ (bkts.val[j]).toList := by
      suffices bkt = bkts.val[j] by rwa [this] at hAb
      have := @List.get_append _ _ (bkts.val[i] :: bs₂) j hJ
      dsimp at this
      rw [← hEq, ← this, ← get_of_eq hTgt ⟨j, _⟩]
      rfl
    rwa [hLen, ← H.hash_self _ _ _ this] at hJ

theorem toListModel_reinsertAux (tgt : Buckets α β) (a : α) (b : β) :
    (reinsertAux tgt a b).toListModel ~ (a, b) :: tgt.toListModel := by
  unfold reinsertAux
  have ⟨l₁, l₂, hTgt, hUpd⟩ :=
    haveI := mkIdx (hash a) tgt.property
    tgt.exists_of_toListModel_update this.1 (.cons a b (tgt.1[this.1.toNat]'this.2)) this.2
  simp [hTgt, hUpd, perm_middle]

theorem toListModel_foldl_reinsertAux (bkt : List (α × β)) (tgt : Buckets α β) :
    (bkt.foldl (init := tgt) fun acc x => reinsertAux acc x.fst x.snd).toListModel
    ~ tgt.toListModel ++ bkt := by
  induction bkt generalizing tgt with
  | nil => simp [Perm.refl]
  | cons p ps ih =>
    refine Perm.trans (ih _) ?_
    refine Perm.trans (Perm.append_right ps (toListModel_reinsertAux _ _ _)) ?_
    rw [cons_append]
    refine Perm.trans (Perm.symm perm_middle) ?_
    apply Perm.append_left _ (Perm.refl _)

theorem toListModel_expand (size : Nat) (bkts : Buckets α β) :
    (expand size bkts).buckets.toListModel ~ bkts.toListModel := by
  refine (go _ _ _).trans ?_
  rw [toListModel_mk, toListModel_eq]
  simp [Perm.refl]
where
  go (i : Nat) (src : Array (AssocList α β)) (target : Buckets α β) :
      (expand.go i src target).toListModel
      ~ (src.data.drop i).foldl (init := target.toListModel) (fun a b => a ++ b.toList) := by
    unfold expand.go; split
    case inl hI =>
      refine (go (i +1) _ _).trans ?_
      have h₀ : (src.data.set i AssocList.nil).drop (i + 1) = src.data.drop (i + 1) := by
        apply drop_ext
        intro j hJ
        apply get?_set_ne _ _ (Nat.ne_of_lt <| Nat.lt_of_succ_le hJ)
      have h₁ : (drop i src.data).bind (·.toList) = src.data[i].toList
          ++ (drop (i + 1) src.data).bind (·.toList) := by
        have : i < src.data.length := by simp [hI]
        simp [drop_eq_cons_get _ _ this]
      simp [h₀, h₁]
      rw [← append_assoc]
      refine Perm.append ?_ (Perm.refl _)
      refine Perm.trans (toListModel_foldl_reinsertAux (AssocList.toList src[i]) _) ?_
      exact Perm.refl _
    case inr hI =>
      have : src.data.length ≤ i := by simp [Nat.le_of_not_lt, hI]
      simp [Perm.refl, drop_eq_nil_of_le this]
    termination_by _ i src _ => src.size - i

end Buckets

theorem findEntry?_eq (m : Imp α β) (H : m.buckets.WF) (a : α)
    : m.findEntry? a = m.buckets.toListModel.find? (·.1 == a) := by
  have hPairwiseBkt :
      haveI := mkIdx (hash a) m.buckets.property
      Pairwise (fun p q => p.1 == a → q.1 != a) (m.buckets.val[this.1]'this.2).toList :=
    by apply Buckets.Pairwise_bne_bucket' m.buckets H
  apply Option.ext
  intro (a', b)
  simp only [Option.mem_def, findEntry?, Imp.findEntry?, AssocList.findEntry?_eq,
    find?_eq_some_of_unique (Buckets.Pairwise_bne_toListModel' m.buckets H a),
    find?_eq_some_of_unique hPairwiseBkt,
    and_congr_left_iff]
  intro hBeq
  have : hash a' = hash a := LawfulHashable.hash_eq hBeq
  simp [Buckets.mem_toListModel_iff_mem_bucket m.buckets H, mkIdx, this]

theorem eraseP_toListModel_of_not_contains (m : Imp α β) (H : m.buckets.WF) (a : α) :
    haveI := mkIdx (hash a) m.buckets.property
    ¬(m.buckets.val[this.1.toNat]'this.2).contains a →
    m.buckets.toListModel.eraseP (·.1 == a) = m.buckets.toListModel := by
  intro hContains
  apply eraseP_of_forall_not
  intro ab hMem hEq
  have :
      haveI := mkIdx (hash a) m.buckets.property
      (m.buckets.val[this.1.toNat]'this.2).contains a := by
    simp only [AssocList.contains_eq, List.any_eq_true, mkIdx, ← LawfulHashable.hash_eq hEq]
    exact ⟨ab, (Buckets.mem_toListModel_iff_mem_bucket m.buckets H ab).mp hMem, hEq⟩
  contradiction

theorem toListModel_insert_perm (m : Imp α β) (H : m.buckets.WF) (a : α) (b : β) :
    (m.insert a b).buckets.toListModel ~ (a, b) :: m.buckets.toListModel.eraseP (·.1 == a) := by
  dsimp [insert, cond]; split
  next hContains =>
    have ⟨l₁, l₂, hTgt, hUpd, hProp⟩ :=
      haveI := mkIdx (hash a) m.buckets.property
      m.buckets.exists_of_toListModel_update_WF H this.1
        ((m.buckets.1[this.1.toNat]'this.2).replace a b) this.2
    rw [hUpd, hTgt]
    have hL₁ : ∀ ab ∈ l₁, ¬(ab.fst == a) := fun ab h hEq =>
      Nat.ne_of_lt (LawfulHashable.hash_eq hEq ▸ hProp ab h) rfl
    have ⟨p, hMem, hP⟩ := any_eq_true.mp (AssocList.contains_eq a _ ▸ hContains)
    simp [eraseP_append_right _ hL₁,
      eraseP_append_left (p := fun ab => ab.fst == a) hP _ hMem]
    -- begin cursed manual proofs
    refine Perm.trans ?_ perm_middle
    refine Perm.append (Perm.refl _) ?_
    rw [← cons_append]
    refine Perm.append ?_ (Perm.refl _)
    refine Perm.trans
      (replaceF_of_unique
        (b := (a, b))
        (f := fun a_1 => bif a_1.fst == a then some (a, b) else none)
        hMem
        (by simp [hP])
        (by
          refine Pairwise.imp ?_ (Buckets.Pairwise_bne_bucket' m.buckets H _ a)
          intro p q h hSome
          dsimp at *
          cases hEq: p.fst == a with
          | false => cases hEq ▸ hSome
          | true =>
            have : (q.fst == a) = false :=
              Bool.eq_false_iff.mpr (Bool.bne_iff_not_beq.mp <| h hEq)
            simp [this]))
      ?_
    apply List.Perm.of_eq
    congr
    apply funext
    intro x
    cases h : x.fst == a <;> simp [h]
    -- end cursed manual proofs

  next hContains =>
    rw [eraseP_toListModel_of_not_contains m H a (Bool.eq_false_iff.mp hContains)]
    split
    -- TODO(WN): how to merge the two branches below? They are identical except for the initial
    -- `refine`
    next =>
      have ⟨l₁, l₂, hTgt, hUpd⟩ :=
        haveI := mkIdx (hash a) m.buckets.property
        m.buckets.exists_of_toListModel_update this.1
          ((m.buckets.1[this.1.toNat]'this.2).cons a b) this.2
      simp [hTgt, hUpd, perm_middle]
    next =>
      refine Perm.trans (Buckets.toListModel_expand _ _) ?_
      have ⟨l₁, l₂, hTgt, hUpd⟩ :=
        haveI := mkIdx (hash a) m.buckets.property
        m.buckets.exists_of_toListModel_update this.1
          ((m.buckets.1[this.1.toNat]'this.2).cons a b) this.2
      simp [hTgt, hUpd, perm_middle]

theorem toListModel_erase (m : Imp α β) (H : m.buckets.WF) (a : α) :
    (m.erase a).buckets.toListModel = m.buckets.toListModel.eraseP (·.1 == a) := by
  dsimp [erase, cond]; split
  next hContains =>
    have ⟨l₁, l₂, hTgt, hUpd, hProp⟩ :=
      haveI := mkIdx (hash a) m.buckets.property
      m.buckets.exists_of_toListModel_update_WF H this.1
        ((m.buckets.1[this.1.toNat]'this.2).erase a) this.2
    rw [hTgt, hUpd]
    have hL₁ : ∀ ab ∈ l₁, ¬(ab.fst == a) := fun ab h hEq =>
      Nat.ne_of_lt (LawfulHashable.hash_eq hEq ▸ hProp ab h) rfl
    have ⟨p, hMem, hP⟩ := any_eq_true.mp (AssocList.contains_eq a _ ▸ hContains)
    simp [eraseP_append_right _ hL₁, eraseP_append_left (p := fun ab => ab.fst == a) hP _ hMem]
  next hContains =>
    rw [eraseP_toListModel_of_not_contains m H a (Bool.eq_false_iff.mp hContains)]

theorem eraseP_toListModel (m : Imp α β) (H : m.buckets.WF) (a : α) :
    m.buckets.toListModel.eraseP (·.1 == a) = m.buckets.toListModel.filter (·.1 != a) := by
  apply List.eraseP_eq_filter_of_unique
  apply List.Pairwise.imp ?_ (Buckets.Pairwise_bne_toListModel _ H)
  intro (a₁, _) (a₂, _) hA₁Bne hA₁Beq
  rw [Bool.not_eq_true_iff_ne_true, ← Bool.bne_iff_not_beq]
  exact beq_nonsense_1 hA₁Bne hA₁Beq

theorem toListModel_insert_perm' (m : Imp α β) (H : m.buckets.WF) (a : α) (b : β) :
    (m.insert a b).buckets.toListModel ~ (a, b) :: m.buckets.toListModel.filter (·.1 != a) :=
  eraseP_toListModel m H a ▸ toListModel_insert_perm m H a b

theorem toListModel_erase' (m : Imp α β) (H : m.buckets.WF) (a : α) :
    (m.erase a).buckets.toListModel = m.buckets.toListModel.filter (·.1 != a) :=
  eraseP_toListModel m H a ▸ toListModel_erase m H a

/-! ## Useful high-level theorems -/

theorem findEntry?_insert {a a' b} {m : Imp α β} (H : m.WF) :
    a == a' → (m.insert a b).findEntry? a' = some (a, b) := by
  intro hEq
  have hWF := WF_iff.mp H |>.right
  have hInsWF : (m.insert a b).buckets.WF := H.insert.out |>.right
  rw [findEntry?_eq _ hInsWF]
  have hPerm := toListModel_insert_perm m hWF a b
  have hUniq : (insert m a b).buckets.toListModel.unique (·.1 == a') :=
    Buckets.unique_toListModel _ hInsWF a'
  simp [find?_eq_of_perm_of_unique hPerm hUniq, hEq]

theorem findEntry?_insert_of_ne {a a'} {m : Imp α β} (H : m.WF) :
    a != a' → (m.insert a b).findEntry? a' = m.findEntry? a' := by
  intro hNe
  have hWF := WF_iff.mp H |>.right
  have hInsWF : (m.insert a b).buckets.WF := H.insert.out |>.right
  have hPerm := toListModel_insert_perm' m hWF a b
  have hUniq : (insert m a b).buckets.toListModel.unique (·.1 == a') :=
    Buckets.unique_toListModel _ hInsWF a'
  rw [findEntry?_eq _ hWF, findEntry?_eq _ hInsWF,
    find?_eq_of_perm_of_unique hPerm hUniq,
    find?_cons_of_neg _ ?ne]
  case ne => exact Bool.bne_iff_not_beq.mp hNe
  exact find?_filter _ _ _ fun _ => beq_nonsense_3 hNe

theorem findEntry?_erase {a a'} {m : Imp α β} (H : m.WF) :
    a == a' → (m.erase a).findEntry? a' = none := by
  intro hEq
  have hWF := WF_iff.mp H |>.right
  have hErsWF : (m.erase a).buckets.WF := H.erase.out |>.right
  rw [findEntry?_eq _ hErsWF, toListModel_erase' m hWF a,
    find?_filter' _ _ _ ?ne]
  case ne =>
    intro _ h
    simp only [Bool.bnot_eq_to_not_eq, Bool.not_eq_true, Bool.bne_eq_false]
    exact PartialEquivBEq.trans h (PartialEquivBEq.symm hEq)

end Imp

theorem toList_eq_reverse_toListModel (m : HashMap α β) :
    m.toList = m.val.buckets.toListModel.reverse := by
  simp only [toList, Imp.Buckets.toListModel, fold, Imp.fold, Array.foldl_eq_foldl_data,
    AssocList.foldl_eq, List.foldl_cons_fn]
  suffices ∀ (l₁ : List (AssocList α β)) (l₂ : List (α × β)),
      l₁.foldl (init := l₂.reverse) (fun d b => b.toList.reverse ++ d) =
      (l₁.foldl (init := l₂) fun acc bkt => acc ++ bkt.toList).reverse by
    apply this (l₂ := [])
  intro l₁
  induction l₁ with
  | nil => intro; rfl
  | cons a as ih =>
    intro l₂
    simp only [List.foldl, ← List.reverse_append, ih]

/-! `empty` -/

theorem isEmpty_empty : (HashMap.empty : HashMap α β).isEmpty :=
  sorry

/-! `findEntry?` -/

@[simp]
theorem findEntry?_of_isEmpty (m : HashMap α β) (a : α) : m.isEmpty → m.findEntry? a = none :=
  sorry

@[simp]
theorem findEntry?_empty (a : α) : (HashMap.empty : HashMap α β).findEntry? a = none :=
  findEntry?_of_isEmpty _ a isEmpty_empty

theorem findEntry?_insert {a a'} (m : HashMap α β) (b) :
    a == a' → (m.insert a b).findEntry? a' = some (a, b) :=
  m.val.findEntry?_insert m.property

theorem findEntry?_insert_of_ne {a a'} (m : HashMap α β) (b) :
    a != a' → (m.insert a b).findEntry? a' = m.findEntry? a' :=
  m.val.findEntry?_insert_of_ne m.property

theorem findEntry?_erase {a a'} (m : HashMap α β) : a == a' → (m.erase a).findEntry? a' = none :=
  m.val.findEntry?_erase m.property

theorem ext_findEntry? (m₁ m₂ : HashMap α β) : (∀ a, m₁.findEntry? a = m₂.findEntry? a) → m₁ = m₂ :=
  sorry

/-! `find?` -/

theorem find?_eq (m : HashMap α β) (a : α) : m.find? a = (m.findEntry? a).map (·.2) :=
  AssocList.find?_eq_findEntry? _ _

theorem find?_of_isEmpty (m : HashMap α β) (a : α) : m.isEmpty → m.find? a = none :=
  sorry

@[simp]
theorem find?_empty (a : α) : (HashMap.empty : HashMap α β).find? a = none :=
  find?_of_isEmpty _ a isEmpty_empty

theorem find?_insert {a a'} (m : HashMap α β) (b) : a == a' → (m.insert a b).find? a' = some b :=
  fun h => by simp [find?_eq, findEntry?_insert m b h]

theorem find?_insert_of_ne {a a'} (m : HashMap α β) (b) :
    a != a' → (m.insert a b).find? a' = m.find? a' :=
  fun h => by simp [find?_eq, findEntry?_insert_of_ne m b h]

theorem find?_erase {a a'} (m : HashMap α β) : a == a' → (m.erase a).find? a' = none :=
  fun h => by simp [find?_eq, findEntry?_erase m h]

/-! `insert` -/

theorem insert_comm [LawfulBEq α] (m : HashMap α β) (a₁ a₂ : α) (b : β) :
    (m.insert a₁ b).insert a₂ b = (m.insert a₂ b).insert a₁ b := by
  apply ext_findEntry?
  intro a
  cases Bool.beq_or_bne a₁ a <;> cases Bool.beq_or_bne a₂ a <;>
    simp_all [findEntry?_insert, findEntry?_insert_of_ne]
    
/-! `contains` -/

theorem contains_iff (m : HashMap α β) (a : α) :
    m.contains a ↔ ∃ b, m.find? a = some b :=
  sorry

theorem not_contains_iff (m : HashMap α β) (a : α) :
    m.contains a = false ↔ m.find? a = none := by
  have := contains_iff m a
  apply Iff.intro
  . intro h; cases h' : find? m a <;> simp_all
  . intro h; simp_all
  
theorem not_contains_of_isEmpty (m : HashMap α β) (a : α) : m.isEmpty → m.contains a = false :=
  fun h => not_contains_iff _ _ |>.mpr (find?_of_isEmpty m a h)

@[simp]
theorem not_contains_empty (β) (a : α) : (empty : HashMap α β).contains a = false :=
  not_contains_of_isEmpty _ a isEmpty_empty

theorem contains_insert (m : HashMap α β) (a a' : α) (b : β) :
    (m.insert a b).contains a' ↔ (m.contains a' ∨ a == a') := by
  simp only [contains_iff]
  refine ⟨?mp, fun h => h.elim ?mpr₁ ?mpr₂⟩
  case mp =>
    intro ⟨b, hFind⟩
    cases Bool.beq_or_bne a a'
    case inl h =>
      exact Or.inr h
    case inr h =>
      rw [find?_insert_of_ne _ _ h] at hFind
      exact Or.inl ⟨b, hFind⟩
  case mpr₁ =>
    intro ⟨b, hFind⟩
    cases Bool.beq_or_bne a a'
    case inl h =>
      rw [find?_insert _ _ h]
      exact ⟨_, rfl⟩
    case inr h =>
      rw [find?_insert_of_ne _ _ h]
      exact ⟨_, hFind⟩
  case mpr₂ =>
    intro hEq
    rw [find?_insert _ _ hEq]
    exact ⟨_, rfl⟩
  
/-! `fold` -/

/-- If an entry appears in the map, it will appear "last" in a commutative `fold` over the map. -/
theorem fold_of_mapsTo_of_comm [LawfulBEq α] (m : HashMap α β) (f : δ → α → β → δ) (init : δ) :
    m.find? a = some b →
    -- NOTE: This could be strengthened by assuming m.find? a₁ = some b₁
    -- and ditto for a₂, b₂ in the ∀ hypothesis
    (∀ d a₁ b₁ a₂ b₂, f (f d a₁ b₁) a₂ b₂ = f (f d a₂ b₂) a₁ b₁) →
    -- TODO: Might also have to assume assoc
    ∃ d, m.fold f init = f d a b :=
  sorry
  
/-- Analogous to `List.foldlRecOn`. -/
def foldRecOn {C : δ → Sort _} (m : HashMap α β) (f : δ → α → β → δ) (init : δ) (hInit : C init)
    (hf : ∀ d a b, C d → m.find? a = some b → C (f d a b)) : C (m.fold f init) :=
  sorry

end HashMap
