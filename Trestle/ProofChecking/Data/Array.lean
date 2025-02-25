/-
Copyright (c) 2025 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Trestle.Upstream.ToStd

namespace Array

/--
  A variant of `Array.set` that resizes (fills, hence the `F`) the array
  to make room for the new element. Resizing fills the array with
  the `default`.

  TODO: Write custom C code for this.
-/
@[specialize]
def setF (A : Array α) (i : Nat) (v default : α) : Array α :=
  if hi : i < A.size then
    A.set i v hi
  else
    let rec go (j : Nat) (A' : Array α) : Array α :=
      match j with
      | 0 => A'.push v
      | j + 1 => go j (A'.push default)
    go (i - A.size) A

theorem setF_lt {A : Array α} {i : Nat} (hi : i < A.size) (v default : α) :
    A.setF i v default = A.set i v hi := by
  simp [setF, hi]

theorem setF_lt' {A : Array α} (i : Fin A.size) (v default : α) :
    A.setF i v default = A.set i v :=
  setF_lt i.isLt _ _

@[simp]
theorem setF_eq (A : Array α) (v default : α) :
    A.setF A.size v default = A.push v := by
  simp [setF, setF.go]

@[simp]
theorem setF_go_eq (A : Array α) (i : Nat) (v default : α) :
    setF.go v default i A = (A ++ mkArray i default).push v := by
  induction i generalizing A with
  | zero => rfl
  | succ i ih =>
    rw [setF.go, ih (push A default)]
    simp only [push_eq_append_singleton, mkArray_succ', append_assoc]

theorem setF_gt {A : Array α} {i : Nat} (hi : i > A.size) (v default : α) :
    A.setF i v default = A ++ mkArray (i - A.size) default ++ #[v] := by
  simp [setF, Nat.lt_asymm hi, setF_go_eq]

@[simp]
theorem size_setF (A : Array α) (i : Nat) (v default : α) :
    (A.setF i v default).size = max A.size (i + 1) := by
  rcases Nat.lt_trichotomy i A.size with (hi | rfl | hi)
  · rw [setF_lt hi, size_set]
    exact (Nat.max_eq_left hi).symm
  · rw [setF_eq, size_push, Nat.max_eq_right (Nat.le_succ A.size)]
  · simp [setF, Nat.lt_asymm hi, setF_go_eq, size_append]
    have h_le : A.size ≤ i + 1 := by
      exact Nat.le_trans (Nat.le_of_lt hi) (Nat.le_succ _)
    rw [Nat.max_eq_right h_le, ← Nat.add_sub_assoc (Nat.le_of_lt hi),
      Nat.add_comm A.size i, Nat.add_sub_cancel]

theorem size_le_setF_size (A : Array α) (i : Nat) (v default : α) :
    A.size ≤ (A.setF i v default).size := by
  rw [size_setF]
  exact Nat.le_max_left (size A) (i + 1)

theorem lt_size_setF (A : Array α) (i : Nat) (v default : α) :
    i < size (A.setF i v default) := by
  rw [size_setF]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)

-- CC: This is a rather weak lemma, but it's all that's needed for
--     theorems that want to prove facts about the maximum value of an array.
theorem mem_setF (A : Array α) (i : Nat) (v default : α) {a : α} :
    a ∈ (A.setF i v default) → a ∈ A ∨ a = default ∨ a = v := by
  intro ha
  rcases Nat.lt_trichotomy i A.size with (hi | rfl | hi)
  . simp [setF_lt hi] at ha
    rcases mem_or_eq_of_mem_set ha with (ha | rfl)
    · exact Or.inl ha
    · right; right; rfl
  . simp only [setF_eq, mem_push] at ha
    rcases ha with (h | h)
    · exact Or.inl h
    · exact Or.inr <| Or.inr h
  · simp only [setF_gt hi, append_singleton, mem_push,
      mem_append, mem_mkArray, ne_eq] at ha
    rcases ha with ((h | ⟨_, rfl⟩) | rfl)
    · exact Or.inl h
    · exact Or.inr <| Or.inl rfl
      done
    · exact Or.inr <| Or.inr rfl

@[simp]
theorem getElem_setF_self (A : Array α) (i : Nat) (v default : α) :
    (A.setF i v default)[i]'(lt_size_setF A i v default) = v := by
  rcases Nat.lt_trichotomy i A.size with (hi | rfl | hi)
  · simp only [setF_lt hi, getElem_set_self]
  · simp only [setF_eq, getElem_push_eq]
  · simp [setF_gt hi, getElem_push]
    omega -- Generates a contradiction

theorem getElem_setF_lt (A : Array α) (i : Nat) (v default : α)
    : ∀ (j : Nat) (hj : j < A.size),
      (A.setF i v default)[j]'(Nat.lt_of_lt_of_le hj (size_le_setF_size A i v default)) =
      if i = j then v else A[j] := by
  intro j hj
  by_cases hij : i = j
  · simp [hij]
  · rcases Nat.lt_trichotomy i A.size with (hi | rfl | hi)
    · simp [setF_lt hi]
      rw [get_set]
    · simp [setF_eq, getElem_push, hj, hij]
    · simp [setF_gt hi, hij, getElem_push]
      split
      · simp [getElem_append, hj]
      · omega

@[simp]
theorem getElem?_setF_self (A : Array α) (i : Nat) (v default : α) :
    (A.setF i v default)[i]? = some v := by
  apply getElem?_eq_some_iff.mpr
  simp
  omega

/-@[simp]
theorem getElem?_setF_lt (A : Array α) (i : Nat) (v default : α) :
    ∀ (j : Nat) (hj : j < A.size),
      (A.setF i v default)[j]? = if i = j then some v else some A[j] := by
  intro j hj
  split <;> rename_i hij
  · simp [hij]
  ·

    done
  simp [getElem?_eq_some_iff]
  rw [getElem_setF_lt]
  done -/

/-- CC: Fully characterizes `setF` without worrying about ranges. Kind of a pain though. -/
theorem getElem?_setF (A : Array α) (i j : Nat) (v default : α) :
    (A.setF i v default)[j]? =
      if i = j then some v
      else if i < A.size then A[j]?
      else if hj : j < A.size then some A[j]
      else if j < i then some default
      else none := by
  split <;> rename_i hij
  · simp [hij]
  split <;> rename_i hi
  · simp [setF_lt hi, getElem?_set_ne _ _ hi _ hij]
  split <;> rename_i hj
  · have : j < (setF A i v default).size := by simp; omega
    simp [getElem?_eq_getElem this, getElem_setF_lt A i v default j hj, hij]
  split <;> rename_i hj'
  · by_cases hi_size : i = A.size
    · subst_vars; omega
    · replace hi : i > A.size := by omega
      have : A.size + (i - A.size) = i := by omega
      simp [setF_gt hi, getElem?_push, this, Ne.symm hij, getElem?_append,
        hj, getElem?_mkArray]
      omega
  · by_cases hi_size : i = A.size
    · subst_vars; simp; omega
    · replace hi : i > A.size := by omega
      have : A.size + (i - A.size) = i := by omega
      simp [setF_gt hi, getElem?_push, this, Ne.symm hij, getElem?_append,
        hj, getElem?_mkArray]
      omega

#exit

@[simp]
theorem get_setF_lt_setF (A : Array α) (i : Nat) (v default : α)
    : ∀ (j : Nat) (hj : j < (A.setF i v default).size),
        (A.setF i v default)[j] =
          if h_lt_size : j < A.size then
            A[j]
          else if h_lt : j < i then A[j]'(by
            have := size_setF A i v default

            )
          else default := by

  done
#exit

theorem get_setF' (A : Array α) (i : Nat) (v default : α) :
  ∀ {j : Fin A.size}, j.val ≠ i →
    (A.setF i v default).get ⟨j.val, Nat.lt_of_lt_of_le j.isLt (size_le_setF_size _ _ _ _)⟩ = A.get j := by
  sorry
  done

@[simp] theorem getElem_setF (A : Array α) (i : Nat) (v default : α) :
    (A.setF i v default)[i]'(lt_size_setF A i v default) = v := by
  sorry
  done
  /-
  by_cases hi : i < A.size
  · have := Array.setF_eq_set hi v default
    have h := Array.get_set A ⟨i, hi⟩ i hi v
    simp at h
    sorry
    --rw [← Array.get_eq_getElem] at h
    --have : (set A ⟨i, hi⟩ v)[i] = (setF A i v default)[i] := by
    --  sorry
    --  done
    --rw [← Array.get_eq_getElem] at this
    done
  sorry
  done -/

-- TODO: Match form of Array.get?_set
@[simp] theorem getElem?_setF (A : Array α) (i : Nat) (v default : α) :
    (A.setF i v default)[i]? = some v := by
  sorry

theorem getElem?_setF' {i j : Nat} :
    i ≠ j → ∀ (A : Array α) (v default), (A.setF i v default)[j]? = A[j]? := by
  sorry
  done

end Array
