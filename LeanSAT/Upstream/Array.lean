import Std
import Init.Data.Nat.Basic
import LeanSAT.Upstream.ToStd

namespace Array

open Nat

/-! # setF - a dynamic sizing setting function for arrays -/

/- A new set operation that fills in with a provided default value until hitting the index -/

/-
Custom-written C++ code is yet to be written.
Below is a functional implementation.

One alternate implementation is to use Array.ofFn to copy over the array.
In order to determine if it's better, profile it.

Note: @implemented_by can refer to other Lean implementations!
  That can help profile the different versions at runtime.
-/

def setF (A : Array α) (i : Nat) (v default : α) : Array α :=
  if hi : i < A.size then
    A.set ⟨i, hi⟩ v
  else
    let rec go (j : Nat) (A' : Array α) : Array α :=
      match j with
      | 0 => A'.push v
      | j + 1 => go j (A'.push default)
    go (i - A.size) A

-- Cayden TODO: An alternate setting that transforms the cell rather than overwriting it
-- Possible time savings
def setF' (A : Array α) (i : Nat) (f : Option α → α) (default : α) : Array α :=
  if hi : i < A.size then
    A.set ⟨i, hi⟩ (f (A.get ⟨i, hi⟩))
  else
    let rec go (j : Nat) (A' : Array α) : Array α :=
      match j with
      | 0 => A'.push (f none)
      | j + 1 => go j (A'.push default)
    go (i - A.size) A

theorem setF_eq_setF' {A : Array α} {i : Nat} {f : Option α → α} {v default : α} :
    (∀ (x : Option α), f x = v) → A.setF i v default = A.setF' i f default := by
  intro hf
  simp [setF, setF']
  by_cases hi : i < A.size
  <;> simp [hi, hf]
  · sorry

section setF

theorem setF_eq_set {A : Array α} {i : Nat} (hi : i < A.size) (v default : α) :
    A.setF i v default = A.set ⟨i, hi⟩ v := by
  simp [setF, hi]

theorem setF_eq_set' {A : Array α} (i : Fin A.size) :
    ∀ (v default), A.setF i v default = A.set i v :=
  Array.setF_eq_set i.isLt

theorem setF_eq_push {A : Array α} (v default : α) :
    A.setF A.size v default = A.push v := by
  simp [setF, setF.go]

-- CC TODO: Private lemmas for the next two, since they refer to setF.go?
theorem setF_go_eq (A : Array α) (i : Nat) (v default : α) :
    setF.go v default i A = (A ++ mkArray i default).push v := by
  induction i generalizing A with
  | zero => rfl
  | succ i ih =>
    rw [setF.go, ih (push A default)]
    apply congrArg₂
    · rw [mkArray_succ, Array.push_eq_append_singleton, Array.append_assoc]
    · rfl

theorem size_setF_go (A : Array α) (i : Nat) (v default : α) :
    (Array.setF.go v default i A).size = A.size + i + 1 := by
  rw [Array.setF_go_eq, Array.size_push, Array.size_append, Array.size_mkArray]

@[simp] theorem size_setF (A : Array α) (i : Nat) (v default : α) :
    (A.setF i v default).size = max A.size (i + 1) := by
  rcases Nat.lt_trichotomy i A.size with (hi | rfl | hi)
  · rw [setF_eq_set hi, size_set]
    exact (Nat.max_eq_left hi).symm
  · rw [setF_eq_push, size_push, Nat.max_eq_right (le_succ A.size)]
  · simp [setF, Nat.lt_asymm hi, setF_go_eq, size_append]
    have h_le : A.size ≤ i + 1 := by
      exact Nat.le_trans (Nat.le_of_lt hi) (Nat.le_succ _)
    rw [Nat.max_eq_right h_le, ← Nat.add_sub_assoc (Nat.le_of_lt hi),
      Nat.add_comm A.size i, Nat.add_sub_cancel]

theorem size_le_setF_size (A : Array α) (i : Nat) (v default : α) :
    A.size ≤ (A.setF i v default).size := by
  rw [Array.size_setF]
  exact Nat.le_max_left (size A) (i + 1)

theorem lt_size_setF (A : Array α) (i : Nat) (v default : α) :
    i < size (A.setF i v default) := by
  rw [Array.size_setF]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)

theorem setF_eq_of_gt (A : Array α) {i : Nat} (hi : i > A.size) (v default : α) :
    A.setF i v default = A ++ mkArray (i - A.size) default ++ #[v] := by
  simp [setF, Nat.lt_asymm hi, Array.setF_go_eq]; rfl

theorem setF_eq_of_ge (A : Array α) {i : Nat} (hi : i ≥ A.size) (v default : α) :
    A.setF i v default = (A ++ mkArray (i - A.size) default).push v := by
  simp [setF, Nat.not_lt.mpr hi, Array.setF_go_eq]

theorem setF_setF (A : Array α) (i : Nat) (v v' default : α) :
    (A.setF i v default).setF i v' default = A.setF i v' default := by
  by_cases hi : i < A.size
  · rw [Array.setF_eq_set hi, Array.setF_eq_set hi]
    rw [← Array.size_set A ⟨i, hi⟩ v] at hi
    rw [Array.setF_eq_set hi]
    apply Array.set_set
  · have : i < size (A.setF i v default) := by
      rw [Array.size_setF]
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)
    simp [Array.setF, hi, this]
    have : i < size (setF.go v default (i - size A) A) := by
      rw [Array.size_setF_go A (i - A.size) v default, ← Nat.add_sub_assoc (Nat.not_lt.mp hi),
        Nat.add_comm A.size i, Nat.add_sub_cancel]
      exact Nat.lt_succ_self _
    simp [this]
    sorry
    done
  done

theorem mem_setF (A : Array α) (i : Nat) (v default : α) :
    ∀ a ∈ (A.setF i v default).data, a ∈ A.data ∨ a = default ∨ a = v := by
  intro a ha
  by_cases h : i < A.size
  . simp [Array.setF_eq_set h] at ha
    rcases List.mem_set ha with (ha | rfl)
    · exact Or.inl ha
    · right; right; rfl
  . rw [Nat.not_lt] at h
    simp only [A.setF_eq_of_ge h,  push_data, append_data, mkArray_data,
      List.append_assoc, List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | ha | rfl)
    · exact Or.inl ha
    · right; left; exact List.eq_of_mem_replicate ha
    · right; right; rfl

/-
#check Array.get_set
∀ {α : Type u_1} (a : Array α) (i : Fin (Array.size a)) (j : ℕ) (hj : j < Array.size a) (v : α),
  (Array.set a i v)[j] = if ↑i = j then v else a[j]
-/

-- TODO: Expand this into the upper definition later
theorem get_setF (A : Array α) (i : Nat) (v default : α) :
    (A.setF i v default).get ⟨i, lt_size_setF A i v default⟩ = v := by sorry

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

theorem getElem?_setF' (A : Array α) {i j : Nat} (v default : α) :
    i ≠ j → (A.setF i v default)[j]? = A[j]? := by
  sorry
  done

end setF /- section -/

end Array
