/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Experiments.Keller.Autos

import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.LiftLets
import Lean.Elab.GuardMsgs

namespace Keller.SymmBreak

/-! ## Matrix Symmetries

For Keller graph with `n≥5`, we can freely swap the last `n-2` columns
on dimension indices 2,3,4 from `c_7`, `c_11`, `c_19`
by permuting those indices and renumbering the colors at each index.
-/

@[ext]
structure Matrix (s) where
  data : Vector (Vector (Fin s) 3) 3
  transpose_one : ∀ i j : Fin 3, data[i][j].val = 1 ∨ data[j][i].val = 1
deriving DecidableEq, Repr

abbrev Matrix.get (r c : Fin 3) (m: Matrix s) : Fin s := m.data[r][c]

theorem Matrix.s_ge_2 (m : Matrix s) : s ≥ 2 := by
  have := m.data[0][0].isLt
  have := m.transpose_one 0 0
  simp at this
  omega

instance : Inhabited (Matrix (s+2)) where
  default := { data := Vector.ofFn fun r => Vector.ofFn fun c => 1, transpose_one := by simp }

def Matrix.toVec (m : Matrix s) : Vector (Fin s) 6 :=
  ⟨#[m.get 0 1, m.get 0 2, m.get 1 0, m.get 1 2, m.get 2 0, m.get 2 1],by simp⟩

def Matrix.ofVec? (v : Vector (Fin s) 6) : Option (Matrix s) :=
  if h : 1 < s then
    let data := data h
    if transpose_one : _ then
      some { data, transpose_one }
    else none
  else none
where data (h) := ⟨#[
  ⟨#[⟨1,h⟩,v[0] ,v[1] ],by simp⟩,
  ⟨#[v[2] ,⟨1,h⟩,v[3] ],by simp⟩,
  ⟨#[v[4] ,v[5] ,⟨1,h⟩],by simp⟩], by simp⟩

theorem Matrix.ofVec?.data_toVec (m : Matrix s) : Matrix.ofVec?.data m.toVec m.s_ge_2 = m.data := by
  rcases m with ⟨d,t⟩
  simp [toVec, data]
  have t00 := t 0 0; have t11 := t 1 1; have t22 := t 2 2
  simp at t00 t11 t22
  ext r hr c hc
  rcases r with (_|_|_) <;> (
    simp; simp [Nat.add_one_lt_add_one_iff] at hr
    rcases c with (_|_|_) <;> (
      simp [Nat.add_one_lt_add_one_iff] at hc
      simp [*]))

@[simp]
theorem Matrix.ofVec?_toVec (m : Matrix s) : Matrix.ofVec? m.toVec = some m := by
  have h : 1 < s := m.s_ge_2
  simp only [ofVec?, h, dite_true, ofVec?.data_toVec]
  simp only [Option.dite_none_right_eq_some, exists_prop, and_true]
  exact m.transpose_one

theorem Matrix.toVec_inj (m1 m2 : Matrix s) : m1.toVec = m2.toVec → m1 = m2 := by
  intro h
  simpa [Matrix.ofVec?_toVec] using congrArg Matrix.ofVec? h

/-! ### Matrix <, ≤

We use these relations to justify an inductive argument that
all matrices are related to canonical ones.
-/

def Matrix.lt (x y : Matrix s) : Bool :=
  Prod.Lex (· > ·) (· < ·) (aux x) (aux y)
where aux (m : Matrix s) :=
  ( decide (m.data[0][2].val = 1)
  , m.toVec.toList )

instance : LT (Matrix s) where
  lt := (Matrix.lt · · = true)

instance {x y : Matrix s} : Decidable (x < y) := Bool.decEq ..
instance : IsTrans (Matrix s) (· < ·) where
  trans := by
    intro a b c; simp [instLTMatrix, Matrix.lt]
    intro h1 h2; trans; exact h1; exact h2

instance : IsIrrefl (Matrix s) (· < ·) where
  irrefl := by
    intro a
    simp [instLTMatrix, Matrix.lt, Prod.lex_iff]

def Matrix.le (x y : Matrix s) : Bool :=
  Prod.Lex (· > ·) (· ≤ ·) (Matrix.lt.aux x) (Matrix.lt.aux y)

instance : LE (Matrix s) where
  le := (Matrix.le · · = true)

instance {x y : Matrix s} : Decidable (x ≤ y) := Bool.decEq ..
instance : IsTrans (Matrix s) (· ≤ ·) where
  trans := by
    intro a b c; simp [instLEMatrix, Matrix.le]
    intro h1 h2; trans; exact h1; exact h2

instance : IsAntisymm (Matrix s) (· ≤ ·) where
  antisymm := by
    intro a b h1 h2
    simp [instLEMatrix, Matrix.le] at h1 h2
    have := Prod.instIsAntisymmLexOfIsStrictOrder.antisymm _ _ h1 h2
    simp [Matrix.lt.aux, Vector.map] at this
    apply Matrix.toVec_inj; apply Vector.ext'
    exact this.2

instance : IsTotal (Matrix s) (· ≤ ·) where
  total := by
    intro a b
    simp [instLEMatrix, Matrix.le]
    exact
      total_of (Prod.Lex (fun x1 x2 => x1 > x2) fun x1 x2 => x1 ≤ x2) (Matrix.lt.aux a)
        (Matrix.lt.aux b)

def Matrix.castLE (m : Matrix s) {s'} (h : s ≤ s') : Matrix s' where
  data := .ofFn fun r => .ofFn fun c => m.data[r][c].castLE h
  transpose_one := by simp; exact m.transpose_one


/-! ### Matrix Fintype

`Matrix s` is a finite type. We use this to show that `Matrix.lt` is well-founded.

It also allows us to iterate over all matrices,
so universally quantified statements `∀ m : Matrix s, P m` are decidable.
We use this in the proof of `Matrix.canonicalCases_are_canonical`,
which is proven by `decide`.
-/

instance : Fintype (Matrix s) where
  elems :=
    Finset.univ (α := Vector (Vector (Fin s) 3) 3)
    |>.filterMap (fun v =>
      if h : _ then
        some ⟨v,h⟩
      else none)
      (by simp only [Option.mem_def, Option.dite_none_right_eq_some, Option.some.injEq, forall_exists_index, forall_apply_eq_imp_iff, Matrix.mk.injEq]
          intro _ _ _ _ h; exact h.symm)
  complete := by
    intro m
    simp only [Finset.mem_filterMap, Finset.mem_univ, Option.dite_none_right_eq_some, true_and]
    use m.data, m.transpose_one

instance : WellFoundedLT (Matrix s) where
  wf := Finite.wellFounded_of_trans_of_irrefl ..


/-! ### Matrix.Perm

This is one of the two operations which we use to canonicalize the matrices.
-/

def Matrix.Perm := Equiv.Perm (Fin 3)

def Matrix.Perm.all : List Matrix.Perm := [
  Equiv.refl _,
  Equiv.Perm.setAll [(0,0),(1,2),(2,1)],
  Equiv.Perm.setAll [(0,1),(1,0),(2,2)],
  Equiv.Perm.setAll [(0,1),(1,2),(2,0)],
  Equiv.Perm.setAll [(0,2),(1,0),(2,1)],
  Equiv.Perm.setAll [(0,2),(1,1),(2,0)],
]

@[simp] theorem Matrix.Perm.mem_all (p : Matrix.Perm) : p ∈ all := by
  simp [all, p.ext_iff, Fin.forall_fin_succ, Equiv.Perm.setAll, Equiv.setAll, Equiv.setValue, Equiv.swap, Equiv.swapCore]
  have p01 : (show Equiv.Perm _ from p) 0 ≠ (show Equiv.Perm _ from p) 1 := by simp
  have p02 : (show Equiv.Perm _ from p) 0 ≠ (show Equiv.Perm _ from p) 2 := by simp
  have p12 : (show Equiv.Perm _ from p) 1 ≠ (show Equiv.Perm _ from p) 2 := by simp
  generalize (show Equiv.Perm _ from p) 0 = p0 at *
  generalize (show Equiv.Perm _ from p) 1 = p1 at *
  generalize (show Equiv.Perm _ from p) 2 = p2 at *
  rcases p0 with ⟨(_|_|_),_⟩ <;>
    rcases p1 with ⟨(_|_|_),_⟩ <;>
      rcases p2 with ⟨(_|_|_),_⟩ <;> simp_all [Fin.ext_iff] <;> omega

def Matrix.Perm.apply (m : Matrix s) (a: Matrix.Perm) : Matrix s := {
  data := Vector.ofFn fun r => Vector.ofFn fun c => m.get (a.toFun r) (a.toFun c)
  transpose_one := by intros; simp; apply m.transpose_one
}

def Matrix.Perm.id : Matrix.Perm := Equiv.refl _

@[simp] theorem Matrix.Perm.apply_id (m : Matrix s) :
    Matrix.Perm.apply m id = m := by
  ext; simp [apply, id]


/-! ### Matrix.Renumber

This is the second of the two operations which we use to canonicalize the matrices.
-/

structure Matrix.Renumber (s) (h : s > 1 := by trivial) where
  renumber : Fin 3 → (Fin s ≃ Fin s)
  renumber_0 : ∀ i, (renumber i) ⟨0,by omega⟩ = ⟨0,by omega⟩
  renumber_1 : ∀ i, (renumber i) ⟨1,by omega⟩ = ⟨1,by omega⟩

def Matrix.Renumber.apply (m : Matrix s) (a : Matrix.Renumber s h) : Matrix s := {
  data := Vector.ofFn fun r => Vector.ofFn fun c => (a.renumber c) (m.get r c)
  transpose_one := by
    intro x y
    rcases m.transpose_one x y with (h1|h1) <;> (
      simp at h1
      replace h1 := Fin.eq_of_val_eq (j := ⟨1,h⟩) h1
      simp [h1, a.renumber_1])
}

def Matrix.Renumber.id (s) (h : s > 1 := by trivial) : Matrix.Renumber s h where
  renumber := fun _ => Equiv.refl _
  renumber_0 := by simp
  renumber_1 := by simp

@[simp] theorem Matrix.Renumber.apply_id (m : Matrix s) (h : s > 1 := by trivial) :
    Matrix.Renumber.apply m (id s h) = m := by
  ext; simp [apply, id]

/-! ### Increment Sorted

We say a list is "increment sorted" when every
element in the list is `≤ (max before the element)+1`.

For example, `[0,1,2,0]` is inc sorted, and `[0,1,3,0]` is not.

For any list `L`, we can construct a permutation `p`
such that `L.map p` is inc sorted.

This is a funky looking function with a big job.
Given a list `L : List (Fin s)` of values, it returns a permutation on `Fin s`
such that `L` mapped by the permutation is "incrementally increasing".
i.e. `L'[j] = x + 1` implies `∃ j' < j, L[j'] = x`.
-/

def incSorted (L : List (Fin s)) : Prop :=
  ∀ pre x, pre ≠ [] → (pre ++ [x]) <+: L → ∃ y ∈ pre, x.val ≤ y.val + 1

theorem incSorted.nil : incSorted (s := s) [] := by simp [incSorted]
theorem incSorted.singleton : incSorted (s := s) [x] := by
  simp [incSorted]
  rintro (_|⟨pre_hd,pre_tl⟩) y h1 h2 <;> simp_all

theorem incSorted.snoc (L : List (Fin s)) (x : Fin s) (exists_prev : ∃ y ∈ L, x.val ≤ y.val + 1) (h : incSorted L) :
      incSorted (L ++ [x]) := by
  intro pre y pre_ne_nil pre_prefix
  rw [List.prefix_concat_iff] at pre_prefix
  cases pre_prefix
  case inl pre_eq_L =>
    replace pre_eq_L := List.append_inj' pre_eq_L rfl
    simp at pre_eq_L; rcases pre_eq_L with ⟨rfl,rfl⟩
    exact exists_prev
  case inr pre_prefix =>
    exact h pre y pre_ne_nil pre_prefix

def renumberIncr (L : List (Fin s)) : Equiv.Perm (Fin s) :=
  let dedup := L.reverse.dedup.reverse
  let pairs := dedup.zip (List.finRange s)
  Equiv.Perm.setAll pairs

/-- info: [0, 1, 2, 1, 3, 4, 0] -/
#guard_msgs in
#eval let L : List (Fin 10) := [0,2,1,2,5,3,0]
      L.map (renumberIncr L)

lemma renumberIncr.dedup_length (L : List (Fin s)) : L.dedup.length ≤ s := by
  simpa only [Fintype.card_fin] using L.nodup_dedup.length_le_card

lemma renumberIncr.dedup_length_of_not_mem (L : List (Fin s)) {x : Fin s} (hx : x ∉ L) :
    L.dedup.length < s := by
  simpa only [Fintype.card_fin, hx, not_false_eq_true, List.dedup_cons_of_not_mem]
    using (x :: L).nodup_dedup.length_le_card

theorem renumberIncr.eq_of_mem' (L : List (Fin s)) (i : Nat) (hi : i < L.reverse.dedup.reverse.length) :
      renumberIncr L (L.reverse.dedup.reverse[i]'hi) = ⟨i, by
        have := dedup_length L.reverse
        simp at hi; omega⟩ := by
  apply Equiv.Perm.setAll_eq_of_mem
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj i_lt_j
    simp at hi hj ⊢
    rw [L.reverse.nodup_dedup.getElem_inj_iff]
    omega
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj i_lt_j
    simp at hi hj ⊢
    omega
  · apply List.mem_iff_getElem.mpr
    have := dedup_length L.reverse
    simp at hi; simp_all

theorem renumberIncr.eq_of_mem (L : List (Fin s)) {x y : Fin s}
      (hy : y.val < L.reverse.dedup.reverse.length) (h : x = L.reverse.dedup.reverse[y]) :
      renumberIncr L x = y := by
  apply Equiv.Perm.setAll_eq_of_mem
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj i_lt_j
    simp at hi hj ⊢
    rw [L.reverse.nodup_dedup.getElem_inj_iff]
    omega
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj i_lt_j
    simp at hi hj ⊢
    omega
  · apply List.mem_iff_getElem.mpr
    have := dedup_length L.reverse
    use y
    simp at hy
    simp_all

theorem renumberIncr.snoc_mem (L : List (Fin s)) {x : Fin s} (x_mem : x ∈ L) :
    renumberIncr (L ++ [x]) = renumberIncr L := by
  simp [renumberIncr, x_mem]

theorem renumberIncr.snoc_not_mem (L : List (Fin s)) {x : Fin s} (x_not_mem : x ∉ L) :
    (∀ y ∈ L, renumberIncr (L ++ [x]) y = renumberIncr L y) ∧
      renumberIncr (L ++ [x]) x = ⟨L.reverse.dedup.length, dedup_length_of_not_mem L.reverse (by simpa using x_not_mem)⟩ := by
  constructor
  · intro y y_mem
    have ⟨i,hi, (h : L.reverse.dedup.reverse[i]'hi = y)⟩ := List.getElem_of_mem (by simp [y_mem])
    subst y
    rw [List.length_reverse] at hi
    refine Eq.trans (b := ⟨i,?i_lt⟩) ?L (Eq.symm ?R)
    case i_lt =>
      have := dedup_length L.reverse; omega
    case L =>
      apply eq_of_mem
      · simp [x_not_mem, List.getElem_append, hi]
      · simp [x_not_mem]; omega
    case R =>
      apply eq_of_mem
      · simp [x_not_mem, List.getElem_append, hi]
      · simp [x_not_mem]; omega
  · apply eq_of_mem <;> simp [x_not_mem]

theorem renumberIncr.exists_max (L : List (Fin s)) (nonempty : L ≠ []) :
    ∃ y ∈ L, renumberIncr L y = ⟨L.reverse.dedup.reverse.length-1, by
      have := dedup_length L.reverse; have := y.isLt; simp; omega⟩ := by
  have dedup_nonempty : L.reverse.dedup.reverse.length ≠ 0 := by
    intro h; simp at h; contradiction
  let prev_max := L.reverse.dedup.reverse[L.reverse.dedup.reverse.length-1]
  have : prev_max ∈ L := by
    have : prev_max ∈ _ := List.getElem_mem ..
    simpa using this
  use prev_max, this
  apply eq_of_mem
  · simp [prev_max]
  · simp; rw [List.length_reverse] at dedup_nonempty; omega

theorem renumberIncr.incSorted_map (L : List (Fin s)) :
    incSorted (L.map <| renumberIncr L) := by
  rw [← List.reverse_reverse L]
  induction L.reverse with
  | nil => simp; exact incSorted.nil
  | cons hd tl ih =>
    by_cases tl.length = 0
    case pos len_zero =>
      match tl with | [] => apply incSorted.singleton
    case neg tl_len_pos =>
    rw [List.reverse_cons, List.map_append]
    by_cases hd ∈ tl
    case pos mem =>
      rw [snoc_mem _ (by simpa using mem)]
      apply incSorted.snoc
      · simp; use hd; simp [mem]
      · simpa using ih
    case neg mem =>
      have ⟨tl_same, hd_maps⟩ := snoc_not_mem tl.reverse (mem ∘ List.mem_reverse.mp)
      simp_rw [List.mem_reverse] at tl_same
      apply incSorted.snoc
      · simp
        have ⟨y, y_mem, hy⟩ := exists_max tl.reverse (by simpa using tl_len_pos)
        use y
        rw [List.mem_reverse] at y_mem
        specialize tl_same _ y_mem
        simp [tl_same, y_mem, hd_maps, hy]
        omega
      · convert ih using 1
        simp +contextual [tl_same]


/-! ### findSmaller?

This section implements the computation for checking
that all matrices are related to a canonical matrix.
We do not need to verify anything about the code for *finding* appropriate permutations--
all we care about is that one exists.
-/


def Matrix.findSmallerRenumber? (m : Matrix s) (h : s > 2 := by trivial) : Option (Matrix s) := do
  let p : Matrix.Renumber s (by omega) ← (do
    let renumber := fun c =>
      renumberIncr <| ⟨0,by omega⟩ :: ⟨1,by omega⟩ :: (List.finRange 3 |>.filter (· ≠ c) |>.map fun r => m.get r c)
    if h : _ then some {
      renumber := renumber
      renumber_0 := And.left h
      renumber_1 := And.right h
    } else none)
  let m' := p.apply m
  guard (m' < m)
  return m'

theorem Matrix.findSmallerRenumber?_eq_some (m m' : Matrix s) (h : s > 2 := by trivial) :
    m.findSmallerRenumber? = some m' →
      ∃ (r : Renumber s (by omega)), r.apply m = m' ∧ m' < m := by
  unfold findSmallerRenumber?
  suffices ∀ popt : Option _, bind popt _ = some m' → _ from this _
  rintro (_|r)
  · simp
  · simp [Option.bind_eq_some]; simp +contextual [eq_comm]

def Matrix.findSmaller? (m : Matrix s) (h : s > 2 := by trivial) : Option (Matrix s) :=
  let perms := Matrix.Perm.all.map (fun p => p.apply m)
  match perms.find? (· < m) with
  | some p => some p
  | none =>
    perms.findSome? fun p =>
      p.findSmallerRenumber?.filter (· < m)

theorem Matrix.findSmaller?_eq_some (m m' : Matrix s) (h : s > 2 := by trivial) :
    m.findSmaller? = some m' →
      ∃ (p : Perm) (r : Renumber s (by omega)), r.apply (p.apply m) = m' ∧ m' < m := by
  intro eq_some
  simp [Id.run, findSmaller?] at eq_some
  split at eq_some
  next m1 ms_related =>
    cases eq_some; simp at ms_related
    rcases ms_related with ⟨p,smaller,rfl⟩
    use p, Renumber.id s (by omega)
    simp [List.find?_eq_some_iff_append] at smaller
    simp [smaller]
  simp [List.findSome?_eq_some_iff, List.map_eq_append_iff, List.map_eq_cons_iff] at eq_some
  rcases eq_some with ⟨-,m_mid,⟨-,-,-,-,-,p,-,-,h_mid,-⟩,⟨h,hlt⟩,-⟩
  replace h := findSmallerRenumber?_eq_some _ _ (by omega) h
  use p; subst m_mid; aesop

/-! ### Canonical cases

Here we list the canonical matrices and perform the computation that says all matrices are related to these.
-/
def Matrix.canonicalCases :=
  Array.filterMap aux #[
  #[0, 1, 1, 0, 0, 1] ,
  #[0, 1, 1, 0, 1, 1] ,
  #[0, 1, 1, 0, 2, 1] ,
  #[0, 1, 1, 1, 0, 0] ,
  #[0, 1, 1, 1, 0, 2] ,
  #[0, 1, 1, 1, 1, 0] ,
  #[0, 1, 1, 1, 1, 1] ,
  #[0, 1, 1, 1, 1, 2] ,
  #[0, 1, 1, 1, 2, 0] ,
  #[0, 1, 1, 1, 2, 1] ,
  #[0, 1, 1, 1, 2, 2] ,
  #[0, 1, 1, 2, 1, 1] ,
  #[0, 1, 1, 2, 2, 1] ,
  #[1, 1, 0, 0, 1, 1] ,
  #[1, 1, 0, 0, 2, 1] ,
  #[1, 1, 0, 2, 1, 1] ,
  #[1, 1, 0, 2, 2, 1] ,
  #[1, 1, 1, 1, 1, 1] ,
  #[1, 1, 1, 1, 1, 2] ,
  #[1, 1, 1, 1, 2, 2] ,
  #[1, 1, 1, 2, 2, 1] ,
  #[1, 1, 2, 0, 2, 1] ,
  #[1, 1, 2, 0, 3, 1] ,
  #[1, 1, 2, 1, 2, 1] ,
  #[1, 1, 2, 1, 2, 2] ,
  #[1, 1, 2, 1, 3, 1] ,
  #[1, 1, 2, 1, 3, 2] ,
  #[2, 1, 1, 2, 2, 1] ]
  |>.insertionSort
where aux (a : Array Nat) : Option (Matrix 4) :=
  if h : _ then
    Matrix.ofVec? ⟨a.map (Fin.ofNat' 4),h⟩
  else none

theorem Matrix.canonicalCases_are_canonical : ∀ m : Matrix 4, m ∈ canonicalCases ∨ (findSmaller? m).isSome := by
  decide +native
