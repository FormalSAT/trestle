import Std

-- Cayden note: Possible @[simp] lemmas for if b then c else d = c → b, etc.
/-
theorem tt_of_cond_ne_second [DecidableEq α] {c d : α} {b : Bool} :
  cond b c d ≠ d → b = true := by
  cases b
  · simp only [cond_false, ne_eq, not_true, imp_self]
  · simp only [cond_true, ne_eq, implies_true]

theorem ff_of_cond_ne_first [DecidableEq α] {c d : α} {b : Bool} :
  cond b c d ≠ c → b = false := by
  cases b
  · simp only [cond_false, ne_eq, implies_true]
  · simp only [cond_true, ne_eq, not_true, imp_self]

theorem tt_of_ne_second_of_cond_eq [DecidableEq α] {c d e : α} {b : Bool} :
  d ≠ e → cond b c d = e → b = true := by
  cases b
  · intros, contradiction }, { tautology }

theorem ff_of_ne_first_of_cond_eq [DecidableEq α] {c d e : α} {b : Bool} :
  c ≠ e → cond b c d = e → b = false := by
by { cases b, { tautology }, { intros, contradiction } }

theorem tt_of_ne_of_cond_eq_first [DecidableEq α] {c d : α} {b : Bool} :
  c ≠ d → cond b c d = c → b = true :=
by { cases b, { intros h₁ h₂, exact absurd h₂.symm h₁ }, { tautology } }

theorem ff_of_ne_of_cond_eq_second [DecidableEq α] {c d : α} {b : Bool} :
  c ≠ d → cond b c d = d → b = false :=
by { cases b, { tautology }, { intros, contradiction }} -/

-- TODO: A better implementation exists, probably by writing a custom looper/recursive function
def Array.foldlIdxM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
  (as : Array α) (f : β → Fin as.size → α → m β) (init : β) (start := 0) (stop := as.size) : m β :=
  if hz : 0 < as.size then
    return Prod.fst <| ← (as.foldlM (fun (acc, idx) a =>
      if hidx : idx + 1 < as.size then
        return (← f acc idx a, ⟨idx + 1, hidx⟩)
      else
        return (← f acc idx a, ⟨0, hz⟩)) (⟨init, ⟨0, hz⟩⟩ : β × Fin as.size) start stop)
  else
    return init

@[inline]
def Array.foldlIdx {α : Type u} {β : Type v} (as : Array α) (f : β → Fin as.size → α → β)
    (init : β) (start := 0) (stop := as.size) : β :=
  Id.run <| as.foldlIdxM f init start stop

def Array.foldrIdxM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
    (as : Array α) (f : Fin as.size → α → β → m β) (init : β) (start := as.size) (stop := 0) : m β :=
  if hz : 0 < as.size then
    return Prod.fst <| ← (as.foldrM (fun a (acc, idx) =>
      if hidx : idx + 1 < as.size then
        return (← f idx a acc, ⟨idx + 1, hidx⟩)
      else
        return (← f idx a acc, ⟨0, hz⟩)) (⟨init, ⟨0, hz⟩⟩ : β × Fin as.size) start stop)
  else
    return init

@[inline]
def Array.foldrIdx {α : Type u} {β : Type v} (as : Array α) (f : Fin as.size → α → β → β)
    (init : β) (start := as.size) (stop := 0) : β :=
  Id.run <| as.foldrIdxM f init start stop


-- Theorems on foldlIdx

--theorem Array.foldlIdx_index_eq (as : Array α) (f : β → Fin as.size → α → β) (init : β) :
  --as.foldlIdx = something about Array.enum

theorem Array.foldlIdx_of_comm (A : Array α) (f : β → Fin A.size → α → β) (init : β) :
    -- Commutativity assumption
    (∀ (acc : β) (idx₁ idx₂ : Fin A.size),
      f (f acc idx₁ (A.get idx₁)) idx₂ (A.get idx₂) = f (f acc idx₂ (A.get idx₂)) idx₁ (A.get idx₁)) →

    -- For all indexes, we can move its function application to the end
    ∀ (idx : Fin A.size), ∃ (acc : β), A.foldlIdx f init = f acc idx (A.get idx) := by sorry


/-! # ResultT -/

-- α is the "final result" type, and β is the "partial result" type
inductive ResultT (α : Type u) (β : Type v) where
  | done : α → ResultT α β
  | ok : β → ResultT α β

-- Cayden TODO: "done" is a reserved keyword in Lean. Pick a different one?
-- Cayden note: This is just the Except monad, with ok = ok and done = error
-- Cayden q: What's the difference between Except and ExceptT? Why the "T"?
export ResultT (done ok)

abbrev Result (α : Type u) := ResultT α α

namespace ResultT

@[always_inline, inline]
protected def bind : ResultT α β → (β → ResultT α γ) → ResultT α γ
  | done a, _ => done a
  | ok b, f   => f b

open Std in
protected def repr [Repr α] [Repr β] : ResultT α β → Nat → Format
  | done a, prec => Repr.addAppParen ("done " ++ reprArg a) prec
  | ok a,   prec => Repr.addAppParen ("ok " ++ reprArg a) prec

end ResultT

@[always_inline]
instance : Monad (ResultT α) where
  pure := ResultT.ok
  bind := ResultT.bind

instance : LawfulMonad (ResultT α) := LawfulMonad.mk'
  (id_map := fun x => by cases x <;> rfl)
  (pure_bind := fun x f => rfl)
  (bind_assoc := fun x f g => by cases x <;> rfl)
  (bind_pure_comp := fun f x => by cases x <;> rfl)

-- A quick example
#eval match [1, 2, 3, 4, 5, 6].foldlM (init := 5) (fun acc x =>
  dbg_trace s!"{x}"
  if x % 2 = 0 then ResultT.done 0 else ResultT.ok (acc + x)) with
    | .ok x => x
    | .done x => x

@[simp] theorem SatisfiesM_ResultT_eq : SatisfiesM (m := ResultT α) p x ↔ ∀ b, x = ok b → p b :=
  ⟨by revert x; intro | .ok _, ⟨.ok ⟨_, h⟩, rfl⟩, _, rfl => exact h,
   fun h => match x with | ok b => ⟨ok ⟨b, h _ rfl⟩, rfl⟩ | done a => ⟨done a, rfl⟩⟩

/-

-- Cayden: Note that the Result monad can be used on normal foldl, instead of a new type

/- Making a foldl which can 'return early' -/
inductive FoldResult (α : Type _)
  | ok (v : α) : FoldResult α
  | done (v : α) : FoldResult α

namespace List

variable {m : Type u → Type v} [Monad m] {α : Type u} {β : Type w}

@[coe, reducible] def toFoldResult {α : Type _} (v : α) : FoldResult α := .ok v
instance {α : Type _} : Coe α (FoldResult α) where coe := toFoldResult

-- Handles early returns, while keeping a fold
@[specialize]
def foldlM' (f : α → β → m (FoldResult α)) : (init : FoldResult α) → List β → m α
  | .done a, _ => return a
  | .ok a, nil => return a
  | .ok a, cons b l => do foldlM' f (← f a b) l

@[inline]
def foldl' (f : α → β → FoldResult α) (init : FoldResult α) (l : List β) : α :=
  Id.run <| l.foldlM' f init

@[simp]
theorem foldl'_nil (f : α → β → FoldResult α) (a : α) : foldl' f a [] = a := rfl

@[simp]
theorem foldl'_cons (f : α → β → FoldResult α) (a : α) (b : β) (l : List β) :
  foldl' f (.ok a) (b :: l) = foldl' f (f a b) l := rfl

@[simp]
theorem foldl'_done (f : α → β → FoldResult α) (a : α) (l : List β) :
  foldl' f (.done a) l = a := by rw [foldl', foldlM', Id.run, Id.pure_eq]

theorem foldl'_eq_foldlM' (f : β → α → (FoldResult β)) (b) (l : List α) :
    l.foldl' f b = l.foldlM' (m := Id) f b := by
  induction l generalizing b <;> simp [*, foldl', Id.run]

#check foldl_eq_foldlM
end List

namespace Array

variable {m : Type u → Type v} [Monad m] {α : Type u} {β : Type w}

@[coe, reducible] def toFoldResult {α : Type _} (v : α) : FoldResult α := .ok v
instance {α : Type _} : Coe α (FoldResult α) where coe := toFoldResult

-- Handles early returns, while keeping a fold
@[specialize]
def foldlM' (f : α → β → m (FoldResult α)) : (init : FoldResult α) → Array β → m α
  | .done a, _ => return a
  | .ok a, A => do
    -- TODO: Do with rec-loop later
    let mut acc := a
    for b in A do
      match ← f acc b with
        | .ok a' => acc := a'; continue
        | .done a' => return a'
    return acc

@[inline]
def foldl' (f : α → β → FoldResult α) (init : FoldResult α) (l : Array β) : α :=
  Id.run <| l.foldlM' f init

@[simp]
theorem foldl'_nil (f : α → β → FoldResult α) (a : α) : foldl' f a #[] = a := rfl

#check List.foldl_eq_foldlM
#check foldlM_eq_foldlM_data
#check foldl_eq_foldl_data
/-
theorem foldl_eq_foldl_data (f : β → α → β) (init : β) (arr : Array α) :
    arr.foldl f init = arr.data.foldl f init :=
  List.foldl_eq_foldlM .. ▸ foldlM_eq_foldlM_data ..
-/

/-
theorem foldlM_eq_foldlM_data [Monad m]
    (f : β → α → m β) (init : β) (arr : Array α) :
    arr.foldlM f init = arr.data.foldlM f init := by
  simp [foldlM, foldlM_eq_foldlM_data.aux]
-/

/-
theorem foldlM'_eq_foldlM'_data.aux
    (f : α → β → m (FoldResult α)) (arr : Array β) (i j) (H : arr.size ≤ i + j) (b) :
    foldlM'.loop f arr arr.size (Nat.le_refl _) i j b = (arr.data.drop j).foldlM' f b := by
  unfold foldlM.loop
  split; split
  · cases Nat.not_le_of_gt ‹_› (Nat.zero_add _ ▸ H)
  · rename_i i; rw [Nat.succ_add] at H
    simp [foldlM_eq_foldlM_data.aux f arr i (j+1) H]
    conv => rhs; rw [← List.get_drop_eq_drop _ _ ‹_›]
  · rw [List.drop_length_le (Nat.ge_of_not_lt ‹_›)]; rfl -/

theorem foldlM'_eq_foldlM'_data (f : α → β → m (FoldResult α)) (init : α) (arr : Array β) :
    arr.foldlM' f init = arr.data.foldlM' f init := by
  simp [foldlM']
  sorry

theorem foldl'_eq_foldl'_data (f : α → β → FoldResult α) (init : FoldResult α) (arr : Array β) :
    arr.foldl' f init = arr.data.foldl' f init :=
  sorry
  --List.foldl'_eq_foldlM' .. ▸ foldlM'_eq_foldlM'_data ..

end Array
-/
