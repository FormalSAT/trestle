/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio, Cayden Codel
-/

import Std

def List.enum' (L : List α) : List (Fin L.length × α) :=
  let rec go (rest : List α) (i : Nat)
              (h : i + rest.length = L.length) :=
    match rest, h with
    | [], _ => []
    | (x :: xs), h =>
      (⟨i, (h.symm ▸ Nat.lt_add_of_pos_right (Nat.zero_lt_succ _))⟩, x)
      :: go xs (i+1) (by
        rw [length_cons, Nat.add_comm _ 1, ←  Nat.add_assoc] at h
        exact h)
  go L 0 (by simp)

def Fin.pred? : Fin n → Option (Fin n)
| ⟨0, _⟩ => none
| ⟨i+1,h⟩ => some ⟨i, Nat.le_of_succ_le h⟩

/-- if i > 0, then i-1, else none -/
def Fin.predCast : Fin n → Option (Fin n.pred)
| ⟨0, _⟩ => none
| ⟨i+1,h⟩ => some ⟨i, Nat.le_pred_of_lt h⟩

/-- if i < Fin.last n then i, else none -/
-- NOTE: in mathlib, castPred : Fin (n + 2) → Fin (n + 1)
def Fin.castPred' (i : Fin n) : Option (Fin n.pred) :=
  match n with
  | 0 => i.elim0
  | n+1 =>
    if h : ↑i = n
    then none
    else some ⟨i, by simp; exact Nat.lt_of_le_of_ne (Nat.le_of_succ_le_succ i.isLt) h⟩

def Fin.succ? : {n : Nat} → Fin n → Option (Fin n)
| 0, i => i.elim0
| n+1, ⟨i,_⟩ =>
  if h : i < n
  then some ⟨i+1, Nat.succ_le_succ h⟩
  else none

def Function.iterate (f : α → α) : Nat → (α → α)
| 0 => id
| n+1 => iterate f n ∘ f

/-! Array -/

def Array.pop? (A : Array α) :=
  match A.back? with
  | none => none
  | some a => some (A.pop, a)

@[simp]
theorem Array.size_pop? : A.pop? = some (A', a) → size A' + 1 = size A := by
  rcases A with ⟨h,t⟩
  <;> simp [pop?, back?, getElem?, pop, decidableGetElem?]
  rintro rfl
  simp

def Array.maxBy (f : α → β) [Max β] (A : Array α) : Option β :=
  if h : A.size > 0 then
    let b0 := f A[0]
    some <| A.foldl (start := 1) (max · <| f ·) b0
  else
    none

theorem Array.mkArray_succ_eq_singleton_append (n : Nat) (a : α) :
    Array.mkArray (n + 1) a = #[a] ++ (Array.mkArray n a) := by
  apply Array.ext'; simp; rfl

@[deprecated Array.mkArray_succ (since := "v4.16.0")]
theorem Array.mkArray_succ' (n : Nat) (a : α) :
    Array.mkArray (n + 1) a = (Array.mkArray n a).push a := by
  apply Array.ext'
  simp [Array.toList_mkArray, List.replicate]
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate]; exact ih

@[simp]
theorem Array.foldl_empty (f : β → α → β) (init : β) (start stop : Nat) :
    Array.foldl f init #[] start stop = init := by
  simp [foldl, foldlM, Id.run]

@[simp]
theorem Array.foldl_nil (f : β → α → β) (init : β) (start stop : Nat) :
    Array.foldl f init { toList := [] } start stop = init :=
  Array.foldl_empty f init start stop

@[simp]
theorem Array.foldl_cons (f : β → α → β) (init : β) (a : α) (as : List α) :
    Array.foldl f init { toList := a :: as } 0 (size { toList := a :: as }) =
      Array.foldl f (f init a) { toList := as } 0 (size { toList := as }) := by
  simp only [size_toArray, List.length_cons, List.foldl_toArray', List.foldl_cons]

@[simp]
theorem Array.foldl_append (f : β → α → β) (init : β) (A B : Array α) :
    Array.foldl f init (A ++ B) 0 (size (A ++ B)) =
      Array.foldl f (Array.foldl f init A 0 (size A)) B 0 (size B) := by
  have ⟨A⟩ := A
  have ⟨B⟩ := B
  simp only [List.append_toArray, size_toArray, List.length_append,
    List.foldl_toArray', List.foldl_append]

@[simp] theorem Array.size_set! (A : Array α) (i : Nat) (v : α) : (A.set! i v).size = A.size := by
  rw [set!, Array.size_setIfInBounds]

@[simp]
theorem Array.mem_ofFn {a : α} {f : Fin n → α}
  : a ∈ Array.ofFn f ↔ ∃ i, f i = a := by
  simp [Array.mem_iff_getElem, Fin.exists_iff]

/-! List -/

open List in
theorem List.Sublist.sizeOf_le [SizeOf α] {L₁ L₂ : List α} :
        L₁ <+ L₂ → sizeOf L₁ ≤ sizeOf L₂ := by
  intro h
  induction h
  · simp
  · simp; omega
  · simp; assumption

def List.distinct [DecidableEq α] (L : List α) : List α :=
  L.foldl (·.insert ·) []

def List.isDistinct [BEq α] : List α → Bool
| [] => true
| x::xs => !xs.contains x && xs.isDistinct

def List.fins (n : Nat) : List (Fin n) :=
  finsAux n (Nat.le_refl _) []
where
  finsAux : (i : Nat) → i ≤ n → List (Fin n) → List (Fin n)
  | 0, _, acc => acc
  | i+1, h, acc => finsAux i (Nat.le_of_lt h) (⟨i,h⟩ :: acc)

@[simp] theorem List.length_fins (n : Nat) : (List.fins n).length = n := by
  unfold fins
  suffices ∀ i (hi : i ≤ n) acc, length (fins.finsAux n i hi acc) = length acc + i
    by have := this n (Nat.le_refl _) []; simp at this; exact this
  intro i hi acc
  induction i generalizing acc
  <;> unfold fins.finsAux
  · rw [Nat.add_zero]
  · rename_i n' ih
    rw [ih (Nat.le_of_succ_le hi) (⟨n', hi⟩ :: acc), List.length,
      Nat.add_assoc, Nat.add_comm 1]

@[simp] theorem List.fins_zero : List.fins 0 = [] := rfl

theorem List.fins_succ (n : Nat)
  : List.fins (n.succ) = (List.fins n).map (Fin.castSucc) ++ [Fin.last n] := by
  unfold fins
  conv => lhs; unfold fins.finsAux
  suffices ∀ i (hi : i ≤ n) acc,
      fins.finsAux n.succ i (trans hi (Nat.le_succ _)) (map Fin.castSucc acc ++ [Fin.last n]) =
        map Fin.castSucc (fins.finsAux n i hi acc) ++ [Fin.last n]
    by have := this n (Nat.le_refl _) []; simpa using this
  intro i hi acc
  induction i generalizing acc with
  | zero => unfold fins.finsAux; simp
  | succ i ih =>
    unfold fins.finsAux
    replace ih := ih (Nat.le_of_lt hi) (⟨i,hi⟩ :: acc)
    simpa using ih

@[simp]
theorem List.get_fins {n : Nat} (i : Fin (List.fins n).length)
  : (List.fins n).get i = ⟨i, by cases i; simp; simp_all⟩ := by
  rcases i with ⟨j, hj⟩
  revert hj
  induction n with
  | zero => simp only [fins_zero, length_nil, Nat.not_lt_zero, get_eq_getElem, forall_false]
  | succ i ih =>
    intro hj
    --rw [List.length_fins] at hj
    by_cases h : j = i
    · subst h
      simp only [get_eq_getElem, fins_succ, Fin.last, length_map,
        length_fins, getElem_concat_length]
    · rw [List.length_fins] at hj
      have := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) h
      simp only [length_fins, get_eq_getElem] at ih
      simp only [get_eq_getElem, fins_succ, getElem_append,
        length_map, length_fins, this, ↓reduceDIte, getElem_map, ih this]
      rfl

@[simp]
theorem List.get_fins' {n i : Nat} (hi : i < n)
    : (List.fins n).get ⟨i, by rw [List.length_fins]; exact hi⟩ = ⟨i, hi⟩ :=
  List.get_fins ⟨i, by rw [List.length_fins]; exact hi⟩

@[simp]
theorem List.mem_fins {n : Nat} (x : Fin n) : x ∈ List.fins n := by
  rw [mem_iff_get]
  refine ⟨⟨x,?_⟩,?_⟩
  · simp only [length_fins, Fin.is_lt]
  · rw [List.get_fins' x.isLt]

/- Better parallelism primitive, that is actually like Scala's Future -/
def TaskIO (α) := IO (Task (Except IO.Error α))

namespace TaskIO

instance : Monad TaskIO where
  pure a := pure (f := IO) <| Task.pure (Except.ok a)
  bind a f := bind (m := IO) a (fun task =>
    IO.bindTask task (fun res => do
      let res ← ofExcept res
      f res))

instance : MonadLift IO TaskIO where
  monadLift io := io.map (fun a => Task.pure (Except.ok a))

def wait (task : TaskIO α) : IO α := do
  let task ← task
  let x ← IO.wait task
  ofExcept x

instance : MonadExceptOf IO.Error TaskIO where
  throw e := show IO _ from throw e
  tryCatch a f := bind (m := IO) a (IO.bindTask · fun
    | .ok a => show TaskIO _ from pure a
    | .error e => f e)

def par [ForIn IO σ α] (xs : σ) (f : α → TaskIO β)
    : TaskIO (List β) := show IO _ from do
  let mut tasks := #[]
  for x in xs do
    tasks := tasks.push (← (f x))
  let task ← IO.mapTasks (fun bs => do
    return ←bs.mapM (fun b => ofExcept b)
  ) tasks.toList
  return task

def parUnit [ForIn IO σ α] (xs : σ) (f : α → TaskIO Unit)
    : TaskIO Unit := do
  let _allUnits ← par xs f
  return ()

def parTasks [ForIn IO σ α] (xs : σ) (f : α → IO β)
    : TaskIO (List β) := do
  par xs (fun a => liftM (n := IO) <| IO.asTask (do f a))

def parTasksUnit [ForIn IO σ α] (xs : σ) (f : α → IO Unit)
    : TaskIO Unit := do
  parUnit xs (fun a => liftM (n := IO) <| IO.asTask (do f a))

end TaskIO

def Option.forIn [Monad m] (o : Option α) (b : β) (f : α → β → m (ForInStep β)) : m β := do
  match o with
  | none => return b
  | some a =>
  match ← f a b with
  | .done b => return b
  | .yield b => return b

instance : ForIn m (Option α) α where
  forIn := Option.forIn

def IO.timeMs (prog : IO α) : IO (Nat × α) := do
  let start ← IO.monoMsNow
  let res ← prog
  let end_ ← IO.monoMsNow

  return (end_ - start, res)

instance : GetElem String Nat Char (fun s i => i < s.length) where
  getElem | xs, i, _ => xs.get (String.Pos.mk i)

def randFin (n) (_h : n > 0) : IO (Fin n) := do
  let i ← IO.rand 0 n.pred
  if h : i < n then
    return ⟨i,h⟩
  else
    panic! s!"failed to get random number {i} < {n}"

/- Generate a random permutation of the list.
Implementation is quadratic in length of L. -/
def IO.randPerm (L : List α) : IO (List α) :=
  randPermTR L [] 0
where randPermTR (L acc n) := do
  match L with
  | [] => return acc
  | x::xs =>
    let idx ← IO.rand 0 n
    let acc' := acc.insertIdx idx x
    randPermTR xs acc' (n+1)


@[simp]
theorem List.sizeOf_filter [SizeOf α] (f) (L : List α)
  : sizeOf (List.filter f L) ≤ sizeOf L
  := by
  induction L <;> simp [filter]
  split
  . simp only [cons.sizeOf_spec, Nat.add_le_add_iff_left]
    assumption
  . apply Nat.le_trans ?_ (Nat.le_add_left _ _)
    assumption

theorem List.sizeOf_filter_lt_of_ne [SizeOf α] (f) (L : List α)
    (h : List.filter f L ≠ L)
  : sizeOf (List.filter f L) < sizeOf L
  := by
  induction L <;> simp [filter] at *
  next hd tl ih =>
  split
  next hHd =>
    simp [hHd] at h
    simp [_sizeOf_1]
    rcases h with ⟨x, hx₁, hx₂⟩
    exact ih _ hx₁ hx₂
  next hHd =>
    clear h hHd
    apply Nat.lt_of_le_of_lt (sizeOf_filter _ _)
    rw [Nat.add_comm, Nat.add_comm 1, Nat.add_one, Nat.add_succ]
    apply Nat.succ_le_succ
    apply Nat.le_add_right

def List.subtypeSize [SizeOf α] : (L : List α) → List {a : α // sizeOf a < sizeOf L}
| [] => []
| x::xs =>
  have : sizeOf x < sizeOf (x::xs) := by
    simp
    calc sizeOf x
      _ < sizeOf x + 1 := Nat.lt_succ_self _
      _ = 1 + sizeOf x := by rw [Nat.add_comm]
      _ ≤ 1 + sizeOf x + sizeOf xs := Nat.le_add_right _ _
  ⟨x, this⟩ :: xs.subtypeSize.map (fun ⟨a,h⟩ =>
    ⟨a, by
      simp
      calc sizeOf a
      _ < sizeOf xs := h
      _ ≤ 1 + sizeOf x + sizeOf xs := Nat.le_add_left _ _⟩)

unsafe def Array.subtypeSizeUnsafe [SizeOf α] (A : Array α) : Array {a : α // sizeOf a < sizeOf A} :=
  unsafeCast A

@[implemented_by subtypeSizeUnsafe]
def Array.subtypeSize [SizeOf α] : (A : Array α) → Array {a : α // sizeOf a < sizeOf A}
| ⟨L⟩ => ⟨L.subtypeSize.map (fun ⟨x,h⟩ => ⟨x, by simp; rw [Nat.add_comm]; apply Nat.lt_add_right; exact h⟩)⟩

/-- Like `forDiagM`, but only runs `f e e'` (not `f e e`). -/
@[simp] def List.forPairsM [Monad m] (f : α → α → m PUnit) : List α → m PUnit
  | [] => pure ⟨⟩
  | x :: xs => do xs.forM (f x); xs.forPairsM f

@[inline]
def Option.expectSome (err : Unit → ε) : Option α → Except ε α
| none => .error (err ())
| some a => .ok a

structure NonemptyList (α) where
  hd : α
  tl : List α

@[inline]
def List.expectNonempty (err : Unit → ε) : List α → Except ε (NonemptyList α)
| [] => .error (err ())
| hd::tl => .ok ⟨hd,tl⟩


def PrinterM := StateM String
def PrinterM.putStr : String → PrinterM Unit :=
  fun string state => ((), state.append string)
def PrinterM.run : PrinterM Unit → String := (StateT.run · "" |>.2)

instance : Monad PrinterM := show Monad (StateM String) from inferInstance

@[simp]
theorem Array.ofFn_data (f : Fin n → α)
  : (Array.ofFn f).toList = (List.fins n).map f := by
  ext i x
  simp
  refine ⟨?mp, ?mpr⟩
  case mp =>
    rintro ⟨h,rfl⟩
    refine ⟨_,?_,rfl⟩
    have := List.length_fins n ▸ h
    simp only [List.getElem?_eq_getElem this, Option.some.injEq]
    have := List.get_fins' h
    simp only [List.get_eq_getElem] at this
    rw [this]
  case mpr =>
    rintro ⟨a, ha, rfl⟩
    rcases List.getElem?_eq_some_iff.mp ha with ⟨hi, rfl⟩
    have := List.get_fins ⟨_, hi⟩
    simp at this
    rw [this]
    exact ⟨List.length_fins n ▸ hi, rfl⟩
