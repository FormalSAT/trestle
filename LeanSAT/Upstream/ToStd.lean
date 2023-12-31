import Std
import Mathlib.Tactic
import Init.Data.Nat.Basic

/-! # List -/

def List.enum' (L : List α) : List (Fin L.length × α) :=
  let rec go (rest : List α) (i : Nat)
              (h : i + rest.length = L.length) :=
    match rest, h with
    | [], _ => []
    | (x :: xs), h =>
      (⟨i, (h.symm ▸ Nat.lt_add_of_pos_right (Nat.zero_lt_succ _))⟩, x)
      :: go xs (i+1) (by
        simp [←h, Nat.add_succ, Nat.succ_add])
  go L 0 (by simp)

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

def List.mem_set : ∀ {l : List α} {i : Nat} {a a' : α},
    a' ∈ l.set i a → a' ∈ l ∨ a' = a
  | cons _ bs, 0, _, _, h => by
    simp only [set, mem_cons] at h ⊢
    tauto
  | cons b bs, Nat.succ n, _, _, h => by
    simp only [set, mem_cons] at h ⊢
    cases' h with h h
    . tauto
    . have := mem_set h
      tauto
  | nil, _, _, _, h => Or.inl h

/-! # Fin -/

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

lemma Fin.foldl_induction (n) (f : α → Fin n → α) (init : α) (P : α → Fin (n+1) → Prop)
    (hInit : P init 0)
    (hSucc : ∀ a (i : Fin n), P a ⟨i.val, Nat.lt_succ_of_lt i.is_lt⟩ → P (f a i) ⟨i.val+1, Nat.succ_lt_succ i.is_lt⟩) :
    P (Fin.foldl n f init) ⟨n, Nat.lt_succ_self n⟩ :=
  loop init 0 hInit
where
  loop (x : α) (i : Fin (n+1)) (h : P x i) : P (Fin.foldl.loop n f x i.val) ⟨n, Nat.lt_succ_self n⟩ := by
    unfold foldl.loop
    split
    next h =>
      have := loop (f x ⟨i.val, h⟩) ⟨i.val+1, Nat.succ_lt_succ h⟩
      apply this
      apply hSucc
      assumption
    next h =>
      have : i.val = n := Nat.eq_of_le_of_lt_succ (not_lt.mp h) i.is_lt
      simp_rw [← this]
      assumption
  termination_by loop x i h => n - i

lemma Fin.foldl_induction' (n) (f : α → Fin n → α) (init : α) (P : α → Prop)
    (hInit : P init)
    (hSucc : ∀ a i, P a → P (f a i)) :
    P (Fin.foldl n f init) :=
  Fin.foldl_induction n f init (fun a _ => P a) hInit hSucc

lemma Fin.foldl_of_comm (n) (f : α → Fin n → α) (init : α) (i : Fin n)
    (H : ∀ (acc : α) (i₁ i₂ : Fin n), f (f acc i₁) i₂ = f (f acc i₂) i₁) :
    ∃ (acc : α), Fin.foldl n f init = f acc i :=
  have : i.val < n → ∃ (acc : α), Fin.foldl n f init = f acc i :=
    Fin.foldl_induction n f init (fun res j => i.val < j.val → ∃ (acc : α), res = f acc i)
      (nomatch ·)
      (by
        intro a j ih h
        cases' lt_or_eq_of_le (Nat.lt_succ.mp h) with h
        . have ⟨acc, hAcc⟩ := ih h
          use (f acc j)
          rw [hAcc, H]
        . have : i = j := by ext; assumption
          use a
          rw [this])
  this i.is_lt

def Function.iterate (f : α → α) : Nat → (α → α)
| 0 => id
| n+1 => iterate f n ∘ f

/-! # Array -/

def Array.init (n : Nat) (f : Fin n → α) : Array α := Id.run do
  let mut A := Array.mkEmpty n
  for h:i in [0:n] do
    A := A.push (f ⟨i,h.2⟩)
  return A

def Array.initM [Monad m] (n : Nat) (f : Fin n → m α) : m (Array α) := do
  let mut A := Array.mkEmpty n
  for h:i in [0:n] do
    A := A.push (← f ⟨i,h.2⟩)
  return A

theorem Array.init_zero : Array.init 0 f = #[] := by
  simp [init, Id.run, forIn', Std.Range.forIn']
  unfold Std.Range.forIn'.loop
  simp

theorem Array.init_succ {f : Fin n.succ → α}
  : Array.init n.succ f = (
      Array.init n (fun i => f ⟨i,Nat.lt_trans i.isLt (by exact Nat.le_refl _)⟩)
    ).push (f ⟨n, by exact Nat.le_refl _⟩)
  := by
  simp [init, Id.run, forIn', Std.Range.forIn']
  suffices ∀ i (hi : i ≤ n) o (_ : o.size = n-i),
    Std.Range.forIn'.loop (m := Id) 0 n.succ 1
      (fun i h r => ForInStep.yield (push r (f ⟨i, h.2⟩)))
      i.succ (n-i)
      (Nat.zero_le _)
      o
    = push (Std.Range.forIn'.loop (m := Id) 0 n 1
      (fun i h r => ForInStep.yield (push r (f ⟨i, Nat.le_step h.2⟩)))
      i (n-i)
      (Nat.zero_le _)
      o) (f ⟨n, Nat.lt_succ_self n⟩)
    by
    have := this n (Nat.le_refl _) #[] (by simp)
    simp at this
    exact this
  intro i hi o ho
  induction i generalizing o with
  | zero =>
    unfold Std.Range.forIn'.loop
    unfold Std.Range.forIn'.loop
    simp
  | succ i ih =>
    conv => lhs; unfold Std.Range.forIn'.loop
    conv => rhs; unfold Std.Range.forIn'.loop
    simp
    have hn := Nat.sub_lt_of_pos_le (Nat.succ_pos _) hi
    have hn' : n - Nat.succ i < Nat.succ n := Nat.le_step hn
    simp [hn, hn']
    have : n - Nat.succ i + 1 = n - i := by
      simp [Nat.sub_succ]
      rw [Nat.add_one, Nat.succ_pred_eq_of_pos (Nat.zero_lt_sub_of_lt hi)]
    suffices ∀ j, j = n - Nat.succ i + 1 →
      Std.Range.forIn'.loop (m := Id)  _ _ _ _ _ j (Nat.zero_le _) _
      = push (Std.Range.forIn'.loop (m := Id) _ _ _ _ _ j (Nat.zero_le _) _) _
      from this _ rfl
    intro j hj
    rw [this] at hj
    cases hj
    apply ih
    exact Nat.le_of_lt hi
    simp [ho, this]

@[simp]
theorem Array.size_init : (Array.init n f).size = n := by
  induction n
  . simp [size, init_zero]
  . next ih =>
    simp [init_succ]; exact ih

@[simp]
theorem Array.get_init {i : Nat} {h} : (Array.init n f)[i]'h = f ⟨i, @size_init n _ f ▸ h⟩ := by
  induction n generalizing i with
  | zero => simp at h
  | succ n ih =>
    simp [init_succ, get_push]
    split
    next h =>
      have := @ih (fun i => f ⟨i,Nat.lt_trans i.isLt (by exact Nat.le_refl _)⟩) i (by simp; assumption)
      simp at this ⊢
      rw [this]
    next h' =>
      simp at h'
      have : i = n := Nat.le_antisymm
        (Nat.le_of_succ_le_succ (by rw [size_init] at h; exact h))
        h'
      cases this
      congr

def Array.pop? (A : Array α) :=
  match A.back? with
  | none => none
  | some a => some (A.pop, a)

@[simp] theorem Array.size_pop?
  : A.pop? = some (A', a) → size A' + 1 = size A
  := by rcases A with ⟨h,t⟩
          <;> simp [pop?, back?, getElem?, pop]
        rintro rfl
        simp

def Array.maxBy (f : α → β) [Max β] (A : Array α) : Option β :=
  if h : A.size > 0 then
    let b0 := f A[0]
    some <| A.foldl (start := 1) (max · <| f ·) b0
  else
    none

theorem Array.mem_data_iff {A : Array α} {a : α} : a ∈ A.data ↔ ∃ (i : Fin A.size), A[i] = a := by
  constructor
  · exact List.get_of_mem
  · rintro ⟨i, rfl⟩
    exact Array.getElem_mem_data A i.isLt

@[simp] theorem Array.size_append (A B : Array α) : size (A ++ B) = size A + size B := by
  simp [Array.size]

theorem Array.push_eq_append_singleton (A : Array α) (a : α) : A.push a = A ++ #[a] := rfl

theorem Array.append_assoc (A B C : Array α) : (A ++ B) ++ C = A ++ (B ++ C) := by
  apply Array.ext'; simp only [append_data, List.append_assoc]

theorem Array.mkArray_succ (n : Nat) (a : α) :
    Array.mkArray (n + 1) a = #[a] ++ (Array.mkArray n a) := by
  apply Array.ext'
  simp only [mkArray_data, List.replicate, Nat.add_eq, add_zero,
    append_data, data_toArray, List.singleton_append]

theorem Array.mkArray_succ' (n : Nat) (a : α) :
    Array.mkArray (n + 1) a = (Array.mkArray n a).push a := by
  apply Array.ext'
  simp only [mkArray_data, List.replicate, Nat.add_eq, add_zero, push_data]
  induction' n with n ih
  · rfl
  · simp only [List.replicate, List.cons_append, List.cons.injEq, true_and]
    exact ih

/-! # setF -/

/- A new set operation that fills in with a provided default value until hitting the index -/

/-
Custom-written C++ code is yet to be written.
Below is a functional implementation.

One alternate implementation is to use Array.ofFn to copy over the array.
In order to determine if it's better, profile it.

Note: @implemented_by can refer to other Lean implementations!
  That can help profile the different versions at runtime.
-/

def Array.setF (A : Array α) (i : Nat) (v default : α) : Array α :=
  if hi : i < A.size then
    A.set ⟨i, hi⟩ v
  else
    let rec go (j : Nat) (A' : Array α) : Array α :=
      match j with
      | 0 => A'.push v
      | j + 1 => go j (A'.push default)
    go (i - A.size) A

theorem Array.setF_eq_set {A : Array α} {i : Nat} (hi : i < A.size) (v default : α) :
    A.setF i v default = A.set ⟨i, hi⟩ v := by
  simp [setF, hi]

theorem Array.setF_eq_set' {A : Array α} (i : Fin A.size) :
    ∀ (v default : α), A.setF i v default = A.set i v :=
  Array.setF_eq_set i.isLt

theorem Array.setF_eq_push {A : Array α} (v default : α) :
    A.setF A.size v default = A.push v := by
  simp [setF, setF.go]

-- TODO: Private lemmas for the next two?
theorem Array.setF_go_eq (A : Array α) (i : Nat) (v default : α) :
    Array.setF.go v default i A = (A ++ Array.mkArray i default).push v := by
  induction' i with i ih generalizing A
  · rfl
  · rw [setF.go, ih (push A default)]
    apply congrArg₂
    · rw [mkArray_succ, Array.push_eq_append_singleton, Array.append_assoc]
    · rfl

theorem Array.size_setF_go (A : Array α) (i : Nat) (v default : α) :
    (Array.setF.go v default i A).size = A.size + i + 1 := by
  rw [Array.setF_go_eq, Array.size_push, Array.size_append, Array.size_mkArray]

theorem Array.size_setF (A : Array α) (i : Nat) (v default : α) :
    (A.setF i v default).size = max A.size (i + 1) := by
  rcases Nat.lt_trichotomy i A.size with (hi | rfl | hi)
  · rw [Array.setF_eq_set hi, Array.size_set]
    exact (Nat.max_eq_left hi).symm
  · rw [Array.setF_eq_push, Array.size_push]
    simp only [ge_iff_le, add_le_iff_nonpos_right, nonpos_iff_eq_zero,
      le_add_iff_nonneg_right, zero_le, max_eq_right]
  · simp [setF, Nat.lt_asymm hi, Array.setF_go_eq]
    rw [max_eq_right (Nat.le_succ_of_le (le_of_lt hi)),
      ← Nat.add_sub_assoc (le_of_lt hi), add_comm (size A) i, Nat.add_sub_cancel]

theorem Array.lt_size_setF (A : Array α) (i : Nat) (v default : α) :
    i < size (A.setF i v default) := by
  rw [Array.size_setF]
  exact lt_max_of_lt_right (Nat.lt_succ_self _)

theorem Array.setF_eq_of_gt (A : Array α) {i : Nat} (hi : i > A.size) (v default : α) :
    A.setF i v default = A ++ mkArray (i - A.size) default ++ #[v] := by
  simp [setF, Nat.lt_asymm hi, Array.setF_go_eq]; rfl

theorem Array.setF_eq_of_ge (A : Array α) {i : Nat} (hi : i ≥ A.size) (v default : α) :
    A.setF i v default = (A ++ mkArray (i - A.size) default).push v := by
  simp [setF, Nat.not_lt.mpr hi, Array.setF_go_eq]

theorem Array.setF_setF (A : Array α) (i : Nat) (v v' default : α) :
    (A.setF i v default).setF i v' default = A.setF i v' default := by
  by_cases hi : i < A.size
  · rw [Array.setF_eq_set hi, Array.setF_eq_set hi]
    rw [← Array.size_set A ⟨i, hi⟩ v] at hi
    rw [Array.setF_eq_set hi]
    exact Array.set_set _ _ _ _
  · have : i < size (A.setF i v default) := by
      rw [Array.size_setF, max_eq_right_of_lt (Nat.lt_succ_of_le (Nat.not_lt.mp hi))]
      exact Nat.lt_succ_self _
    simp [Array.setF, hi, this]
    have : i < size (setF.go v default (i - size A) A) := by
      rw [Array.size_setF_go A (i - A.size) v default, ← Nat.add_sub_assoc (Nat.not_lt.mp hi),
        add_comm A.size i, Nat.add_sub_cancel]
      exact Nat.lt_succ_self _
    simp [this]
    sorry
    done
  done

theorem Array.mem_setF (A : Array α) (i : Nat) (v default : α) :
    ∀ a ∈ (A.setF i v default).data, a ∈ A.data ∨ a = default ∨ a = v := by
  intro a ha
  by_cases h : i < A.size
  . rw [Array.setF_eq_set h] at ha
    have ha := List.mem_set ha
    tauto
  . rw [not_lt] at h
    simp only [A.setF_eq_of_ge h,  push_data, append_data, mkArray_data,
      List.append_assoc, List.mem_append, List.mem_singleton] at ha
    rcases ha with _ | ha | _ <;> try { tauto }
    have := List.eq_of_mem_replicate ha
    tauto

/-
#check Array.get_set
∀ {α : Type u_1} (a : Array α) (i : Fin (Array.size a)) (j : ℕ) (hj : j < Array.size a) (v : α),
  (Array.set a i v)[j] = if ↑i = j then v else a[j]
-/

-- TODO: Expand this into the upper definition later
theorem Array.get_setF (A : Array α) (i : Nat) (v default : α) :
    (A.setF i v default).get ⟨i, Array.lt_size_setF A i v default⟩ = v := by sorry

theorem Array.getElem_setF (A : Array α) (i : Nat) (v default : α) :
    (A.setF i v default)[i]'(Array.lt_size_setF A i v default) = v := by
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
theorem Array.getElem?_setF (A : Array α) (i : Nat) (v default : α) :
    (A.setF i v default)[i]? = some v := by
  sorry

theorem Array.getElem?_setF' (A : Array α) {i j : Nat} (v default : α) :
    i ≠ j → (A.setF i v default)[j]? = A[j]? := by
  sorry
  done

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
    let acc' := acc.insertNth idx x
    randPermTR xs acc' (n+1)


@[simp]
theorem List.sizeOf_filter [SizeOf α] (f) (L : List α)
  : sizeOf (List.filter f L) ≤ sizeOf L
  := by
  induction L <;> simp [filter]
  split
  . simp
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
    exact ih h
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

@[simp] theorem List.find?_map (p : β → Bool) (f : α → β) (L : List α)
  : List.find? p (List.map f L) = Option.map f (List.find? (p ∘ f) L)
  := by induction L <;> simp [find?]; split <;> simp [*]

/-- Like `forDiagM`, but only runs `f e e'` (not `f e e`). -/
@[simp] def List.forPairsM [Monad m] (f : α → α → m PUnit) : List α → m PUnit
  | [] => pure ⟨⟩
  | x :: xs => do xs.forM (f x); xs.forPairsM f

@[simp]
def Std.AssocList.ofList : List (α × β) → Std.AssocList α β
| [] => .nil
| (a,b)::tail => .cons a b (ofList tail)

@[simp] theorem Std.AssocList.toList_ofList (L : List (α × β))
  : toList (ofList L) = L
  := by induction L <;> simp [*]

@[simp]
theorem Std.HashMap.find?_ofList {B : BEq α} {H : Hashable α} (a : List (α × β)) (k : α)
  : (@Std.HashMap.ofList _ _ B H a |>.find? k) = (Std.AssocList.ofList a |>.find? k)
  := sorry

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

def IO.FS.withTempFile (f : System.FilePath → IO α) : IO α := do
  let mut file := ".tmp" ++ toString (← IO.rand 0 999999)
  while ← System.FilePath.pathExists file do
    file := file ++ toString (← IO.rand 0 999999)

  IO.FS.writeFile file ""
  let res ←
    try f file
    finally
      if ← System.FilePath.pathExists file then
        IO.FS.removeFile file

  return res