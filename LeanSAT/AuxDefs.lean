import Std
import Std

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

def Fin.last (n : Nat) (_ : 0 < n) : Fin n :=
  match n with
  | 0 => by contradiction
  | n+1 => ⟨n, Nat.le_refl _⟩

def Fin.pred? : Fin n → Option (Fin n)
| ⟨0, _⟩ => none
| ⟨i+1,h⟩ => some ⟨i, Nat.le_of_succ_le h⟩

def Fin.succ? : {n : Nat} → Fin n → Option (Fin n)
| 0, i => i.elim0
| n+1, ⟨i,_⟩ =>
  if h : i < n
  then some ⟨i+1, Nat.succ_le_succ h⟩
  else none

def Function.iterate (f : α → α) : Nat → (α → α)
| 0 => id
| n+1 => iterate f n ∘ f

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
    have hn := Nat.sub_lt_of_pos_le _ _ (Nat.succ_pos _) hi
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
  | zero => simp at h; exact False.elim <| Nat.not_lt_zero _ h
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
    apply Nat.add_le_add_left
    assumption
  . simp
    apply Nat.le_trans ?_ (Nat.le_add_left _ _)
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
    apply Nat.add_lt_add_left
    apply ih
    assumption
  next hHd =>
    clear h hHd
    apply Nat.lt_of_le_of_lt (sizeOf_filter _ _)
    rw [Nat.add_comm, Nat.add_comm 1, Nat.add_one, Nat.add_succ]
    apply Nat.succ_le_succ
    apply Nat.le_add_right


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
