import Std
import LeanSAT.CNF
import LeanSAT.AuxDefs

open Std

namespace LeanSAT.Encode

namespace EncCNF

/-- State for an encoding -/
structure State where
  nextVar : Nat
  clauses : List Clause
  names   : HashMap Var String
  varCtx  : String
  conditionCtx : List Literal

namespace State

def new : State := ⟨0, [], HashMap.empty, "", []⟩

instance : Inhabited State := ⟨new⟩

def scramble (s : State) : IO State := do
  let litsScrambled ← s.clauses.mapM fun ⟨lits⟩ => do
    return ⟨← (IO.randPerm lits)⟩
  let clausesScrambled ← IO.randPerm litsScrambled
  return { s with clauses := clausesScrambled }

def toFormula : State → Formula
| {clauses, ..} => ⟨clauses⟩

def toString : State → String
| {clauses,names,nextVar, ..} => Id.run do
  let mut acc := ""
  for i in [0:nextVar] do
    match names.find? i with
    | none => ()
    | some name => acc := acc ++ s!"c {i} {name}\n"
  acc ++ Formula.toString ⟨clauses⟩

instance : ToString State := ⟨toString⟩
end State

end EncCNF

@[reducible]
def EncCNF := ExceptT String (StateM EncCNF.State)

namespace EncCNF

nonrec def run? (s : State) (e : EncCNF α) : Except String (α × State) := do
  let (a,s) := e.run s
  return (←a, s)

nonrec def run! [Inhabited α] (s : State) (e : EncCNF α) : α × State :=
  (run? s e).toOption.get!

nonrec def new? : EncCNF α → Except String (α × State)  := run? .new
nonrec def new! [Inhabited α] : EncCNF α → α × State    := run! .new

instance [Inhabited α] : Inhabited (EncCNF α) := ⟨do return default⟩

def newCtx (name : String) (inner : EncCNF α) : EncCNF α := do
  let oldState ← get
  set {oldState with varCtx := oldState.varCtx ++ name}
  let res ← inner
  let newState ← get
  set {newState with varCtx := oldState.varCtx}
  return res

def mkVar (name : String) : EncCNF Var := do
  let oldState ← get
  set { oldState with
    nextVar := oldState.nextVar+1,
    names := oldState.names.insert oldState.nextVar
                (oldState.varCtx ++ name)}
  return oldState.nextVar

def mkTemp : EncCNF Var := do
  let oldState ← get
  return ← mkVar ("tmp" ++ toString oldState.nextVar)

def addClause (C : Clause) : EncCNF Unit := do
  let oldState ← get
  set { oldState with
    clauses := ⟨oldState.conditionCtx ++ C.lits⟩ :: oldState.clauses }

/-- runs `e`, adding `ls` to each generated clause -/
def unlessOneOf (ls : List Literal) (e : EncCNF α) : EncCNF α := do
  let oldState ← get
  set { oldState with conditionCtx := ls ++ oldState.conditionCtx }
  let res ← e
  let newState ← get
  set { newState with conditionCtx := oldState.conditionCtx }
  return res

def assuming (ls : List Literal) (e : EncCNF α) : EncCNF α :=
  unlessOneOf (ls.map (·.not)) e

structure VarBlock (dims : List Nat) where
  start : Var
  h_dims : dims.length > 0

instance : Inhabited (VarBlock (x::xs)) where
  default := {start := 0, h_dims := by simp [Nat.succ_pos]}

@[reducible, inline, simp]
def VarBlock.hdLen : VarBlock ds → Nat
| ⟨_, _⟩ =>
  match ds with
  | [] => by contradiction
  | d::_ => d

@[reducible, inline, simp]
def VarBlock.elemTy : List Nat → Type
  | [] => Empty
  | [_] => Var
  | _::d'::ds' => VarBlock (d'::ds')

@[inline]
def VarBlock.get (v : VarBlock ds) (i : Fin v.hdLen)
  : VarBlock.elemTy ds
  := match ds, v with
  | [],         ⟨_    ,_⟩ => by contradiction
  | [_],        ⟨start,_⟩ => Nat.add start i
  | _::d'::ds', ⟨start,_⟩ =>
    ⟨Nat.add start (Nat.mul i ((d'::ds').foldl (· * ·) 1)), by
      simp; apply Nat.zero_lt_succ⟩

instance : GetElem (VarBlock ds) Nat (VarBlock.elemTy ds) (fun v i => i < v.hdLen) where
  getElem v i h := v.get ⟨i,h⟩


def mkVarBlock (name : String) (dims : List Nat) (h : dims.length > 0 := by simp)
  : EncCNF (VarBlock dims) := do
  let state ← get
  let start := state.nextVar
  gen dims name
  return ⟨start, h⟩
where gen (dims : List Nat) (pref : String) : EncCNF Unit := do
  match dims with
  | [] =>
    let _ ← mkVar pref
  | d::ds =>
    for i in [0:d] do
      gen ds s!"{pref}[{i}]"

def mkTempBlock (dims : List Nat) (h : dims.length > 0 := by simp)
  : EncCNF (VarBlock dims) := do
  return ← mkVarBlock ("tmp" ++ toString (← get).nextVar) dims h

def blockAssn (a : Assn) : EncCNF Unit := addClause ⟨a.toList.map (.not ·)⟩

def addAssn (a : Assn) : EncCNF Unit := do
  for l in a.toList do
    addClause l
