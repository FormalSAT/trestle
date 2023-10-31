import Std
import LeanSAT.Data.Cnf
import LeanSAT.Data.ICnf
import LeanSAT.Data.HashAssn
import LeanSAT.AuxDefs
import LeanSAT.Upstream.PNat

open Std

namespace LeanSAT.Encode

namespace EncCNF

/-- State for an encoding -/
structure State where
  nextVar : PNat
  clauses : List (IClause)
  names   : HashMap IVar String
  varCtx  : String
  conditionCtx : Array ILit

namespace State

def new : State := ⟨1, [], HashMap.empty, "", #[]⟩

instance : Inhabited State := ⟨new⟩

def scramble (s : State) : IO State := do
  let litsScrambled ← s.clauses.mapM fun ⟨lits⟩ => do
    return ⟨← (IO.randPerm lits)⟩
  let clausesScrambled ← IO.randPerm litsScrambled
  return { s with clauses := clausesScrambled }

def toFormula : State → ICnf
| {clauses, ..} => clauses.toArray

nonrec def toString : State → String
| {clauses,names,nextVar, ..} => Id.run do
  let mut acc := ""
  for i in [0:nextVar] do
    match names.find? (i.succPNat) with
    | none => ()
    | some name => acc := acc ++ s!"c {i} {name}\n"
  acc ++ toString clauses

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

def mkVar (name : String) : EncCNF IVar := do
  let oldState ← get
  set { oldState with
    nextVar := oldState.nextVar + 1,
    names := oldState.names.insert oldState.nextVar
                (oldState.varCtx ++ name)}
  return oldState.nextVar

def mkTemp : EncCNF IVar := do
  let oldState ← get
  return ← mkVar ("tmp" ++ toString oldState.nextVar)

def addClause (C : IClause) : EncCNF Unit := do
  let oldState ← get
  set { oldState with
    clauses := (oldState.conditionCtx ++ C) :: oldState.clauses }

/-- runs `e`, adding `ls` to each generated clause -/
def unlessOneOf (ls : Array ILit) (e : EncCNF α) : EncCNF α := do
  let oldState ← get
  set { oldState with conditionCtx := oldState.conditionCtx ++ ls }
  let res ← e
  let newState ← get
  set { newState with conditionCtx := oldState.conditionCtx }
  return res

def assuming (ls : Array ILit) (e : EncCNF α) : EncCNF α :=
  -- Literal negation here
  unlessOneOf (ls.map (- ·)) e

structure IVarBlock (dims : List Nat) where
  start : IVar
  h_dims : dims.length > 0

namespace IVarBlock

instance : Inhabited (IVarBlock (x::xs)) where
  default := {start := 1, h_dims := by simp [Nat.succ_pos]}

@[reducible, inline, simp]
def hdLen : IVarBlock ds → Nat
| ⟨_, _⟩ =>
  match ds with
  | [] => by contradiction
  | d::_ => d

@[reducible, inline, simp]
def elemTy : List Nat → Type
  | [] => Empty
  | [_] => IVar
  | _::d'::ds' => IVarBlock (d'::ds')

@[inline]
def get (v : IVarBlock ds) (i : Fin v.hdLen)
  : IVarBlock.elemTy ds
  := match ds, v with
  | [],         ⟨_    ,_⟩ => by contradiction
  | [_],        ⟨start,_⟩ => ⟨start + i.val, Nat.add_pos_left start.property _⟩
  | _::d'::ds', ⟨start,_⟩ =>
    { start := ⟨start + (Nat.mul i ((d'::ds').foldl (· * ·) 1)), Nat.add_pos_left start.property _⟩
      h_dims := by simp
    }

instance : GetElem (IVarBlock ds) Nat (IVarBlock.elemTy ds) (fun v i => i < v.hdLen) where
  getElem v i h := v.get ⟨i,h⟩

end IVarBlock

def mkVarBlock (name : String) (dims : List Nat) (h : dims.length > 0 := by simp)
  : EncCNF (IVarBlock dims) := do
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
  : EncCNF (IVarBlock dims) := do
  return ← mkVarBlock ("tmp" ++ toString (← get).nextVar) dims h

def blockAssn (a : PAssnHash ILit) : EncCNF Unit := addClause (a.toLitArray.map (- ·))

def addAssn (a : PAssnHash ILit) : EncCNF Unit := do
  for l in a.toLitArray do
    addClause #[l]
