import Std

namespace LeanSAT


/-- CNF variable

NOTE: Unlike DIMACS, 0 is a valid variable. See `Var.toDIMACS`.
-/
def Var := Nat
deriving Inhabited, DecidableEq, Hashable, Repr, ToString

namespace Var

/-- Allow nat literals `5392` as notation for variables -/
instance : OfNat Var n := ⟨n⟩
end Var



/-- CNF literal -/
inductive Literal
| pos (v : Var) | neg (v : Var)
deriving Inhabited, DecidableEq, Hashable, Repr

namespace Literal

/-- The literal's variable -/
def var : Literal → Var
| pos v => v | neg v => v

/-- True iff the literal is `.pos v` -/
def isPos : Literal → Bool
| pos _ => true | neg _ => false

/-- True iff the literal is `.neg v` -/
def isNeg (l) := not (isPos l)

def not : Literal → Literal
| pos v => neg v
| neg v => pos v

/-- Automatically lift variables to positive literals -/
instance : Coe Var Literal := ⟨.pos⟩
/-- Allow literals to be written as nat constants -/
instance : OfNat Literal n := ⟨show Var from n⟩

instance : ToString Literal where
  toString | pos v => s!"{v}"
           | neg v => s!"¬{v}"

end Literal


/-- (Partial) assignment to the variables of a formula -/
def Assn := Std.HashMap Var Bool

namespace Assn

@[simp] def hasTrue   (v : Var) (a : Assn) : Bool := a.find? v = some true
@[simp] def hasFalse  (v : Var) (a : Assn) : Bool := a.find? v = some false
@[simp] def undecided (v : Var) (a : Assn) : Bool := a.find? v = none

def litTrue       (l : Literal) (a : Assn) : Bool := a.find? l.var = some l.isPos
def litFalse      (l : Literal) (a : Assn) : Bool := a.find? l.var = some l.isNeg
def litUndecided  (l : Literal) (a : Assn) : Bool := a.find? l.var = none

@[simp] theorem litTrue_pos : litTrue (.pos v) a = hasTrue v a := rfl
@[simp] theorem litTrue_neg : litTrue (.neg v) a = hasFalse v a := rfl
@[simp] theorem litFalse_pos : litFalse (.pos v) a = hasFalse v a := rfl
@[simp] theorem litFalse_neg : litFalse (.neg v) a = hasTrue v a := rfl
@[simp] theorem litUndecided_pos : litUndecided (.pos v) a = undecided v a := rfl
@[simp] theorem litUndecided_neg : litUndecided (.neg v) a = undecided v a := rfl

def insertLit (l : Literal) (a : Assn) : Assn :=
  a.insert l.var l.isPos

def toList (a : Assn) : List Literal :=
  Std.HashMap.toList a |>.map (fun (v,pos) => if pos then .pos v else .neg v)

instance : ToString Assn :=
  ⟨fun assn => assn.toList |>.map toString |> String.intercalate " "⟩

end Assn


/-- CNF clause: just a list of literals -/
structure Clause where
  lits : List Literal
deriving Inhabited, DecidableEq, Hashable, Repr

namespace Clause

/-- ⊥ / false clause -/
def empty : Clause := ⟨[]⟩

/-- Check whether any literals in `c` are set true by `a` -/
def eval (a : Assn) (c : Clause) : Bool :=
  c.lits.any a.litTrue

@[simp]
theorem eval_nil : eval a ⟨[]⟩ = false
  := by
  simp [eval, List.any, List.foldr]

@[simp]
theorem eval_cons : eval a ⟨l::ls⟩ = (a.litTrue l || eval a ⟨ls⟩)
  := by
  simp [eval, List.any, List.foldr]

instance : OfNat Clause n := ⟨(⟨[.pos n]⟩)⟩
instance : Coe Literal Clause := ⟨(⟨[·]⟩)⟩
instance : Coe (List Literal) Clause := ⟨(⟨·⟩)⟩

instance : ToString Clause where
  toString | ⟨lits⟩ => lits.map toString |> String.intercalate " "

end Clause



/-- CNF formula: a collection of clauses.

This structure is used for formalizing lemmas about sat/unsat
reductions and the likes. -/
structure Formula where
  clauses : List Clause
deriving DecidableEq, Repr

namespace Formula

def numVars : Formula → Nat
| ⟨clauses⟩ =>
  clauses.filterMap (·.lits.map (β := Nat) Literal.var |>.maximum?)
  |>.maximum?.map Nat.succ |>.getD 0

def vars : Formula → List Var
| ⟨clauses⟩ => Id.run do
  let mut set := Std.HashMap.empty
  for c in clauses do
    for l in c.lits do
      set := set.insert l.var ()
  return set.toList.map (·.1)

/-- ⊤ / true Formula -/
def empty : Formula := ⟨[]⟩

/-- Check whether all clauses in `c` are satisfied by `a` -/
def eval (a : Assn) (c : Formula) : Bool :=
  c.clauses.all (·.eval a)

@[simp]
theorem eval_nil : eval a ⟨[]⟩ = true
  := by
  simp [eval, List.all, List.foldr]

@[simp]
theorem eval_cons : eval a ⟨c::cs⟩ = (c.eval a && eval a ⟨cs⟩)
  := by
  simp [eval, List.all, List.foldr]

/-- Formula `c` is satisfiable if there exists a variable assignment
on which it is satisfied. -/
def satisfiable (c : Formula) := ∃ a, c.eval a = true

/-- Formula `c` is unsatisfiable iff there does not exist a variable
assignment on which it is satisfied. -/
def unsat (c : Formula) := ¬c.satisfiable

instance : Coe Clause Formula := ⟨(⟨[·]⟩)⟩
instance : OfNat Formula n := ⟨Literal.pos n⟩

nonrec def toString (f : Formula) : String :=
  f.clauses.map toString |> String.intercalate "\n"

instance : ToString Formula := ⟨toString⟩
end Formula


/-! CNF notation -/
namespace Notation

scoped notation:30 a:31 " ∨ " b:30 => Clause.mk (List.append (Clause.lits a) (Clause.lits b))
scoped notation a "∧" b => Formula.mk (List.append (Formula.clauses a) (Formula.clauses b))
scoped notation:max "¬" l:40 => Literal.not l

example : Literal := 5
example : Literal := ¬5
example : Clause  := ¬5 ∨ ¬10
example : Formula := (¬5 ∨ ¬10) ∧ 20 ∧ ¬30

end Notation
