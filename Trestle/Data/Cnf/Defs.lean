import Trestle.Data.LitVar.Defs

import Batteries.Data.List.Basic

namespace Trestle

/-- A disjunction of literals -/
abbrev Clause (L : Type u) := Array L

/-- A conjunction of clauses -/
abbrev Cnf (L : Type u) := Array (Clause L)

/-- A conjunction of literals.
The implementation is identical to clauses,
but the interpretation is different.
-/
def Cube (L : Type u) := Array L

namespace Clause

instance instToString [ToString L] : ToString (Clause L) where
  toString C := s!"({String.intercalate " ∨ " (C.map toString).toList})"

variable {L : Type u} {ν : Type v} [LitVar L ν]

def or (c1 c2 : Clause L) : Clause L :=
  c1 ++ c2

def negate (c : Clause L) : Cube L :=
  Array.map (-·) c

nonrec def map (L') [LitVar L' ν'] (f : ν → ν') (c : Clause L) : Clause L' :=
  c.map (LitVar.map f)

end Clause

namespace Cnf

instance instToString [ToString L] : ToString (Cnf L) where
  toString C := s!"{String.intercalate " ∧ " (C.map toString).toList}"

variable {L : Type u} {ν : Type v} [LitVar L ν]

def addClause (f : Cnf L) (C : Clause L) : Cnf L := f.push C

def and (f1 f2 : Cnf L) : Cnf L := f1 ++ f2

def not (c : Clause L) : Cnf L :=
  Array.map (fun l => #[-l]) c

def any (ls : Array L) : Cnf L := #[ls]

def all (ls : Array L) : Cnf L :=
  Array.map (fun l => #[l]) ls

end Cnf


namespace Cube

instance [ToString L] : ToString (Cube L) where
  toString C := s!"({String.intercalate " ∧ " (C.map toString).toList})"

variable {L : Type u} {ν : Type v} [LitVar L ν]

abbrev toArray (c : Cube L) : Array L := c

instance : CoeHead (Cube L) (Array L) := ⟨toArray⟩

def and (c1 c2 : Cube L) : Cube L :=
  c1.toArray ++ c2.toArray

nonrec def map (L') [LitVar L' ν'] (f : ν → ν') (c : Cube L) : Cube L' :=
  c.map (LitVar.map f)

def negate (c : Cube L) : Clause L :=
  Array.map (- ·) c

end Cube

abbrev Cubing (L) := List (Cube L)

namespace Cubing

def unit : Cubing L := [#[]]

def prod (c1 c2 : Cubing L) : Cubing L :=
  List.product c1 c2
  |>.map fun (a,b) => a.and b

end Cubing

end Trestle
