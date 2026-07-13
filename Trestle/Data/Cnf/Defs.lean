
import Trestle.Data.LitVar.Defs
import Batteries.Data.List.Basic
import Trestle.Upstream.ToStd

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

/--
  A logical string representation of a clause.

  This is NOT a `ToString` instance because the `abbrev` overrides
  the printing of *any* `Array Lit`, which is undesirable.
-/
def toLString [ToString L] (C : Clause L) : String :=
  String.intercalate " " (C.map toString).toList ++ " 0"

variable {L : Type u} {ν : Type v} [LitVar L ν]

def or (c1 c2 : Clause L) : Clause L :=
  c1 ++ c2

def negate (c : Clause L) : Cube L :=
  Array.map (-·) c

nonrec def map [LitVar L' ν'] (f : ν → ν') (c : Clause L) : Clause L' :=
  c.map (LitVar.map f)

def maxVar [Ord ν] [LitVar L ν] (C : Clause L) : Option ν :=
  Array.map LitVar.toVar C |>.max?

end Clause

namespace Cnf

/--
  A logical string representation of a CNF formula.

  This is NOT a `ToString` instance because the `abbrev` overrides
  the printing of *any* `Array (Clause Lit)`, which is undesirable.
-/
def toLString [ToString L] (F : Cnf L) : String :=
  String.intercalate " " (F.map (Clause.toLString)).toList

variable {L : Type u} {ν : Type v} [LitVar L ν]

def addClause (f : Cnf L) (C : Clause L) : Cnf L := f.push C

def and (f1 f2 : Cnf L) : Cnf L := f1 ++ f2

def not (c : Clause L) : Cnf L :=
  Array.map (fun l => #[-l]) c

def any (ls : Array L) : Cnf L := #[ls]

def all (ls : Array L) : Cnf L :=
  Array.map (fun l => #[l]) ls

def maxVar [Ord ν] [LitVar L ν] (F : Cnf L) : Option ν :=
  match Array.map Clause.maxVar F |>.max? with
  | none => none
  | some none => none
  | some (some v) => some v

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
