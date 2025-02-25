import Trestle.Data.LitVar.Defs

namespace Trestle

abbrev Clause (L : Type u) := Array L
abbrev Cnf (L : Type u) := Array (Clause L)

namespace Clause

instance instToString [ToString L] : ToString (Clause L) where
  toString C := s!"({String.intercalate " ∨ " (C.map toString).toList})"

variable {L : Type u} {ν : Type v} [LitVar L ν]

def or (c1 c2 : Clause L) : Clause L :=
  c1 ++ c2

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

end Trestle
