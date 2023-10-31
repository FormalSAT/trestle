import LeanSAT.Data.Cnf

namespace LeanSAT

/-- Partial assignment implementation backed by `Std.HashMap`.

Good for sparse partial assignments.
-/
def PAssnHash (L : Type u) [LitVar L ν] [BEq ν] [Hashable ν] :=
  Std.HashMap ν Bool

namespace PAssnHash

variable {L : Type u} {ν : Type v} [LitVar L ν] [BEq ν] [Hashable ν]

def empty : PAssnHash L := Std.HashMap.empty

variable (self : PAssnHash L)

def set (l : L) : PAssnHash L := Std.HashMap.insert self (LitVar.toVar l) (LitVar.polarity l)

def toLitArray : Array L := Std.HashMap.toArray self |>.map (fun (a,b) => LitVar.mkLit L a b)

instance [ToString L] : ToString (PAssnHash L) where
  toString a := a.fold (fun s v b => s ++ toString (LitVar.mkLit L v b)) ""
