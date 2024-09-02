/-
Copyright (c) 2024 The LeanSAT Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import LeanSAT.Data.Cnf

namespace LeanSAT

/-- Partial assignment implementation backed by `Batteries.HashMap`.

Good for sparse partial assignments.
-/
def HashAssn (L : Type u) [LitVar L ν] [BEq ν] [Hashable ν] :=
  Batteries.HashMap ν Bool

namespace HashAssn

variable {L : Type u} {ν : Type v} [LitVar L ν] [BEq ν] [Hashable ν]

def empty : HashAssn L := Batteries.HashMap.empty

variable (self : HashAssn L)

def set (l : L) : HashAssn L := Batteries.HashMap.insert self (LitVar.toVar l) (LitVar.polarity l)

def toLitArray : Array L := Batteries.HashMap.toArray self |>.map (fun (a,b) => LitVar.mkLit L a b)

instance [ToString L] : ToString (HashAssn L) where
  toString a := a.fold (fun s v b => s ++ toString (LitVar.mkLit L v b)) ""
