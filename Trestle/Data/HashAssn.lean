/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Trestle.Data.Cnf
import Trestle.Model.PropAssn

namespace Trestle

/-- Partial assignment implementation backed by `Std.HashMap`.

Good for sparse partial assignments.
-/
def HashAssn (L : Type u) [LitVar L ν] [BEq ν] [Hashable ν] :=
  Std.HashMap ν Bool

namespace HashAssn

variable {L : Type u} {ν : Type v} [LitVar L ν] [BEq ν] [Hashable ν]

def empty : HashAssn L := Std.HashMap.empty

variable (self : HashAssn L)

def set (l : L) : HashAssn L := Std.HashMap.insert self (LitVar.toVar l) (LitVar.polarity l)

def toLitArray : Array L := Std.HashMap.toArray self |>.map (fun (a,b) => LitVar.mkLit L a b)

def toPropAssn : Model.PropAssignment ν :=
  fun v => self.get? v |>.getD false

instance [ToString L] : ToString (HashAssn L) where
  toString a := a.toList.map (fun (v,b) => toString (LitVar.mkLit L v b)) |> String.intercalate " "
