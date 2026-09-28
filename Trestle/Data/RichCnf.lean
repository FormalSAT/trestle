/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Trestle.Data.ICnf

namespace Trestle

namespace RichCnf

inductive Line (L : Type u)
  | clause (c : Clause L)
  | comment (s : String)

end RichCnf /- namespace -/

def RichCnf (L : Type u) := Array (RichCnf.Line L)
abbrev RichICnf := RichCnf ILit

namespace RichCnf

variable {L : Type u}

def toCnf : RichCnf L → Cnf L :=
  Array.filterMap (fun | .clause c => some c | .comment _ => none)

def fromCnf : Cnf L → RichCnf L :=
  Array.map (.clause ·)

instance instCoeToCnf : Coe (RichCnf L) (Cnf L) := ⟨toCnf⟩
instance instCoeOfCnf : Coe (Cnf L) (RichCnf L) := ⟨fromCnf⟩

@[simp]
def toPropFun {ν : Type v} [LitVar L ν] (F : RichCnf L) : Model.PropFun ν :=
  F.toCnf.toPropFun

def addClause (c : Clause L) (F : RichCnf L) : RichCnf L :=
  F.push (.clause c)

def addComment (s : String) (F : RichCnf L) : RichCnf L :=
  F.push (.comment s)

def maxVar {ν : Type v} [Max ν] [LitVar L ν] (F : RichCnf L) : Option ν :=
  F.toCnf.maxVar

@[simp]
theorem addClause_toCnf (c : Clause L) (F : RichCnf L) : (addClause c F).toCnf = F.toCnf.addClause c := by
  suffices h : ∀ xs : Array (Line L), toCnf (xs.push (.clause c)) = (toCnf xs).addClause c from h F
  intro xs
  simp [toCnf, Cnf.addClause]

@[simp]
theorem addComment_toCnf (s : String) (F : RichCnf L) : (addComment s F).toCnf = F.toCnf := by
  suffices h : ∀ xs : Array (Line L), toCnf (xs.push (.comment s)) = toCnf xs from h F
  intro xs
  simp [toCnf]

instance instInhabited (L : Type u) : Inhabited (RichCnf L) := ⟨Array.empty⟩

end RichCnf /- namespace -/

end Trestle /- namespace -/
