/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Trestle.Data.ICnf

namespace Trestle

namespace RichCnf

inductive Line
| clause (c : IClause)
| comment (s : String)

end RichCnf

def RichCnf := Array RichCnf.Line

namespace RichCnf

def toICnf : RichCnf → ICnf :=
  Array.filterMap (fun | .clause c => some c | .comment _ => none)

def fromICnf : ICnf → RichCnf := Array.map (.clause ·)

@[simp] def toPropFun (c : RichCnf) : Model.PropFun IVar :=
  c.toICnf.toPropFun

def maxVar (fml : RichCnf) : Nat :=
  fml.maxBy (fun
    | .comment _ => 0
    | .clause c => c.maxBy (LitVar.toVar · |>.val) |>.getD 0
  ) |>.getD 0

def addClause (c : IClause) (a : RichCnf) : RichCnf :=
  a.push (.clause c)

@[simp] theorem addClause_toICnf (c a) :
    (addClause c a).toICnf = a.toICnf.addClause c := by
  simp [addClause, toICnf, Cnf.addClause, Array.push]

def addComment (s : String) (a : RichCnf) : RichCnf :=
  a.push (.comment s)

@[simp] theorem addComment_toICnf (s a) :
    (addComment s a).toICnf = a.toICnf := by
  simp only [addComment, toICnf, ← Array.toList_inj, Array.toList_filterMap]
  simp

end RichCnf
