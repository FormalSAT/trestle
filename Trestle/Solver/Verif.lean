/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Std.Data.HashMap
import Trestle.Data.Cnf
import Trestle.Data.HashAssn
import Trestle.Data.ICnf

open Std

namespace Trestle.VSolver

open Model PropFun

inductive Res (φ : ICnf)
| sat (assn : HashAssn ILit) (h : assn.toPropAssn ⊨ φ.toPropFun)
| unsat (h : ∀ (τ : PropAssignment IVar), τ ⊭ φ.toPropFun)
| error

end VSolver

class VSolver (m : Type → Type v) where
  solve : [Monad m] → (φ : ICnf) → m (VSolver.Res φ)
