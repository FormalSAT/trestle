import Trestle.Data.Cnf
import Trestle.Solver.Dimacs

namespace Trestle

namespace SR

structure Line (L) [LitVar L ν] where
  c : Clause L
  pivot : L
  true_lits : Array L
  substs : Array (ν × L)

variable [LitVar L ν] [Repr L] [BEq L] [DecidableEq ν]

instance [Inhabited ν] : Inhabited (Line L) where
  default := { c := default, pivot := LitVar.mkPos default, true_lits := default, substs := default }

def mkLine (c : Clause L) (hc : c.size > 0 := by simp)
        (true_lits : Array L)
        (substs : Array (ν × L)) : Line L :=
  have : Inhabited ν := ⟨LitVar.toVar c[0]⟩
  if true_lits.isEmpty then
    if !substs.isEmpty then
      panic! s!"true_lits empty but substs nonempty?! clause: {repr c}"
    else
      { c, pivot := c[0], true_lits := #[], substs := #[] }
  else
  have : Inhabited _ := ⟨c[0]⟩
  -- let's filter out true_lits from substs
  let substs := substs.filter (fun (a,b) => !true_lits.any (LitVar.toVar · = a))
  -- we should pick a pivot `p ∈ c` such that `p ∈ true_lits`
  let pivot :=
    match c.find? (true_lits.contains ·) with
    | some p => p
    | none =>
      panic! s!"mkLine could not select a pivot! clause: {repr c}\ntrue_lits: {repr true_lits}"
  -- sanity check that the negation of the pivot isn't ALSO in true_lits
  if true_lits.contains (-pivot) then
    panic! s!"true_lits contains literal {repr pivot} *and* its negation?\nclause: {repr c}\ntrue_lits: {repr true_lits}"
  else
  -- now let's ensure pivot is at the front of the clause
  let c := #[pivot] ++ c.filter (· != pivot)
  -- and then filter it out of true_lits
  let true_lits := true_lits.filter (· != pivot)
  { c, pivot, true_lits, substs }

open Solver.Dimacs in
@[inline]
def printSRLine [Monad m] (putStr : String → m Unit)
    (c : IClause) (pivot : ILit) (true_lits : Array ILit) (substs : Array (IVar × ILit)) := do
  if true_lits.isEmpty ∧ substs.isEmpty then
    putStr <| Trestle.Solver.Dimacs.formatClause c
    putStr "\n"
  else
    for l in c do
      putStr <| formatLit l
      putStr <| " "

    putStr <| formatLit pivot
    putStr <| " "
    for l in true_lits do
      putStr <| formatLit l
      putStr <| " "

    putStr <| formatLit pivot
    putStr <| " "
    for (v,l) in substs do
      putStr s!"{formatVar v} {formatLit l} "
    putStr "0\n"
