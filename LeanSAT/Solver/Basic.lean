import Std.Data.HashMap
import LeanSAT.Data.Cnf
import LeanSAT.Data.HashAssn
import LeanSAT.Data.ICnf

open Std

namespace LeanSAT.Solver

inductive Res
| sat (assn : HashAssn ILit)
| unsat
| error

instance : ToString Res where
  toString  | .error => "error"
            | .unsat => "unsat"
            | .sat assn => "sat: " ++ toString assn

def Res.isSat : Res → Bool
| .sat _  => true
| _       => false

def Res.getAssn? : Res → Option (HashAssn ILit)
| .sat assn => some assn
| _         => none

end Solver

class Solver (m : Type → Type v) where
  solve : [Monad m] → ICnf → m Solver.Res

namespace Solver

def Solutions (_f : ICnf) (_varsToBlock : List IVar) : Type := Unit
def solutions (f vars) : Solutions f vars := ()

instance [Solver m] : ForIn m (Solutions f vars) (HashAssn ILit) where
  forIn _ b perItem := do
    let mut b := b
    let mut state := some f
    while state.isSome do
      match state with
      | none => panic! "woo"
      | some f =>
      match ← solve f with
      | .error
      | .unsat =>
        state := none
      | .sat assn =>
      match ← perItem assn b with
      | .done b' =>
        return b'
      | .yield b' =>
        b := b'
        let blocking_clause : List ILit :=
          vars.filterMap (fun v =>
            assn.find? v |>.map (if · then LitVar.mkNeg v else LitVar.mkPos v))
        let f' := f.push blocking_clause.toArray
        state := some f'
    return b

def allSolutions [Monad m] [Solver m] (f : ICnf) (varsToBlock : List IVar)
  : m (List (HashAssn ILit)) := do
  let mut sols := []
  for assn in solutions f varsToBlock do
    sols := assn :: sols
  return sols


class IpasirSolver (S : outParam Type) (m : Type → Type v) where
  new : m S
  addClause : IClause → S → m S
  solve : S → m SolveRes

instance [Monad m] [IpasirSolver S m] : Solver m where
  solve f := do
    let s : S ← IpasirSolver.new
    let s ← f.foldlM (fun s c => IpasirSolver.addClause c s) s
    IpasirSolver.solve s

class ModelCount (m : Type → Type v) [outParam (Monad m)] where
  modelCount : ICnf → Option (List IVar) → m Nat

class ModelSample (m : Type → Type v) where
  modelSample : ICnf → Option (List IVar) → Nat → m (List (HashAssn ILit))
