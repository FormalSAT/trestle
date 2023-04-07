import Std.Data.HashMap
import LeanSAT.CNF

open Std

namespace LeanSAT.Solver

inductive Res
| sat (assn : Assn)
| unsat
| error

instance : ToString Res where
  toString  | .error => "error"
            | .unsat => "unsat"
            | .sat assn => "sat: " ++ toString assn

def Res.isSat : Res → Bool
| .sat _  => true
| _       => false

def Res.getAssn? : Res → Option Assn
| .sat assn => some assn
| _         => none

end Solver

class Solver (m : Type → Type v) [outParam (Monad m)] where
  solve : Formula → m Solver.Res

namespace Solver

def Solutions (f : Formula) (varsToBlock : List Var) : Type := Unit
def solutions (f vars) : Solutions f vars := ()

instance [@Solver m _mm] : ForIn m (Solutions f vars) Assn where
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
        let blocking_clause : List Literal :=
          vars.filterMap (fun v =>
            assn.find? v |>.map (if · then .neg v else .pos v))
        let f' :=
          ⟨blocking_clause :: f.clauses⟩
        state := some f'
    return b

def allSolutions [@Solver m _mm] (f : Formula) (varsToBlock : List Var)
  : m (List Assn) := do
  let mut sols := []
  for assn in solutions f varsToBlock do
    sols := assn :: sols
  return sols


class IpasirSolver (S : Type) (m : Type → Type v) [outParam (Monad m)] where
  new : m S
  addClause : Clause → S → m S
  solve : S → m SolveRes

instance [Monad m] [IpasirSolver S m] : Solver m where
  solve f := do
    let s : S ← IpasirSolver.new
    let s ← f.clauses.foldlM (fun s c => IpasirSolver.addClause c s) s
    IpasirSolver.solve s

class ModelCount (m : Type → Type v) [outParam (Monad m)] where
  modelCount : Formula → Option (List Var) → m Nat

class ModelSample (m : Type → Type v) where
  modelSample : Formula → Option (List Var) → Nat → m (List Assn)
