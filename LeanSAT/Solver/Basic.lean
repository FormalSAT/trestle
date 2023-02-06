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

def allSolutions [@Solver m _mm] (f : Formula) (varsToBlock : List Var)
  : m (List Assn) := do
  let mut sols := []
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
      sols := assn :: sols
      let blocking_clause : List Literal :=
        varsToBlock.filterMap (fun v =>
          assn.find? v |>.map (if · then .pos v else .neg v))
      let f' :=
        ⟨blocking_clause :: f.clauses⟩
      state := some f'
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

structure ApproxModelCount.Res where
  mult : Nat
  base : Nat
  pow  : Nat
deriving Inhabited

namespace ApproxModelCount.Res

instance : ToString ApproxModelCount.Res where
  toString | ⟨mult,base,pow⟩ => s!"{mult} * {base}^{pow}"

def toNat : ApproxModelCount.Res → Nat
| {mult, base, pow} => mult * base^pow

end ApproxModelCount.Res

class ApproxModelCount (m : Type → Type v) [outParam (Monad m)] where
  approxModelCount : Formula → Option (List Var) → m ApproxModelCount.Res
