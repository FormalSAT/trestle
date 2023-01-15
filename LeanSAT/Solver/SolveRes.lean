import Std.Data.HashMap
import LeanSAT.CNF

namespace LeanSAT

open Std

inductive SolveRes
| sat (assn : HashMap Var Bool)
| unsat
| error

def SolveRes.isSat : SolveRes → Bool
| .sat _  => true
| _       => false

def SolveRes.getAssn? : SolveRes → Option (HashMap Var Bool)
| .sat assn => some assn
| _         => none
