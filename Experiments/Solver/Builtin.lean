import Init.Tactics
import Qq
import Mathlib.Tactic.ToExpr

import Trestle.Data.ICnf

open Qq Lean

namespace Trestle.Solver.Builtin

def icnf_to_cnf (f : ICnf) : Std.Sat.CNF Nat :=
  f.map (fun clause =>
    clause
    |> Array.map (fun l => ⟨(LitVar.toVar l).natPred, LitVar.polarity l⟩)
    |>.toList)
  |>.toList

theorem unsat_of_icnf_to_cnf_unsat (f : ICnf) :
  (icnf_to_cnf f).Unsat → f.Unsat := by
  intro h
  unfold icnf_to_cnf Std.Sat.CNF.Unsat at h
  unfold Trestle.ICnf.Unsat Trestle.ICnf.Sat Model.PropFun.satisfiable
  rintro ⟨τ,f_sat⟩
  specialize h (fun i => τ (IVar.fromIndex i))
  simp [IVar.fromIndex, Std.Sat.CNF.eval, Std.Sat.CNF.Clause.eval] at h
  rcases h with ⟨i,i_range,h⟩
  rw [Cnf.satisfies_iff] at f_sat
  specialize f_sat f[i] (by simp)
  rw [Clause.satisfies_iff] at f_sat
  simp_rw [Array.mem_iff_getElem] at f_sat
  rcases f_sat with ⟨_,⟨lidx,lidx_range,rfl⟩,l_sat⟩
  specialize h lidx lidx_range
  simp [LitVar.satisfies_iff] at l_sat
  contradiction

open Lean Elab.Tactic Parser.Tactic in
elab "trestle_unsat" cfg:optConfig : tactic => unsafe do
  withMainContext do
    let goal ← getMainGoal
    let goalDecl ← goal.getDecl
    let goalType := goalDecl.type
    let ⟨Level.succ Level.zero, ~q(Prop), ~q(Trestle.ICnf.Unsat $f)⟩ ← inferTypeQ goalType
      | throwError f!"expected goal to look like: Trestle.ICnf.Unsat _; got: {goalType}"

    let icnf ← Meta.evalExpr ICnf q(ICnf) f
    let cnf := icnf_to_cnf icnf

    let cfg ← BVDecide.Frontend.elabBVDecideConfig cfg
    IO.FS.withTempFile fun _ lratFile => do
      let cfg ← BVDecide.Frontend.TacticContext.new lratFile cfg

      let .ok cert ← BVDecide.Frontend.runExternal cnf cfg.solver cfg.lratPath cfg.config.trimProofs cfg.config.timeout cfg.config.binaryProofs
        | throwError f!"Call to SAT solver failed to return unsat"

      let pf ← Lean.Elab.Tactic.BVDecide.Frontend.LratCert.toReflectionProof cert cfg cnf
        ``Std.Tactic.BVDecide.Reflect.verifyCert ``Std.Tactic.BVDecide.Reflect.verifyCert_correct

      goal.assign (mkApp2 (mkConst ``unsat_of_icnf_to_cnf_unsat) f pf)


def testCnf : ICnf := #[ #[1,2,3], #[-1], #[-2], #[-3, 1] ]

theorem test : testCnf.Unsat := by
  trestle_unsat
