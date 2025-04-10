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

initialize registerTraceClass `Trestle.Solver.Builtin

open Lean Meta Elab.Tactic.BVDecide.Frontend in
/-- this is modified from BVDecide.Frontend mkReflectionProof -/
def mkReflectionProof (cert : LratCert) (cfg : TacticContext)
    (reflectedExpr : Expr)
    (verifier : Name) (unsat_of_verifier_eq_true : Name) : MetaM Expr := do

  let certType := toTypeExpr LratCert

  withTraceNode `Trestle.Solver.Builtin (fun _ => return "Compiling proof certificate term") do
    mkAuxDecl cfg.certDef (toExpr cert) certType

  let certExpr := mkConst cfg.certDef

  withTraceNode `Trestle.Solver.Builtin (fun _ => return "Compiling reflection proof term") do
    let auxValue := mkApp2 (mkConst verifier) reflectedExpr certExpr
    mkAuxDecl cfg.reflectionDef auxValue (mkConst ``Bool)

  let auxType ← mkEq (mkConst cfg.reflectionDef) (toExpr true)
  let auxProof :=
    mkApp3
      (mkConst ``Lean.ofReduceBool)
      (mkConst cfg.reflectionDef)
      (toExpr true)
      (← mkEqRefl (toExpr true))
  try
    let auxLemma ←
      -- disable async TC so we can catch its exceptions
      withOptions (Elab.async.set · false) do
        withTraceNode `Trestle.Solver.Builtin (fun _ => return "Verifying LRAT certificate") do
          mkAuxLemma [] auxType auxProof
    return mkApp3 (mkConst unsat_of_verifier_eq_true) reflectedExpr certExpr (mkConst auxLemma)
  catch e =>
    throwError m!"Failed to check the LRAT certificate in the kernel:\n{e.toMessageData}"

open Lean Elab.Tactic Parser.Tactic in
elab "trestle_unsat" cfg:optConfig : tactic => unsafe do
  withMainContext do
    let goal ← getMainGoal
    let goalDecl ← goal.getDecl
    let goalType := goalDecl.type
    let ⟨Level.succ Level.zero, ~q(Prop), ~q(Trestle.ICnf.Unsat $f)⟩ ← inferTypeQ goalType
      | throwError f!"expected goal to look like: Trestle.ICnf.Unsat _; got: {goalType}"

    let icnf ← Meta.evalExpr ICnf q(ICnf) f
    trace[Trestle.Solver.Builtin] m!"Running solver on CNF with {icnf.size} clauses"
    let cnf := icnf_to_cnf icnf

    let cfg ← BVDecide.Frontend.elabBVDecideConfig cfg
    IO.FS.withTempFile fun _ lratFile => do
      let cfg ← BVDecide.Frontend.TacticContext.new lratFile cfg

      let .ok cert ← BVDecide.Frontend.runExternal cnf cfg.solver cfg.lratPath cfg.config.trimProofs cfg.config.timeout cfg.config.binaryProofs
        | throwError f!"Call to SAT solver failed to return unsat"

      trace[Trestle.Solver.Builtin] m!"Solver found UNSAT proof of length {String.length cert} bytes"

      let pf ← mkReflectionProof cert cfg q(icnf_to_cnf $f)
        ``Std.Tactic.BVDecide.Reflect.verifyCert ``Std.Tactic.BVDecide.Reflect.verifyCert_correct

      goal.assign (mkApp2 (mkConst ``unsat_of_icnf_to_cnf_unsat) f pf)

def testCnf : ICnf :=
  let allOfEm := List.range 10000 |>.map Nat.succPNat
  allOfEm.toArray.map (#[LitVar.mkNeg ·])
  |>.push (allOfEm.toArray.map (LitVar.mkPos ·))

theorem test : testCnf.Unsat := by
  trestle_unsat

/--
info: 'Trestle.Solver.Builtin.test' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in
#print axioms test
