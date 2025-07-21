import Lean

/-! #### Stored Proofs

For large or difficult SAT problems, we sometimes want to apply
proof techniques like Cube and Conquer (CnC),
where many clausal proofs are checked in parallel
and then the results combined to obtain some overall proof.

This presents a challenge for verifying CnC results;
we need a way to *store* certificates which somehow provide strong evidence
a given CNF is certifiably UNSAT.


-/

namespace Trestle.StoredProofs

/- To prevent tampering with this file, we hash our own contents
and mix them into the calculations down further. -/
run_meta do
  let env ← Lean.MonadEnv.getEnv
  let curFile := Lean.modToFilePath (← IO.currentDir) env.mainModule "lean"
  let hash := hash (← IO.FS.readFile curFile)
  Lean.liftCommandElabM do
    Lean.Elab.Command.elabCommand <| ← `(command|
      def $(Lean.mkIdent `srcFileHash) : UInt64 := $(Lean.Syntax.mkNatLit hash.toNat)
    )

#eval srcFileHash


/- We need to be able to get the axioms of a given thingo -/
#print axioms srcFileHash

run_meta do
  let res ← Lean.collectAxioms ``srcFileHash
  IO.println res

/-
def exCNF : Array (Array Int) := Array.ofFn (n := 100000) fun cid =>
  Array.ofFn (n := hash cid % 20 |>.toNat) fun lid =>
    let res := hash (cid,lid)
    if res &&& 1 == 0 then
      (res >>> 1) % 10000 |>.toNat
    else
      (res >>> 1) % 10000 |>.toNat |> (-·)

#eval hash (exCNF.push #[1,-1,3])

#eval mixHash (hash exCNF) (hash #[1,-1,3])
-/
