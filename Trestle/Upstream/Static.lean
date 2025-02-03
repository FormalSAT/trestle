-- a file which knows its own hash
import Lean

open Lean Core in
elab "#hash " id:ident : command => do
  let ctx ← Elab.Command.liftCoreM (read)
  let name := ctx.fileName
  let hash :=
    (← IO.FS.readFile name)
    |> hash
  Elab.Command.elabCommand (← `(
    def $id := $(Syntax.mkNatLit hash.toNat)
  ))

#hash thisFilesHash

#eval thisFilesHash
