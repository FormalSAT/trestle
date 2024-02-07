# LeanSAT

LeanSAT is a collection of utilities for SAT work. This includes:
- Encoding utilities
- Solver APIs
- Printers and parsers for common file formats

## Getting it

Add the following to your project's `lakefile`:
```
require «lean-sat» from git
  "https://github.com/JamesGallicchio/LeanSAT" @ "main"
```
Then `import LeanSAT` will import everything in the library.

## Usage

Everything in the library is under the `LeanSAT` namespace,
so we generally assume you have `open LeanSAT` at the top of your files.

Important types:
- `PropFun`: **The mathematical model of a propositional formula**.
  Two `PropFun`s are equal iff they have the same interpretation under all assignments.
- `EncCNF`: **The encoding monad.**
  This monad allows you to build up a CNF via do-notation.
  See `Examples/Encoding` for example usage.
- `VEncCNF`: **Verified encoding.**
  Similar to `EncCNF`, but the type specifies a `PropFun`
  which the object provably encodes.
  This connects `EncCNF` to the `PropFun` math model.
- `Solver`, `Solver.ModelCount`, `Solver.ModelSample`: **Solver interfaces.**
  These are each typeclasses.
  The idea is that you should have an `instance` of the `Solver` typeclass in scope
  when you go to solve a CNF formula.
  See `Examples/Cadical.lean` for how to declare a solver instance.

### Notation

TODO(JG): describe available notation for `PropFun`, `PropForm`

## Planned scope

- Support (verified?) encoding to non-CNF formulas (KNF, d-DNNF, XOR-CNF, ...)
- Add verified checkers for sat certificates
  - See e.g. [here](https://github.com/joehendrix/lean-sat-checker),
      [here](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/Sat/FromLRAT.lean),
      [here](https://github.com/leanprover/leansat)
- Add verified model counting
  - See [Bryant et al 2023](https://github.com/rebryant/cpog)
- Add verified pre-processing
