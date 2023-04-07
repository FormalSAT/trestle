# LeanSAT

LeanSAT is a collection of utilities for SAT work. This includes:
- Encoding utilities
- Solver APIs
- Common file formats

## Getting it

Add the following to your project's `lakefile`:
```
require «lean-sat» from git
  "https://github.com/JamesGallicchio/LeanSAT" @ "main"
```
Then `import LeanSAT` will import everything in the library.

## Usage

Important namespaces:
- `LeanSAT`: everything in the library is under `LeanSAT`, so you probably want to `open LeanSAT` at the top of your files
- `LeanSAT.Notation`: this exposes nice notation for writing CNFs. It is under a separate namespace because it clashes with proposition notation, so you should only open `Notation` in the declarations where you are using it (via `open Notation in ...`)

Important types:
- `EncCNF`: the encoding monad. You can generate variables and add clauses. It also keeps track of meta-info about the variable names and so on. See `Examples/Encoding` for example usage.
- `Solver`, `Solver.ModelCount`, `Solver.ModelSample`: interfaces for solvers (and model counters/model samplers). These are each typeclasses. The idea is that you should have an `instance` of the `Solver` typeclass in scope when you go to solve a CNF formula. See `Examples/Cadical.lean` for how to declare a solver instance.

## Planned scope

We are planning to add support for:
- Non-CNF formulas (KNF, d-DNNF, XOR-CNF, ...)
- Verification
  - Verified encodings (see [Cayden Codel's work](https://github.com/ccodel/verified-encodings))
  - Verification of sat witnesses/unsat proofs (see e.g. [here](https://github.com/joehendrix/lean-sat-checker) and [here](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/Sat/FromLRAT.lean))
  - Verified model counting
- Pre-processing techniques
