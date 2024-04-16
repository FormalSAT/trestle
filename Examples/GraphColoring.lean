import LeanSAT.Model.PropFun
import LeanSAT.Encode.EncCNF
import LeanSAT.Encode.VEncCNF
import LeanSAT.Solver.Basic
import LeanSAT.Solver.Dimacs
import LeanSAT.Data.ICnf
import LeanSAT.Upstream.ToMathlib

import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Sum.Order
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic

open LeanColls LeanSAT LeanSAT.Model PropFun

-- A graph is a symmetric function from two vertices to a boolean
-- The number of vertices `n` is specified ahead of time
abbrev Graph (n : Nat) := SimpleGraph (Fin n)

def Coloring (n : Nat) (numColors : Nat) := (Fin n) → (Fin numColors)

def isValidColoring (G : Graph n) (C : Coloring n c) :=
  ∀ ⦃u v⦄, G.Adj u v → C u ≠ C v

-- Vertex variables involved in graph coloring
inductive ColorVars (n : Nat)
  | blue   (v : Fin n)
  | red    (v : Fin n)
  | green  (v : Fin n)
  | yellow (v : Fin n)
  deriving DecidableEq, Repr, IndexType

-- Open the namespace so we can use "blue" instead of "Coloring.blue", etc.
open ColorVars

-- Given a vertex, we should expect that it gets a color
def eachVertexGetsAColor (u : Fin n) : PropFun (ColorVars n) :=
  [propfun|
    ({blue   u}  ∨
     {red    u}  ∨
     {green  u}  ∨
     {yellow u})
  ]

-- Alternative definition treating CNF clauses as boolean algebras
def eachVertexGetsAColor' (v : Fin n) : PropFun (ColorVars n) :=
  (blue v) ⊔ (red v) ⊔ (green v) ⊔ (yellow v)

-- Each vertex gets a color
def vertexColorConstraints (n : Nat) : PropPred (ColorVars n) := fun τ =>
  ∀ (v : Fin n), τ ⊨ (eachVertexGetsAColor v)

def adjacentVertexesGetDifferentColors (u v : Fin n) : PropFun (ColorVars n) :=
  [propfun|
    (¬ ({blue    u} ∧ {blue   v})) ∧
    (¬ ({red     u} ∧ {red    v})) ∧
    (¬ ({green   u} ∧ {green  v})) ∧
    (¬ ({yellow  u} ∧ {yellow v}))
  ]

def adjacentVertexesGetDifferentColors' (u v : Fin n) : PropFun (ColorVars n) :=
  ((blue   u)ᶜ ⊔ (blue   v)ᶜ) ⊓
  ((red    u)ᶜ ⊔ (red    v)ᶜ) ⊓
  ((green  u)ᶜ ⊔ (green  v)ᶜ) ⊓
  ((yellow u)ᶜ ⊔ (yellow v)ᶜ)

-- Each edge has different colors
def edgeConstraints (G : Graph n) : PropPred (ColorVars n) := fun τ =>
  ∀ (u v), G.Adj u v → τ ⊨ adjacentVertexesGetDifferentColors u v

-- The graph coloring problem
def graphColoring (G : Graph n) : PropPred (ColorVars n) := fun τ =>
  (τ |> vertexColorConstraints n) ∧
  (τ |> edgeConstraints G)

------------------------------------------------------------------------
-- Now we express the graph coloring problem as a CNF
/-! # CNF -/

open Encode VEncCNF LitVar

abbrev VCnf (n : Nat) := VEncCNF (ColorVars n) Unit

def vertexColorClause (v : Fin n) : VCnf n (eachVertexGetsAColor v) :=
  (addClause #[mkPos <| blue v, mkPos <| red v, mkPos <| green v, mkPos <| yellow v])
  |> mapProp (by
    simp [eachVertexGetsAColor, Clause.toPropFun]
  )

def vertexColorClauses (n : Nat) : VCnf n (vertexColorConstraints n) :=
  ( let U := (Array.finRange n)
    for_all U fun v =>
      vertexColorClause v)
  |> mapProp (by ext τ; apply forall_congr'; simp)

def adjacentVertexesClauses (G : Graph n) [DecidableRel G.Adj] : VCnf n (edgeConstraints G) :=
  ( let U := (Array.finRange n)
    for_all U fun u =>
    for_all U fun v =>
    VEncCNF.guard (u ≠ v) fun _ =>
    VEncCNF.guard (G.Adj u v) fun _ =>
      seq[
        addClause #[mkNeg <| blue   u, mkNeg <| blue   v],
        addClause #[mkNeg <| red    u, mkNeg <| red    v],
        addClause #[mkNeg <| green  u, mkNeg <| green  v],
        addClause #[mkNeg <| yellow u, mkNeg <| yellow v]
      ])
  |> mapProp (by
    ext τ
    simp [edgeConstraints, adjacentVertexesGetDifferentColors, Clause.toPropFun]
    apply forall_congr'; intro u
    apply forall_congr'; intro v
    aesop)

def graphColoringCNF (G : Graph n) [DecidableRel G.Adj] : VCnf n (graphColoring G) :=
  (seq[
    vertexColorClauses n,
    adjacentVertexesClauses G
  ]).mapProp (by simp [graphColoring]; rfl)

------------------------------------------------------------------------

-- Now we prove that if there is a valid coloring, then we can produce an
-- assignment on the variables for the graph

def coloringAssignment (C : Coloring n 4) : PropAssignment (ColorVars n) :=
  fun
  | .blue   v => C v = ⟨0, by decide⟩
  | .red    v => C v = ⟨1, by decide⟩
  | .green  v => C v = ⟨2, by decide⟩
  | .yellow v => C v = ⟨3, by decide⟩

theorem coloringAssignment_exists_of_validColoring {G : Graph n} :
  (∃ (C : Coloring n 4), isValidColoring G C) →
  (∃ (τ : PropAssignment (ColorVars n)), τ |> graphColoring G) := by
  rintro ⟨C, hC⟩
  use coloringAssignment C
  simp only [graphColoring]
  constructor
  · simp only [vertexColorConstraints, eachVertexGetsAColor, satisfies_disj, satisfies_var,
    coloringAssignment, Fin.zero_eta, decide_eq_true_eq, Fin.mk_one]
    intro v
    generalize C v = Cv
    fin_cases Cv <;> simp
  · simp only [edgeConstraints, adjacentVertexesGetDifferentColors, compl_inf, satisfies_conj,
    satisfies_disj, PropFun.satisfies_neg, satisfies_var, coloringAssignment, Fin.zero_eta,
    decide_eq_true_eq, Fin.mk_one]
    intro u v huv
    have h_ne := hC huv
    generalize C u = Cu at h_ne ⊢
    generalize C v = Cv at h_ne ⊢
    fin_cases Cu <;> fin_cases Cv <;> simp at *

-- Now generate an actual CNF for a graph object
def K8 : Graph 8 := completeGraph (Fin 8)

instance : DecidableRel K8.Adj := by
  unfold DecidableRel
  intro a b
  by_cases h : Ne a b
  · exact isTrue h
  · exact isFalse h

def K8_CNF : VCnf 8 (graphColoring K8) :=
  graphColoringCNF K8

def PrintTheCNF : IO Unit :=
  let cnf := K8_CNF.val.toICnf
  Solver.Dimacs.printFormula IO.print cnf

-- In case we want to print the CNF to the Lean infoview.
-- #eval PrintTheCNF

-- We trust the SAT solver and axiomatize the UNSAT result
-- TODO: Replace `axiom` with tactic to trust/insert SAT results directly from the solver.
axiom cnfUnsat : ¬∃ τ : PropAssignment IVar, τ ⊨ K8_CNF.val.toICnf.toPropFun

theorem unsat_result : ¬∃ (C : Coloring 8 4), isValidColoring K8 C := by
  apply mt (@coloringAssignment_exists_of_validColoring 8 K8)
  rintro ⟨τ, hτ⟩
  have h_unsat := cnfUnsat
  rcases (EncCNF.encodesProp_equisatisfiable K8_CNF.val (graphColoring K8) K8_CNF.property).mp ⟨τ, hτ⟩ with ⟨σ, hσ⟩
  simp at h_unsat
  replace h_unsat := h_unsat σ
  exact absurd hσ h_unsat
