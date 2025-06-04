import tactic
import data.nat.basic
import combinatorics.simple_graph.basic
import data.fintype.card

/-
Note: adjacent_fn just says that (v1.nth i).val = (v2.nth i).val + s, rather than (v1.nth i).val = (v2.nth i).val + s ∨
(v1.nth i).val + s = (v2.nth i).val because simple_graph.from_rel symmetrizes the relation that it is given
-/
def Keller_graph (d : ℕ) (s : ℕ) : simple_graph (vector (fin (2*s)) d) :=
  let vertex : Type := vector (fin (2*s)) d in
  let adjacent_fn : vertex → vertex → Prop := 
    λ v1, λ v2, ∃ i : fin d, ∃ j : fin d,
    (v1.nth i).val = (v2.nth i).val + s ∧ v1.nth j ≠ v2.nth j ∧ i ≠ j
  in simple_graph.from_rel adjacent_fn

--Asserts that the Keller graph G_{n,s} has a clique of size m
def has_clique {d : ℕ} {s : ℕ} (G : simple_graph (vector (fin (2*s)) d)) (m : ℕ) :=
  let vertex : Type := vector (fin (2*s)) d in
  ∃ clique : finset vertex, clique.card = m ∧
  ∀ v1 : vertex, ∀ v2 : vertex, v1 ∈ clique → v2 ∈ clique → v1 ≠ v2 → G.adj v1 v2