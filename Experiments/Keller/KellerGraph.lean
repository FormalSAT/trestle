import Experiments.Keller.Upstream

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique

structure KellerVertex (n s : Nat) where
  bv : BitVec n
  colors : Vector (Fin s) n
deriving Repr, DecidableEq

nonrec def KellerVertex.toString (v : KellerVertex n s) : String :=
  s!"{v.bv};{v.colors.toList}"

instance : ToString (KellerVertex n s) where
  toString := KellerVertex.toString

def KellerAdj (v₁ v₂ : KellerVertex n s) : Prop :=
  ∃ (j₁ : Fin n),
      v₁.bv[j₁] ≠ v₂.bv[j₁] ∧ v₁.colors[j₁] = v₂.colors[j₁] ∧
    ∃ j₂, j₁ ≠ j₂ ∧
      (v₁.bv[j₂] ≠ v₂.bv[j₂] ∨ v₁.colors[j₂] ≠ v₂.colors[j₂])

instance : DecidableRel (KellerAdj (n := n) (s := s)) :=
  fun v₁ v₂ => by unfold KellerAdj; infer_instance

theorem KellerAdj.symm : Symmetric (KellerAdj (n := n) (s := s)) := by
  intro x y h
  unfold KellerAdj at h ⊢
  rcases h with ⟨j₁,hb1,hc1,j₂,hj,h2⟩
  refine ⟨j₁,hb1.symm,hc1.symm,j₂,hj,?_⟩
  aesop

theorem KellerAdj.irrefl : Irreflexive (KellerAdj (n := n) (s := s)) := by
  intro x; unfold KellerAdj; simp

def KellerGraph (n s) : SimpleGraph (KellerVertex n s) where
  Adj := KellerAdj
  symm := KellerAdj.symm
  loopless := KellerAdj.irrefl

theorem sameBV_not_adj (v₁ v₂ : KellerVertex n s)
  : v₁.bv = v₂.bv → ¬ KellerAdj v₁ v₂ := by
  intro h
  unfold KellerAdj; simp [h]

theorem sameBV_ind_set (i : BitVec n) :
  (KellerGraph n s)ᶜ.IsClique (fun v => v.bv = i) := by
  rw [SimpleGraph.isClique_iff]
  intro v1 h1 v2 h2 hne
  rw [SimpleGraph.compl_adj]
  refine ⟨hne,?_⟩
  apply sameBV_not_adj
  rw [h1,h2]

theorem maxClique_le : (KellerGraph n s).cliqueNum ≤ 2^n := by
  unfold SimpleGraph.cliqueNum
  generalize hsizes : setOf _ = sizes
  by_contra h
  simp [] at h
  have : ∃ size ∈ sizes, size > 2^n := by
    clear hsizes
    exact exists_lt_of_lt_csSup' h
  clear h
  simp [← hsizes] at this; clear hsizes
  rcases this with ⟨size,⟨clique,⟨hclique,rfl⟩⟩,h⟩
  have := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := clique) (t := Finset.univ (α := Fin (2^n)))
    (f := fun v => v.bv.toFin)
  simp [h, BitVec.toFin_inj] at this; clear h
  rcases this with ⟨x, hx, y, hy, hne, h⟩
  apply sameBV_not_adj x y h
  apply hclique hx hy hne


structure KellerCliqueData (n s : Nat) where
  vertices : Vector (Vector (Fin s) n) (2^n)
deriving Repr

def KellerCliqueData.get (i : BitVec n) (kc : KellerCliqueData n s): KellerVertex n s :=
  { bv := i, colors := kc.vertices[i.toFin] }

instance : ToString (KellerCliqueData n s) where
  toString := fun kc => toString <| kc.vertices.toArray.map (·.toArray)


def checkAll (kc : KellerCliqueData n s) : Bool :=
  decide (∀ i i' : Fin (2^n), i < i' → KellerAdj (kc.get i) (kc.get i'))
