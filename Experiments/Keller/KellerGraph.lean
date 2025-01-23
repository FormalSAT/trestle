import Experiments.Keller.Upstream

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique

@[ext]
structure KellerVertex (n s : Nat) where
  bv : BitVec n
  colors : Vector (Fin s) n
deriving Repr, DecidableEq

namespace KellerVertex

nonrec def toString (v : KellerVertex n s) : String :=
  s!"{v.bv};{v.colors.toList}"

instance : ToString (KellerVertex n s) where
  toString := KellerVertex.toString

def flip (j : Fin n) (v : KellerVertex n s) : KellerVertex n s :=
  { bv := v.bv ^^^ BitVec.shiftLeft 1 j, colors := v.colors }

@[simp] theorem colors_flip {j} {v : KellerVertex n s} : (flip j v).colors = v.colors := rfl
@[simp] theorem bv_flip_eq {j} {v : KellerVertex (n+1) s} : (flip j v).bv[(↑j : Nat)] = !v.bv[j] := by
  simp [flip]
@[simp] theorem bv_flip_ne {j j'} {v : KellerVertex (n+1) s} (h : j ≠ j') :
    (flip j v).bv[↑(j' : Nat)] = v.bv[j'] := by
  simp [flip]
  by_cases j' < j <;> simp [*]
  by_cases (↑j' : Nat) - ↑j = 0
  · omega
  · simp [*]

@[simp] def flip_flip (j : Fin n) {v : KellerVertex n s} : (v.flip j).flip j = v := by
  simp [flip, BitVec.xor_assoc]

def permute (j : Fin n) (f : Fin s → Fin s) (v : KellerVertex n s) : KellerVertex n s :=
  { bv := v.bv, colors := Vector.ofFn (fun j' => if j = j' then f v.colors[j'] else v.colors[j']) }

@[simp] theorem bv_permute {j f} {v : KellerVertex n s} : bv (permute j f v) = v.bv := rfl
@[simp] theorem colors_permute_eq {j f} {v : KellerVertex n s} {hj} :
    (permute j f v).colors[(j : Nat)]'hj = f v.colors[j] := by
  simp [permute, Vector.ofFn, getElem]; simp [Vector.get]
@[simp] theorem colors_permute_ne {j j' f} {v : KellerVertex n s} {hj'} (h : j ≠ j') :
    (permute j f v).colors[(j' : Nat)]'hj' = v.colors[j'] := by
  simp [permute, Vector.ofFn, getElem]; simp [Vector.get, h]

@[simp] def permute_id (j : Fin n) {v : KellerVertex n s} : permute j id v = v := by
  simp [permute]
  congr
  ext i hi
  simp

@[simp] def permute_comp (j : Fin n) (f₁ f₂ : Fin s → Fin s) {v} :
    (permute j f₁ v).permute j f₂ = permute j (f₂ ∘ f₁) v := by
  simp [permute]
  ext i hi; simp
  split <;> simp

end KellerVertex

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

@[simp] theorem KellerGraph.Adj : (KellerGraph n s).Adj = KellerAdj := rfl

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


def KellerAuto (n s) := SimpleGraph.Iso (KellerGraph n s) (KellerGraph n s)

def KellerAuto.flip (j : Fin (n+1)) : KellerAuto (n+1) s :=
  RelIso.mk ({
    toFun := KellerVertex.flip j
    invFun := KellerVertex.flip j
    left_inv := by apply KellerVertex.flip_flip
    right_inv := by apply KellerVertex.flip_flip
  }) (by
    intro v₁ v₂
    simp [KellerAdj]
    constructor
    · rintro ⟨j₁,hb1,hc1,j₂,hne,h2⟩
      replace hb1 : v₁.bv[j₁] ≠ v₂.bv[j₁] := by
        by_cases hj1 : j = j₁ <;> (simp [hj1] at hb1; exact hb1)
      use j₁, hb1, hc1, j₂, hne
      cases h2
      case inr => simp [*]
      case inl h2 =>
      left
      by_cases hj2 : j = j₂ <;> (simp [hj2] at h2; exact h2)
    · rintro ⟨j₁,hb1,hc1,j₂,hne,h2⟩
      use j₁
      constructor
      · by_cases hj1 : j = j₁ <;> (simp [hj1, hb1])
      use hc1, j₂, hne
      cases h2
      case inr => simp [*]
      case inl h2 =>
      left
      by_cases hj2 : j = j₂ <;> (simp [hj2]; exact h2)
    )

def KellerAuto.permute (j : Fin (n+1)) (f : Fin s ≃ Fin s) : KellerAuto (n+1) s :=
  RelIso.mk ({
    toFun := KellerVertex.permute j f
    invFun := KellerVertex.permute j f.symm
    left_inv := by intro; simp
    right_inv := by intro; simp
  }
  ) (by
    intro v₁ v₂
    simp [KellerAdj]
    constructor
    · rintro ⟨j₁,hb1,hc1,j₂,hne,h2⟩
      replace hc1 : v₁.colors[j₁] = v₂.colors[j₁] := by
        by_cases hj1 : j = j₁ <;> simpa [hj1] using hc1
      use j₁, hb1, hc1, j₂, hne
      cases h2
      case inl => simp [*]
      case inr h2 =>
      right
      by_cases hj2 : j = j₂ <;> (simp [hj2] at h2; exact h2)
    · rintro ⟨j₁,hb1,hc1,j₂,hne,h2⟩
      use j₁
      refine ⟨?_,?_,?_⟩
      · assumption
      · by_cases hj1 : j = j₁ <;> (simp [hj1, hc1])
      use j₂, hne
      cases h2
      case inl => simp [*]
      case inr h2 =>
      right
      by_cases hj2 : j = j₂ <;> (simp [hj2]; exact h2)
  )


structure KellerCliqueData (n s : Nat) where
  vertices : Vector (Vector (Fin s) n) (2^n)
deriving Repr

def KellerCliqueData.get (i : BitVec n) (kc : KellerCliqueData n s): KellerVertex n s :=
  { bv := i, colors := kc.vertices[i.toFin] }

instance : ToString (KellerCliqueData n s) where
  toString := fun kc => toString <| kc.vertices.toArray.map (·.toArray)


def checkAll (kc : KellerCliqueData n s) : Bool :=
  decide (∀ i i' : Fin (2^n), i < i' → KellerAdj (kc.get i) (kc.get i'))
