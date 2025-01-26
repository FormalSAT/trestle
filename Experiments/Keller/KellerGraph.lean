import Experiments.Keller.Upstream

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique

namespace Keller

@[ext]
structure KVertex (n s : Nat) where
  bv : BitVec n
  colors : Vector (Fin s) n
deriving Repr, DecidableEq

namespace KVertex

nonrec def toString (v : KVertex n s) : String :=
  s!"{v.bv};{v.colors.toList}"

instance : ToString (KVertex n s) where
  toString := KVertex.toString

def flip (j : Fin n) (v : KVertex n s) : KVertex n s :=
  { bv := v.bv ^^^ BitVec.shiftLeft 1 j, colors := v.colors }

@[simp] theorem colors_flip {j} {v : KVertex n s} : (flip j v).colors = v.colors := rfl
@[simp] theorem bv_flip_eq {j} {v : KVertex (n+1) s} : (flip j v).bv[(↑j : Nat)] = !v.bv[j] := by
  simp [flip]
@[simp] theorem bv_flip_ne {j j'} {v : KVertex (n+1) s} (h : j ≠ j') :
    (flip j v).bv[↑(j' : Nat)] = v.bv[j'] := by
  simp [flip]
  by_cases j' < j <;> simp [*]
  by_cases (↑j' : Nat) - ↑j = 0
  · omega
  · simp [*]

@[simp] theorem flip_flip (j : Fin n) {v : KVertex n s} : (v.flip j).flip j = v := by
  simp [flip, BitVec.xor_assoc]

theorem flip_comm (j₁ j₂ : Fin n) {v : KVertex n s} : (v.flip j₂).flip j₁ = (v.flip j₁).flip j₂ := by
  simp [flip]; rw [BitVec.xor_assoc]
  conv => enter [1,2]; rw [BitVec.xor_comm]
  rw [BitVec.xor_assoc]

def permute (j : Fin n) (f : Fin s → Fin s) (v : KVertex n s) : KVertex n s :=
  { bv := v.bv, colors := Vector.ofFn (fun j' => if j = j' then f v.colors[j'] else v.colors[j']) }

@[simp] theorem bv_permute {j f} {v : KVertex n s} : bv (permute j f v) = v.bv := rfl
@[simp] theorem colors_permute_eq {j f} {v : KVertex n s} {hj} :
    (permute j f v).colors[(j : Nat)]'hj = f v.colors[j] := by
  simp [permute, Vector.ofFn, getElem]; simp [Vector.get]
@[simp] theorem colors_permute_ne {j j' f} {v : KVertex n s} {hj'} (h : j ≠ j') :
    (permute j f v).colors[(j' : Nat)]'hj' = v.colors[j'] := by
  simp [permute, Vector.ofFn, getElem]; simp [Vector.get, h]

@[simp] theorem permute_id (j : Fin n) {v : KVertex n s} : permute j id v = v := by
  simp [permute]
  congr
  ext i hi
  simp

@[simp] theorem permute_comp (j : Fin n) (f₁ f₂ : Fin s → Fin s) {v} :
    (permute j f₁ v).permute j f₂ = permute j (f₂ ∘ f₁) v := by
  simp [permute]
  ext i hi; simp
  split <;> simp

theorem permute_commute (j₁ j₂ : Fin n) (f₁ f₂ : Fin s → Fin s) {v} :
    j₁ ≠ j₂ → (permute j₁ f₁ (permute j₂ f₂ v)) = permute j₂ f₂ (permute j₁ f₁ v) := by
  intro hne
  simp [permute]
  ext i hi; simp
  split <;> split <;> simp_all

end KVertex

def KAdj (v₁ v₂ : KVertex n s) : Prop :=
  ∃ (j₁ : Fin n),
      v₁.bv[j₁] ≠ v₂.bv[j₁] ∧ v₁.colors[j₁] = v₂.colors[j₁] ∧
    ∃ j₂, j₁ ≠ j₂ ∧
      (v₁.bv[j₂] ≠ v₂.bv[j₂] ∨ v₁.colors[j₂] ≠ v₂.colors[j₂])

instance : DecidableRel (KAdj (n := n) (s := s)) :=
  fun v₁ v₂ => by unfold KAdj; infer_instance

theorem KAdj.symm : Symmetric (KAdj (n := n) (s := s)) := by
  intro x y h
  unfold KAdj at h ⊢
  rcases h with ⟨j₁,hb1,hc1,j₂,hj,h2⟩
  refine ⟨j₁,hb1.symm,hc1.symm,j₂,hj,?_⟩
  aesop

theorem KAdj.irrefl : Irreflexive (KAdj (n := n) (s := s)) := by
  intro x; unfold KAdj; simp

def KGraph (n s) : SimpleGraph (KVertex n s) where
  Adj := KAdj
  symm := KAdj.symm
  loopless := KAdj.irrefl

@[simp] theorem KGraph.Adj : (KGraph n s).Adj = KAdj := rfl

theorem sameBV_not_adj (v₁ v₂ : KVertex n s)
  : v₁.bv = v₂.bv → ¬ KAdj v₁ v₂ := by
  intro h
  unfold KAdj; simp [h]

theorem KVertex.bv_injOn_clique (isClique : (KGraph n s).IsClique vs) :
    vs.InjOn KVertex.bv := by
  intro v₁ hv₁ v₂ hv₂ h
  by_contra hne
  have := sameBV_not_adj v₁ v₂ h
  have := isClique hv₁ hv₂ hne
  contradiction

theorem clique_finite (isClique : (KGraph n s).IsClique vs) :
    vs.Finite := by
  apply Set.Finite.of_finite_image (f := KVertex.bv)
  · exact Set.toFinite (KVertex.bv '' vs)
  · apply KVertex.bv_injOn_clique
    exact isClique

theorem clique_to_nclique (isClique : (KGraph n s).IsClique vs) :
  ∃ (size : Nat) (vs' : Finset _) (_eq : vs ≃ vs'),
      (KGraph n s).IsNClique size vs' := by
  have := clique_finite isClique
  use this.toFinset.card, this.toFinset, this.subtypeEquivToFinset
  rw [SimpleGraph.isNClique_iff]; simp [isClique]

theorem nclique_card_le (isNClique : (KGraph n s).IsNClique size vs) :
    vs.card ≤ 2^n := by
  rw [← BitVec.card (n := n)]
  apply Finset.card_le_card_of_injOn
  · simp
  · apply KVertex.bv_injOn_clique isNClique.isClique

theorem sameBV_ind_set (i : BitVec n) :
  (KGraph n s)ᶜ.IsClique (fun v => v.bv = i) := by
  rw [SimpleGraph.isClique_iff]
  intro v1 h1 v2 h2 hne
  rw [SimpleGraph.compl_adj]
  refine ⟨hne,?_⟩
  apply sameBV_not_adj
  rw [h1,h2]

theorem maxClique_le : (KGraph n s).cliqueNum ≤ 2^n := by
  unfold SimpleGraph.cliqueNum
  generalize hsizes : setOf _ = sizes
  by_contra h
  simp at h
  have : ∃ size ∈ sizes, size > 2^n := by
    clear hsizes
    exact exists_lt_of_lt_csSup' h
  clear h
  simp [← hsizes] at this; clear hsizes
  rcases this with ⟨size,⟨clique,isNclique⟩,h⟩
  have := nclique_card_le isNclique
  have := isNclique.card_eq
  omega


def KClique (vs : Finset (KVertex n s)) :=
  (KGraph n s).IsNClique (2^n) vs

def KClique.get (i : BitVec n) (h : KClique (n := n) (s := s) vs)
    : Vector (Fin s) n :=
  vs.choose (fun v => v.bv = i) (by
    apply existsUnique_of_exists_of_unique
    · have := Finset.surj_on_of_inj_on_of_card_le
        (s := vs) (t := Finset.univ) (f := fun a _ => a.bv)
        (hf := by simp)
        (hinj := fun _ _ c d => KVertex.bv_injOn_clique h.isClique c d)
        (hst := by simp [h.card_eq])
        i (by simp)
      rcases this with ⟨v,hv,rfl⟩
      use v, hv
    · rintro x1 x2 ⟨h1,rfl⟩ ⟨h2,hbv⟩
      apply KVertex.bv_injOn_clique h.isClique h1 h2 hbv.symm
  ) |>.2

theorem KClique.get_mem (i : BitVec n) (h : KClique (n := n) (s := s) vs)
    : ⟨i, h.get i⟩ ∈ vs := by
  unfold get
  generalize hv : Finset.choose (fun v => v.bv = i) vs _ = v
  have ⟨mem,prop⟩ : v ∈ vs ∧ v.bv = i := by
    rw [← hv]; apply Finset.choose_spec
  convert mem
  exact prop.symm


def conjectureIn (n : Nat) : Prop :=
  ∀ s, ¬∃ vs : Finset (KVertex n s), KClique vs



def KAuto (n s) := SimpleGraph.Iso (KGraph n s) (KGraph n s)

def KAuto.flip (j : Fin (n+1)) : KAuto (n+1) s :=
  RelIso.mk ({
    toFun := KVertex.flip j
    invFun := KVertex.flip j
    left_inv := by apply KVertex.flip_flip
    right_inv := by apply KVertex.flip_flip
  }) (by
    intro v₁ v₂
    simp [KAdj]
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

def KAuto.permute (j : Fin (n+1)) (f : Fin s ≃ Fin s) : KAuto (n+1) s :=
  RelIso.mk ({
    toFun := KVertex.permute j f
    invFun := KVertex.permute j f.symm
    left_inv := by intro; simp
    right_inv := by intro; simp
  }
  ) (by
    intro v₁ v₂
    simp [KAdj]
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

structure SB0 (n s) where
  vs : Finset (KVertex n s)
  kclique : KClique vs

structure SB1 (n s) extends SB0 (n+2) (s+1) where
  c0 : kclique.get 0 = ⟨#[0,0] ++ Array.mkArray n 0, by simp; omega⟩
  c1 : kclique.get 1 = ⟨#[0,1] ++ Array.mkArray n 0, by simp; omega⟩

theorem SB0.pick_pair {n s} (x : SB0 (n+2) (s+1)) (h : conjectureIn (n+1))
  : ∃ i₁ i₂ j₁ j₂, j₁ ≠ j₂ ∧ ∀ j (h : j < n+2),
      (j ≠ j₁ → i₁[j] = i₂[j]) ∧
      (j ≠ j₂ → (x.kclique.get i₁)[j] = (x.kclique.get i₂)[j])
  := by
  let K_0 : Finset (KVertex (n+1) (s+1)) := (Finset.univ (α := BitVec (n+1)))
    |>.map ⟨fun i =>
        let i' := i.cons false
        let v := x.kclique.get i'
        ⟨i, v.take (n+1) |>.cast (by omega)⟩
      , by
        intro x1 x2 heq
        simp at heq; exact heq.1⟩
  have K_0_card : K_0.card = (2^(n+1)) := by simp [K_0]
  have K_0_not_clique := not_exists.mp (h (s+1)) K_0
  -- find the vertices in K_0 which are the not adjacent
  simp [KClique, SimpleGraph.isNClique_iff, K_0_card,
      SimpleGraph.isClique_iff, Set.Pairwise] at K_0_not_clique
  clear K_0_card h
  rcases K_0_not_clique with ⟨⟨i₁,c₁⟩, hv₁, ⟨i₂,c₂⟩, hv₂, hne, hnotadj⟩
  simp [K_0] at hv₁ hv₂; clear K_0
  -- the indices in smaller graph must be diff
  have i_diff : i₁ ≠ i₂ := by
    intro contra; subst hv₁ hv₂; simp [contra] at hne
  clear hne
  -- name the corresponding colors in bigger graph
  generalize hk₁ : KClique.get _ _ = k₁ at hv₁
  generalize hk₂ : KClique.get _ _ = k₂ at hv₂
  subst hv₁ hv₂
  -- the corresponding vertices are adjacent in big graph
  have : KAdj ⟨i₁.cons false, k₁⟩ ⟨i₂.cons false,k₂⟩ := by
    subst hk₁ hk₂
    apply x.kclique.isClique
    iterate 2 (apply KClique.get_mem)
    simp [i_diff]
  simp [KAdj] at this hnotadj
  rcases this with ⟨⟨j₁,hj₁⟩,is_have_diff,ks_same,⟨j₂,hj₂⟩,js_diff,h⟩
  simp_all
  -- the i's are different at index j₁
  have : j₁ ≠ n+1 := by intro contra; simp [BitVec.getElem_cons, contra] at is_have_diff
  simp [BitVec.getElem_cons, this] at is_have_diff
  replace hj₁ : j₁ < n+1 := by omega
  clear this
  specialize hnotadj ⟨j₁, hj₁⟩ is_have_diff ks_same
  -- j₂ must be n+1
  by_cases this : j₂ = n+1
  case neg =>
    exfalso
    replace hj₂ : j₂ < n+1 := by omega
    specialize hnotadj ⟨j₂,hj₂⟩
    simp [js_diff] at hnotadj
    simp [BitVec.getElem_cons, Nat.ne_of_lt hj₂, hnotadj.2] at h
    apply h hnotadj.1
  subst this
  simp [BitVec.getElem_cons] at h
  use (i₁.cons false), (i₂.cons false), j₁, (n+1)
  simp [hk₁, hk₂, js_diff]
  intro j hj
  constructor
  · intro hne
    simp [BitVec.getElem_cons]
    by_cases not_last : j = n+1
    case pos => simp [not_last]
    case neg =>
      specialize hnotadj ⟨j, by omega⟩ (by simp; exact Ne.symm hne)
      simpa [not_last] using hnotadj.1
  · rintro not_last
    if hne: j = j₁ then
      subst_vars; exact ks_same
    else
      exact (hnotadj ⟨j, by omega⟩ (by simp; exact Ne.symm hne)).2

theorem SB0.to_SB1 {n s} (x : SB0 (n+2) (s+1)) (h : conjectureIn (n+1))
  : Nonempty (SB1 n s) := by
  have ⟨i₁, i₂, j₁, j₂, hne, same_on⟩ := SB0.pick_pair x h
  clear h
  refine ⟨{vs:=?vs,kclique:=?kclique,c0:=?c0,c1:=?c1}⟩
  stop _


structure KellerCliqueData (n s : Nat) where
  vertices : Vector (Vector (Fin s) n) (2^n)
deriving Repr

def KellerCliqueData.get (i : BitVec n) (kc : KellerCliqueData n s): KVertex n s :=
  { bv := i, colors := kc.vertices[i.toFin] }

instance : ToString (KellerCliqueData n s) where
  toString := fun kc => toString <| kc.vertices.toArray.map (·.toArray)


def checkAll (kc : KellerCliqueData n s) : Bool :=
  decide (∀ i i' : Fin (2^n), i < i' → KAdj (kc.get i) (kc.get i'))
