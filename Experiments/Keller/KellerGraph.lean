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

def KClique (vs : Finset (KVertex n s)) :=
  (KGraph n s).IsNClique (2^n) vs

def conjectureIn (n : Nat) : Prop :=
  ∀ s, ¬∃ vs : Finset (KVertex n s), KClique vs





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

theorem nclique_card_le (isNClique : (KGraph n s).IsNClique size vs) :
    vs.card ≤ 2^n := by
  rw [← BitVec.card (n := n)]
  apply Finset.card_le_card_of_injOn
  · simp
  · apply KVertex.bv_injOn_clique isNClique.isClique

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


theorem KClique.exists_unique (i : BitVec n) (h : KClique (n := n) (s := s) vs)
    : ∃! a, a ∈ vs ∧ (fun v => v.bv = i) a := by
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

def KClique.get (i : BitVec n) (h : KClique (n := n) (s := s) vs)
    : Vector (Fin s) n :=
  vs.choose _ (h.exists_unique i) |>.2

theorem KClique.get_mem (i : BitVec n) (h : KClique (n := n) (s := s) vs)
    : ⟨i, h.get i⟩ ∈ vs := by
  unfold get
  generalize hv : Finset.choose (fun v => v.bv = i) vs _ = v
  have ⟨mem,prop⟩ : v ∈ vs ∧ v.bv = i := by
    rw [← hv]; apply Finset.choose_spec
  convert mem
  exact prop.symm

theorem KClique.get_eq_iff_mem (i : BitVec n) (h : KClique (n := n) (s := s) vs)
    : h.get i = k ↔ ⟨i,k⟩ ∈ vs := by
  unfold get
  generalize hv : Finset.choose (·.bv = i) vs _ = v
  have ⟨mem,rfl⟩ : v ∈ vs ∧ v.bv = i := by
    rw [hv.symm]; apply Finset.choose_spec
  clear hv
  constructor
  · rintro rfl; exact mem
  · intro mem2
    have := h.exists_unique v.bv |>.unique ⟨mem,rfl⟩ ⟨mem2,rfl⟩
    rw [this]

def KAuto (n s) := SimpleGraph.Iso (KGraph n s) (KGraph n s)

def KClique.map (a : KAuto n s) (k : KClique vs) :
      KClique (vs.map a.toEmbedding.toEmbedding) := by
  have {card_eq, isClique} := k
  simp only [KClique, SimpleGraph.isNClique_iff,
    Finset.card_map, card_eq, and_true]
  clear card_eq
  generalize hvs' : vs.map _ = vs'
  simp [Finset.ext_iff] at hvs'
  intro v₁ hv₁ v₂ hv₂ hne
  simp [← hvs'] at hv₁ hv₂; clear hvs'
  rcases hv₁ with ⟨v₁,hv₁,rfl⟩; rcases hv₂ with ⟨v₂,hv₂,rfl⟩
  apply a.map_adj_iff.mpr
  simp [SimpleGraph.isClique_iff]
  replace hne : v₁ ≠ v₂ := fun h => hne (congrArg a.toFun h)
  apply isClique ?_ ?_ hne <;> simp [hv₁, hv₂]


namespace KVertex

def flip (mask : BitVec n) (v : KVertex n s) : KVertex n s :=
  { bv := v.bv ^^^ mask, colors := v.colors }

theorem bv_flip (mask) {v : KVertex n s} : (flip mask v).bv = v.bv ^^^ mask := rfl
@[simp] theorem bv_colors (mask) {v : KVertex n s} : (flip mask v).colors = v.colors := rfl

@[simp] theorem flip_flip (mask : BitVec n) {v : KVertex n s} : (v.flip mask).flip mask = v := by
  simp [flip, BitVec.xor_assoc]


def permute (f : Fin n → Fin s → Fin s) (v : KVertex n s) : KVertex n s :=
  { bv := v.bv, colors := Vector.ofFn (fun j => (f j) v.colors[j]) }

@[simp] theorem bv_permute (f) {v : KVertex n s} : (permute f v).bv = v.bv := rfl

theorem colors_permute (f) (v : KVertex n s) {j h} :
    (permute f v).colors[j]'h = (f ⟨j,h⟩) v.colors[j] := by
  simp [permute]


theorem permute_permute (f₁ f₂ : Fin n → Fin s → Fin s) {v} :
    permute f₁ (permute f₂ v) = permute (fun j => f₁ j ∘ f₂ j) v := by
  simp [permute]

@[simp] theorem permute_id {v : KVertex n s} : permute (fun _ => id) v = v := by
  simp [permute]
  congr
  ext i hi
  simp


def reorder (f : Fin n → Fin n) (v : KVertex n s) : KVertex n s :=
  ⟨ BitVec.ofFn (v.bv[f ·])
  , Vector.ofFn (v.colors[f ·])⟩

theorem bv_reorder (f : Fin n → Fin n) (v : KVertex n s) {j hj} :
    (v.reorder f).bv[j]'hj = v.bv[f ⟨j,hj⟩] := by
  simp [reorder]

theorem colors_reorder (f : Fin n → Fin n) (v : KVertex n s) {j hj} :
    (v.reorder f).colors[j]'hj = v.colors[f ⟨j,hj⟩] := by
  simp [reorder]

theorem reorder_comp (f₁ f₂ : Fin n → Fin n) (v : KVertex n s)
    : reorder f₁ (reorder f₂ v) = reorder (f₂ ∘ f₁) v := by
  simp [reorder]

@[simp] theorem reorder_id (v : KVertex n s) : reorder id v = v := by
  ext <;> simp [reorder]

end KVertex


namespace KAuto

def id : KAuto n s := RelIso.refl _

def flip (mask : BitVec n) : KAuto n s :=
  RelIso.mk ({
    toFun := KVertex.flip mask
    invFun := KVertex.flip mask
    left_inv  := by intro; simp
    right_inv := by intro; simp
  }) (by
    simp [KAdj, KVertex.bv_flip]
  )

@[simp] theorem toFun_flip {x : KVertex _ _ } :
  DFunLike.coe (F := KAdj ≃r KAdj) (α := KVertex n s) (β := fun _ => KVertex n s)
    (flip (n := n) (s := s) mask) x = KVertex.flip mask x := rfl

def permute (f : Fin n → Fin s ≃ Fin s) : KAuto n s :=
  RelIso.mk ({
    toFun := KVertex.permute (fun j => f j)
    invFun := KVertex.permute (fun j => (f j).symm)
    left_inv  := by intro; simp [KVertex.permute_permute]
    right_inv := by intro; simp [KVertex.permute_permute]
  }) (by
    intro v₁ v₂
    simp [KAdj, KVertex.colors_permute])

@[simp] theorem toFun_permute {x : KVertex _ _ } :
  DFunLike.coe (F := KAdj ≃r KAdj) (α := KVertex n s) (β := fun _ => KVertex n s)
    (permute (n := n) (s := s) f) x = KVertex.permute (fun j => f j) x := rfl

def reorder (f : Fin n ≃ Fin n) : KAuto n s :=
  RelIso.mk {
    toFun := KVertex.reorder f
    invFun := KVertex.reorder f.invFun
    left_inv := by intro; simp [KVertex.reorder_comp]
    right_inv := by intro; simp [KVertex.reorder_comp]
  } (by
    intro a b
    simp [KAdj, KVertex.reorder]
    constructor
    · rintro ⟨j₁,hbv₁,hc1,j₂,hne,h⟩
      use f j₁, hbv₁, hc1, f j₂
      rw [EmbeddingLike.apply_eq_iff_eq]
      simp [hne, h]
    · rintro ⟨j₁,hbv₁,hc1,j₂,hne,h⟩
      use f.symm j₁; simp
      use hbv₁, hc1, f.symm j₂
      rw [EmbeddingLike.apply_eq_iff_eq]
      simp [hne, h]
  )

@[simp] theorem toFun_reorder {x : KVertex _ _ } :
  DFunLike.coe (F := KAdj ≃r KAdj) (α := KVertex n s) (β := fun _ => KVertex n s)
    (reorder (n := n) (s := s) f) x = KVertex.reorder (fun j => f j) x := rfl

def swap [DecidableEq α] (L : List (α × α)) : α ≃ α :=
  match L with
  | [] => Equiv.refl _
  | (a,b) :: tail => (swap tail).insert a b

@[simp] theorem swap_nil [DecidableEq α] : swap (α := α) [] i = i := rfl

@[simp] theorem swap_cons_of_eq_left [DecidableEq α] :
    swap (α := α) ((i,o) :: tail) i = o := by
  simp [swap]

@[simp] theorem swap_cons_of_eq_right [DecidableEq α]
      (htail : swap tail i' = o) :
    swap (α := α) ((i,o) :: tail) i' = swap tail i := by
  simp [swap, htail]; rw [Equiv.insert_right]; exact htail

@[simp] theorem swap_cons_of_ne [DecidableEq α]
      (hhead : i' ≠ i) (htail : swap tail i' ≠ o) :
    swap (α := α) ((i,o) :: tail) i' = swap tail i' := by
  simp [swap, htail]; rw [Equiv.insert_unchanged] <;> assumption

theorem swap_eq_of_mem [DecidableEq α] (L : List (α × α))
    (is_distinct : L.Pairwise (·.1 ≠ ·.1)) (os_distinct : L.Pairwise (·.2 ≠ ·.2))
    (pair_mem : (i,o) ∈ L) :
    swap L i = o := by
  induction L generalizing i o with
  | nil => simp at pair_mem
  | cons hd tl ih =>
    simp at pair_mem
    rcases pair_mem with (rfl|pair_mem)
    case inl => simp
    case inr =>
    specialize ih is_distinct.tail os_distinct.tail pair_mem
    replace is_distinct := Ne.symm <| List.rel_of_pairwise_cons is_distinct pair_mem
    replace os_distinct := Ne.symm <| List.rel_of_pairwise_cons os_distinct pair_mem
    clear pair_mem
    rcases hd with ⟨x,y⟩; dsimp at is_distinct os_distinct ⊢
    simp [swap]; rw [← ih] at os_distinct ⊢
    apply Equiv.insert_unchanged <;> assumption


end KAuto


structure SB0 (n s) where
  vs : Finset (KVertex n s)
  kclique : KClique vs

structure SB1 (n s) extends SB0 (n+2) (s+1) where
  c0 : kclique.get 0 = ⟨Array.mkArray (n+2) 0, by simp⟩
  c1 : kclique.get 1 = ⟨#[0,1] ++ Array.mkArray n 0, by simp; omega⟩

theorem SB0.pick_pair {n s} (x : SB0 (n+2) (s+1)) (h : conjectureIn (n+1))
  : ∃ (i₁ i₂ : BitVec (n+2)) (j₁ j₂ : Fin (n+2)), j₁ ≠ j₂ ∧ ∀ j (h : j < n+2),
      (j ≠ j₁ ↔ i₁[j] = i₂[j]) ∧
      (j ≠ j₂ ↔ (x.kclique.get i₁)[j] = (x.kclique.get i₂)[j])
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
  -- now we fill the goal
  use (i₁.cons false), (i₂.cons false), ⟨j₁,‹_›⟩, ⟨n+1, by omega⟩
  simp [hk₁, hk₂, js_diff]
  rintro j -
  by_cases eq_j1 : j = j₁
  · simp_all [BitVec.getElem_cons]
  · by_cases eq_last : j = n+1
    · simp_all [BitVec.getElem_cons]
    · specialize hnotadj ⟨j, by omega⟩ (by simp; exact Ne.symm eq_j1)
      simp_all [BitVec.getElem_cons]; exact hnotadj.1

def SB0.reorder (j₁ j₂ : Fin (n+2)) := KAuto.swap [(0,j₁), (1,j₂)]

@[simp] theorem SB0.reorder_0 (j1 j2 : Fin (n+2)) : reorder j1 j2 0 = j1 := by
  simp [reorder]
@[simp] theorem SB0.reorder_eq_j1 (j1 j2 : Fin (n+2)) : reorder j1 j2 j = j1 ↔ j = 0 := by
  conv => lhs; rhs; rw [← SB0.reorder_0 j1 j2]
  rw [Equiv.apply_eq_iff_eq]
@[simp] theorem SB0.reorder_1 (j1 j2 : Fin (n+2)) (h : j1 ≠ j2) : reorder j1 j2 1 = j2 := by
  simp [reorder]; rw [KAuto.swap_eq_of_mem] <;> simp [h]
@[simp] theorem SB0.reorder_eq_j2 (j1 j2 : Fin (n+2)) (h : j1 ≠ j2) : reorder j1 j2 j = j2 ↔ j = 1 := by
  conv => lhs; rhs; rw [← SB0.reorder_1 j1 j2 h]
  rw [Equiv.apply_eq_iff_eq]

/-- The automorphism which moves v₁ to ⟨0,[0*]⟩ and v₂ to ⟨1,[0,1,0*]⟩ -/
def SB0.auto {n s} (v₁ v₂ : KVertex (n+2) (s+2)) : KAuto (n+2) (s+2) :=
  (KAuto.flip v₁.bv)
  |>.trans (KAuto.permute fun j =>
    if j = 1 then
      KAuto.swap [(v₁.colors[j], 0), (v₂.colors[j], 1)]
    else
      KAuto.swap [(v₁.colors[j], 0)]
  )

theorem SB0.auto_v₁ {v₁ v₂ : KVertex (n+2) (s+2)} :
      (SB0.auto v₁ v₂).toFun v₁ = ⟨0, Vector.mkVector _ 0⟩ := by
  ext j hj
  · unfold auto; simp [KVertex.bv_flip]
  · unfold auto; simp [KVertex.colors_permute, Vector.mkVector]
    if hj : j = 1 then
      simp [hj]
    else
      simp [← Fin.val_eq_val, hj]

theorem SB0.auto_v₂ {v₁ v₂ : KVertex (n+2) (s+2)}
      (h : ∀ j (h : j < n+2),
          (j ≠ 0 ↔ v₁.bv[j] = v₂.bv[j]) ∧
          (j ≠ 1 ↔ v₁.colors[j] = v₂.colors[j])) :
      (SB0.auto v₁ v₂).toFun v₂ = ⟨1, ⟨#[0,1] ++ Array.mkArray n 0, by simp; omega⟩⟩ := by
  ext j hj <;> specialize h j hj
  · replace h := h.1
    unfold auto; simp [KVertex.bv_flip]
    by_cases j = 0 <;> aesop
  · replace h := h.2
    unfold auto; simp [KVertex.colors_permute, Vector.mkVector]
    if hj : j = 1 then
      simp [hj, Array.getElem_append]
      simp [hj] at h
      rw [KAuto.swap_eq_of_mem]
      case is_distinct => simp [h]
      case os_distinct => simp
      case pair_mem => simp; right; rfl
      rfl
    else
      simp [hj] at h
      simp [← Fin.val_eq_val, hj, h, Array.getElem_append]
      split
      · have : j = 0 := by omega
        simp [this]
      · rfl

theorem SB0.to_SB1 {n s} (k : SB0 (n+2) (s+2)) (h : conjectureIn (n+1))
  : Nonempty (SB1 n (s+1)) := by
  have ⟨ai, bi, j₁, j₂, hne, same_on⟩ := k.pick_pair h
  -- clean up the context a *bunch*
  -- TODO(JG): just change pick_pair to be in the form I actually want it in
  clear h; rcases k with ⟨vs,k⟩
  generalize a_mem_vs : k.get ai = a_cs at same_on
  generalize b_mem_vs : k.get bi = b_cs at same_on
  rw [KClique.get_eq_iff_mem] at a_mem_vs b_mem_vs
  generalize ha : KVertex.mk ai a_cs = a at a_mem_vs
  generalize hb : KVertex.mk bi b_cs = b at b_mem_vs
  simp [KVertex.ext_iff] at ha hb
  rcases ha with ⟨rfl,rfl⟩; rcases hb with ⟨rfl,rfl⟩
  -- okay, context is now pretty reasonable
  -- apply the reordering automorphism to get vs2, k2, a2, b2
  have k2 := k.map (KAuto.reorder <| SB0.reorder j₁ j₂)
  generalize hvs2 : vs.map _ = vs2 at k2
  let a2 := (KAuto.reorder (reorder j₁ j₂)).toFun a
  let b2 := (KAuto.reorder (reorder j₁ j₂)).toFun b
  -- apply the "move to all 0s" automorphism to get vs3, k3
  have k3 := k2.map (SB0.auto a2 b2)
  generalize hvs3 : vs2.map _ = vs3 at k3

  -- k3 is the clique we want! just have to prove 0 ↦ 0*, 1 ↦ 0,1,0*
  refine ⟨{vs := vs3, kclique := k3, c0 := ?c0, c1 := ?c1}⟩
  case c0 =>
    rw [KClique.get_eq_iff_mem]; simp [← hvs3]
    use a2
    constructor
    · rw [← hvs2]; apply Finset.mem_map_of_mem; exact a_mem_vs
    · apply SB0.auto_v₁
  case c1 =>
    rw [KClique.get_eq_iff_mem]; simp [← hvs3]
    use b2
    constructor
    · rw [← hvs2]; apply Finset.mem_map_of_mem; exact b_mem_vs
    · apply SB0.auto_v₂
      intro j hj
      simp [a2, b2, KVertex.bv_reorder, KVertex.colors_reorder]
      constructor
      · rw [← (same_on _ _).1, not_iff_not, Fin.val_eq_val,
          SB0.reorder_eq_j1, ← Fin.val_eq_val]
        rfl
      · rw [← (same_on _ _).2, not_iff_not, Fin.val_eq_val,
          SB0.reorder_eq_j2 _ _ hne, ← Fin.val_eq_val]
        rfl



structure KellerCliqueData (n s : Nat) where
  vertices : Vector (Vector (Fin s) n) (2^n)
deriving Repr

def KellerCliqueData.get (i : BitVec n) (kc : KellerCliqueData n s): KVertex n s :=
  { bv := i, colors := kc.vertices[i.toFin] }

instance : ToString (KellerCliqueData n s) where
  toString := fun kc => toString <| kc.vertices.toArray.map (·.toArray)


def checkAll (kc : KellerCliqueData n s) : Bool :=
  decide (∀ i i' : Fin (2^n), i < i' → KAdj (kc.get i) (kc.get i'))
