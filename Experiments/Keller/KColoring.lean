import Mathlib.Tactic.Use
import Mathlib.Tactic.Abel
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.WLOG

import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Fin.Basic

import Experiments.Keller.Upstream

namespace Keller

/-! ##### BitVec utilities -/

def bvhd (b : BitVec (n+1)) : Bool := b[n]
def bvtl (b : BitVec (n+1)) : BitVec n := b.extractLsb' 0 n

theorem bvhd_cons (b) (v : BitVec n) : bvhd (v.cons b) = b := by
  unfold bvhd
  simp [BitVec.getElem_cons]

theorem bvtl_cons (b) (v : BitVec n) : bvtl (v.cons b) = v := by
  unfold bvtl
  ext i hi
  simp [BitVec.getLsbD_cons, hi, Nat.ne_of_lt]

theorem cons_hdtl (v : BitVec (n+1)) : BitVec.cons (bvhd v) (bvtl v) = v := by
  ext i hi
  if eq : i = n then
    simp [BitVec.getElem_cons, eq, bvhd]
  else
    simp [BitVec.getElem_cons, eq, bvtl, hi]

@[simp] abbrev adjacentAt (i j : BitVec n) (d : Fin n) : Prop :=
  i[d] ≠ j[d] ∧ ∀ d' ≠ d, i[d'] = j[d']

theorem adjacentAt_iff_xor_eq_oneAt :
    adjacentAt i j d ↔ i ^^^ j = .oneAt d := by
  constructor
  · rintro ⟨ne,eq⟩
    ext d' d'_range
    specialize eq ⟨d',d'_range⟩
    by_cases d' = d <;> simp_all [Fin.ext_iff, eq_comm (a := d')]
  · intro h
    constructor
    · replace is_xor := congrArg (·[d]) h
      simpa using is_xor
    · intro d' d'_ne
      replace is_xor := congrArg (·[d']) h
      rw [ne_eq, eq_comm, Fin.ext_iff] at d'_ne
      simpa [d'_ne] using is_xor

theorem adjacentAt_symm : adjacentAt i j d ↔ adjacentAt j i d := by
  aesop

def adjacent (i j : BitVec n) : Prop :=
  ∃ d : Fin n, adjacentAt i j d

instance : Decidable (adjacent i j) := by
  unfold adjacent adjacentAt
  infer_instance

theorem adjacent_symm : adjacent i j ↔ adjacent j i := by
  unfold adjacent; simp_rw [adjacentAt_symm]

theorem ne_of_adjacent (h : adjacent (n := n) i j) : i ≠ j := by
  rintro rfl; simp [adjacent] at h

theorem adjacent_xor_oneAt (i : BitVec n) (d : Fin n) : adjacent i (i ^^^ BitVec.oneAt d) := by
  use d; simp +contextual [@eq_comm _ _ d, Fin.ext_iff]

theorem adjacent_iff_xors_adjacent (i₁ i₂ mask : BitVec n) :
    adjacent i₁ i₂ ↔ adjacent (i₁ ^^^ mask) (i₂ ^^^ mask) := by
  unfold adjacent; simp

theorem adjacent_cons {i j : BitVec n} (b) (adj : adjacent i j) : adjacent (i.cons b) (j.cons b) := by
  obtain ⟨d,ne,eq⟩ := adj
  use d.castSucc
  constructor
  · simpa [BitVec.cons, BitVec.getElem_append] using ne
  · rintro ⟨d',d'lt⟩ d'_ne
    if d' = n then
      subst d'; simp [BitVec.cons, BitVec.getElem_append]
    else
      replace d'lt: d' < n := by omega
      specialize eq ⟨d',d'lt⟩ (by simpa [Fin.ext_iff] using d'_ne)
      simpa [d'lt, BitVec.cons, BitVec.getElem_append] using eq

theorem adjacent_bvhd_eq {i j : BitVec (n+1)} (adj : adjacent i j)
    (h : bvhd i = bvhd j) : adjacent (bvtl i) (bvtl j) := by
  rcases adj with ⟨⟨d,hd⟩,is_ne,cs_eq⟩
  have : d ≠ n := by rintro rfl; apply is_ne; simpa [bvhd] using h
  use ⟨d,by omega⟩
  constructor
  · simpa [bvtl] using is_ne
  · intro d' d'_ne
    simpa [bvtl] using cs_eq d'.castSucc
                        (by simpa [Fin.ext_iff] using d'_ne)

theorem adjacent_bvhd_ne {i j : BitVec (n+1)} (adj : adjacent i j)
    (h : bvhd i ≠ bvhd j) : (bvtl i) = (bvtl j) := by
  simp [bvhd] at h
  rcases adj with ⟨⟨d,hd⟩,-,cs_eq⟩
  have : n = d := by
    simpa [Fin.ext_iff, h] using cs_eq (Fin.last n)
  subst d
  ext d hd
  simpa [bvtl] using cs_eq ⟨d,by omega⟩ (by simp [Nat.ne_of_lt hd])


/-! #### Keller Colorings -/

@[ext]
structure KColoring (n s : Nat) where
  data : BitVec n → Vector (Fin s) n
  same : ∀ i j : BitVec n, i ≠ j → ∃ d : Fin n,
    i[d] ≠ j[d] ∧ (data i)[d] = (data j)[d]
  diff : ∀ i j : BitVec n, adjacent i j → ∃ d : Fin n,
    (data i)[d] ≠ (data j)[d]


namespace KColoring

theorem oneAt_eq (K : KColoring n s) (i : BitVec n) (d : Fin n) :
    (K.data (i ^^^ .oneAt d))[d] = (K.data i)[d] := by
  obtain ⟨ds,h⟩ := K.same i (i ^^^ .oneAt d) (by
    apply ne_of_adjacent
    apply adjacent_xor_oneAt)
  rw [ne_eq, eq_comm] at h
  simp_all

theorem same_adjAt (K : KColoring n s) (adj : adjacentAt i j d) :
    (K.data i)[d] = (K.data j)[d] := by
  obtain ⟨d', hd'⟩ := K.same i j (ne_of_adjacent ⟨d,adj⟩)
  if d' = d then
    subst d'; exact hd'.2
  else
    exfalso
    apply hd'.1 <| adj.2 d' ‹_›

theorem diff_adjAt (K : KColoring n s) (i j : BitVec n) (adj : adjacentAt i j d) :
    ∃ d2 : Fin n, d2 ≠ d ∧ (K.data i)[d2] ≠ (K.data j)[d2] := by
  obtain ⟨d2,cs_ne⟩ := K.diff i j ⟨d,adj⟩
  have : d2 ≠ d := by
    rintro rfl; apply cs_ne; apply same_adjAt K adj
  use d2, this, cs_ne

private theorem bv_oneBit_fixed_card (j : Fin (n+1)) :
    (Finset.univ |>.filter (α := BitVec (n+1)) (·[j])).card = 2^n := by
  let trues := Finset.filter (α := BitVec (n+1)) (fun x => x[j] = true) Finset.univ
  let falses := Finset.filter (α := BitVec (n+1)) (fun x => x[j] = false) Finset.univ
  refold_let trues

  have : trues.card = falses.card := by
    apply Finset.card_bijective (e := (· ^^^ .oneAt j))
    case he =>
      apply Function.Involutive.bijective
      intro x; simp [BitVec.xor_assoc]
    case hst =>
      simp +zetaDelta

  have : trues.card + falses.card = 2^(n+1) := by
    have disj : Disjoint trues falses := by
      rw [Finset.disjoint_iff_ne]; intro a a_mem b b_mem
      simp +zetaDelta at a_mem b_mem
      rintro rfl; simp_all
    have : trues.disjUnion falses disj = Finset.univ := by
      ext v; simp +zetaDelta
    rw [← Finset.card_disjUnion, this]; simp

  omega

private def colorsInCol_lt {n} (c : KColoring (n+1) s) (j : Fin (n+1)) :
    Finset.card {(c.data i)[j] | (i) } ≤ 2^n := by
  let S :=
    Finset.univ |>.filter (α := BitVec (n+1)) (·[j])
    |>.image (fun i => (c.data i)[j])
  calc
    _ = S.card := by
      congr 1
      ext k
      simp [S]
      constructor
      · rintro ⟨i,rfl⟩
        if h : i[j] then
          use i, h
        else
          let i' := i ^^^ .oneAt j
          have : i'[j] := by unfold i'; simp_all
          use i', this
          apply c.same_adjAt (i := i') (j := i) (d := j)
          simp +contextual [i', Fin.ext_iff, eq_comm]
      · rintro ⟨i,_,h⟩
        exact ⟨i,h⟩
    _ ≤ (Finset.filter _ Finset.univ).card :=
      Finset.card_image_le
    _ = 2^n := bv_oneBit_fixed_card j

def normS (C : KColoring (n + 1) s) : Nonempty (KColoring (n+1) (2^n)) := by
  have : ∀ d : Fin (n+1), {(C.data i)[d] | (i) } ↪ Fin (2^n) :=
    fun d =>
      have set_to_fincard := Finset.equivFin { (C.data i)[d] | (i) }
      .trans (Equiv.toEmbedding <| by simp; apply Equiv.refl)
        (.trans set_to_fincard.toEmbedding
          (Fin.castLEOrderEmb (colorsInCol_lt C d)).toEmbedding)
  exact ⟨{
    data := fun i => Vector.ofFn fun d => this d ⟨(C.data i)[d],_,rfl⟩
    same := by
      intro i j ne
      obtain ⟨d,is_ne,cs_eq⟩ := C.same i j ne
      use d
      simp_all
    diff := by
      intro i j adj
      obtain ⟨d,ne⟩ := C.diff i j adj
      use d
      simp_all
  }⟩


def stepN (C : KColoring n s) (hn : n > 0) (hs : s > 1) : KColoring (n+1) s where
  data := fun i =>
    (if bvhd i then
      (C.data (bvtl i)).map (· + ⟨1,hs⟩)
    else
      (C.data (bvtl i))).push ⟨0,by omega⟩
  same := by
    intro i j ne
    by_cases bvhd i = bvhd j
    case neg h =>
      use ⟨n,by omega⟩, h
      simp
    case pos h =>
      have : (bvtl i) ≠ (bvtl j) := by
        intro eq; apply ne
        rw [← cons_hdtl i, ← cons_hdtl j, h, eq]
      obtain ⟨d,is_ne,cs_eq⟩ := C.same (bvtl i) (bvtl j) this
      use d.castSucc
      constructor
      · simpa [bvtl] using is_ne
      · simp_all
        split <;> simp [cs_eq]
  diff := by
    have : NeZero s := ⟨by omega⟩
    intro i j adj
    by_cases bvhd i = bvhd j
    case pos h =>
      obtain ⟨d,ne⟩ := C.diff _ _ (adjacent_bvhd_eq adj h)
      use d.castSucc
      rw [h]
      split <;> simpa using ne
    case neg h =>
      use ⟨0,by omega⟩
      have := adjacent_bvhd_ne adj h
      rw [← ne_eq, ← Bool.not_eq] at h
      rw [← h]
      cases bvhd i <;> simp [*]

def liftN (C : KColoring n s) (hn : n > 0) (hs : s > 1) (h : n ≤ n') : KColoring n' s :=
  if eq : n = n' then
    eq ▸ C
  else
    (C.stepN hn hs).liftN (by omega) hs (by omega)
