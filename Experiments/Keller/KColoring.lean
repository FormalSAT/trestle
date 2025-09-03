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

def adjacent (i j : BitVec n) : Prop :=
  ∃ d : Fin n, adjacentAt i j d

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

def liftS (C : KColoring n s) (h : s ≤ s') : KColoring n s' where
  data := fun i => (C.data i).map (·.castLE h)
  same := by
    intro i j ne
    obtain ⟨d,is_ne,cs_eq⟩ := C.same i j ne
    use d
    simp_all
  diff := by
    intro i j adj
    obtain ⟨d,ne⟩ := C.diff i j adj
    use d
    simp only [Fin.getElem_fin, Vector.getElem_map] at ne ⊢
    generalize (C.data i)[d.val] = id at ne ⊢
    generalize (C.data j)[d.val] = jd at ne ⊢
    cases id; cases jd
    simp_all

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
