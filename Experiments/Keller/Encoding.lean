/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Trestle.Encode
import Trestle.Solver.Dimacs
import Trestle.Upstream.IndexTypeInstances
import Experiments.Keller.KellerGraph
import Experiments.Keller.SymmBreak.Matrix

namespace Keller.Encoding

open Trestle Encode

inductive Vars (n s : Nat)
-- coordinates of each of the 2^n clique nodes
| x (i : BitVec n) (j : Fin n) (k : Fin s)
deriving IndexType, Hashable

def allBitVecs (n) : Array (BitVec n) := Array.ofFn (BitVec.ofFin)

@[simp] theorem mem_allBitVecs (x : BitVec n) : x ∈ allBitVecs n := by
  simp [allBitVecs]



section Spec

def cliqueToAssn (c : KClique n s) : Model.PropAssignment (Vars n s) :=
  fun | .x i j k => (c.get i)[j] = k

def assnToVertices (τ : Model.PropAssignment (Vars n s)) : Set (KVertex n s) :=
  fun ⟨i,cs⟩ => ∀ j, τ (Vars.x i j (cs[j]))

end Spec


section Base
open VEncCNF Model Vars

/-- ensure that each vertex has a defined coordinate on each dimension -/
def coordinates : VEncCNF (Vars n s) Unit (fun τ =>
    open PropFun in ∀ i j, ∃! k, τ ⊨ .var (x i j k) ) :=
  (for_all (allBitVecs n) fun i =>
    for_all (Array.finRange n) fun j =>
      newCtx s!"exactly one x_{i.toNat},{j}" <|
      let vars := Array.ofFn (fun k => Literal.pos <| Vars.x i j k)
      seq[
        -- at least one of the `c_ij-` variables is true
        Cardinality.atLeastOne vars,
        -- at most one of the `c_ij-` variables is true
        Cardinality.amoSeqCounter vars
      ]
  ).mapProp (by
    -- annoying boilerplate
    ext τ; simp
    apply forall_congr'; intro i
    apply forall_congr'; intro j
    -- LHS says card is equal to one
    rw [← Nat.le_antisymm_iff, eq_comm, Cardinality.card_eq_one]
    case nodup =>
      simp [List.nodup_ofFn]; intro; simp [LitVar.ext_iff]
    -- wiggle some defs around
    simp [List.mem_ofFn, LitVar.mkPos]
    simp_rw [ExistsUnique, ← exists_and_right]
    aesop
  )



-- ensure for all pairs where only one coordinate *must* be different,
-- that there is a second coordinate which is also different
def twoDiffs : VEncCNF (Vars n s) Unit (fun τ =>
    ∀ (i i' : BitVec n) (j : Fin n), i ^^^ i' = 1#n <<< j.val → ∃ j' ≠ j, ∃ k, τ (x i j' k) ≠ τ (x i' j' k)) :=
  (for_all (allBitVecs n) fun i =>
    for_all (Array.finRange n) fun j =>
      -- the bitvector which must be different only at coord `j`
      let i' : BitVec n := i ^^^ BitVec.shiftLeft 1 j
      -- this is symmetric so only output the i < i' case
      VEncCNF.guard (i < i') fun h =>
        twoDiffsAt i i' j
  ).mapProp (by
    ext τ; simp
    constructor
    · intro h i i'; revert h
      wlog h_lt : i ≤ i'
      · specialize this τ i' i (BitVec.le_total _ _ |>.resolve_left h_lt)
        simp_rw [BitVec.xor_comm (x := i) (y := i'), eq_comm (a := τ (x i _ _))]
        exact this
      intro h j i_i'
      specialize h i j
      have : i ^^^ 1#n <<< j.val = i' := by
        rw [← i_i', ← BitVec.xor_assoc]; simp
      have : i < i' := by
        apply BitVec.lt_of_le_ne ‹_›; rintro rfl
        have := congrArg (·[j]) i_i'; simp at this; subst n; exact j.elim0
      simp [*] at h
      exact h
    · intro h i j
      split <;> simp
      next h_lt =>
      apply h
      simp [← BitVec.xor_assoc]
  )
where
  twoDiffsAt (i i' j) : VEncCNF (Vars n s) Unit
    (fun τ => ∃ j' ≠ j, ∃ k, τ (x i j' k) ≠ τ (x i' j' k))
  :=
    (newCtx s!"two diffs c{i.toNat} c{i'.toNat}" <|
    withTemps (Fin n × Fin s) <|
    seq[
      for_all (Array.finRange n) fun j' =>
        VEncCNF.guard (j' ≠ j) fun _h =>
          for_all (Array.finRange s) fun k =>
            xNeAt i i' j' k
    , addClause (Array.mk (do
        let j' ← List.finRange n
        guard (j' ≠ j)
        let k ← List.finRange s
        return Literal.pos (Sum.inr (j',k))
      ))
    ]).mapProp (by
      ext τ
      simp [Clause.satisfies_iff, _root_.guard, failure]
      constructor
      · rintro ⟨σ,rfl,h1,_,⟨j',j'_ne,k,rfl⟩,h_sat⟩
        simp at h_sat
        use j', j'_ne, k
        specialize h1 j'; simp [j'_ne, h_sat] at h1
        specialize h1 k; simp [h_sat] at h1
        simp [h1]
      · rintro ⟨j',j'_ne,k,h⟩
        use (fun | .inl v => τ v | .inr (_j',_k) => j' = _j' ∧ k = _k)
        refine ⟨?_,?_,?_⟩
        · ext v; simp
        · intro _j'; split <;> aesop
        · use Literal.pos (.inr (j',k))
          simp
          use j', j'_ne, k
      )
  xNeAt (i i' j' k) : VEncCNF (Vars n s ⊕ _ × _) Unit
        (fun τ => τ (.inr (j',k)) → τ (.inl <| x i j' k) ≠ τ (.inl <| x i' j' k)) :=
    let temp := Literal.neg (Sum.inr (j',k))
    seq[
      addClause #[temp, Literal.pos <| Sum.inl (Vars.x i j' k), Literal.pos <| Sum.inl (Vars.x i' j' k)],
      addClause #[temp, Literal.neg <| Sum.inl (Vars.x i j' k), Literal.neg <| Sum.inl (Vars.x i' j' k)]]
    |>.mapProp (by
      ext τ; simp [Clause.satisfies_iff, temp]
      generalize τ _ = a; generalize τ _ = b; generalize τ _ = c
      cases a <;> cases b <;> simp
    )


-- ensures `i` and `i'` have a coord `j` on which the bits differ but colors equal
def hasSGap (i i' : BitVec n) : VEncCNF (Vars n s) Unit
      (fun τ => ∃ j, i[j] ≠ i'[j] ∧ ∀ k, τ (x i j k) = τ (x i' j k))
  :=
  -- only can consider those `j` for which `i` and `i'` could have an `s`-gap
  (let potentialJs := Array.finRange n |>.filter fun j => i[j] ≠ i'[j]
  newCtx s!"s gap c{i.toNat} c{i'.toNat}" <|
  withTemps (Fin n) <|
    seq[
      for_all potentialJs fun j =>
        newCtx s!"s gap c{i.toNat} c{i'.toNat} at {j}" <|
        for_all (Array.finRange s) fun k =>
          seq[
            addClause #[Literal.neg (Sum.inr j),
              Literal.pos (Sum.inl (x i j k)), Literal.neg (Sum.inl (x i' j k))],
            addClause #[Literal.neg (Sum.inr j),
              Literal.neg (Sum.inl (x i j k)), Literal.pos (Sum.inl (x i' j k))]
          ]
    , addClause (potentialJs |>.map (Literal.pos <| Sum.inr ·)) ]
  )
  |>.mapProp (by
    ext τ; simp [Clause.satisfies_iff]
    constructor
    · rintro ⟨σ, rfl, h_js, j, is_ne_at_j, j_true⟩
      use j, is_ne_at_j
      intro k
      specialize h_js j is_ne_at_j k
      aesop
    · rintro ⟨j,is_ne_at_j,h⟩
      use (fun | .inl v => τ v | .inr _j => _j = j)
      constructor
      · ext v; simp
      · simp +contextual [← imp_iff_not_or, h, is_ne_at_j])

def allSGap : VEncCNF (Vars n s) Unit (fun τ =>
    ∀ i i', i ≠ i' → ∃ j, i[j] ≠ i'[j] ∧ ∀ k, τ (x i j k) = τ (x i' j k)) :=
  (for_all (allBitVecs n) fun i =>
    for_all (allBitVecs n) fun i' =>
      guard (i < i') fun _h => hasSGap i i'
  ).mapProp (by
    ext τ; simp
    constructor
    · intro h i i' is_ne
      wlog h_lt : i < i'
      · replace is_ne := Ne.symm is_ne
        replace h_lt := BitVec.lt_of_le_ne (BitVec.not_lt.mp h_lt) is_ne
        specialize this τ h i' i is_ne h_lt
        simp_rw [eq_comm (a := i[_]'_), eq_comm (a := τ (x i _ _))]
        exact this
      simpa [h_lt] using h i i'
    · intro h i i'
      split <;> simp
      exact h i i' (BitVec.ne_of_lt ‹_›)
  )

def baseEncoding (n s) : VEncCNF (Vars n s) Unit
    (fun τ => ∃ c : KClique n s, τ = cliqueToAssn c) :=
  seq[
    coordinates,
    twoDiffs,
    allSGap
  ]
  |>.mapProp (by
    ext τ
    constructor
    · rintro ⟨coords,twoDiffs,sGaps,-⟩
      let verts : Finset (KVertex n s) :=
        Finset.univ (α := BitVec n)
        |>.map ⟨fun i => ⟨i,Vector.ofFn fun j => (coords i j).choose⟩
          , by intro; simp⟩
      refine ⟨
        ⟨verts
        ,?isClique,?card⟩
        ,?eqτ⟩
      case card => simp [verts]
      case isClique =>
        rintro ⟨i1,c1⟩ mem1 ⟨i2,c2⟩ mem2 ne
        -- mem1 and mem2 essentially tell us how to interpret τ
        replace mem1 : ∀ j k, τ (x i1 j k) = true ↔ k = c1[j.val] := by
          intro j k
          have := mem1; simp [verts] at this
          have := congrArg (·[j]) this; simp at this
          have := this ▸ Exists.choose_spec (coords i1 j)
          exact ⟨this.2 k, fun h => h ▸ this.1⟩
        replace mem2 : ∀ j k, τ (x i2 j k) = true ↔ k = c2[j.val] := by
          intro j k
          have := mem2; simp [verts] at this
          have := congrArg (·[j]) this; simp at this
          have := this ▸ Exists.choose_spec (coords i2 j)
          exact ⟨this.2 k, fun h => h ▸ this.1⟩
        -- now we can show the indices are diff
        replace ne : i1 ≠ i2 := by
          rintro rfl; apply ne; simp; ext1 j hj
          rw [← mem2 ⟨j,hj⟩, mem1]
        -- get the sgap
        specialize sGaps i1 i2 ne
        rcases sGaps with ⟨j1,is_ne_j1,cs_eq_j1⟩
        use j1, is_ne_j1
        constructor
        · -- this is a cool case to step through
          simp; rw [← mem2 j1, ← cs_eq_j1, mem1]
        if just_one_diff : i1 ^^^ i2 = 1#n <<< j1.val then
          specialize twoDiffs i1 i2 j1 just_one_diff
          rcases twoDiffs with ⟨j2,js_ne,k,x_ne⟩
          use j2, js_ne.symm
          rw [Ne, Bool.eq_iff_iff, mem1, mem2] at x_ne
          right; intro; simp_all
        else
          rw [BitVec.eq_of_getElem_eq_iff] at just_one_diff
          simp at just_one_diff
          rcases just_one_diff with ⟨j2,hj2,h⟩
          use ⟨j2,hj2⟩
          rw [Bool.eq_iff_iff, not_iff] at h
          simp at h
          have : j1 ≠ ⟨j2,hj2⟩ := by
            rintro rfl; simp [h] at is_ne_j1; omega
          simp [this]; left
          cases j1; simp_all; omega
      case eqτ =>
        ext ⟨i,j,k⟩
        rw [Bool.eq_iff_iff]
        simp only [cliqueToAssn]
        generalize hcs : KClique.get _ _ = cs
        rw [KClique.get_eq_iff_mem] at hcs
        simp [verts] at hcs; subst hcs
        simp
        have := Exists.choose_spec (coords i j)
        simp at this
        generalize Exists.choose _ = boop at this ⊢
        clear * - this
        aesop
    · rintro ⟨clique,rfl⟩
      simp [cliqueToAssn]
      constructor
      · intro i i' j h
        have := clique.get_adj_one_diff (i₁ := i) (i₂ := i') j
          (by simpa [Nat.zero_lt_of_lt j.isLt] using congrArg (·[j]) h)
          (by intro j' hj'; simp at hj'
              have := congrArg (·[j']) h
              rw [Bool.eq_iff_iff] at this; simp [hj'] at this; omega)
        rcases this with ⟨-,j',js_ne,cs_ne⟩
        use j', js_ne, (clique.get i')[j']
        simpa using cs_ne
      · intro i i' is_ne
        have ⟨j1,bv_ne_j1,cs_eq_j1,_⟩ := clique.get_adj is_ne
        use j1, bv_ne_j1, cs_eq_j1
  )

end Base

section SymmBreaking
open EncCNF Vars

def c0_c1_c3 (n s) : EncCNF (Vars n s) Unit := do
  if hs : s ≥ 2 then do
  if hn : n ≥ 2 then do
  -- c0 = (0, 0, 0, 0, 0, 0*)
  for hi : j in [0:n] do
    have : j < n := hi.upper
    set 0 j 0
  -- c1 = (0, 1, 0, 0, 0, 0*)
  set 1 0 0
  set 1 1 1
  for hi : j in [2:n] do
    have : j < n := hi.upper
    set 1 j 0
  if hn' : n ≥ 5 then do
    -- c3 = (0, 1, 1, 1, 1, _*)
    set 3 0 0
    for hi : j in [1:5] do
      have : j < 5 := hi.upper
      set 3 j 1
    -- c7 = (0, 1, 1, _, _, _*)
    set 7 0 0; set 7 1 1; set 7 2 1
    -- c11 = (0, 1, _, 1, _, _*)
    set 11 0 0; set 11 1 1; set 11 3 1
    -- c19 = (0, 1, _, _, 1, _*)
    set 19 0 0; set 19 1 1; set 19 4 1
where set (a b c) (hb : b < n := by omega) (hc : c < s := by omega) :=
  unit <| .pos <| x a ⟨b,hb⟩ ⟨c,hc⟩

-- we are sorting each column with respect to an odd order of i's:
def iOfIdx : Equiv.Perm (BitVec n) :=
    Equiv.Perm.setAll [(0, 0), (1, 1), (2, 3), (3, 7), (4, 11), (5, 19)]


def slowIncreasingUnits (j : Fin n) (startIdx : BitVec n) (startColor : Fin s) : EncCNF (Vars n s) Unit := do
  -- Under iOfIdx ordering, the first six indices are all pretty low.
  -- so we can insert lots of units implied by the other symmetry breaking and slowIncreasingStrict
  for h : a in [0: (2^n - startIdx.toNat) ⊓ (s-startColor.val)] do
    have : a < min _ _ := h.upper
    let i := (iOfIdx ⟨startIdx.toNat+a, by omega⟩)
    for h : k in [startColor+a:s] do
      have : k < s := h.upper
      unit <| .neg <| x i j ⟨k, by omega⟩


def slowIncreasingStrict (j : Fin n) : EncCNF (Vars n s) Unit := do
  -- temporary `m_idx,k` is true when
  -- the max color in col `j` *prior* to `idx` is `≥ k`
  let TempTy := BitVec n × Fin s
  withTemps TempTy do
    -- the max starts out below 0, so all m_0,k are false
    for k in List.fins s do
      addClause #[.neg (.inr (0,k))]

    -- now we can define m_idx,k in terms of values to the left and above
    -- `m_idx+1,k ↔ x_i[idx],k ∨ m_idx,k ∨ m_idx+1,k+1`
    for idx in allBitVecs n do
      match idx.toFin.succ? with
      | none => pure ()
      | some idxsucc =>
      for k in List.fins s do
        let misk : Vars n s ⊕ TempTy := .inr (idxsucc,k)
        let xiik : Vars n s ⊕ TempTy := .inl (x (iOfIdx idx) j k)
        let mik  : Vars n s ⊕ TempTy := .inr (idx,k)
        match k.succ? with
        | none =>
          Subtype.val <| tseitin[ {misk} ↔ {xiik} ∨ {mik} ]
        | some ksucc =>
          let misks : Vars n s ⊕ (BitVec n × Fin s) := .inr (idxsucc,ksucc)
          Subtype.val <| tseitin[ {misk} ↔ {xiik} ∨ {mik} ∨ {misks}]

    -- now the symmetry breaking kicker: the max can only increase by one each i!
    for i in allBitVecs n do
      match i.toFin.succ? with
      | none => pure ()
      | some isucc =>
      for k in List.fins s do
        match k.succ? with
        | none => pure ()
        | some ksucc =>
          addClause #[.pos (.inr (i,k)), .neg (.inr (isucc,ksucc))]

def matrixCubes (hn : n ≥ 5) (hs : s ≥ 4) : List (Clause <| Literal (Vars n s)) :=
  let matrixList := SymmBreak.Matrix.canonicalCases.toList
  let idxs := #[7, 11, 19]
  matrixList.map fun m =>
    Array.mk <| List.flatten <|
      List.ofFn fun r : Fin 3 => List.ofFn fun c : Fin 3 =>
        let mval : Fin s := m.data[r][c].castLE (by omega)
        .pos (x idxs[r] ⟨2+c, by omega⟩ mval)

def triangle (L : List α) (n : Nat) : List (Vector α n) :=
  aux L n |>.map (·.reverse)
where aux (L : List α) (n : Nat) : List (Vector α n) :=
  match n with
  | 0 => [⟨#[], by simp⟩]
  | n+1 =>
    L.tails.flatMap (fun
      | []     => []
      | hd::tl =>
        aux (hd::tl) n |>.map (·.push hd)
    )

def canonicalColumn (start : Fin s) (len : Nat) : List (Vector (Fin s) len) :=
  aux start len |>.map (Vector.reverse)
where aux (start : Fin s) (len) : List (Vector (Fin s) len) :=
  have : NeZero s := ⟨fun h => (h ▸ start).elim0⟩
  match len with
  | 0 => [⟨#[],by simp⟩]
  | len+1 => do
    let tail := aux start len
    (List.range (start+1)).flatMap (fun hd =>
      let hd : Fin s := hd
      tail.map (·.push hd)) ++
    (aux (start+1) len).map (fun tl =>
      tl.push (Fin.ofNat' s (start+1)))

def canonicalColumns (n : Nat) (len : Nat) (hs : s > 0) : List (Vector (Vector (Fin s) len) n) :=
  let cols := canonicalColumn (s := s) ⟨0,hs⟩ len
  triangle cols n

def lastColsCubes (hn : n ≥ 5) (hs : s ≥ 4) : List (Clause <| Literal (Vars n s)) :=
  let idxs := #[3, 7, 11, 19]
  let colsList := canonicalColumns (n-5) idxs.size (by omega)
  colsList.map fun cols =>
    let cube := Array.flatten (
      Array.ofFn fun r => Array.ofFn (n := n-5) fun c =>
        .pos <| x idxs[r] ⟨c+5, by omega⟩ cols[c][r])
    cube

end SymmBreaking

def fullEncoding (n s) : EncCNF (Vars n s) Unit := do
  baseEncoding n s
  c0_c1_c3 n s
  if hn : n ≥ 5 then
    if hn : s > 5 then
      slowIncreasingUnits ⟨0,by omega⟩ 6 ⟨2,by omega⟩
      slowIncreasingUnits ⟨1,by omega⟩ 6 ⟨3,by omega⟩
      slowIncreasingUnits ⟨2,by omega⟩ 6 ⟨5,by omega⟩
      slowIncreasingUnits ⟨3,by omega⟩ 6 ⟨5,by omega⟩
      slowIncreasingUnits ⟨4,by omega⟩ 6 ⟨5,by omega⟩
      for h : i in [5:n] do
        slowIncreasingUnits ⟨i,h.upper⟩ 2 ⟨2,by omega⟩


def allCubes : List (Clause <| Literal <| Vars n s) :=
  if hn : n ≥ 5 then
    if hs : s ≥ 4 then
      matrixCubes hn hs ×ˢ lastColsCubes hn hs
      |>.map (fun (a,b) => a ++ b)
    else []
  else []
