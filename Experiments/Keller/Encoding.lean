/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Trestle.Encode
import Trestle.Solver.Dimacs
import Trestle.Upstream.IndexTypeInstances

import Experiments.Keller.KellerGraph
import Experiments.Keller.SymmBreak.TwoCubes
import Experiments.Keller.SymmBreak.Matrix

namespace Keller.Encoding

open Trestle Encode

inductive Vars (n s : Nat)
-- coordinates of each of the 2^n clique nodes
| x (i : BitVec n) (j : Fin n) (k : Fin s)
deriving IndexType, Hashable, Ord

instance : ToString (Vars n s) where
  toString | Vars.x i j k => s!"x{i.toNat},{j},{k}"

inductive AllVars (n s : Nat)
| x (i : BitVec n) (j : Fin n) (k : Fin s)
| y (i i' : BitVec n) (j : Fin n) (k : Fin s)
| z (i i' : BitVec n) (j : Fin n)
deriving DecidableEq

instance : ToString (AllVars n s) where
  toString
    | .x i j k    => s!"x{i.toNat},{j},{k}"
    | .y i i' j k => s!"y{i.toNat},{i'.toNat},{j},{k}"
    | .z i i' j   => s!"z{i.toNat},{i'.toNat},{j}"

def allBitVecs (n) : Array (BitVec n) := Array.ofFn (BitVec.ofFin)

@[simp] theorem mem_allBitVecs (x : BitVec n) : x ∈ allBitVecs n := by
  simp [allBitVecs]



section Spec

open Vars

def baseSpec : Model.PropPred (Vars n s) :=
  (fun τ =>
    -- type 1 clauses in paper
    (∀ (i : BitVec n) (j : Fin n), ∃! k, τ (x i j k)) ∧
    -- type 2 clauses in paper
    (∀ (i i' : BitVec n) (j : Fin n), i ^^^ i' = BitVec.oneAt j →
        ∃ j', j' ≠ j ∧ ∃ k, τ (x i j' k) ≠ τ (x i' j' k)) ∧
    -- type 5/6 clauses in paper
    (∀ (i i' : BitVec n), i ≠ i' → ∃ j, i[j] ≠ i'[j] ∧ ∀ (k : Fin s), τ (x i j k) = τ (x i' j k)))

def c0_c1_spec : Model.PropPred (Vars (n+2) (s+2)) :=
  fun τ =>
    (∀ j, τ (x 0 j SymmBreak.TwoCubes.c0_colors[j])) ∧
    (∀ j, τ (x 1 j SymmBreak.TwoCubes.c1_colors[j]))

def c3_spec : Model.PropPred (Vars (n+5) (s+2)) :=
  fun τ => ∀ j, j ∈ [2,3,4] → τ (x 3 j 1)

def full_spec : Model.PropPred (Vars n s) :=
  fun τ =>
    baseSpec τ ∧
    (match n,s with | _+2, _+2 => c0_c1_spec τ  | _,_ => True) ∧
    (match n,s with | _+5, _+2 => c3_spec τ     | _,_ => True)


def cliqueToAssn (c : KClique n s) : Model.PropAssignment (Vars n s) :=
  fun | .x i j k => (c.get i)[j] = k

def assnToVertices (τ : Model.PropAssignment (Vars n s)) : Set (KVertex n s) :=
  fun ⟨i,cs⟩ => ∀ j, τ (x i j (cs[j]))

open Model.PropPred in
/-- `baseSpec` is satisfied by the assignment generated by `c` -/
theorem cliqueToAssn_satisfies_baseSpec (c : KClique n s) :
    cliqueToAssn c ⊨ baseSpec := by
  unfold baseSpec cliqueToAssn
  refine ⟨?_,?_,?_⟩
  · -- this should just be simp but for some reason existsUnique_eq' is not applying
    intro i j; simp only [Model.PropFun.satisfies_var, decide_eq_true_eq]; apply existsUnique_eq' (a' := (c.get i)[j])
  · intro i i' j is_xor
    have ⟨_,j2,js_ne,h⟩ := c.get_adj_of_xor_eq j is_xor
    use j2, js_ne, (c.get i')[j2]
    simpa using h
  · intro i i' is_ne
    have ⟨j1,is_ne_j1,cs_eq_j1,_⟩ := c.get_adj is_ne
    use j1, is_ne_j1
    simpa using cs_eq_j1

/-- This direction is more complicated, and also we don't need it,
    but we prove it as an interesting aside. -/
theorem clique_of_satisfies_baseSpec {τ : Model.PropAssignment (Vars n s)} :
    open Model.PropPred in τ ⊨ baseSpec → ∃ c : KClique n s, τ = cliqueToAssn c := by
  rintro ⟨coords,twoDiffs,sGaps⟩
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
    replace mem1 : ∀ j k, τ (Vars.x i1 j k) = true ↔ k = c1[j.val] := by
      intro j k
      have := mem1; simp [verts] at this
      have := congrArg (·[j]) this; simp at this
      have := this ▸ Exists.choose_spec (coords i1 j)
      exact ⟨this.2 k, fun h => h ▸ this.1⟩
    replace mem2 : ∀ j k, τ (Vars.x i2 j k) = true ↔ k = c2[j.val] := by
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

end Spec


section CNF
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
        Cardinality.amoPairwise vars
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



/-- ensure for all pairs where only one coordinate is guaranteed to be different,
that there is a second coordinate which is also different -/
def twoDiffs : VEncCNF (Vars n s) Unit (fun τ =>
    ∀ (i i' : BitVec n) (j : Fin n), i ^^^ i' = .oneAt j → ∃ j' ≠ j, ∃ k, τ (x i j' k) ≠ τ (x i' j' k)) :=
  (for_all (allBitVecs n) fun i =>
    for_all (Array.finRange n) fun j =>
      -- the bitvector which must be different only at coord `j`
      let i' : BitVec n := i ^^^ .oneAt j
      -- this is symmetric so only output the i < i' case
      VEncCNF.guard (i < i') fun h =>
        twoDiffsAt i i' j
  ).mapProp (by
    ext τ; simp
    constructor
    · intro h i i'; revert h
      wlog h_le : i ≤ i'
      · specialize this τ i' i (BitVec.le_total _ _ |>.resolve_left h_le)
        convert this using 3
        · rw [BitVec.xor_comm]
        · simp_rw [eq_comm (a := τ (x i _ _))]
      intro h j i_i'
      have : i < i' := by
        apply BitVec.lt_of_le_ne h_le; rintro rfl
        simpa using congrArg (·[j]) i_i'
      specialize h i j
      simp [← i_i', ← BitVec.xor_assoc, this] at h
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
    withTemps (Fin n × Fin s)
      (names := some fun (j',k) => toString (AllVars.y i i' j' k)) <|
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


/-- ensures `i` and `i'` have a coord `j` on which the bits differ but colors equal -/
def hasSGap (i i' : BitVec n) : VEncCNF (Vars n s) Unit
      (fun τ => ∃ j, i[j] ≠ i'[j] ∧ ∀ k, τ (x i j k) = τ (x i' j k)) :=
  -- only can consider those `j` for which `i` and `i'` could have an `s`-gap
  (let potentialJs := Array.finRange n |>.filter fun j => i[j] ≠ i'[j]
  newCtx s!"s gap c{i.toNat} c{i'.toNat}" <|
  withTemps (Fin n) (names := some fun j => toString (AllVars.z (s := s) i i' j)) <|
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

/-- ensures all pairs of vertices have an s-gap  -/
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

def baseEncoding (n s) : VEncCNF (Vars n s) Unit baseSpec :=
  seq[
    coordinates,
    twoDiffs,
    allSGap
  ] |>.mapProp (by ext τ; simp [baseSpec])

def c0_c1 (n s) : VEncCNF (Vars (n+2) (s+2)) Unit c0_c1_spec :=
  seq[
    -- c0 = (0, 0, 0, 0, 0, 0*)
    for_all (Array.finRange _) fun j =>
      unit <| .pos (x 0 j SymmBreak.TwoCubes.c0_colors[j])
  , -- c1 = (0, 1, 0, 0, 0, 0*)
    for_all (Array.finRange _) fun j =>
      unit <| .pos (x 1 j SymmBreak.TwoCubes.c1_colors[j])
  ]
  |>.mapProp (by ext τ; simp [c0_c1_spec])

def c3 (n s) : VEncCNF (Vars (n+5) (s+2)) Unit c3_spec :=
  seq[
    -- c3 = (0, 1, 1, 1, 1, _*)
    unit <| .pos (x 3 2 1),
    unit <| .pos (x 3 3 1),
    unit <| .pos (x 3 4 1)
  ]
  |>.mapProp (by ext τ; simp [c3_spec])

def fullEncoding (n s) : VEncCNF (Vars n s) Unit full_spec :=
  seq[
    baseEncoding n s
  , VEncCNF.guard (n ≥ 2 ∧ s ≥ 2) fun h =>
      c0_c1 (n-2) (s-2)
      |>.castVar (by congr <;> simp [h])
  , VEncCNF.guard (n ≥ 5 ∧ s ≥ 2) fun h =>
      c3 (n-5) (s-2)
      |>.castVar (by congr <;> simp [h])
  ]
  |>.mapProp (by
    ext τ
    unfold full_spec
    simp; rintro -
    match s with
    | 0 | 1 => simp
    | s+2 =>
    match n with
    | 0 | 1 | 2 | 3 | 4 => simp
    | n+5 => simp
  )

end CNF

namespace SR

structure Line (n s) where
  c : Clause (Literal (AllVars n s))
  pivot : Literal (AllVars n s)
  true_lits : List (Literal (AllVars n s))
  substs : List (AllVars n s × Literal (AllVars n s))

def lineOfClauseAndSubsts (c : Clause (Literal (AllVars n s))) (hc : c.size > 0 := by simp)
        (substs : List (AllVars n s × Literal (AllVars n s))) : Line n s :=
  -- take the first literal as the pivot
  let pivot := c[0]
  let true_lits :=
    List.ofFn (n := c.size-1) fun i => c[i.val+1]
  let substs := substs.filterMap fun (v, l) =>
    match v with
    | .x i j k =>
      if c.any fun cvar => LitVar.toVar cvar = .x i j k then
        none
      else some (v,l)
    | _ => some (v, l)
  { c, pivot, true_lits, substs }

def renumberSwapSubsts (j : Fin n) (k k' : Fin s) := Id.run do
  let mut substs : Array (AllVars n s × Literal (AllVars n s)) := #[]
  -- x_i,j,k <-> x_i,j,k'
  for i in allBitVecs n do
    substs := substs.push (.x i j k , .pos (.x i j k'))
    substs := substs.push (.x i j k', .pos (.x i j k ))
  -- y_i,i',j,k <-> y_i,i',j,k'
  for i in allBitVecs n do
    for hjd: jdiff in [0:n] do
      let i' := i ^^^ BitVec.oneAt ⟨jdiff, hjd.upper⟩
      if i < i' then
        substs := substs.push (.y i i' j k, .pos (.y i i' j k'))
        substs := substs.push (.y i i' j k', .pos (.y i i' j k))
  return substs

def matrixIndices : Array (BitVec n) := #[7#n,11#n,19#n,35#n,67#n]

open AllVars in
def matrixRenumber (n s) : Array (Line n s) :=
  if hn : ¬(5 ≤ n ∧ n ≤ 7) then #[] else
  if hs : ¬(4 ≤ s) then #[] else Id.run do
  let mut res := #[]

  let j : Fin n := ⟨2,by omega⟩
  let k : Fin s := ⟨3,by omega⟩
  let k' : Fin s := ⟨2,by omega⟩
  res := res.push <|
    lineOfClauseAndSubsts
      (c := #[Literal.neg <| .x 11#n j k, Literal.pos <| .x 11#n j k'])
      (substs := renumberSwapSubsts j k k' |>.toList)

--  for hj : j in [2:n] do
--    let j : Fin n := ⟨j,hj.upper⟩
--
--    for h : matRow in [0:n-2] do
--      let i : BitVec n := matrixIndices[matRow]'(by
--        have := h.upper; simp +zetaDelta [matrixIndices] at this hn ⊢; omega
--      )
--      -- we want to show c_i[j] < idx+2, eg c_i[j] ≠ k for k >= idx+2
--      -- proof by swapping k to idx+1 (within column j)
--      if hswap : matRow+2 < s then
--        let kswap : Fin s := ⟨matRow+2, hswap⟩
--        let substs := renumberSwapSubsts j k kswap
--        let c := #[.neg (.x i j k) ]

  return res

def test (n s) : Array (Line n s) :=
  if h : n ≥ 5 ∧ s > 4 then
    #[
      lineOfClauseAndSubsts
        (c := #[ Literal.neg <| .x 11#n ⟨2,by omega⟩ ⟨3,by omega⟩ ])
        (substs := renumberSwapSubsts ⟨2,by omega⟩ ⟨3,by omega⟩ ⟨2,by omega⟩ |>.toList)
    ,  lineOfClauseAndSubsts
        (c := #[ Literal.neg <| .x 11#n ⟨2,by omega⟩ ⟨4,by omega⟩ ])
        (substs := renumberSwapSubsts ⟨2,by omega⟩ ⟨4,by omega⟩ ⟨2,by omega⟩ |>.toList)
    ]
  else #[]

def all (n s) : Array (Line n s) :=
  test n s

end SR

namespace Cubes

open Vars

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


def allCubes : List (Clause <| Literal <| Vars n s) :=
  if hn : n ≥ 5 then
    if hs : s ≥ 4 then
      matrixCubes hn hs ×ˢ lastColsCubes hn hs
      |>.map (fun (a,b) => a ++ b)
    else []
  else []

end Cubes
