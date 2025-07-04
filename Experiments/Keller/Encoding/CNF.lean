/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Trestle.Encode
import Trestle.Solver.Dimacs
import Trestle.Upstream.IndexTypeInstances

import Experiments.Keller.Encoding.Spec

namespace Keller.Encoding

open Trestle Encode VEncCNF Model

open Spec Vars

namespace CNF

/-- ensure that each vertex has a defined coordinate on each dimension -/
def coordinates : VEncCNF (Vars n s) Unit (fun τ =>
    open PropFun in ∀ i j, ∃! k, τ ⊨ .var (x i j k) ) :=
  (for_all (allBitVecs n) fun i =>
    for_all (Array.finRange n) fun j =>
      newCtx s!"exactly one x_{i.toNat},{j}" <|
      let vars := Array.ofFn (fun k => Literal.pos <| Vars.x i j k)
      Cardinality.sinzExactlyOne vars
      --show VEncCNF _ Unit (Cardinality.exactly 1 vars.toList) from
      --seq[
      --  -- at least one of the `c_ij-` variables is true
      --  Cardinality.atLeastOne vars,
      --  -- at most one of the `c_ij-` variables is true
      --  Cardinality.amoPairwise vars
      --] |>.mapProp (by ext; simp; omega)
  ).mapProp (by
    -- annoying boilerplate
    ext τ; simp [-Cardinality.satisfies_cardPred]
    apply forall_congr'; intro i
    apply forall_congr'; intro j
    rw [Cardinality.exactly_one_iff_unique_idx]
    simp [ExistsUnique, Fin.exists_iff, Fin.forall_iff]
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
    · intro h i j h_lt
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
        · aesop
        · use Literal.pos (.inr (j',k))
          simp [j'_ne]
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
    ext τ
    simp [Clause.satisfies_iff, -Array.size_finRange]
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
    · intro h i i' i_lt
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

def c3_sorted (n s) : VEncCNF (Vars (n+2) (s+2)) Unit c3_sorted_spec :=
  (for_all (Array.finRange (n+2)) fun j =>
    VEncCNF.guard (2 ≤ j.val ∧ j.val+1 < n+2) fun h =>
      addClause #[Literal.neg <| x 3 ⟨j,by omega⟩ 0
                , Literal.pos <| x 3 ⟨j+1,by omega⟩ 0]
  ).mapProp (by
    ext τ; simp [-Bool.not_eq_true, c3_sorted_spec, Clause.satisfies_iff]
    constructor
    · intro h j range; specialize h ⟨j,by omega⟩ (by simp; omega)
      simp only [← imp_iff_not_or] at h
      exact h
    · intro h j range
      rw [← imp_iff_not_or]; apply h; omega
  )

-- TODO(JG): this def is SUPER slow, fix it somehow
seal BitVec.ofNat in
def c3_more_nonzero (n s) : VEncCNF (Vars (n+2) (s+2)) Unit c3_more_nonzero_spec :=
  ( for_all (Array.finRange (n+2)) fun j =>
    VEncCNF.guard (2 ≤ j.val ∧ j.val + 1 < n+2) fun h =>
      for_all (Array.finRange (n+2)) fun col =>
      VEncCNF.guard (2 ≤ col.val ∧ col.val ≤ j.val) fun cr =>
        aux j h col cr
  ).mapProp (by
    ext τ; simp only [Array.mem_finRange, add_lt_add_iff_right,
      BitVec.ofNat_eq_ofNat, Fin.eta, and_imp, forall_const, c3_more_nonzero_spec]
    constructor
    · intro h j jr col cr
      exact h ⟨j,by omega⟩ (by dsimp; omega) ⟨col,by omega⟩ (by dsimp; omega)
    · intro h j jr col cr
      exact h j.val jr col.val cr
  )
where
  aux (j : Nat) (jr : 2 ≤ j ∧ j + 1 < n+2)
      (col : Nat) (cr : 2 ≤ col ∧ col ≤ j)
      : VEncCNF (Vars (n+2) (s+2)) Unit (fun τ =>
        ¬ τ (x 3 ⟨j,by omega⟩ 0) ∧ τ (x 3 ⟨j+1,by omega⟩ 0) →
        (∀ (_j : Nat) (range : 2 ≤ _j ∧ _j ≤ j),
          ¬ τ (x (SymmBreak.C3Zeros.X col (by omega)) ⟨_j,by omega⟩ 0))
        → (∀ (_j : Nat) (range : j < _j ∧ _j < n + 2),
          τ (x (SymmBreak.C3Zeros.X col (by omega)) ⟨_j,by omega⟩ 0))
      ) :=
    let idx : BitVec (n+2) := (SymmBreak.C3Zeros.X col (by omega))
    VEncCNF.andImplyAnd
      (hyps :=
        #[Literal.neg (x 3 ⟨j,by omega⟩ 0), Literal.pos (x 3 ⟨j+1,by omega⟩ 0)]
        ++ Array.ofFn (n := (j+1)-2) fun _j => Literal.neg <| x idx ⟨2+_j,by omega⟩ 0)
      (concs :=
        Array.ofFn (n := (n+2)-(j+1)) fun _j => Literal.pos <| x idx ⟨j+1+_j,by omega⟩ 0)
    |>.mapProp (by
      ext τ
      simp +contextual [-Bool.not_eq_true,-BitVec.ofNat_eq_ofNat,or_imp,forall_and]
      apply imp_congr_right; rintro -; apply imp_congr_right; rintro -
      constructor
      · rintro h cX_nz
        specialize h (fun a => cX_nz _ (by omega))
        intro j' range'
        convert h ⟨j'-(j+1),by omega⟩
        dsimp; omega
      · intro h hyps j'
        apply h ?_ _ (by omega)
        intro j' range'
        convert hyps ⟨j'-2,by omega⟩
        dsimp; omega)

def c3_min_zeros.aux (j) (hj : 5 ≤ j ∧ j < n+2) (i) : VEncCNF (Vars (n+2) (s+2)) Unit (fun τ =>
      ¬τ (x 3 ⟨j-1,by omega⟩ 0) → τ (x 3 ⟨j,by omega⟩ 0) →
      (∀ j' (hj : 2 ≤ j' ∧ j' < n+2), i[j'] = true → ¬τ (x i ⟨j',by omega⟩ 0)) →
        Cardinality.atLeast (n+2-j) (Multiset.ofList <| c3_min_zero_spec.zeroLits i) τ
    ) :=
  (Cardinality.naiveAtLeastK.cond
    (cond := #[.pos (x 3 ⟨j - 1, by omega⟩ 0), .neg (x 3 ⟨j, by omega⟩ 0)]
              ++ (Array.finRange _ |>.filter (fun j => 2 ≤ j.val ∧ i[j] = true)).map (fun j => .pos (x i j 0)))
    (n+2-j)
    (c3_min_zero_spec.zeroLits i).toArray
  ).mapProp (by
    ext τ
    conv => lhs; simp only [
      Pi.himp_apply, Pi.compl_apply, compl_iff_not, himp_iff_imp,
      Clause.satisfies_iff, LitVar.toPropFun_mkPos, LitVar.toPropFun_mkNeg,
      PropFun.satisfies_neg, PropFun.satisfies_var,
      Fin.forall_iff, Fin.getElem_fin,
      forall_and, forall_eq, not_exists,
      true_imp_iff, false_imp_iff, imp_true_iff, not_and, and_true, and_imp, or_imp, not_not,
      decide_eq_true_iff,
      Array.mem_append, Array.mem_toArray, List.mem_cons, List.not_mem_nil,
      Array.forall_mem_map, Array.forall_mem_filter, Array.mem_finRange
      ]
    apply imp_congr_right; rintro -
    apply imp_congr_right; rintro -
    apply imp_congr_left
    aesop)

def c3_min_zeros (n s) : VEncCNF (Vars (n+2) (s+2)) Unit c3_min_zero_spec :=
  ( for_all (Array.finRange (n+2)) fun j =>
    VEncCNF.guard (5 ≤ j.val) fun h =>
      for_all (allBitVecs (n+2)) fun i =>
      VEncCNF.guard (i[1] = true) fun h =>
        c3_min_zeros.aux j (by omega) i
  ).mapProp (by
    ext τ
    simp only [Array.mem_finRange, mem_allBitVecs,
      Pi.himp_apply, Pi.compl_apply, compl_iff_not,
      himp_iff_imp, forall_const, and_imp]
    unfold c3_min_zero_spec
    simp only [Fin.forall_iff]
    constructor
    · rintro h j j_bounds c3_nz c3_z i i1_true high_bits
      exact h j j_bounds.2 j_bounds.1 i i1_true c3_nz c3_z high_bits
    · rintro h j j_upper j_lower i i1_true c3_nz c3_z high_bits
      exact h j ⟨j_lower, j_upper⟩ c3_nz c3_z i i1_true high_bits
  )


def fullEncoding (n s) : VEncCNF (Vars n s) Unit fullSpec :=
  seq[
    baseEncoding n s
  , VEncCNF.guard (n ≥ 2 ∧ s ≥ 2) fun h =>
      seq[
        c0_c1 (n-2) (s-2)
      , c3_sorted (n-2) (s-2)
      , c3_more_nonzero (n-2) (s-2)
      ]
      |>.castVar (by congr <;> simp [h])
  ]
  |>.mapProp (by
    ext τ
    unfold fullSpec
    simp; rintro -
    match s with
    | 0 | 1 => simp
    | s+2 =>
    match n with
    | 0 | 1 => simp
    | n+2 => simp
  )
