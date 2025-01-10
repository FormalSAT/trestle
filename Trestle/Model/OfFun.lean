/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Trestle.Model.PropVars

namespace Trestle.Model


/-! ### `ofFun` -/

namespace PropForm

def ofBool (b : Bool) : PropForm V :=
  if b then .tr else .fls

@[simp]
theorem eval_ofBool (b : Bool) : (PropForm.ofBool b).eval τ = b := by
  cases b <;> simp

/-- Any function from assignments to `Prop` over a list of variables
can be written as a `PropForm`, by truth table construction. -/
def ofFun [DecidableEq V] (p : PropAssignment V → Bool) (L : List V) (h : ∀ v, v ∈ L) :=
  aux L (fun v h => by simp [*] at h)
where aux (rem : List V) (passn : (v : V) → ¬ v ∈ rem → Bool) : PropForm V :=
  match rem with
  | [] =>
    ofBool <| p fun v => passn v (by simp)
  | v::vs =>
    disj
      (conj (var v) (aux vs fun v' h' =>
        if h : v' = v then true  else passn v' (by simp [*, h'])))
      (conj (neg <| var v) (aux vs fun v' h' =>
        if h : v' = v then false else passn v' (by simp [*, h'])))

@[simp]
theorem eval_ofFun [DecidableEq V] {L : List V} {hc}
    : (PropForm.ofFun p L hc).eval τ = p τ := by
  unfold ofFun
  suffices ∀ {rem passn},
    (∀ v h, passn v h = τ v ) →
    eval τ (ofFun.aux p rem passn) = p τ
    from this (fun v h => by have := h (hc v); contradiction)
  intro rem passn ht
  induction rem with
  | nil => simp [ofFun.aux]; congr; funext v; simp [*]
  | cons head tail ih =>
    simp
    cases hhead : τ head <;> (simp; apply ih; intro v h; split <;> simp [*])

@[simp]
theorem entails_ofFun [DecidableEq V] {L : List V} {hc} (p τ)
    : τ ⊨ (PropForm.ofFun p L hc) ↔ p τ := by
  simp [SemanticEntails.entails, satisfies]

end PropForm

namespace PropFun

def ofFun {V : Type u} [DecidableEq V] [Fintype V]
    (p : PropAssignment V → Bool) : PropFun V :=
  Fintype.elim_elems (fun L h1 _ => ⟦ PropForm.ofFun p L h1 ⟧) (by
    intro L1 L2 h1 _ h2 _
    simp; ext; rw [satisfies_mk, satisfies_mk]
    simp [SemanticEntails.entails, PropForm.satisfies]
  )

@[simp]
theorem entails_ofFun [DecidableEq V] [Fintype V] (p : PropAssignment V → Bool) (τ)
    : τ ⊨ ofFun p ↔ p τ := by
  simp [SemanticEntails.entails, satisfies, ofFun]
  apply Fintype.elim_elems_eq_forall (V := V)
  intro L h1 h2 h'
  rw [h']
  simp

/-! ### `ofSet` -/

def ofSet {V : Type u} [DecidableEq V] [Fintype V]
      (S : Set (PropAssignment V)) [DecidablePred (· ∈ S)] : PropFun V :=
  ofFun (· ∈ S)

@[simp]
theorem satisfies_ofSet [DecidableEq V] [Fintype V] (S) [DecidablePred (· ∈ S)]
    : τ ⊨ ofSet (V := V) S ↔ τ ∈ S := by
  simp [ofSet]

end PropFun
