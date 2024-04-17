/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import ProofChecker.Data.ICnf
import ProofChecker.Data.Pog
import ProofChecker.Model.PropVars
import ProofChecker.Model.Extensions
import ProofChecker.Count.PropForm

/-! Justifications of CPOG steps. -/

open PropTerm

theorem addDisj_new_var_equiv {A : Set Var} (Γ l₁ l₂ φ₁ φ₂ : PropTerm Var) :
    s ∉ A → X ⊆ A → ↑Γ.semVars ⊆ A → ↑l₁.semVars ⊆ A → ↑l₂.semVars ⊆ A →
    equivalentOver X (l₁ ⊓ Γ) φ₁ → equivalentOver X (l₂ ⊓ Γ) φ₂ →
    equivalentOver X (.var s ⊓ Γ ⊓ (.biImpl (.var s) (l₁ ⊔ l₂))) (φ₁ ⊔ φ₂) := by
  intro hNMem hXA hΓ hL₁ hL₂ e₁ e₂ τ
  have hMem : s ∉ X := fun h => absurd (hXA h) hNMem
  have hΓ : s ∉ Γ.semVars := fun h => absurd (hΓ h) hNMem
  have hL₁ : s ∉ l₁.semVars := fun h => absurd (hL₁ h) hNMem
  have hL₂ : s ∉ l₂.semVars := fun h => absurd (hL₂ h) hNMem
  constructor
  case mp =>
    intro ⟨σ₁, hAgree, h₁⟩
    simp at h₁
    have : σ₁ ⊨ Γ := by tauto
    have : σ₁ ⊨ l₁ ⊔ l₂ := by simp; tauto
    cases satisfies_disj.mp this with
    | inl h =>
      have : σ₁ ⊨ l₁ ⊓ Γ := by simp; tauto
      have ⟨σ₂, hAgree₂, h₂⟩ := e₁ τ |>.mp ⟨σ₁, hAgree, this⟩
      exact ⟨σ₂, hAgree₂, satisfies_disj.mpr (.inl h₂)⟩
    | inr h =>
      have : σ₁ ⊨ l₂ ⊓ Γ := by simp; tauto
      have ⟨σ₂, hAgree₂, h₂⟩ := e₂ τ |>.mp ⟨σ₁, hAgree, this⟩
      exact ⟨σ₂, hAgree₂, satisfies_disj.mpr (.inr h₂)⟩
  case mpr =>
    intro ⟨σ₂, hAgree, h₂⟩
    cases satisfies_disj.mp h₂ with
    | inl h =>
      have ⟨σ₁, hAgree₁, h₁⟩ := e₁ τ |>.mpr ⟨σ₂, hAgree, h⟩
      let σ₁' := σ₁.set s ⊤
      have : σ₁' ⊨ .var s := by simp
      have hAgree₁' : σ₁'.agreeOn X σ₁ := σ₁.agreeOn_set_of_not_mem _ hMem
      have : σ₁'.agreeOn X τ := hAgree₁'.trans hAgree₁
      have : σ₁' ⊨ Γ := agreeOn_semVars (σ₁.agreeOn_set_of_not_mem _ hΓ) |>.mpr
        (satisfies_conj.mp h₁).right
      have : σ₁' ⊨ l₁ := agreeOn_semVars (σ₁.agreeOn_set_of_not_mem _ hL₁) |>.mpr
        (satisfies_conj.mp h₁).left
      exact ⟨σ₁', by assumption, by simp; tauto⟩
    | inr h =>
      have ⟨σ₁, hAgree₁, h₁⟩ := e₂ τ |>.mpr ⟨σ₂, hAgree, h⟩
      let σ₁' := σ₁.set s true
      have : σ₁' ⊨ .var s := by simp
      have hAgree₁' : σ₁'.agreeOn X σ₁ := σ₁.agreeOn_set_of_not_mem _ hMem
      have : σ₁'.agreeOn X τ := hAgree₁'.trans hAgree₁
      have : σ₁' ⊨ Γ := agreeOn_semVars (σ₁.agreeOn_set_of_not_mem _ hΓ) |>.mpr
        (satisfies_conj.mp h₁).right
      have : σ₁' ⊨ l₂ := agreeOn_semVars (σ₁.agreeOn_set_of_not_mem _ hL₂) |>.mpr
        (satisfies_conj.mp h₁).left
      exact ⟨σ₁', by assumption, by simp; tauto⟩

theorem addDisj_partitioned {A : Set Var} (Γ l₁ l₂ : PropTerm Var) (φ₁ φ₂ : PropForm Var) :
    -- Note: also works with l₁.semVars ⊆ A
    ↑l₂.semVars ⊆ A → hasUniqueExtension X A Γ →
    Γ ⊓ l₁ ⊓ l₂ ≤ ⊥ → equivalentOver X (l₁ ⊓ Γ) ⟦φ₁⟧ → equivalentOver X (l₂ ⊓ Γ) ⟦φ₂⟧ →
    φ₁.partitioned → φ₂.partitioned → (φ₁.disj φ₂).partitioned := by
  intro hL₂ hUep hImp e₁ e₂ hD₁ hD₂
  refine ⟨hD₁, hD₂, fun τ ⟨h₁, h₂⟩ => ?_⟩
  have h₁ : τ ⊨ ⟦φ₁⟧ := h₁
  have h₂ : τ ⊨ ⟦φ₂⟧ := h₂
  have ⟨σ₁, hAgree₁, hσ₁⟩ := e₁ τ |>.mpr ⟨τ, PropAssignment.agreeOn_refl _ _, h₁⟩
  have ⟨σ₂, hAgree₂, hσ₂⟩ := e₂ τ |>.mpr ⟨τ, PropAssignment.agreeOn_refl _ _, h₂⟩
  simp at hσ₁ hσ₂
  have hσ₁Γ : σ₁ ⊨ Γ := by tauto
  have hσ₂Γ : σ₂ ⊨ Γ := by tauto
  have hAgree : σ₁.agreeOn A σ₂ := hUep hσ₁Γ hσ₂Γ (hAgree₁.trans hAgree₂.symm)
  have : σ₂ ⊨ l₂ := by tauto
  have : σ₁ ⊨ l₂ := agreeOn_semVars (hAgree.subset hL₂) |>.mpr this
  have : σ₁ ⊨ ⊥ := entails_ext.mp hImp _ (by simp; tauto)
  simp at this

-- Alternative: use disjoint variables condition on φ₁/φ₂ to put together pair of assignments?!
theorem addConj_new_var_equiv₂ {A : Set Var} (Γ l₁ l₂ φ₁ φ₂ : PropTerm Var) :
    -- Note: also works with φ₁.semVars ⊆ X
    p ∉ X → p ∉ Γ.semVars → p ∉ l₁.semVars → p ∉ l₂.semVars → φ₂.semVars ⊆ X →
    -- Note: also works with l₁.semVars ⊆ A
    ↑l₂.semVars ⊆ A → hasUniqueExtension X A Γ →
    equivalentOver X (l₁ ⊓ Γ) φ₁ → equivalentOver X (l₂ ⊓ Γ) φ₂ →
    equivalentOver X (.var p ⊓ (.biImpl (.var p) (l₁ ⊓ l₂)) ⊓ Γ) (φ₁ ⊓ φ₂) := by
  intro hMem hΓ hL₁ hL₂ hφ₂ hL₂Γ hUep e₁ e₂ τ
  constructor
  case mp =>
    intro ⟨σ₁, hAgree, h₁⟩
    simp at h₁
    have ⟨σ₂, hAgree₂, h₂⟩ := e₁ τ |>.mp ⟨σ₁, hAgree, by simp; tauto⟩
    have ⟨σ₂', hAgree₂', h₂'⟩ := e₂ τ |>.mp ⟨σ₁, hAgree, by simp; tauto⟩
    have : σ₂.agreeOn X σ₂' := hAgree₂.trans hAgree₂'.symm
    have : σ₂ ⊨ φ₂ := agreeOn_semVars (this.subset hφ₂) |>.mpr h₂'
    exact ⟨σ₂, hAgree₂, by simp; tauto⟩
  case mpr =>
    intro ⟨σ₂, hAgree, h₂⟩
    simp at h₂
    have ⟨σ₁, hAgree₁, h₁⟩ := e₁ τ |>.mpr ⟨σ₂, hAgree, by tauto⟩
    have ⟨σ₁', hAgree₁', h₁'⟩ := e₂ τ |>.mpr ⟨σ₂, hAgree, by tauto⟩
    simp at h₁ h₁'
    have hσ₁Γ : σ₁ ⊨ Γ := by tauto
    have hσ₁'Γ : σ₁' ⊨ Γ := by tauto
    have hAgree₁₁' : σ₁.agreeOn A σ₁' := hUep hσ₁Γ hσ₁'Γ (hAgree₁.trans hAgree₁'.symm)
    have : σ₁ ⊨ l₂ := agreeOn_semVars (hAgree₁₁'.subset hL₂Γ) |>.mpr (by tauto)
    let σ₃ := σ₁.set p true
    have : σ₃ ⊨ .var p := by simp
    have : σ₃ ⊨ l₁ := agreeOn_semVars (σ₁.agreeOn_set_of_not_mem _ hL₁) |>.mpr (by tauto)
    have : σ₃ ⊨ l₂ := agreeOn_semVars (σ₁.agreeOn_set_of_not_mem _ hL₂) |>.mpr (by tauto)
    have : σ₃ ⊨ Γ := agreeOn_semVars (σ₁.agreeOn_set_of_not_mem _ hΓ) |>.mpr (by tauto)
    exact ⟨σ₃, σ₁.agreeOn_set_of_not_mem _ hMem |>.trans hAgree₁, by simp; tauto⟩

theorem addConj_new_var_equiv {A : Set Var} (G : Pog) (Γ : PropTerm Var) (ls : Array ILit) :
    p ∉ A → X ⊆ A → ↑Γ.semVars ⊆ A → hasUniqueExtension X A Γ →
    (∀ σ₁, ∃ (σ₂ : PropAssignment Var), σ₂.agreeOn X σ₁ ∧ σ₂ ⊨ Γ) →
    (∀ l ∈ ls.data, l.var ∈ A ∧ ↑(PropTerm.semVars ⟦G.toPropForm l⟧) ⊆ X ∧
      equivalentOver X (l.toPropTerm ⊓ Γ) ⟦G.toPropForm l⟧) →
    equivalentOver X
      (.var p ⊓ (Γ ⊓ .biImpl (.var p) ⟦PropForm.arrayConj (ls.map ILit.toPropForm)⟧))
      ⟦PropForm.arrayConj (ls.map G.toPropForm)⟧ := by
  intro hMem hX hΓ hUep hExt hLs τ
  refine ⟨?mp, ?mpr⟩ <;>
    simp only [PropForm.mk_arrayConj, satisfies_conj, satisfies_biImpl,
      PropForm.satisfies_arrayConjTerm, Array.map_data, List.mem_map', and_imp,
      forall_apply_eq_imp_iff₂, forall_exists_index, ILit.mk_toPropForm]
  case mp =>
    intro σ₁ hAgree hσ₁p hσ₁Γ hσ₁
    simp only [hσ₁p, true_iff, ILit.mk_toPropForm] at hσ₁
    refine ⟨σ₁, hAgree, ?_⟩
    intro l hL
    have ⟨_, hTpf, hEquiv⟩ := hLs l hL
    have : σ₁ ⊨ l.toPropTerm := hσ₁ l hL
    have : σ₁ ⊨ l.toPropTerm ⊓ Γ := by simp [this, hσ₁Γ]
    have ⟨σ₂, hAgree₂, hσ₂⟩ := hEquiv τ |>.mp ⟨σ₁, hAgree, this⟩
    apply agreeOn_semVars ?_ |>.mp hσ₂
    exact (hAgree₂.trans hAgree.symm).subset hTpf
  case mpr =>
    intro σ₂ hAgree₂ hTpfs
    have ⟨σ₁, hAgree₁, h₁⟩ := hExt τ
    let σ₁' := σ₁.set p true
    have hσ₁'p : σ₁' ⊨ .var p := by simp
    have hAgree₁'A : σ₁'.agreeOn A σ₁ := σ₁.agreeOn_set_of_not_mem _ hMem
    have hAgree₁' : σ₁'.agreeOn X τ := hAgree₁'A.subset hX |>.trans hAgree₁
    have hσ₁'Γ : σ₁' ⊨ Γ := agreeOn_semVars (hAgree₁'A.subset hΓ) |>.mpr h₁
    refine ⟨σ₁', hAgree₁', hσ₁'p, hσ₁'Γ, ⟨fun _ => ?_, fun _ => hσ₁'p⟩⟩
    intro l hL
    have : σ₂ ⊨ ⟦G.toPropForm l⟧ := hTpfs l hL
    have ⟨σ₃, hAgree₃, h₃⟩ := (hLs l hL).right.right τ |>.mpr ⟨σ₂, hAgree₂, this⟩
    refine agreeOn_semVars ?_ |>.mp (satisfies_conj.mp h₃).left
    have : ↑l.toPropTerm.semVars ⊆ A := by simp [(hLs l hL).left]
    apply PropAssignment.agreeOn.subset this
    exact hUep (satisfies_conj.mp h₃).right hσ₁'Γ (hAgree₃.trans hAgree₁'.symm)

/-! Other stuff that doesn't fit anywhere. -/

theorem partitioned_lit (l : ILit) : l.toPropForm.partitioned := by
  dsimp [ILit.toPropForm]
  cases l.polarity <;> simp [PropForm.partitioned]