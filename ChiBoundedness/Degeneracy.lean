import Mathlib

set_option linter.style.openClassical false

section Degeneracy

open Classical

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

def IsDegenerate (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ (H : G.Subgraph), H ≠ ⊥ → ∃ v ∈ H.verts, (H.degree v) ≤ d

def IsDegenerate' (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ (A : Set V), A.Nonempty → ∃ v ∈ A, Set.ncard {u ∈ A | G.Adj u v} ≤ d

theorem degeneracy_def_equivalent (G : SimpleGraph V) (d : ℕ) :
    IsDegenerate G d ↔ IsDegenerate' G d := by
  constructor
  · intro h A hA
    let H := (⊤ : G.Subgraph).induce A
    have h_Hverts_eq_A : H.verts = A := by exact (H.induce_verts A)
    have hH_notempty : H ≠ ⊥ := by
      apply H.ne_bot_iff_nonempty_verts.mpr
      rw [h_Hverts_eq_A]
      exact hA
    have ⟨ v, hv ⟩  := h H hH_notempty
    use v
    constructor
    · rw [← h_Hverts_eq_A]
      exact hv.left
    · let h₁ := hv.right
      unfold SimpleGraph.Subgraph.degree at h₁
      have h₂ : H.neighborSet v = { u ∈ A | G.Adj u v} := by
        unfold SimpleGraph.Subgraph.neighborSet
        apply Set.ext_iff.mpr
        intro x
        simp only [Set.mem_setOf_eq]
        constructor
        · intro hx
          exact ⟨ H.edge_vert hx.symm, H.adj_sub hx.symm ⟩
        · intro hx
          rw [(⊤ : G.Subgraph).induce_adj]
          exact ⟨ hv.left, ⟨ hx.left, hx.right.symm ⟩ ⟩
      rw [← Set.toFinset_card] at h₁
      simp [h₂] at h₁
      rw [Set.ncard_eq_toFinset_card']
      simp [h₁]
  · intro h H hH
    let A := H.verts
    have ⟨ v, hv ⟩ := h A (H.ne_bot_iff_nonempty_verts.mp hH)
    use v
    constructor
    · exact hv.left
    · unfold SimpleGraph.Subgraph.degree
      rw [← Set.toFinset_card, ← Set.ncard_eq_toFinset_card']
      suffices h₁ : H.neighborSet v ⊆ { u | u ∈ A ∧ G.Adj u v} by
        exact le_trans (Set.ncard_le_ncard h₁) hv.right
      intro x hx
      have hx' := (H.mem_neighborSet v x).mp hx
      simp only [Set.mem_setOf_eq]
      constructor
      · exact H.edge_vert hx'.symm
      · exact H.adj_sub hx'.symm

theorem empty_zero_degenerate (G : SimpleGraph V) (d : ℕ) : G = ⊥ → IsDegenerate G d := by
  intro h H h_H_not_bot
  obtain ⟨ v, hv ⟩ := H.ne_bot_iff_nonempty_verts.mp h_H_not_bot
  use v
  constructor
  · exact hv
  · suffices h₁ : (H.neighborSet v) = ∅ by
      unfold SimpleGraph.Subgraph.degree
      rw [← Set.toFinset_card, ← Set.ncard_eq_toFinset_card']
      apply (H.neighborSet v).ncard_eq_zero.mpr at h₁
      simp [h₁]
    unfold SimpleGraph.Subgraph.neighborSet
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    suffices h₂ : ¬G.Adj v x by
      exact mt H.adj_sub h₂
    simp [h]

theorem mon_degeneracy (G : SimpleGraph V) (d₁ d₂ : ℕ) :
    IsDegenerate G d₁ → d₁ ≤ d₂ → IsDegenerate G d₂ := by
  intro h₁ h_ineq H h_H_neq_bot
  obtain ⟨ v, hv ⟩ := h₁ H h_H_neq_bot
  exact ⟨ v, ⟨ hv.left, le_trans hv.right h_ineq ⟩ ⟩

theorem degeneracy_le_maxDegree (G : SimpleGraph V) : IsDegenerate G G.maxDegree := by
  intro H h_H_neq_bot
  obtain ⟨ v, hv ⟩ := H.ne_bot_iff_nonempty_verts.mp h_H_neq_bot
  exact ⟨ v, ⟨ hv, le_trans (H.degree_le v) (G.degree_le_maxDegree v) ⟩ ⟩

theorem degeneracy_subgraph_monotone (G : SimpleGraph V) (H : G.Subgraph) (d : ℕ) :
    IsDegenerate G d → IsDegenerate H.coe d := by
  intro h K h_K_neq_bot
  obtain K' := H.coeSubgraph K
  have h_K'_neq_bot : K' ≠ ⊥ := by sorry
  obtain ⟨ v, hv ⟩ := h K' h_K'_neq_bot
  sorry

end Degeneracy
