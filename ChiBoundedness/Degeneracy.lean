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
end Degeneracy
