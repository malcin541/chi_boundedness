import Mathlib

set_option linter.style.openClassical false
set_option linter.unusedFintypeInType false

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
  let K' := H.coeSubgraph K
  have h_verts_equal : (K.verts : Set V) = K'.verts := by trivial
  have h_verts_equal' : K.verts = Subtype.val⁻¹' K'.verts := by
    rw [← h_verts_equal, Set.preimage_image_eq _ Subtype.val_injective]
  have h_K'_neq_bot : K' ≠ ⊥ := by
    apply K'.ne_bot_iff_nonempty_verts.mpr
    apply K.ne_bot_iff_nonempty_verts.mp at h_K_neq_bot
    exact Set.Nonempty.image _ h_K_neq_bot
  obtain ⟨ v, ⟨ hv_where, hv_deg ⟩ ⟩ := h K' h_K'_neq_bot
  have h_K_subset_H : (K.verts : Set V) ⊆ H.verts := by simp
  have h_v_in_Hverts : v ∈ H.verts := h_K_subset_H hv_where
  let v' := H.vert v h_v_in_Hverts
  use v'
  constructor
  · rw [h_verts_equal']
    exact hv_where
  · suffices h_deg_equal : K.degree v' ≤ K'.degree v by
      exact le_trans h_deg_equal hv_deg
    suffices h_nei_subset : (K.neighborSet v' : Set V) ⊆ K'.neighborSet v by
      unfold SimpleGraph.Subgraph.degree
      simp only [← Set.toFinset_card, ← Set.ncard_eq_toFinset_card',
                 ← (Set.ncard_image_of_injective _ Subtype.val_injective),
                 Set.ncard_le_ncard h_nei_subset]
    intro x hx
    unfold SimpleGraph.Subgraph.neighborSet
    unfold SimpleGraph.Subgraph.neighborSet at hx
    obtain ⟨ ⟨ y, hy_in_Hverts ⟩ , ⟨ hy₁, hy₂ ⟩ ⟩ := hx
    simp only [Set.mem_setOf_eq]
    apply (H.coeSubgraph_adj K v x).mpr
    use h_v_in_Hverts
    simp only at hy₂
    rw [hy₂] at hy_in_Hverts
    use hy_in_Hverts
    simp only [Set.mem_setOf_eq, hy₂] at hy₁
    exact hy₁

theorem degeneracy_subgraph_monotone' (G : SimpleGraph V) (H : G.Subgraph) (d : ℕ) :
    IsDegenerate' G d → IsDegenerate' H.coe d := by
  intro h_G_deg A h_A_nonempty
  let A_in_G := (A : Set V)
  obtain ⟨ v_in_G, ⟨ h_v_where, h_v_nei_card⟩ ⟩ :=
    h_G_deg A_in_G (Set.Nonempty.image Subtype.val h_A_nonempty)
  have h_A_subset_H : A_in_G ⊆ H.verts := by exact Subtype.coe_image_subset H.verts A
  have h_v_in_H : v_in_G ∈ H.verts := by exact Set.mem_of_subset_of_mem h_A_subset_H h_v_where
  let v := H.vert v_in_G h_v_in_H
  have h_v_in_A : v ∈ A := by exact Set.mem_of_mem_image_val h_v_where
  use v
  constructor
  · exact h_v_in_A
  · suffices h : Subtype.val '' {u | u ∈ A ∧ H.coe.Adj u v} ⊆ {u | u ∈ A_in_G ∧ G.Adj u v_in_G} by
      rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
      exact le_trans (Set.ncard_le_ncard h) h_v_nei_card
    intro u ⟨ u', ⟨ h_u'_where, h_u'_adj ⟩, h_u'_eq ⟩
    constructor
    · rw [← h_u'_eq]
      exact Set.mem_image_of_mem Subtype.val h_u'_where
    · rw [H.coe_adj u' v, h_u'_eq] at h_u'_adj
      exact SimpleGraph.Subgraph.Adj.adj_sub h_u'_adj

theorem degeneracy_subgraph_monotone'' (G : SimpleGraph V) (H : G.Subgraph) (d : ℕ) :
    IsDegenerate G d → IsDegenerate H.coe d := fun h =>
      (degeneracy_def_equivalent H.coe d).mpr
        ((degeneracy_subgraph_monotone' G H d)
          ((degeneracy_def_equivalent G d).mp h))

theorem degeneracy_to_coloring (G : SimpleGraph V) (d : ℕ) :
    IsDegenerate G d -> G.Colorable (d+1) := by
  induction hcard : Fintype.card V generalizing V with
  | zero =>
    intro _
    exact @SimpleGraph.Colorable.of_isEmpty V G (Fintype.card_eq_zero_iff.mp hcard) (d + 1)
  | succ n ih =>
    intro h_G_deg
    let G_as_subgraph := (⊤ : G.Subgraph)
    have h_G_card : G_as_subgraph.verts.ncard = n + 1 := by
      rw [Set.ncard_eq_toFinset_card', Set.toFinset_card,
          SimpleGraph.Subgraph.verts_top, Fintype.card_setUniv]
      exact hcard
    have h_G_nonempty : G_as_subgraph ≠ ⊥ := by
      suffices h_V_nonempty : Nonempty V by
        refine (SimpleGraph.Subgraph.ne_bot_iff_nonempty_verts G_as_subgraph).mpr ?_
        exact Set.univ_nonempty
      apply Fintype.card_pos_iff.mp
      simp only [hcard, Nat.succ_pos n]
    obtain ⟨ v, hv ⟩ := h_G_deg G_as_subgraph h_G_nonempty
    let G' := G_as_subgraph.deleteVerts {v}
    have h_G'_verts : G'.verts = G_as_subgraph.verts \ {v} := SimpleGraph.Subgraph.deleteVerts_verts
    have h_G'_card : Fintype.card G'.verts = n := by
      suffices h₁ : G'.verts.ncard = n by
        rw [← Set.toFinset_card, ← Set.ncard_eq_toFinset_card', h₁]
      rw [SimpleGraph.Subgraph.deleteVerts_verts, Set.ncard_diff_singleton_of_mem hv.left, h_G_card]
      rfl
    have h_not_v_in_G' : ∀ x : V, x ≠ v → x ∈ G'.verts := by
      intro x hx
      rw [h_G'_verts]
      exact Set.mem_diff_of_mem trivial hx
    have h_G'_deg : IsDegenerate G'.coe d := by
      apply degeneracy_subgraph_monotone
      exact h_G_deg
    have h_G'_colorable : G'.coe.Colorable (d + 1) := ih G'.coe h_G'_card h_G'_deg
    obtain ⟨ f' ⟩ := h_G'_colorable
    let nv := {u | G.Adj u v ∧ u ∈ G'.verts}
    have h_nv_card : nv.ncard ≤ d := by
      suffices h_subset : nv ⊆ G.neighborSet v by
        rw [← SimpleGraph.Subgraph.neighborSet_top] at h_subset
        refine le_trans (Set.ncard_le_ncard h_subset) ?_
        rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
        exact hv.right
      intro u ⟨ h_u_adj, _ ⟩
      exact (G.adj_comm u v).mp h_u_adj
    let used_cols := f' '' (Subtype.val⁻¹' nv)
    have h_used_cols_card : used_cols.ncard ≤ d := by
      calc
      _ ≤ (Subtype.val⁻¹' nv).ncard := Set.ncard_image_le
      _ = (Subtype.val⁻¹' nv).encard.toNat := by rfl
      _ ≤ nv.encard.toNat := by
        refine ENat.toNat_le_toNat (Set.encard_preimage_val_le_encard_right G'.verts nv) ?_
        simp only [ne_eq, Set.encard_eq_top_iff, Set.not_infinite]
        exact nv.toFinite
      _ = nv.ncard := by rfl
      _ ≤ d := h_nv_card
    have h_sizes_lt : used_cols.ncard < (Set.univ : Set (Fin (d+1))).ncard := by
        simp [h_used_cols_card]
    obtain ⟨ a, ⟨ _, h_a_unused ⟩ ⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard h_sizes_lt
    let f : V → Fin (d+1) := fun u => if h : u = v then a else
      have h_u_in_G' : u ∈ G'.verts := by
        rw [h_G'_verts, SimpleGraph.Subgraph.verts_top]
        simp [Set.mem_diff, Set.mem_singleton_iff, h]
      f' ⟨ u, h_u_in_G' ⟩
    have h_f_f'_equal: ∀ x : V, ∀ hx: x ∈ G'.verts, f' ⟨ x, hx ⟩  = f x := by grind
    have h_fv_eq_a : f v = a := by grind
    have h_f_v_valid : ∀ x : V, G.Adj v x → f v ≠ f x := by
      intro x h_adj
      have h_x_ne_v : x ≠ v := G.ne_of_adj h_adj.symm
      have h_x_in_G' : x ∈ G'.verts := h_not_v_in_G' x h_x_ne_v
      rw [h_fv_eq_a, ← h_f_f'_equal x h_x_in_G']
      suffices x ∈ nv by grind
      exact ⟨ h_adj.symm, h_x_in_G' ⟩
    have h_f_valid : ∀ {x y : V}, G.Adj x y → f x ≠ f y := by
      intro x y h_adj
      by_cases h₁ : x = v
      · rw [h₁]
        rw [h₁] at h_adj
        exact h_f_v_valid y h_adj
      · by_cases h₂ : y = v
        · rw [h₂]
          rw [h₂] at h_adj
          exact (h_f_v_valid x h_adj.symm).symm
        · have h_x_in_G' : x ∈ G'.verts := h_not_v_in_G' x h₁
          have h_y_in_G' : y ∈ G'.verts := h_not_v_in_G' y h₂
          rw [← h_f_f'_equal x h_x_in_G', ← h_f_f'_equal y h_y_in_G']
          suffices h_xy_adj_in_G' : G'.coe.Adj ⟨ x, h_x_in_G' ⟩  ⟨ y, h_y_in_G' ⟩  by
            exact f'.valid h_xy_adj_in_G'
          simp only [SimpleGraph.Subgraph.coe_adj]
          exact SimpleGraph.Subgraph.deleteVerts_adj.mpr ⟨ by trivial, h₁, by trivial, h₂, h_adj ⟩
    have f_as_col := (SimpleGraph.Coloring.mk f h_f_valid).colorable
    rw [Fintype.card_fin] at f_as_col
    exact f_as_col


/- Degeneracy orderings -/
def IsDegenerateOrder (G : SimpleGraph V) (o : LinearOrder V) (d : ℕ) : Prop :=
  ∀ v : V, {u | G.Adj v u ∧ o.lt u v}.ncard ≤ d

theorem degenerate_iff_degenerate_order (G : SimpleGraph V) (d : ℕ) :
    IsDegenerate G d ↔ ∃ (o : LinearOrder V), IsDegenerateOrder G o d := by
  constructor
  · induction hcard : Fintype.card V generalizing V with
  | zero =>
    intro _
    letI : IsEmpty V := Fintype.card_eq_zero_iff.mp hcard
    use { le := fun x _ => (IsEmpty.false x).elim
          le_refl  := fun x => (IsEmpty.false x).elim
          le_trans := fun x _ _ _ _ => (IsEmpty.false x).elim
          le_antisymm := fun x _ _ _ => (IsEmpty.false x).elim
          le_total := fun x _ => (IsEmpty.false x).elim
          toDecidableLE := fun x _ => (IsEmpty.false x).elim}
    intro v
    exact (IsEmpty.false v).elim
  | succ n ih =>
    intro h_G_deg
    let h_G_deg' := (degeneracy_def_equivalent G d).mp h_G_deg
    have h_V_nonempty : Nonempty V := by
      apply Fintype.card_pos_iff.mp
      simp only [hcard, Nat.succ_pos n]
    obtain ⟨ v, ⟨ _, hv ⟩ ⟩ := h_G_deg' Set.univ (Set.nonempty_iff_univ_nonempty.mp h_V_nonempty)
    let G_as_subgraph := (⊤ : G.Subgraph)
    have h_G_card : G_as_subgraph.verts.ncard = n + 1 := by
      rw [Set.ncard_eq_toFinset_card', Set.toFinset_card,
          SimpleGraph.Subgraph.verts_top, Fintype.card_setUniv]
      exact hcard
    have h_G_nonempty : G_as_subgraph ≠ ⊥ := by
      refine (SimpleGraph.Subgraph.ne_bot_iff_nonempty_verts G_as_subgraph).mpr ?_
      exact Set.univ_nonempty
    let G' := G_as_subgraph.deleteVerts {v}
    have h_G'_verts : G'.verts = G_as_subgraph.verts \ {v} := SimpleGraph.Subgraph.deleteVerts_verts
    have h_G'_card : Fintype.card G'.verts = n := by
      suffices h₁ : G'.verts.ncard = n by
        rw [← Set.toFinset_card, ← Set.ncard_eq_toFinset_card', h₁]
      rw [SimpleGraph.Subgraph.deleteVerts_verts,
        Set.ncard_diff_singleton_of_mem
          (by
            rw [SimpleGraph.Subgraph.verts_top]
            trivial),
          h_G_card]
      rfl
    have h_not_v_in_G' : ∀ x : V, x ≠ v → x ∈ G'.verts := by
      intro x hx
      rw [h_G'_verts]
      exact Set.mem_diff_of_mem trivial hx
    have h_G'_deg : IsDegenerate G'.coe d := by
      apply degeneracy_subgraph_monotone
      exact h_G_deg
    obtain ⟨ o', ho' ⟩ := ih G'.coe h_G'_card h_G'_deg
    let o : LinearOrder V := {
      le x y :=
        if hy : y = v then True
        else if hx : x = v then False
        else o'.le ⟨ x, h_not_v_in_G' x hx ⟩ ⟨ y, h_not_v_in_G' y hy ⟩
      le_refl x := by simp
      le_trans x y z hxy hyz := by grind
      le_antisymm x y hxy hyx := by grind
      le_total x y := by grind
      toDecidableLE x y := by dsimp; exact inferInstance
    }
    letI := o
    use o
    intro w
    by_cases h : w = v
    · rw [h]
      suffices h_subset : {u | G.Adj v u ∧ u < v } ⊆ {u | u ∈ Set.univ ∧ G.Adj u v} by
        exact le_trans (Set.ncard_le_ncard h_subset) hv
      intro u ⟨ h_u_adj_v , h_u_lt_v ⟩
      simp [h_u_adj_v.symm]
    · have h_w_lt_v : o.le w v := by grind
      have h_u_neq_v : ∀ u, u < w → u ≠ v := fun u hu =>
        ne_iff_lt_or_gt.mpr (Or.inl (lt_of_lt_of_le hu h_w_lt_v))
      have h_u_in_G' : ∀u, u < w → u ∈ G'.verts := fun u hu => h_not_v_in_G' u (h_u_neq_v u hu)
      let w' := (⟨ w, h_not_v_in_G' w h ⟩ : G'.verts)
      let how := ho' w'
      have h_incl : ∀ u, ∀ h_w_adj_u : G.Adj w u, ∀ h_u_lt_w : u < w,
          G'.coe.Adj w' ⟨ u, (h_u_in_G' u h_u_lt_w) ⟩ ∧ ⟨ u, (h_u_in_G' u h_u_lt_w) ⟩ < w' := by
        intro u h_w_adj_u h_u_lt_w
        constructor
        · suffices h_adj_in_G' : G'.Adj w u by
            exact SimpleGraph.Subgraph.Adj.coe h_adj_in_G'
          apply SimpleGraph.Subgraph.deleteVerts_adj.mpr
          exact ⟨ by rw [SimpleGraph.Subgraph.verts_top]; trivial,
                  h,
                  by rw [SimpleGraph.Subgraph.verts_top]; trivial,
                  h_u_neq_v u h_u_lt_w,
                  SimpleGraph.Subgraph.top_adj.mpr h_w_adj_u ⟩
        · exact h_u_lt_w
      let f (u' : {x // x ∈ G'.verts}) :=  (u' : V)
      have h_f_inj : Function.Injective f := by
        exact Subtype.val_injective
      let S' := {u | G'.coe.Adj w' u ∧ u < w'}
      let S := {u | G.Adj w u ∧ u < w}
      have h_inc : ∀ u' : {x // x ∈ G'.verts}, u' ∈ S' → f u' ∈ S := by
        sorry
      have h_subset_range : S ⊆ Set.range f := by
        sorry
      have h_f_inv_S_is_S' : f⁻¹' S = S' := by
        sorry
      have h := Set.ncard_preimage_of_injective_subset_range h_f_inj h_subset_range
      rw [← h, h_f_inv_S_is_S']
      sorry -- exact ho' w'
  · rintro ⟨ o, ho ⟩
    suffices h : IsDegenerate' G d by exact (degeneracy_def_equivalent G d).mpr h
    intro A h_A_Nonempty
    let A' := A.toFinset
    have h_A'_Nonempty : A'.Nonempty := by
       exact Set.toFinset_nonempty.mpr h_A_Nonempty
    letI := o
    let v := A'.max' h_A'_Nonempty
    use v
    constructor
    · exact Set.mem_toFinset.mp (A'.max'_mem h_A'_Nonempty)
    · suffices h_subset : { u | u ∈ A ∧ G.Adj u v } ⊆ { u | G.Adj v u ∧ u < v} by
        exact le_trans (Set.ncard_le_ncard h_subset) (ho v)
      intro u ⟨ h_u_in_A,  h_u_adj_v ⟩
      exact ⟨ h_u_adj_v.symm, Std.lt_of_le_of_ne
          (A'.le_max' u (Set.mem_toFinset.mpr h_u_in_A))
          (G.ne_of_adj h_u_adj_v) ⟩

end Degeneracy
