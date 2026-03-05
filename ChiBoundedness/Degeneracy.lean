import Mathlib
import ChiBoundedness.Tools

set_option linter.style.openClassical false
set_option linter.unusedFintypeInType false

section Degeneracy

variable {V : Type*} [Fintype V]

open Classical

/- Main definition of degeneracy -/
def IsDegenerate (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ (H : G.Subgraph), H ≠ ⊥ → ∃ v ∈ H.verts, (H.degree v) ≤ d

/- Bounded degree graphs are degenerate -/
lemma isDegenerate_boundedDegree (G : SimpleGraph V) (d : ℕ) :
  (∀ v, G.degree v ≤ d) → IsDegenerate G d := by
  intro h_G_maxdeg H h_H_not_bot
  obtain ⟨ v, hv ⟩ := H.ne_bot_iff_nonempty_verts.mp h_H_not_bot
  exact ⟨ v, hv, le_trans (H.degree_le v) (h_G_maxdeg v) ⟩

lemma isDegenerate_maxDegree (G : SimpleGraph V) : IsDegenerate G G.maxDegree :=
  isDegenerate_boundedDegree G G.maxDegree (fun v => G.degree_le_maxDegree v)

theorem isDegenerate_emptyGraph (d : ℕ) : IsDegenerate (SimpleGraph.emptyGraph V) d := by
  apply isDegenerate_boundedDegree
  intro v
  simp

/- Equivalent degeneracy definition -/
def IsDegenerate' (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ (A : Set V), A.Nonempty → ∃ v ∈ A, Set.ncard {u ∈ A | G.Adj u v} ≤ d

theorem isDegenerate_iff_isDegenerate' (G : SimpleGraph V) (d : ℕ) :
    IsDegenerate G d ↔ IsDegenerate' G d := by
  constructor
  · intro h A hA
    let H := (⊤ : G.Subgraph).induce A
    have ⟨ v, ⟨ h_v_in_A, h_v_deg ⟩ ⟩  := h H (H.ne_bot_iff_nonempty_verts.mpr hA)
    refine ⟨ v, h_v_in_A, ?_ ⟩
    have h_v_neiSet_rewrite : H.neighborSet v = { u ∈ A | G.Adj u v} := by
      apply Set.ext_iff.mpr
      intro _
      simp only [Set.mem_setOf_eq]
      exact ⟨ fun hx => ⟨ H.edge_vert hx.symm, H.adj_sub hx.symm ⟩,
              fun hx => ⟨ h_v_in_A, ⟨ hx.left, hx.right.symm ⟩ ⟩ ⟩
    unfold SimpleGraph.Subgraph.degree at h_v_deg
    rw [← Set.toFinset_card] at h_v_deg
    simp [h_v_neiSet_rewrite] at h_v_deg
    simp [Set.ncard_eq_toFinset_card', h_v_deg]
  · intro h H hH
    have ⟨ v, ⟨ h_v_in_H, h_deg_v ⟩ ⟩ := h H.verts (H.ne_bot_iff_nonempty_verts.mp hH)
    refine ⟨ v, h_v_in_H, ?_ ⟩
    unfold SimpleGraph.Subgraph.degree
    rw [← Set.toFinset_card, ← Set.ncard_eq_toFinset_card']
    refine le_trans (Set.ncard_le_ncard ?_) h_deg_v
    intro x hx
    have hx' := ((H.mem_neighborSet x v).mp hx.symm)
    exact ⟨ H.edge_vert hx', H.adj_sub hx' ⟩

theorem isDegenerate_nondecreasing (G : SimpleGraph V) (d₁ d₂ : ℕ) :
    IsDegenerate G d₁ → d₁ ≤ d₂ → IsDegenerate G d₂ := by
  intro h₁ h_ineq H h_H_neq_bot
  obtain ⟨ v, hv ⟩ := h₁ H h_H_neq_bot
  exact ⟨ v, ⟨ hv.left, le_trans hv.right h_ineq ⟩ ⟩

theorem isDegenerate_subgraph' (G : SimpleGraph V) (H : G.Subgraph) (d : ℕ) :
    IsDegenerate' G d → IsDegenerate' H.coe d := by
  intro h_G_deg A h_A_nonempty
  obtain ⟨ v_in_G, ⟨ h_v_where, h_v_nei_card⟩ ⟩ :=
    h_G_deg (A : Set V) (Set.Nonempty.image Subtype.val h_A_nonempty)
  let v := H.vert v_in_G (Set.mem_of_subset_of_mem (Subtype.coe_image_subset H.verts A) h_v_where)
  refine ⟨ v, Set.mem_of_mem_image_val h_v_where, ?_ ⟩
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  refine le_trans (Set.ncard_le_ncard ?_) h_v_nei_card
  intro u ⟨ u', ⟨ h_u'_where, h_u'_adj ⟩, h_u'_eq ⟩
  exact ⟨ h_u'_eq ▸ Set.mem_image_of_mem Subtype.val h_u'_where,
    SimpleGraph.Subgraph.Adj.adj_sub (h_u'_eq ▸ (H.coe_adj u' v) ▸ h_u'_adj) ⟩

theorem isDegenerate_subgraph (G : SimpleGraph V) (H : G.Subgraph) (d : ℕ) :
    IsDegenerate G d → IsDegenerate H.coe d := fun h =>
      (isDegenerate_iff_isDegenerate' H.coe d).mpr
        ((isDegenerate_subgraph' G H d)
          ((isDegenerate_iff_isDegenerate' G d).mp h))

/- This one is the same as isDegenerate_subgraph', but it is proven directly from the definition
   as an exercise. Quite an ugly type-casting exercise. -/
theorem isDegenerate_subgraph_exercise (G : SimpleGraph V) (H : G.Subgraph) (d : ℕ) :
    IsDegenerate G d → IsDegenerate H.coe d := by
  intro h K h_K_neq_bot
  let K' := H.coeSubgraph K
  have h_verts_equal : (K.verts : Set V) = K'.verts := by trivial
  have h_verts_equal' : K.verts = Subtype.val⁻¹' K'.verts := by
    rw [← h_verts_equal, Set.preimage_image_eq _ Subtype.val_injective]
  have h_K'_neq_bot : K' ≠ ⊥ :=
    K'.ne_bot_iff_nonempty_verts.mpr (Set.Nonempty.image _
      (K.ne_bot_iff_nonempty_verts.mp h_K_neq_bot))
  obtain ⟨ v, ⟨ hv_where, hv_deg ⟩ ⟩ := h K' h_K'_neq_bot
  have h_K_subset_H : (K.verts : Set V) ⊆ H.verts := by simp
  have h_v_in_Hverts : v ∈ H.verts := h_K_subset_H hv_where
  let v' := H.vert v h_v_in_Hverts
  refine ⟨ v', h_verts_equal' ▸  hv_where, le_trans ?_ hv_deg ⟩
  suffices h_nei_subset : (K.neighborSet v' : Set V) ⊆ K'.neighborSet v by
    unfold SimpleGraph.Subgraph.degree
    simp only [← Set.toFinset_card, ← Set.ncard_eq_toFinset_card',
               ← (Set.ncard_image_of_injective _ Subtype.val_injective),
               Set.ncard_le_ncard h_nei_subset]
  intro x hx
  unfold SimpleGraph.Subgraph.neighborSet
  unfold SimpleGraph.Subgraph.neighborSet at hx
  obtain ⟨ ⟨ y, h_y_in_Hverts ⟩ , ⟨ h_y_in, h_y_eq_x ⟩ ⟩ := hx
  apply (H.coeSubgraph_adj K v x).mpr
  simp only at h_y_eq_x
  rw [h_y_eq_x] at h_y_in_Hverts
  simp only [h_y_eq_x] at h_y_in
  exact ⟨ h_v_in_Hverts, h_y_in_Hverts, h_y_in ⟩

/- Helper lemmata for induction on the number of vertices -/
lemma card_top_of_fincard_V {n : ℕ} (hcard : Fintype.card V = n) (G : SimpleGraph V) :
  (⊤ : G.Subgraph).verts.ncard = n := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card,
          SimpleGraph.Subgraph.verts_top, Fintype.card_setUniv]
    exact hcard

lemma card_del_one_vertex {n : ℕ} (hcard : Fintype.card V = n + 1) (G : SimpleGraph V) (v : V) :
  Fintype.card ((⊤ : G.Subgraph).deleteVerts {v}).verts = n := by
  rw [← Set.toFinset_card, ← Set.ncard_eq_toFinset_card',
      SimpleGraph.Subgraph.deleteVerts_verts, Set.ncard_diff_singleton_of_mem (by trivial),
      card_top_of_fincard_V hcard]
  rfl

theorem colorable_of_isDegenerate (G : SimpleGraph V) (d : ℕ) :
    IsDegenerate G d -> G.Colorable (d+1) := by
  induction hcard : Fintype.card V generalizing V with
  | zero =>
    exact fun _ => @SimpleGraph.Colorable.of_isEmpty V G (Fintype.card_eq_zero_iff.mp hcard) (d + 1)
  | succ n ih =>
    intro h_G_deg
    /- Take v from degeneracy assumption, remove it, and apply induction -/
    obtain ⟨ v, ⟨ _, h_deg_v ⟩  ⟩ := h_G_deg (⊤ : G.Subgraph)
      ((⊤ : G.Subgraph).ne_bot_iff_nonempty_verts.mpr ((⊤ : G.Subgraph).verts.ncard_pos.mp
        ((card_top_of_fincard_V hcard G) ▸ (Nat.succ_pos n))))
    let G' := (⊤ : G.Subgraph).deleteVerts {v}
    obtain ⟨ f' ⟩ :=
      ih G'.coe (card_del_one_vertex hcard G v) (isDegenerate_subgraph G G' d h_G_deg)
    /- Helper lemma -/
    have h_not_v_in_G' : ∀ x, x ≠ v → x ∈ G'.verts :=
      fun _ hx => Set.mem_diff_of_mem (by trivial) hx
    /- Find a color for v: one not used in its neighbors -/
    let nv := G.neighborSet v
    have h_nv_card : (G.neighborSet v).ncard ≤ d := by
      rw [← SimpleGraph.Subgraph.neighborSet_top, Set.ncard_eq_toFinset_card', Set.toFinset_card]
      exact h_deg_v
    let used_cols := f' '' (Subtype.val⁻¹' nv)
    have h_used_cols_card : used_cols.ncard < (Set.univ : Set (Fin (d+1))).ncard := by
      calc
      _ ≤ (Subtype.val⁻¹' nv).ncard := Set.ncard_image_le
      _ ≤ nv.ncard := by
        refine ENat.toNat_le_toNat (Set.encard_preimage_val_le_encard_right G'.verts nv) ?_
        simp only [ne_eq, Set.encard_eq_top_iff, Set.not_infinite, nv.toFinite]
      _ ≤ d := h_nv_card
      _ < (Set.univ : Set (Fin (d+1))).ncard := by simp
    obtain ⟨ a, ⟨ _, h_a_unused ⟩ ⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard h_used_cols_card
    /- Define a prospective coloring of G and prove its properties -/
    let f : V → Fin (d+1) := fun u => if h : u = v then a else f' ⟨ u, h_not_v_in_G' u h ⟩
    refine Fintype.card_fin (d + 1) ▸ (SimpleGraph.Coloring.mk f ?_).colorable
    /- Helper lemmata -/
    have h_f_f'_equal: ∀ x : V, ∀ hx: x ∈ G'.verts, f' ⟨ x, hx ⟩ = f x := fun _ hx =>
      Eq.symm (dif_neg (Set.mem_diff_singleton.mp
        (SimpleGraph.Subgraph.deleteVerts_verts ▸ hx)).right)
    have h_fv_eq_a : f v = a := by exact (Ne.dite_eq_left_iff fun h a ↦ h rfl).mpr rfl
    /- Prove that coloring is proper at v -/
    have h_f_v_valid : ∀ x : V, G.Adj v x → f v ≠ f x := by
      intro x h_adj
      have h_x_in_G' : x ∈ G'.verts := h_not_v_in_G' x (G.ne_of_adj h_adj.symm)
      have h_x_in_nv : x ∈ nv := h_adj
      grind
    /- Final proof that f is proper -/
    intro x y h_adj
    by_cases h₁ : x = v
    · exact h₁ ▸ h_f_v_valid y (h₁ ▸ h_adj)
    by_cases h₂ : y = v
    · exact h₂ ▸ (h_f_v_valid x (h₂ ▸ h_adj.symm)).symm
    rw [← h_f_f'_equal x (h_not_v_in_G' x h₁), ← h_f_f'_equal y (h_not_v_in_G' y h₂)]
    refine f'.valid ?_
    simp only [SimpleGraph.Subgraph.coe_adj]
    exact SimpleGraph.Subgraph.deleteVerts_adj.mpr ⟨ by trivial, h₁, by trivial, h₂, h_adj ⟩

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
    let h_G_deg' := (isDegenerate_iff_isDegenerate' G d).mp h_G_deg
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
      apply isDegenerate_subgraph
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
    have h_o_to_o': ∀ u₁ u₂ : V, ∀ h₁ : ¬u₁ = v, ∀ h₂ : ¬u₂ = v, o.le u₁ u₂ →
      @LE.le {x // x ∈ G'.verts} o'.toLE (⟨ u₁, h_not_v_in_G' u₁ h₁ ⟩ : {x // x ∈ G'.verts})
        (⟨ u₂, h_not_v_in_G' u₂ h₂ ⟩ : {x // x ∈ G'.verts}) := by grind
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
      have h_u_in_G' : ∀ u, u < w → u ∈ G'.verts := fun u hu => h_not_v_in_G' u (h_u_neq_v u hu)
      let how := ho' ⟨ w, h_not_v_in_G' w h ⟩
      have h_incl : ∀ u, ∀ h_w_adj_u : G.Adj w u, ∀ h_u_lt_w : u < w,
          G'.coe.Adj ⟨ w, h_not_v_in_G' w h ⟩ ⟨ u, (h_u_in_G' u h_u_lt_w) ⟩ ∧
            @LT.lt (↑G'.verts) o'.toLT ⟨ u, (h_u_in_G' u h_u_lt_w) ⟩ ⟨ w, h_not_v_in_G' w h ⟩ := by
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
        · have h_u_ne_v : ¬ u = v := h_u_neq_v u h_u_lt_w
          let h_u'_le_w' := h_o_to_o' u w h_u_ne_v h (Std.le_of_lt h_u_lt_w)
          exact @lt_of_le_of_ne (↑G'.verts) o'.toPartialOrder ⟨ u, h_not_v_in_G' u h_u_ne_v ⟩
            ⟨ w, h_not_v_in_G' w h ⟩ h_u'_le_w' (by grind)
      let S := {u | G.Adj w u ∧ u < w}
      let S' := {u' | G'.coe.Adj ⟨ w, h_not_v_in_G' w h ⟩ u' ∧
            @LT.lt (↑G'.verts) o'.toLT u' ⟨ w, h_not_v_in_G' w h ⟩}
      have h_S_to_G' : ∀ u ∈ S, u ∈ G'.verts := by
        intro u ⟨ _ , h_u_lt_w ⟩
        exact h_u_in_G' u h_u_lt_w
      let f (u : S) := (⟨ u.val, h_S_to_G' u.val u.property ⟩ : G'.verts)
      have h_f_inj : Function.Injective f := Set.inclusion_injective h_S_to_G'
      have h_f_S_to_S' : Set.range f ⊆ S' := by
        refine Set.range_subset_iff.mpr ?_
        intro u
        exact h_incl u u.property.left u.property.right
      have h_f_ncard : (Set.range f).ncard = S.ncard := by
        have h_f_ncard' := Set.ncard_image_of_injective (Set.univ : Set S) h_f_inj
        rw [Set.image_univ, Set.ncard_univ] at h_f_ncard'
        exact h_f_ncard'
      rw [← h_f_ncard]
      exact le_trans (Set.ncard_le_ncard h_f_S_to_S') how
  · rintro ⟨ o, ho ⟩
    suffices h : IsDegenerate' G d by exact (isDegenerate_iff_isDegenerate' G d).mpr h
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
