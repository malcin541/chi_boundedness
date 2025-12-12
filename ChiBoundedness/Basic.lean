import Mathlib

open Finset Fintype

variable {V : Type*} [Fintype V] [DecidableEq V] [Inhabited V]

-- variable {G : SimpleGraph V} {H : SimpleGraph V}

-- variable [iFinEdgeG : ∀ v : V, Fintype (G.neighborSet v)]
-- variable [iFinEdgeH : ∀ v : V, Fintype (H.neighborSet v)]

-- variable [iDecGAdj : DecidableRel G.Adj]
-- variable [iDecHAdj : DecidableRel H.Adj]




omit [DecidableEq V] [Inhabited V] in
/- Some unimportant stuff needed because SimpleGraph can be infinite -/
lemma finite_graph_chromaticNumber_ne_top
    (G : SimpleGraph V) :
    G.chromaticNumber ≠ ⊤ := by
  rw [G.chromaticNumber_ne_top_iff_exists]
  use Fintype.card V
  exact G.colorable_of_fintype



omit [DecidableEq V] [Inhabited V] in
-- omit iDecV iInhabV iFinEdgeG iDecGAdj in
lemma size_le_chromaticNumber_times_indepNumber
    (G : SimpleGraph V) :
    Fintype.card V ≤ G.chromaticNumber.toNat * G.indepNum := by
  have hcol : G.Colorable G.chromaticNumber.toNat := by
    exact G.colorable_of_chromaticNumber_ne_top (finite_graph_chromaticNumber_ne_top G)
  /- Define optimum set of colors and coloring -/
  let opt_colors := Fin G.chromaticNumber.toNat
  have h_opt_colors_eq_chi : G.chromaticNumber = Fintype.card opt_colors := by
    simp [opt_colors, ENat.coe_toNat, finite_graph_chromaticNumber_ne_top]
  have h_opt_sufficient : (G.chromaticNumber.toNat ≤ Fintype.card opt_colors) := by
    simp [opt_colors]
  let opt_coloring : G.Coloring opt_colors := hcol.toColoring h_opt_sufficient
  /- Each color class is of size at most the independence number -/
  have h_cc_small : ∀ n, (#(Set.toFinset (opt_coloring.colorClass n)) ≤ G.indepNum) := by
    intro n
    let cc := (opt_coloring.colorClass n).toFinset
    have h_cc_indep : G.IsIndepSet cc := by
      rw [G.isIndepSet_iff, Set.coe_toFinset]
      exact opt_coloring.color_classes_independent n
    exact h_cc_indep.card_le_indepNum
  /- Rewrite the target slightly -/
  rw [h_opt_colors_eq_chi, Nat.mul_comm]
  simp
  /- Conclude the proof -/
  apply Finset.card_le_mul_card_image_of_maps_to (f := opt_coloring)
  case Hf => simp
  case hn =>
    simp_all only [Set.toFinset_card, card_ofFinset, mem_univ, SimpleGraph.completeGraph_eq_top,
      forall_const]
    exact h_cc_small

def IsDegenerate (G : SimpleGraph V) (d : ℕ)
  : Prop :=
  ∀ (H : SimpleGraph V) [DecidableRel H.Adj], (H.IsSubgraph G) → ∃ v : V, (H.degree v) ≤ d


omit [DecidableEq V] in
theorem empty_zero_degenerate (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (d : ℕ) :
    (G = ⊥) → IsDegenerate G d := by
  unfold IsDegenerate
  intro h_Gbot H inst h_sub
  simp_all
  use default
  have deg_default : H.degree default = 0 := by
    apply (SimpleGraph.degree_eq_zero_iff_notMem_support H default).mpr
    simp_all [SimpleGraph.support]
  simp [deg_default]


omit [DecidableEq V] [Inhabited V] in
theorem non_degeneracy (G : SimpleGraph V) (d₁ d₂ : ℕ)
  : IsDegenerate G d₁ → d₁ ≤ d₂ → IsDegenerate G d₂ := by
  intro h₁ h₂ H inst hsub
  unfold IsDegenerate at h₁
  specialize h₁ H hsub
  obtain ⟨ v, hdeg ⟩ := h₁
  use v
  apply le_trans hdeg
  assumption

omit [Fintype V] [DecidableEq V] [Inhabited V] in
theorem SimpleGraph.IsSubgraph.degree_le
  (G H : SimpleGraph V)
  [∀ v : V, Fintype (G.neighborSet v)]
  [∀ v : V, Fintype (H.neighborSet v)]
  (hsub : H.IsSubgraph G) :
  ∀ v : V, H.degree v  ≤ G.degree v := by
  intro v
  exact degree_le_of_le hsub


omit [DecidableEq V] [Inhabited V] in
theorem SimpleGraph.IsSubgraph.sub_degree_le_maxDegree
  (G H : SimpleGraph V)
  [∀ v : V, Fintype (H.neighborSet v)]
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
  (hsub : H.IsSubgraph G):
  ∀ v : V, H.degree v ≤ G.maxDegree := by
  intro v
  apply le_trans (degree_le G H hsub v) (G.degree_le_maxDegree v)



omit [DecidableEq V] in
theorem degeneracy_le_maxDegree
  (G : SimpleGraph V)
  [DecidableRel G.Adj]
  : IsDegenerate G G.maxDegree := by
  unfold IsDegenerate
  intro H insta hsub
  use default
  apply SimpleGraph.IsSubgraph.sub_degree_le_maxDegree
  exact hsub




omit [DecidableEq V] [Inhabited V] in
theorem degeneracy_subgraph_monotone
  (d : ℕ)
  (G H : SimpleGraph V)
  [DecidableRel H.Adj]
  (hsub : H.IsSubgraph G) :
  IsDegenerate G d → IsDegenerate H d := by
    intro h_degenerate_G
    simp [IsDegenerate]
    simp [IsDegenerate] at h_degenerate_G
    intro K iDecAdjK h_KsubH
    specialize h_degenerate_G H hsub
    obtain ⟨v, hdegHv⟩ := h_degenerate_G
    use v
    have s₁ : K.degree v ≤ H.degree v := by
      apply SimpleGraph.IsSubgraph.degree_le
      simp [h_KsubH]
    apply le_trans s₁ hdegHv
