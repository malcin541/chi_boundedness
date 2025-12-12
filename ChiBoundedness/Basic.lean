import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Set.Card
import Mathlib

open Finset Fintype

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

set_option diagnostics true

/- Some unimportant stuff needed because SimpleGraph can be infinite -/
lemma finite_graph_chromaticNumber_ne_top :
    G.chromaticNumber ≠ ⊤ := by
  rw [G.chromaticNumber_ne_top_iff_exists]
  use Fintype.card V
  exact G.colorable_of_fintype

lemma size_le_chromaticNumber_times_indepNumber :
    Fintype.card V ≤ G.chromaticNumber.toNat * G.indepNum := by
  have hcol : G.Colorable G.chromaticNumber.toNat := by
    exact G.colorable_of_chromaticNumber_ne_top finite_graph_chromaticNumber_ne_top
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
    simp_all
    exact h_cc_small

def IsDegenerate (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ (H : G.Subgraph) [DecidableRel H.Adj], H ≠ ⊥
    → ∃ v ∈ H.verts, (H.degree v) ≤ d

theorem empty_zero_degenerate (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
     (G = ⊥) → IsDegenerate G d := by
  unfold IsDegenerate
  intro h_Gbot H inst h_Hbot
  rw [H.ne_bot_iff_nonempty_verts] at h_Hbot
  obtain ⟨ x, hx ⟩ := h_Hbot
  use x
  constructor
  · exact hx
  · have hh : G.degree x = 0 := by
      subst h_Gbot
      convert SimpleGraph.bot_degree x
    have h_le : H.degree x ≤ G.degree x := H.degree_le x
    rw [hh] at h_le
    exact le_trans h_le (Nat.zero_le d)

theorem mon_degeneracy (d₁ d₂ : ℕ) : IsDegenerate G d₁ → d₁ ≤ d₂ → IsDegenerate G d₂ := by
  intro h₁ h₂ H inst h_bot
  obtain ⟨ v, hv, hdeg ⟩ := h₁ H h_bot
  use v
  constructor
  · exact hv
  · exact le_trans hdeg h₂

theorem degeneracy_le_maxDegree [DecidableRel G.Adj] : IsDegenerate G G.maxDegree := by
  unfold IsDegenerate
  intro H insta h_bot
  rw [H.ne_bot_iff_nonempty_verts] at h_bot
  obtain ⟨ x, hx ⟩ := h_bot
  use x
  constructor
  · exact hx
  · exact le_trans (H.degree_le x) (G.degree_le_maxDegree x)

theorem degeneracy_subgraph_monotone [DecidableRel G.Adj] (d : ℕ)
  (H : G.Subgraph) [DecidableRel H.Adj] [DecidablePred (· ∈ H.verts)] :
    IsDegenerate G d → IsDegenerate H.coe d := by
  classical
  intro h_Gdeg K inst h_Kbot
  let K' := H.coeSubgraph K
  have h_K'bot : K' ≠ ⊥ := by
    rw [K'.ne_bot_iff_nonempty_verts]
    rw [K.ne_bot_iff_nonempty_verts] at h_Kbot
    aesop_graph
  obtain h := h_Gdeg K' h_K'bot
  obtain ⟨ v, hv_mem, hv_deg ⟩ := h
  have hv_image : v ∈ Subtype.val '' K.verts := hv_mem
  obtain ⟨x, hx_in_K, hx_eq⟩ := hv_image
  use x
  constructor
  · exact hx_in_K
  · rw [← hx_eq] at hv_deg
    have h_Kverts_equal : K.verts = K'.verts := by aesop_graph
    have h_neiSets_equal : K'.neighborSet x = K.neighborSet x := by
      have h_nei_iff_nei' : ∀ w : H.verts, ↑w ∈ K'.neighborSet x ↔ w ∈ K.neighborSet x := by
        aesop_graph
      apply Set.ext_iff.mpr
      intro y
      by_cases hy : (y ∈ H.verts)
      · simp_all
      · have h₁ : y ∉ K'.neighborSet x := by
          have h₃ : y ∉ K'.verts := by grind
          exact Set.notMem_subset (K'.neighborSet_subset_verts x) h₃
        have h₂ : y ∉ ↑(Subtype.val '' K.neighborSet x) := by grind
        simp [h₁, h₂]
    have h_degrees_equal : K'.degree x = K.degree x := by
      rw [← K'.finset_card_neighborSet_eq_degree]
      rw [← K.finset_card_neighborSet_eq_degree]
      simp [h_neiSets_equal]
      --  ⊢ #(image Subtype.val (K.neighborSet x).toFinset) = Fintype.card ↑(K.neighborSet x)
      refine card_eq_of_equiv_fintype ?_
      --  ⊢ ↥(image Subtype.val (K.neighborSet x).toFinset) ≃ ↑(K.neighborSet x)
      sorry
    rw [← h_degrees_equal]
    -- Lean error:
    -- Tactic `rewrite` failed: Did not find an occurrence of the pattern
    --    K.degree x
    -- in the target expression
    --    K.degree x ≤ d
    sorry
