import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Set.Card
import Mathlib

open Finset Fintype

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

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
