import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Set.Card

open Finset Fintype

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/- Some unimportant stuff needed because SimpleGraph can be infinite -/
lemma finite_graph_chromaticNumber_ne_top :
    G.chromaticNumber ≠ ⊤ := by
  rw [G.chromaticNumber_ne_top_iff_exists]
  use Fintype.card V
  exact G.colorable_of_fintype

lemma size_le_chromaticNumber_times_indepNumber :
    G.chromaticNumber * G.indepNum >= Fintype.card V :=
  have hcol : G.Colorable G.chromaticNumber.toNat := by
    exact G.colorable_of_chromaticNumber_ne_top finite_graph_chromaticNumber_ne_top
  /- Define optimum set of colors and coloring -/
  let opt_colors : Finset ℕ := Finset.range G.chromaticNumber.toNat
  have h_opt_sufficient : (G.chromaticNumber.toNat ≤ Fintype.card opt_colors) := by
    simp [opt_colors]
  let opt_coloring : G.Coloring opt_colors := hcol.toColoring h_opt_sufficient
  /- Each color class is of size at most the independence number -/
  have h_cc_small : ∀ {n : ↥opt_colors},
    (Set.ncard (opt_coloring.colorClass n) ≤ G.indepNum) := by
    intro n
    let cc := (opt_coloring.colorClass n)
    let cc_f := cc.toFinset
    have h_cc_indep : G.IsIndepSet cc_f := by
      rw [G.isIndepSet_iff]
      exact opt_coloring.color_classes_independent n /- This fails if cc is replaced by cc_f -/
    exact h_cc_indep.card_le_indepNum /- This works if h_cc_indep has cc_f instead of cc -/
   sorry /- to be continued -/
