import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Set.Card
import Mathlib

open Finset Fintype

set_option diagnostics true

def has_H_induced_subgraph {V W : Type*} [Finite W] (H : SimpleGraph W)
  (G : SimpleGraph V) := ∃s : Set V, Nonempty (H ≃g (G.induce s))

def is_H_free {V W : Type*} [Finite W] (H : SimpleGraph W)
  (G : SimpleGraph V) := ¬(has_H_induced_subgraph H G)

lemma is_H_free_hereditary {V W : Type*} [Finite W] (H : SimpleGraph W)
    (G : SimpleGraph V) (s : Set V) : is_H_free H G → is_H_free H (G.induce s) := by
  intro hfree ⟨t, ⟨e⟩⟩
  exact hfree ⟨Subtype.val '' t, ⟨e.trans
    { toEquiv := Equiv.Set.image Subtype.val t Subtype.val_injective
      map_rel_iff' := by intro a b; rfl }⟩⟩

/- Some unimportant stuff needed because SimpleGraph can be infinite -/
lemma finite_graph_chromaticNumber_ne_top {V : Type*} [Finite V] (G : SimpleGraph V) :
    G.chromaticNumber ≠ ⊤ := by
  rw [G.chromaticNumber_ne_top_iff_exists]
  haveI := Fintype.ofFinite V
  use Fintype.card V
  exact G.colorable_of_fintype

lemma size_le_chromaticNumber_times_indepNumber {V : Type*} [Finite V] (G : SimpleGraph V) :
    Nat.card V ≤ G.chromaticNumber.toNat * G.indepNum := by
  /- Define optimum set of colors and coloring -/
  set opt_coloring : G.Coloring (Fin G.chromaticNumber.toNat) :=
    (G.colorable_chromaticNumber_of_fintype).toColoring (by simp)
  have h_opt_colors_eq_chi : G.chromaticNumber = Fintype.card (Fin G.chromaticNumber.toNat) := by
    simp [ENat.coe_toNat, finite_graph_chromaticNumber_ne_top]
  /- Apply the crucial cardinality multiplication lemma -/
  haveI := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card, h_opt_colors_eq_chi, ENat.toNat_coe, Nat.mul_comm]
  refine Finset.card_le_mul_card_image_of_maps_to (f := opt_coloring) (by simp) G.indepNum ?_
  /- Conclude that a color class has cardinality at most G.indepNum.
     This should be easy, but there is some tricky typecasting between Finset and Set V -/
  intro cc
  have h_indepSet : G.IsIndepSet (opt_coloring.colorClass cc).toFinset := by
    simpa [SimpleGraph.isIndepSet_iff_isAntichain_adj, Set.coe_toFinset] using
      opt_coloring.color_classes_independent cc
  simpa [SimpleGraph.Coloring.colorClass] using h_indepSet.card_le_indepNum
