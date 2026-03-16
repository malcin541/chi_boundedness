import Mathlib
import ChiBoundedness.Tools
import ChiBoundedness.Basic

set_option linter.style.openClassical false
set_option linter.unusedFintypeInType false

section Gyarfas

variable {V : Type*} [Fintype V]

open Classical

def isInducedPath (G : SimpleGraph V) : Prop :=  G.Preconnected ∧ G.maxDegree ≤ 2

def Pt (t : ℕ) : SimpleGraph (Fin t) where
  Adj v w := (v.val = w.val + 1) ∨ (w.val = v.val + 1)
  symm _ _ := fun h => h.elim Or.inr Or.inl
  loopless := fun v h => Nat.succ_ne_self v.val ((h.elim id id).symm)

def is_Pt_free (t : ℕ) (G : SimpleGraph V) : Prop := is_H_free G (Pt t)

def path_isInduced (G : SimpleGraph V) {u v : V} (p : G.Walk u v) :=
  p.IsPath ∧ (∀ x y : V , x ∈ p.support → y ∈ p.support → G.Adj x y → (s(x, y) ∈ p.edges))

lemma pt_of_inducedPath {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    path_isInduced G p → Nonempty (G.induce (p.support.toFinset) ≃g Pt (p.length + 1)) := by
  sorry

lemma gyarfas_step (G : SimpleGraph V) (hconn : G.Preconnected) {a t : ℕ}
    (h_nei : ∀ w : V, (G.induce (G.neighborSet w)).chromaticNumber ≤ a)
    (h_path : ∃ v : V, ∀ w : V, ∀ p : G.Walk v w, path_isInduced G p → p.length < t) :
    G.Colorable (1 + a * t) := by
  sorry

theorem chiBoundedness_Pt_free (G : SimpleGraph V) (t : ℕ) (h : is_Pt_free (t + 1) G) :
  G.chromaticNumber ≤ (t + 1) ^ G.cliqueNum := by
  induction hω : G.cliqueNum generalizing V with
  | zero =>
    suffices hV : IsEmpty V by
      rw [SimpleGraph.chromaticNumber_eq_zero_of_isEmpty (G := G)]
      simp
    constructor
    intro v
    let s : Finset V := {v}
    have hclique : G.IsClique (↑s : Set V) := by simp [G.isClique_singleton v, s]
    have hs' : s.card ≤ G.cliqueNum := hclique.card_le_cliqueNum
    simp [s, hω] at hs'
  | succ k ih =>
    refine G.chromaticNumber_le_iff_colorable.mpr ?_
    refine G.colorable_iff_forall_connectedComponents.mpr ?_
    intro cc
    refine SimpleGraph.Colorable.mono ?_ (gyarfas_step cc.toSimpleGraph
      cc.connected_toSimpleGraph.preconnected (a := (t + 1)^k) (t := t) ?_ ?_)
    · calc
        1 + (t + 1) ^ k * t ≤ (t + 1) ^ k + (t + 1) ^ k * t := by
          exact Nat.add_le_add_right (Nat.one_le_pow' k t) _
        _ = (t + 1) ^ (k + 1) := by
          rw [Nat.pow_succ, Nat.mul_add, Nat.mul_one, Nat.add_comm]
    · intro w
      apply ih
      · sorry
      · sorry
    · sorry


end Gyarfas
