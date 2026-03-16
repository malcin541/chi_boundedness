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

theorem chiBoundedness_Pt_free (G : SimpleGraph V) (t : ℕ) (h : is_Pt_free t G) :
  G.chromaticNumber ≤ t ^ G.cliqueNum := by
  induction hω : G.cliqueNum with
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
    sorry

end Gyarfas
