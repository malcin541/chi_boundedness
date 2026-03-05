import Mathlib

/-
  Suggested by Bhavit Mehta and Jovan Gerbscheid in thread
  https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Hello.20.26.20graph.20coloring.20exercises/with/577466564
  Used to work around type problems where the decidability field differs.
-/

@[simp]
lemma degree_congr_decidable {V : Type*} {G : SimpleGraph V} (v : V)
    (h : Fintype (G.neighborSet v)) [h' : Fintype ↑(G.neighborSet v)] :
    @SimpleGraph.degree V G v ((fun x ↦ x) h) = @SimpleGraph.degree V G v h' := by
  convert rfl

@[grind =]
lemma degree_congr_decidable' {V : Type*} {G : SimpleGraph V} (v : V)
    (h : Fintype (G.neighborSet v)) [h' : Fintype ↑(G.neighborSet v)] :
    @SimpleGraph.degree V G v h = @SimpleGraph.degree V G v h' := by
  convert rfl
