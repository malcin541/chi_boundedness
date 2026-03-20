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

def is_Pt_free (t : ℕ) (G : SimpleGraph V) : Prop := is_H_free (Pt t) G

lemma pt_hereditary (t₁ t₂ : ℕ) (h_t_mon : t₁ ≤ t₂) : has_H_induced_subgraph (Pt t₁) (Pt t₂) := by
  use {i : Fin t₂ | (i : ℕ) < t₁}
  refine ⟨(SimpleGraph.induceUnivIso (Pt t₁)).symm.trans ?_⟩
  exact
    { toEquiv :=
        { toFun := fun a => Fin.castLEquiv h_t_mon a.1
          invFun := fun b => ⟨(Fin.castLEquiv h_t_mon).symm b, by simp⟩
          left_inv := fun a => by ext; simp
          right_inv := fun b => by ext; simp }
      map_rel_iff' := by simp [Pt] }

lemma is_Pt_free_mon (t₁ t₂ : ℕ) (h_t_mon : t₁ ≤ t₂) {G : SimpleGraph V} :
    is_Pt_free t₁ G → is_Pt_free t₂ G :=
  fun h hp => h (has_H_is_mon (Pt t₁) (Pt t₂) G (pt_hereditary t₁ t₂ h_t_mon) hp)

def path_isInduced (G : SimpleGraph V) {u v : V} (p : G.Walk u v) :=
  p.IsPath ∧ (∀ x y : V , x ∈ p.support → y ∈ p.support → G.Adj x y → (s(x, y) ∈ p.edges))

lemma pt_of_inducedPath {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    path_isInduced G p → Nonempty (G.induce (p.support.toFinset) ≃g Pt (p.length + 1)) := by
  rintro ⟨hp_path, hp_induced⟩
  let supp : Set V := ↑(p.support.toFinset)
  let f : Fin (p.length + 1) → supp := fun i => ⟨ p.getVert i, by simp [supp] ⟩
  let e : Fin (p.length + 1) ≃ supp := Equiv.ofBijective f
    ⟨ fun i j hij => Fin.ext <| hp_path.getVert_injOn
        (Nat.lt_succ_iff.mp i.isLt) (Nat.lt_succ_iff.mp j.isLt) <| by
          simpa [f] using congrArg Subtype.val hij,
      fun x => by
      obtain ⟨n, hxn, hn⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
                              (by simpa [supp] using x.2)
      exact ⟨⟨n, Nat.lt_succ_of_le hn⟩, Subtype.ext <| by simpa [f] using hxn⟩ ⟩
  let eIso : Pt (p.length + 1) ≃g G.induce supp :=
    { toEquiv := e
      map_rel_iff' := by
        intro i j
        constructor
        · intro hij
          have hsub : p.toSubgraph.Adj (e i).1 (e j).1 :=
            SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr
              (hp_induced (e i) (e j) (by simpa [supp] using (e i).2)
                (by simpa [supp] using (e j).2) (by simpa using hij))
          have hneq : i ≠ j := fun h => (h ▸ hsub).ne rfl
          by_cases hi0 : (i : ℕ) = 0
          · right
            have hsnd : p.getVert 1 = p.getVert j := by
              simpa [SimpleGraph.Walk.snd, e, f] using
                hp_path.snd_of_toSubgraph_adj (by simpa [e, f, hi0] using hsub)
            have : (j : ℕ) = 1 := hp_path.getVert_injOn
              (by simpa using Nat.lt_succ_iff.mp j.isLt)
              (by apply Nat.succ_le_of_lt; omega)
              hsnd.symm
            omega
          · by_cases hilt : (i : ℕ) < p.length
            · have hjmem : p.getVert j ∈ p.toSubgraph.neighborSet (p.getVert i) := by
                simpa using hsub
              rw [hp_path.neighborSet_toSubgraph_internal hi0 hilt] at hjmem
              rcases hjmem with hprev | hnext
              · left
                have : (j : ℕ) = i - 1 := hp_path.getVert_injOn
                  (by simpa using Nat.lt_succ_iff.mp j.isLt) (by
                    change (i : ℕ) - 1 ≤ p.length
                    exact (Nat.sub_le _ _).trans (Nat.lt_succ_iff.mp i.isLt)) hprev
                omega
              · right
                have : (j : ℕ) = i + 1 := hp_path.getVert_injOn
                  (by simpa using Nat.lt_succ_iff.mp j.isLt) (Nat.succ_le_of_lt hilt) hnext
                omega
            · left
              have hiel : (i : ℕ) = p.length := by omega
              have hlenpos : 0 < p.length := by omega
              have hjmem : p.getVert j ∈ p.toSubgraph.neighborSet v := by
                simpa [SimpleGraph.Subgraph.mem_neighborSet, hiel, e, f] using hsub
              rw [hp_path.neighborSet_toSubgraph_endpoint (by
                simpa [SimpleGraph.Walk.not_nil_iff_lt_length] using hlenpos)] at hjmem
              have : (j : ℕ) = p.length - 1 := hp_path.getVert_injOn
                (by simpa using Nat.lt_succ_iff.mp j.isLt) (Nat.sub_le _ _) <| by
                  simpa [SimpleGraph.Walk.penultimate] using hjmem
              omega
        · intro hij
          rcases hij with hji | hij
          · simpa [e, f, Pt, hji] using (p.adj_getVert_succ (i := j) (by omega)).symm
          · simpa [e, f, Pt, hij] using p.adj_getVert_succ (i := i) (by omega) }
  exact ⟨eIso.symm⟩

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
    · obtain ⟨ v, h_v_in_cc ⟩  := cc.nonempty_supp
      use ⟨ v, h_v_in_cc ⟩
      intro ⟨ w, h_w_in_cc ⟩ p h_p_induced
      obtain ⟨f⟩ := pt_of_inducedPath p h_p_induced
      sorry


end Gyarfas
