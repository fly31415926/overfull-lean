import Overfull.MatchingExtension

/-!
# Selecting prescribed matching edges away from a witness

Retain exactly the matching edges with both endpoints outside the witness.
Every omitted edge has a distinct endpoint in the witness. For a matching
whose every edge meets the exceptional set, its covered vertices outside
that set inject into the exceptional set through their actual partners.
-/

namespace Overfull.PrescribedMatching

open Finset Classical SimpleGraph

variable {V : Type*}

/-- Keep precisely the matching edges whose endpoints avoid `W`; only
endpoints of the retained edges remain in the subgraph vertex set. -/
def avoidVertices (G : SimpleGraph V) (M : G.Subgraph) (W : Finset V) : G.Subgraph where
  verts := {v | ∃ w, M.Adj v w ∧ v ∉ W ∧ w ∉ W}
  Adj v w := M.Adj v w ∧ v ∉ W ∧ w ∉ W
  adj_sub h := M.adj_sub h.1
  edge_vert h := ⟨_, h⟩
  symm _ _ h := ⟨M.symm h.1, h.2.2, h.2.1⟩

theorem avoidVertices_le (G : SimpleGraph V) (M : G.Subgraph) (W : Finset V) :
    avoidVertices G M W ≤ M := by
  constructor
  · rintro v ⟨w, hw, _, _⟩
    exact M.edge_vert hw
  · intro v w h
    exact h.1

theorem avoidVertices_isMatching (G : SimpleGraph V) (M : G.Subgraph)
    (hM : M.IsMatching) (W : Finset V) : (avoidVertices G M W).IsMatching := by
  rintro v ⟨w, hw⟩
  refine ⟨w, hw, ?_⟩
  intro z hz
  exact hM.eq_of_adj_left hz.1 hw.1

theorem avoidVertices_disjoint (G : SimpleGraph V) (M : G.Subgraph) (W : Finset V) :
    Disjoint (avoidVertices G M W).verts (W : Set V) := by
  apply Set.disjoint_left.mpr
  rintro v ⟨w, _, hv, _⟩ hvW
  exact hv hvW

variable [Fintype V]

theorem avoidVertices_omitted_edges_le (G : SimpleGraph V) (M : G.Subgraph)
    (hM : M.IsMatching) (W : Finset V) :
    (M.edgeSet \ (avoidVertices G M W).edgeSet).ncard ≤ W.card := by
  classical
  have htouch (e : ↥(M.edgeSet \ (avoidVertices G M W).edgeSet)) :
      ∃ v : ↥(W : Set V), v.val ∈ e.val := by
    rcases e with ⟨e, heM, heR⟩
    induction e using Sym2.ind with
    | h a b =>
      have hab : M.Adj a b := heM
      have hnot : ¬(M.Adj a b ∧ a ∉ W ∧ b ∉ W) := heR
      by_cases ha : a ∈ W
      · exact ⟨⟨a, ha⟩, by simp⟩
      · have hb : b ∈ W := by
          by_contra hb
          exact hnot ⟨hab, ha, hb⟩
        exact ⟨⟨b, hb⟩, by simp⟩
  choose pick hpick using htouch
  have hinj : Function.Injective pick := by
    intro e f hef
    have hv : (pick e).val = (pick f).val := congrArg Subtype.val hef
    have hh := MatchingExtension.matching_edge_eq G hM
      ⟨e.val, e.property.1⟩ ⟨f.val, f.property.1⟩ (hpick e) (hv.symm ▸ hpick f)
    exact Subtype.ext (congrArg (fun q : M.edgeSet => q.val) hh)
  have hcard := Nat.card_le_card_of_injective pick hinj
  rw [← Set.ncard_coe_finset W]
  simpa only [Nat.card_coe_set_eq] using hcard

/-- Covered vertices outside an exceptional set have distinct matched
partners in that set. Edges entirely inside the exceptional set are also
allowed by this bound. -/
theorem matching_covered_outside_le (G : SimpleGraph V) (M : G.Subgraph)
    (hM : M.IsMatching) (Z : Finset V)
    (hincident : ∀ u v, M.Adj u v → u ∈ Z ∨ v ∈ Z) :
    (M.verts \ (Z : Set V)).ncard ≤ Z.card := by
  classical
  have hpartner (v : ↥(M.verts \ (Z : Set V))) :
      ∃ w : ↥(Z : Set V), M.Adj v.val w.val := by
    obtain ⟨w, hvw, _⟩ := hM v.property.1
    have hw : w ∈ Z := (hincident v w hvw).resolve_left v.property.2
    exact ⟨⟨w, hw⟩, hvw⟩
  choose partner hpartner using hpartner
  have hinj : Function.Injective partner := by
    intro v w hvw
    have heq : (partner v).val = (partner w).val := congrArg Subtype.val hvw
    exact Subtype.ext (hM.eq_of_adj_right (hpartner v) (heq.symm ▸ hpartner w))
  have hcard := Nat.card_le_card_of_injective partner hinj
  rw [← Set.ncard_coe_finset Z]
  simpa only [Nat.card_coe_set_eq] using hcard

/-- Select an actual prescribed matching outside `W`, with both the
omitted-edge bound and the sharp bound on deleted core vertices. -/
theorem select_prescribed_matching (G : SimpleGraph V) (M : G.Subgraph)
    (hM : M.IsMatching) (Z W : Finset V)
    (hincident : ∀ u v, M.Adj u v → u ∈ Z ∨ v ∈ Z) :
    ∃ R : G.Subgraph, R.IsMatching ∧ R ≤ M ∧ Disjoint R.verts (W : Set V) ∧
      (M.edgeSet \ R.edgeSet).ncard ≤ W.card ∧
      (R.verts \ (Z : Set V)).ncard ≤ Z.card := by
  refine ⟨avoidVertices G M W, avoidVertices_isMatching G M hM W,
    avoidVertices_le G M W, avoidVertices_disjoint G M W,
    avoidVertices_omitted_edges_le G M hM W, ?_⟩
  apply matching_covered_outside_le G _ (avoidVertices_isMatching G M hM W) Z
  intro u v huv
  exact hincident u v huv.1

/-- Completing the retained matching cannot increase the number of
original prescribed edges that are absent. -/
theorem omitted_edges_le_of_extension (G : SimpleGraph V) (M R K : G.Subgraph)
    (hRK : R ≤ K) :
    (M.edgeSet \ K.edgeSet).ncard ≤ (M.edgeSet \ R.edgeSet).ncard := by
  exact Set.ncard_le_ncard
    (fun e he => ⟨he.1, fun heR => he.2 (Subgraph.edgeSet_mono hRK heR)⟩)
    (Set.toFinite _)

end Overfull.PrescribedMatching
