import Overfull.PrescribedMatching.Components
import Overfull.PrescribedMatching.Matching
import Overfull.PrescribedMatching.Selection

/-!
# Prescribed exceptional--core matching edges

This proves manuscript Lemma 4.8. Actual short paths give a bounded
vertex witness for core connectivity. The prescribed matching is
restricted to edges avoiding that witness, and the resulting graph
satisfies Tutte's inequality for every vertex-deletion set. An actual
perfect matching then retains all but at most 135720 prescribed edges.
-/

namespace Overfull.PrescribedMatching

open Finset Classical SimpleGraph

variable {V I : Type*} [Fintype V] [Fintype I]

/-- A matching avoiding the retained core-connection witness extends to
a perfect matching. The proof checks all actual Tutte deletion sets. -/
theorem complete_avoiding_witness [DecidableEq V]
    (G : SimpleGraph V) (U : I → Set V) (Z W : Finset V)
    (hcard : Fintype.card I ≤ 4) (hclique : ∀ i, G.IsClique (U i))
    (hdisjoint : ∀ i, Disjoint (U i) (Z : Set V))
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (horder : ∀ i, 2*Z.card+4 < (U i).ncard)
    (hneighbors : ∀ v ∈ Z, 2*Z.card+4 < (G.neighborSet v \ (Z : Set V)).ncard)
    (K : G.Subgraph) (hK : K.IsPerfectMatching)
    (M : G.Subgraph) (hM : M.IsMatching)
    (hMW : Disjoint M.verts (W : Set V))
    (hMcore : (M.verts \ (Z : Set V)).ncard ≤ Z.card)
    (hW : ∀ Y : Finset V, Y.card ≤ 3 → ∀ i j, i ≠ j →
      CoresConnectedOutside G U Y i j →
      ∃ a ∈ U i, ∃ b ∈ U j, ∃ p : G.Walk a b,
        p.IsPath ∧ p.support.toFinset ⊆ W ∧ ∀ x ∈ p.support, x ∉ Y) :
    ∃ N : G.Subgraph, N.IsPerfectMatching ∧ M ≤ N := by
  classical
  apply complete_of_induced_odd_bounds G M hM
  intro Y
  let X : Set V := Subtype.val '' Y
  have hXcard : X.ncard = Y.ncard := Set.ncard_image_of_injective Y Subtype.val_injective
  have hDcard : ((M.verts ∪ X) \ (Z : Set V)).ncard ≤ Z.card + Y.ncard := by
    exact (deleted_core_union_bound M.verts X (Z : Set V)).trans
      (by omega)
  by_cases hsmall : Y.ncard ≤ 3
  · have hXsmall : X.ncard ≤ 3 := by omega
    have hdeleted : ((M.verts ∪ X) \ (Z : Set V)).ncard < 2*Z.card+4 := by omega
    have hattach := core_attachment_after_deletion G U Z (M.verts ∪ X)
      hcover hneighbors hdeleted
    have hreflect := reachable_reflection_of_witness G U W M.verts X
      hclique hMW hW hXsmall hattach
    have hXdeleted : (X \ (Z : Set V)).ncard < 2*Z.card+4 := by
      have hle := Set.ncard_le_ncard (Set.diff_subset (s := X) (t := (Z : Set V)))
        (Set.toFinite X)
      omega
    have hattachOriginal := core_attachment_after_deletion G U Z X hcover hneighbors hXdeleted
    have hcore : ∀ i, ∃ a ∈ U i, a ∉ M.verts ∪ X := by
      intro i
      exact exists_core_outside (U i) (Z : Set V) (M.verts ∪ X)
        (hdisjoint i) (hdeleted.trans (horder i))
    have hsurvive := component_has_survivor G U M.verts X hclique hattachOriginal hcore
    exact remaining_odd_bound G K hK M hM Y hreflect hsurvive
  · have hfour : 4 ≤ Y.ncard := by omega
    rw [remainingDeletion_oddComponents G M.verts Y]
    calc
      (G.induce (M.verts ∪ X)ᶜ).oddComponents.ncard ≤
          Nat.card (G.induce (M.verts ∪ X)ᶜ).ConnectedComponent :=
        Set.ncard_le_card _
      _ ≤ Y.ncard := by
        by_cases hmedium : Y.ncard < Z.card+4
        · have hdeleted : ((M.verts ∪ X) \ (Z : Set V)).ncard < 2*Z.card+4 := by omega
          have hattach := core_attachment_after_deletion G U Z (M.verts ∪ X)
            hcover hneighbors hdeleted
          exact (component_card_le_after_attachment G U (M.verts ∪ X) hclique hattach).trans
            (hcard.trans hfour)
        · have hle := component_card_le_cores_add_exceptional G U Z hclique hcover
            (M.verts ∪ X)
          omega

end Overfull.PrescribedMatching

namespace Overfull

open Finset Classical SimpleGraph PrescribedMatching

variable {V I : Type*} [Fintype V] [Fintype I]

/-- **Manuscript Lemma 4.8.** In a graph covered by at most four large
core cliques and an exceptional set, an actual perfect matching retains
all but at most 135720 prescribed exceptional--core edges.

The hypotheses below also allow edges with both endpoints exceptional,
and overlapping core cliques: the proof only uses a clique cover outside
the exceptional set. -/
theorem prescribed_exceptional_core_matching
    (G : SimpleGraph V) (U : I → Set V) (Z : Finset V)
    (hcard : Fintype.card I ≤ 4) (hclique : ∀ i, G.IsClique (U i))
    (hdisjoint : ∀ i, Disjoint (U i) (Z : Set V))
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (horder : ∀ i, 2*Z.card+4 < (U i).ncard)
    (hneighbors : ∀ v ∈ Z, 2*Z.card+4 < (G.neighborSet v \ (Z : Set V)).ncard)
    (hperfect : ∃ K : G.Subgraph, K.IsPerfectMatching)
    (M : G.Subgraph) (hM : M.IsMatching)
    (hincident : ∀ u v, M.Adj u v → u ∈ Z ∨ v ∈ Z) :
    ∃ N : G.Subgraph, N.IsPerfectMatching ∧ (M.edgeSet \ N.edgeSet).ncard ≤ 135720 := by
  classical
  obtain ⟨K,hK⟩ := hperfect
  have hattach : ∀ Y : Finset V, Y.card ≤ 3 → ∀ v, v ∉ Y →
      ∃ i, ∃ a ∈ U i, a ∉ Y ∧ (v = a ∨ G.Adj v a) := by
    intro Y hY
    apply core_attachment_after_deletion G U Z (Y : Set V) hcover hneighbors
    have hle : ((Y : Set V) \ (Z : Set V)).ncard ≤ Y.card := by
      simpa only [Set.ncard_coe_finset] using
        Set.ncard_le_ncard (Set.diff_subset (s := (Y : Set V)) (t := (Z : Set V)))
          (Set.toFinite (Y : Set V))
    omega
  obtain ⟨W,hWcard,hW⟩ := exists_core_connection_witness G U hcard hclique hattach
  obtain ⟨M',hM',_hM'sub,hM'W,homitted,hM'core⟩ :=
    select_prescribed_matching G M hM Z W hincident
  obtain ⟨N,hN,hM'N⟩ := complete_avoiding_witness G U Z W hcard hclique
    hdisjoint hcover horder hneighbors K hK M' hM' hM'W hM'core hW
  refine ⟨N,hN,?_⟩
  calc
    (M.edgeSet \ N.edgeSet).ncard ≤ (M.edgeSet \ M'.edgeSet).ncard :=
      omitted_edges_le_of_extension G M M' N hM'N
    _ ≤ W.card := homitted
    _ ≤ 135720 := hWcard

end Overfull
