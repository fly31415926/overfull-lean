import Overfull.ColoringExtension.Deficits
import Overfull.OrdinaryPackingWorking

/-!
# Actual matching subgraphs of a colored simple graph

The vertex set of each subgraph is exactly the vertices covered by that
color. This allows the actual uncovered sets in reserve repair to agree
with the repair sets counted by the coloring deficit lemmas.
-/

namespace Overfull.OrdinaryFactorization

open Finset Classical SimpleGraph
open scoped BigOperators
open OrdinaryPackingWorking BipartitePackingAccounting

variable {V : Type*} [Fintype V] {r : ℕ}

/-- Lift one actual color class to the ambient host, retaining exactly its
covered vertices and its original unordered edges. -/
noncomputable def colorMatching (G J : SimpleGraph V) (hJG : J ≤ G)
    (c : (Multigraph.ofSimpleGraph J).EdgeColoring r) (i : Fin r) : G.Subgraph where
  verts := c.coveredVertices i
  Adj u v := ∃ h : J.Adj u v, c.color (⟨s(u, v), h⟩ : J.edgeSet) = i
  adj_sub := fun h => hJG h.choose
  edge_vert := by
    rintro u v ⟨huv, hc⟩
    exact (c.mem_coveredVertices i u).mpr ⟨⟨s(u, v), huv⟩, hc, by simp [Multigraph.ofSimpleGraph]⟩
  symm := by
    rintro u v ⟨huv, hc⟩
    refine ⟨huv.symm, ?_⟩
    have he : (⟨s(v, u), huv.symm⟩ : J.edgeSet) = ⟨s(u, v), huv⟩ :=
      Subtype.ext Sym2.eq_swap
    rw [he]
    exact hc

@[simp] theorem colorMatching_verts (G J : SimpleGraph V) (hJG : J ≤ G)
    (c : (Multigraph.ofSimpleGraph J).EdgeColoring r) (i : Fin r) :
    (colorMatching G J hJG c i).verts = (c.coveredVertices i : Set V) := rfl

@[simp] theorem colorMatching_adj (G J : SimpleGraph V) (hJG : J ≤ G)
    (c : (Multigraph.ofSimpleGraph J).EdgeColoring r) (i : Fin r) (u v : V) :
    (colorMatching G J hJG c i).Adj u v ↔
      ∃ h : J.Adj u v, c.color (⟨s(u, v), h⟩ : J.edgeSet) = i := Iff.rfl

theorem colorMatching_isMatching (G J : SimpleGraph V) (hJG : J ≤ G)
    (c : (Multigraph.ofSimpleGraph J).EdgeColoring r) (i : Fin r) :
    (colorMatching G J hJG c i).IsMatching := by
  intro v hv
  obtain ⟨e, he, hev⟩ := (c.mem_coveredVertices i v).mp hv
  change v ∈ e.val at hev
  obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp hev
  have hJvw : J.Adj v w := by
    rw [← J.mem_edgeSet, ← hw]
    exact e.property
  have heq : (⟨s(v, w), hJvw⟩ : J.edgeSet) = e := Subtype.ext hw.symm
  have hwc : c.color (⟨s(v, w), hJvw⟩ : J.edgeSet) = i := by rw [heq]; exact he
  refine ⟨w, ⟨hJvw, hwc⟩, ?_⟩
  rintro u ⟨hJvu, huc⟩
  have hh : (⟨s(v, u), hJvu⟩ : J.edgeSet) = ⟨s(v, w), hJvw⟩ :=
    c.proper (v := v) (huc.trans hwc.symm) (by simp [Multigraph.ofSimpleGraph])
      (by simp [Multigraph.ofSimpleGraph])
  have hhval := congrArg Subtype.val hh
  rcases Sym2.eq_iff.mp hhval with ⟨_, huw⟩ | ⟨hvw, huv⟩
  · exact huw
  · exact huv.trans hvw

theorem colorMatching_le (G J : SimpleGraph V) (hJG : J ≤ G)
    (c : (Multigraph.ofSimpleGraph J).EdgeColoring r) (i : Fin r) :
    (colorMatching G J hJG c i).spanningCoe ≤ J := by
  intro u v h
  exact h.choose

theorem colorMatching_pairwise_disjoint (G J : SimpleGraph V) (hJG : J ≤ G)
    (c : (Multigraph.ofSimpleGraph J).EdgeColoring r) :
    Pairwise (fun i j => Disjoint (colorMatching G J hJG c i).spanningCoe
      (colorMatching G J hJG c j).spanningCoe) := by
  intro i j hij
  apply disjoint_iff_inf_le.mpr
  intro u v huv
  rcases huv with ⟨⟨huv, hi⟩, ⟨_, hj⟩⟩
  exact hij (hi.symm.trans hj)

theorem colorMatching_disjoint_reserve (G J R : SimpleGraph V) (hJG : J ≤ G)
    (c : (Multigraph.ofSimpleGraph J).EdgeColoring r) (hJR : Disjoint J R)
    (i : Fin r) : Disjoint (colorMatching G J hJG c i).spanningCoe R :=
  hJR.mono_left (colorMatching_le G J hJG c i)

/-- Every original simple edge occurs in exactly its assigned color class;
the union therefore recovers the whole colored graph. -/
theorem colorMatching_edgeUnion (G J : SimpleGraph V) (hJG : J ≤ G)
    (c : (Multigraph.ofSimpleGraph J).EdgeColoring r) :
    edgeUnion (fun i => (colorMatching G J hJG c i).spanningCoe) univ = J := by
  ext u v
  rw [edgeUnion_adj]
  constructor
  · rintro ⟨i, _, hi⟩
    exact hi.choose
  · intro huv
    exact ⟨c.color ⟨s(u, v), huv⟩, mem_univ _, huv, rfl⟩

@[simp] theorem colorMatching_uncoveredOutside (G J : SimpleGraph V) (hJG : J ≤ G)
    (c : (Multigraph.ofSimpleGraph J).EdgeColoring r) (F : Fin r → Finset V)
    (i : Fin r) :
    uncoveredOutside G (colorMatching G J hJG c i) (F i) = c.repairVertices F i := by
  ext v
  simp only [uncoveredOutside, mem_filter, mem_univ, true_and, colorMatching_verts,
    Finset.mem_coe, c.mem_coveredVertices, c.mem_repairVertices]

theorem colorMatching_avoids_iff (G J : SimpleGraph V) (hJG : J ≤ G)
    (c : (Multigraph.ofSimpleGraph J).EdgeColoring r) (F : Fin r → Finset V) :
    (∀ i, (colorMatching G J hJG c i).verts ⊆ (F i : Set V)ᶜ) ↔ c.AvoidsVertices F := by
  constructor
  · intro hc i v hv
    exact hc i ((c.mem_coveredVertices i v).mpr hv)
  · intro hc i v hv
    exact hc i v ((c.mem_coveredVertices i v).mp hv)

end Overfull.OrdinaryFactorization
