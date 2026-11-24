import Vizing.Graph
import Overfull.Basic

/-!
Conversion from mathlib's finite simple graphs to the adjacency-list graphs
used by Arohee Bhoja's verified Misra--Gries algorithm.
-/

namespace Overfull.VizingAdapter

noncomputable def neighbors {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    _root_.Graph.Nbors n := by
  classical
  exact {
    val := (G.neighborFinset v).toList
    sizeAx := by simpa using G.degree_lt_card_verts v
    nodupAx := Finset.nodup_toList _
  }

noncomputable def graph {n : ℕ} (G : SimpleGraph (Fin n)) :
    _root_.Graph.Graph n := by
  classical
  exact {
    val := Array.ofFn (neighbors G)
    sizeAx := by simp
    symmAx := by
      intro u v
      simpa [neighbors] using G.adj_comm v u
    noSelfLoopsAx := by
      intro u
      simp [neighbors]
  }

@[simp] theorem neighbor_mem {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    u ∈ (_root_.Graph.nbhd (graph G) v).val ↔ G.Adj v u := by
  classical
  simp [graph, _root_.Graph.nbhd, neighbors]

@[simp] theorem degree_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    (_root_.Graph.degree (graph G) v).val = G.degree v := by
  classical
  simp [_root_.Graph.degree, _root_.Graph.nbhd, graph, neighbors]
  unfold SimpleGraph.degree
  apply congrArg Finset.card
  ext u
  simp only [SimpleGraph.mem_neighborFinset]

theorem maxDegree_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    _root_.Graph.maxDegree (graph G) ≤ G.maxDegree := by
  classical
  simp only [_root_.Graph.maxDegree]
  split
  · exact Nat.zero_le _
  · rename_i d hd
    have hmem := (List.argmax_eq_some_iff.mp hd).1
    obtain ⟨v, _, hv⟩ := List.mem_map.mp hmem
    rw [← hv, degree_eq]
    exact G.degree_le_maxDegree v

@[simp] theorem present_iff {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    _root_.Graph.present (graph G) (u, v) ↔ G.Adj u v := by
  simp only [_root_.Graph.present, neighbor_mem]
  exact ⟨And.right, fun h => ⟨h.symm, h⟩⟩

end Overfull.VizingAdapter
