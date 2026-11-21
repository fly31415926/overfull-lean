import Overfull.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
Transport of the graph-theoretic statements under a change of vertex labels.
This connects the explicitly constructed vertex type to `Fin n` in the
manuscript specifications.
-/

namespace Overfull

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

theorem iso_mem_edge (f : G ≃g H) (e : G.edgeSet) (v : V) :
    f v ∈ (f.mapEdgeSet e).val ↔ v ∈ e.val := by
  change f v ∈ Sym2.map f e.val ↔ v ∈ e.val
  rw [Sym2.mem_map]
  constructor
  · rintro ⟨w, hw, hwv⟩
    simpa only [f.injective hwv] using hw
  · intro hv
    exact ⟨v, hv, rfl⟩

/-- Pull an edge coloring back along a graph isomorphism. -/
def EdgeColoring.pullback {k : ℕ} (c : EdgeColoring H k) (f : G ≃g H) :
    EdgeColoring G k where
  color e := c.color (f.mapEdgeSet e)
  proper := by
    intro e d v he hd hcolor
    apply f.mapEdgeSet.injective
    exact c.proper ((iso_mem_edge f e v).mpr he)
      ((iso_mem_edge f d v).mpr hd) hcolor

theorem iso_edgeColorable_iff (f : G ≃g H) (k : ℕ) :
    Nonempty (EdgeColoring G k) ↔ Nonempty (EdgeColoring H k) := by
  constructor
  · rintro ⟨c⟩
    exact ⟨c.pullback f.symm⟩
  · rintro ⟨c⟩
    exact ⟨c.pullback f⟩

variable [Fintype V] [Fintype W]

theorem iso_degree_eq [DecidableRel G.Adj] [DecidableRel H.Adj]
    (f : G ≃g H) (v : V) : G.degree v = H.degree (f v) := by
  have h := Fintype.card_congr (f.mapNeighborSet v)
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using h

theorem iso_maxDegree_eq [DecidableRel G.Adj] [DecidableRel H.Adj]
    (f : G ≃g H) : G.maxDegree = H.maxDegree := by
  apply Nat.le_antisymm
  · apply G.maxDegree_le_of_forall_degree_le
    intro v
    rw [iso_degree_eq f]
    exact H.degree_le_maxDegree (f v)
  · apply H.maxDegree_le_of_forall_degree_le
    intro w
    rw [iso_degree_eq f.symm]
    exact G.degree_le_maxDegree (f.symm w)

theorem iso_internalEdges_card
    (f : G ≃g H) (X : Finset V) :
    (internalEdges G X).card =
      (internalEdges H (X.map f.toEquiv.toEmbedding)).card := by
  classical
  have hmem (e : G.edgeSet) :
      f.mapEdgeSet e ∈ internalEdges H (X.map f.toEquiv.toEmbedding) ↔
        e ∈ internalEdges G X := by
    simp only [internalEdges, Finset.mem_filter, Finset.mem_univ, true_and, Finset.subset_iff, Sym2.mem_toFinset]
    constructor
    · intro h v hv
      have hf : f v ∈ (f.mapEdgeSet e).val :=
        (iso_mem_edge f e v).mpr hv
      have hmap := h hf
      rw [Finset.mem_map_equiv] at hmap
      change f.toEquiv.symm (f.toEquiv v) ∈ X at hmap
      simpa only [Equiv.symm_apply_apply] using hmap
    · intro h w hw
      obtain ⟨v, rfl⟩ := f.surjective w
      have hv : v ∈ e.val := (iso_mem_edge f e v).mp hw
      exact Finset.mem_map.mpr ⟨v, h hv, rfl⟩
  have hmap : (internalEdges G X).map f.mapEdgeSet.toEmbedding =
      internalEdges H (X.map f.toEquiv.toEmbedding) := by
    ext e
    obtain ⟨d, rfl⟩ := f.mapEdgeSet.surjective e
    simp only [Finset.mem_map_equiv, Equiv.symm_apply_apply, hmem]
  rw [← hmap, Finset.card_map]

theorem iso_overfull_iff
    (f : G ≃g H) (X : Finset V) (k : ℕ) :
    IsOverfull G k X ↔ IsOverfull H k (X.map f.toEquiv.toEmbedding) := by
  unfold IsOverfull
  rw [Finset.card_map, iso_internalEdges_card f]

theorem iso_no_overfull_iff
    (f : G ≃g H) (k : ℕ) :
    (∀ X : Finset V, ¬ IsOverfull G k X) ↔
      ∀ Y : Finset W, ¬ IsOverfull H k Y := by
  constructor
  · intro h Y hY
    exact h (Y.map f.symm.toEquiv.toEmbedding)
      ((iso_overfull_iff f.symm Y k).mp hY)
  · intro h X hX
    exact h (X.map f.toEquiv.toEmbedding) ((iso_overfull_iff f X k).mp hX)

end Overfull
