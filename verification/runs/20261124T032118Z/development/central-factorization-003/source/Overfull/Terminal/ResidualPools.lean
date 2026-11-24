import Overfull.Terminal.SimpleBridge
import Overfull.FourOdd.OriginalGraph

/-!
# Retained matching families in the actual simple residual

An original edge-copy pool is pulled back through the injective residual
embedding. Surviving pools retain every copy, incidence, support vertex and
cut count. Exact coverage by a family of retained pools becomes exact
coverage of the joining edges of the simple residual.
-/

noncomputable section

namespace Overfull.Terminal

open Finset Classical SimpleGraph ForeignPhase NativeReserve FourOdd

variable {V : Type*} [Fintype V]

/-- The actual residual copies whose original identities belong to `A`. -/
def residualPool (G : SimpleGraph V) (N : ℕ → G.Subgraph) (q : ℕ)
    (A : Finset G.edgeSet) : Finset (afterDeletions G N q).edgeSet :=
  univ.filter (fun e => residualEdgeEmbedding G N q e ∈ A)

@[simp] theorem mem_residualPool (G : SimpleGraph V) (N : ℕ → G.Subgraph) (q : ℕ)
    (A : Finset G.edgeSet) (e : (afterDeletions G N q).edgeSet) :
    e ∈ residualPool G N q A ↔ residualEdgeEmbedding G N q e ∈ A := by
  simp [residualPool]

theorem residualPool_image (G : SimpleGraph V) (N : ℕ → G.Subgraph) (q : ℕ)
    (A : Finset G.edgeSet) :
    (residualPool G N q A).image (residualEdgeEmbedding G N q) =
      A \ removedCopies (matchingFamilyCopies G N q) univ :=
  residualEdgeEmbedding_image_filter G N q A

theorem residualPool_image_of_survives (G : SimpleGraph V)
    (N : ℕ → G.Subgraph) (q : ℕ) (A : Finset G.edgeSet)
    (hsurvive : ∀ e ∈ A, e ∉ removedCopies (matchingFamilyCopies G N q) univ) :
    (residualPool G N q A).image (residualEdgeEmbedding G N q) = A := by
  rw [residualPool_image]
  ext e
  simp only [mem_sdiff]
  exact ⟨And.left, fun he => ⟨he, hsurvive e he⟩⟩

theorem residualPool_card (G : SimpleGraph V) (N : ℕ → G.Subgraph) (q : ℕ)
    (A : Finset G.edgeSet)
    (hsurvive : ∀ e ∈ A, e ∉ removedCopies (matchingFamilyCopies G N q) univ) :
    (residualPool G N q A).card = A.card := by
  calc
    (residualPool G N q A).card =
        ((residualPool G N q A).image (residualEdgeEmbedding G N q)).card :=
      (card_image_of_injective _ (residualEdgeEmbedding G N q).injective).symm
    _ = A.card := congrArg Finset.card (residualPool_image_of_survives G N q A hsurvive)

theorem residualPool_isMatching (G : SimpleGraph V) (N : ℕ → G.Subgraph) (q : ℕ)
    (A : Finset G.edgeSet) (hA : (Multigraph.ofSimpleGraph G).IsMatching A) :
    (Multigraph.ofSimpleGraph (afterDeletions G N q)).IsMatching (residualPool G N q A) := by
  intro e he f hf v hev hfv
  apply (residualEdgeEmbedding G N q).injective
  exact hA _ ((mem_residualPool G N q A e).mp he)
    _ ((mem_residualPool G N q A f).mp hf) v hev hfv

theorem residualPool_disjoint (G : SimpleGraph V) (N : ℕ → G.Subgraph) (q : ℕ)
    (A B : Finset G.edgeSet) (hAB : Disjoint A B) :
    Disjoint (residualPool G N q A) (residualPool G N q B) := by
  apply disjoint_left.mpr
  intro e he hf
  exact disjoint_left.mp hAB ((mem_residualPool G N q A e).mp he)
    ((mem_residualPool G N q B e).mp hf)

theorem residualPool_cutOn (G : SimpleGraph V) (N : ℕ → G.Subgraph) (q : ℕ)
    (A : Finset G.edgeSet) (X : Finset V) :
    (Multigraph.ofSimpleGraph (afterDeletions G N q)).cutOn (residualPool G N q A) X =
      residualPool G N q ((Multigraph.ofSimpleGraph G).cutOn A X) := by
  ext e
  simp only [Multigraph.mem_cutOn, mem_residualPool, residualEdgeEmbedding_firstEnd,
    residualEdgeEmbedding_secondEnd]

/-- Exact cut cardinality for every retained original-copy pool. -/
theorem residualPool_cutOn_card (G : SimpleGraph V) (N : ℕ → G.Subgraph) (q : ℕ)
    (A : Finset G.edgeSet) (X : Finset V)
    (hsurvive : ∀ e ∈ A, e ∉ removedCopies (matchingFamilyCopies G N q) univ) :
    ((Multigraph.ofSimpleGraph (afterDeletions G N q)).cutOn
      (residualPool G N q A) X).card = ((Multigraph.ofSimpleGraph G).cutOn A X).card := by
  rw [residualPool_cutOn]
  apply residualPool_card
  intro e he
  exact hsurvive e ((Multigraph.mem_cutOn _ _ _ _).mp he).1

theorem residualPool_support_subset (G : SimpleGraph V)
    (N : ℕ → G.Subgraph) (q : ℕ) (A : Finset G.edgeSet) :
    (Multigraph.ofSimpleGraph (afterDeletions G N q)).edgeSupport (residualPool G N q A) ⊆
      (Multigraph.ofSimpleGraph G).edgeSupport A := by
  intro v hv
  obtain ⟨e, he, hev⟩ := (Multigraph.mem_edgeSupport _ _ _).mp hv
  exact (Multigraph.mem_edgeSupport _ _ _).mpr
    ⟨residualEdgeEmbedding G N q e, (mem_residualPool G N q A e).mp he, hev⟩

theorem residualPool_support_eq (G : SimpleGraph V)
    (N : ℕ → G.Subgraph) (q : ℕ) (A : Finset G.edgeSet)
    (hsurvive : ∀ e ∈ A, e ∉ removedCopies (matchingFamilyCopies G N q) univ) :
    (Multigraph.ofSimpleGraph (afterDeletions G N q)).edgeSupport (residualPool G N q A) =
      (Multigraph.ofSimpleGraph G).edgeSupport A := by
  apply Subset.antisymm (residualPool_support_subset G N q A)
  intro v hv
  obtain ⟨e, he, hev⟩ := (Multigraph.mem_edgeSupport _ _ _).mp hv
  refine (Multigraph.mem_edgeSupport _ _ _).mpr
    ⟨residualEdgeEquiv G N q ⟨e, hsurvive e he⟩, ?_, hev⟩
  exact (mem_residualPool G N q A _).mpr he

theorem residualPool_biUnion {J : Type*} (G : SimpleGraph V)
    (N : ℕ → G.Subgraph) (q : ℕ) (T : Finset J) (M : J → Finset G.edgeSet) :
    residualPool G N q (T.biUnion M) = T.biUnion (fun j => residualPool G N q (M j)) := by
  ext e
  simp only [mem_residualPool, mem_biUnion]

theorem residualPool_sdiff_removed (G : SimpleGraph V)
    (N : ℕ → G.Subgraph) (q : ℕ) (A : Finset G.edgeSet) :
    residualPool G N q (A \ removedCopies (matchingFamilyCopies G N q) univ) =
      residualPool G N q A := by
  ext e
  simp only [mem_residualPool, mem_sdiff]
  exact and_iff_left ((mem_residual_iff_not_removed G N q _).mp e.property)

theorem residualPool_joining {I : Type*} [DecidableEq I]
    (G : SimpleGraph V) (N : ℕ → G.Subgraph) (q : ℕ) (label : V → I) :
    residualPool G N q (joiningCopies (Multigraph.ofSimpleGraph G) label) =
      joiningCopies (Multigraph.ofSimpleGraph (afterDeletions G N q)) label := by
  ext e
  simp only [mem_residualPool, mem_joiningCopies, residualEdgeEmbedding_firstEnd,
    residualEdgeEmbedding_secondEnd]

/-- Exact joining coverage by retained original pools becomes exact
joining coverage in the residual. The finite index type is unrestricted. -/
theorem residualFamily_union_joining {I J : Type*} [DecidableEq I]
    (G : SimpleGraph V) (N : ℕ → G.Subgraph) (q : ℕ) (label : V → I)
    (T : Finset J) (M : J → Finset G.edgeSet)
    (hcover : joiningCopies (Multigraph.ofSimpleGraph G) label \
      removedCopies (matchingFamilyCopies G N q) univ = T.biUnion M) :
    T.biUnion (fun j => residualPool G N q (M j)) =
      joiningCopies (Multigraph.ofSimpleGraph (afterDeletions G N q)) label := by
  rw [← residualPool_biUnion, ← hcover, residualPool_sdiff_removed, residualPool_joining]

/-- The same exact joining identity also proves survival of every member,
so no independent nondeletion assumption is needed for cut transport. -/
theorem residualFamily_survives_of_union {I J : Type*} [DecidableEq I]
    (G : SimpleGraph V) (N : ℕ → G.Subgraph) (q : ℕ) (label : V → I)
    (T : Finset J) (M : J → Finset G.edgeSet)
    (hcover : joiningCopies (Multigraph.ofSimpleGraph G) label \
      removedCopies (matchingFamilyCopies G N q) univ = T.biUnion M)
    (j : J) (hj : j ∈ T) (e : G.edgeSet) (he : e ∈ M j) :
    e ∉ removedCopies (matchingFamilyCopies G N q) univ := by
  have hm : e ∈ T.biUnion M := mem_biUnion.mpr ⟨j, hj, he⟩
  rw [← hcover] at hm
  exact (mem_sdiff.mp hm).2

end Overfull.Terminal
