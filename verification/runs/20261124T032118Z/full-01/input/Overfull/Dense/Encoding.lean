import Overfull.Dense.Encoding.Counting
import Overfull.Dense.Encoding.Decomposition

/-!
# The prescribed-coloring encoding lemma

This is Lemma 5.3 (`dense:encoding`) of the manuscript. The host is an
actual finite loopless multigraph. A simple bipartite part is specified
by an injective map from its edges into the host's edge copies, and its
complement carries the prescribed proper coloring. The encoded graph
has the original simple-part edges and the actual available-color edges.

Both directions of the triangle-decomposition equivalence are proved.
There are no nonemptiness or positive-degree assumptions.
-/

namespace Overfull

open Classical Dense.Encoding

/-- Full prescribed-coloring encoding lemma, including exact incidence
identities and equivalence with an actual triangle decomposition. -/
theorem dense_encoding {A B E : Type*} [Fintype A] [Fintype B] [Fintype E]
    (G : Multigraph (A ⊕ B) E)
    (hcross : ∀ e, ∃ a b, G.edge e = s(Sum.inl a, Sum.inr b))
    (H : SimplePart G) (k : ℕ) (c₀ : H.remainder.EdgeColoring k)
    (hregular : ∀ v, G.degree v = k) (hbalance : Fintype.card A = Fintype.card B) :
    (H.encoded c₀).IsLocallyBalanced ∧
    (∀ a, k - ((H.encoded c₀).neighborsWA a).card = H.remainder.degree (.inl a)) ∧
    (∀ b, k - ((H.encoded c₀).neighborsWB b).card = H.remainder.degree (.inr b)) ∧
    (∀ w, Fintype.card A - ((H.encoded c₀).linkA w).card = (H.colorClass c₀ w).card ∧
      Fintype.card B - ((H.encoded c₀).linkB w).card = (H.colorClass c₀ w).card) ∧
    ((∃ c : G.EdgeColoring k, H.Extends c₀ c) ↔
      (H.encoded c₀).HasTriangleDecomposition) := by
  let P := Bipartition.of_crossing G hcross
  refine ⟨H.encoded_locallyBalanced c₀ P hregular hbalance, ?_, ?_, ?_,
    H.extension_iff_triangleDecomposition c₀ hregular⟩
  · intro a
    have h := H.neighborsWA_card_add_remainder_degree c₀ a
    omega
  · intro b
    have h := H.neighborsWB_card_add_remainder_degree c₀ b
    omega
  · intro w
    have hA := H.linkA_card_add_colorClass c₀ P w
    have hB := H.linkB_card_add_colorClass c₀ P w
    omega

end Overfull
