import Overfull.Terminal.SimpleBridge
import Overfull.NativeTerminal.Reassembly

/-!
# Restoring a simple host from its actual residual

The input coloring belongs only to `afterDeletions`. The explicit edge-copy
equivalence transports it to the residual of the original multigraph, and
the generic reassembly theorem restores all original copies. Prefix labels
and shifted residual labels are retained exactly.
-/

noncomputable section

namespace Overfull.Terminal

open Finset Classical SimpleGraph MatchingProbability ForeignPhase NativeReserve
open NativeTerminal CircuitPatterns

variable {V : Type*} [Fintype V] {k : ℕ}

/-- Transport a coloring of the actual simple residual to the surviving
original-copy multigraph. Incidences are unchanged under the equivalence. -/
def residualCopyColoring (G : SimpleGraph V) (N : ℕ → G.Subgraph) (q : ℕ)
    (c : (Multigraph.ofSimpleGraph (afterDeletions G N q)).EdgeColoring k) :
    (residualGraph (Multigraph.ofSimpleGraph G) (matchingFamilyCopies G N q)
      univ).EdgeColoring k where
  color e := c.color (residualEdgeEquiv G N q e)
  proper := by
    intro e f v h he hf
    exact (residualEdgeEquiv G N q).injective (c.proper h he hf)

/-- The inverse transport also preserves actual incidences and properness. -/
def simpleResidualColoring (G : SimpleGraph V) (N : ℕ → G.Subgraph) (q : ℕ)
    (c : (residualGraph (Multigraph.ofSimpleGraph G) (matchingFamilyCopies G N q)
      univ).EdgeColoring k) :
    (Multigraph.ofSimpleGraph (afterDeletions G N q)).EdgeColoring k where
  color e := c.color ((residualEdgeEquiv G N q).symm e)
  proper := by
    intro e f v h he hf
    exact (residualEdgeEquiv G N q).symm.injective (c.proper h he hf)

theorem residualCopyColoring_colorClass_image (G : SimpleGraph V)
    (N : ℕ → G.Subgraph) (q : ℕ)
    (c : (Multigraph.ofSimpleGraph (afterDeletions G N q)).EdgeColoring k) (j : Fin k) :
    ((residualCopyColoring G N q c).colorClass j).image Subtype.val =
      (c.colorClass j).image (residualEdgeEmbedding G N q) := by
  ext e
  simp only [Multigraph.EdgeColoring.colorClass, mem_image, mem_filter,
    mem_univ, true_and]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨residualEdgeEquiv G N q f, hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨(residualEdgeEquiv G N q).symm f, hf, rfl⟩

/-- The original host coloring is constructed from the supplied prefix
matchings and residual coloring, rather than supplied as an assumption. -/
def restoredColoring (G : SimpleGraph V) (N : ℕ → G.Subgraph) (q : ℕ)
    (hmatch : ∀ j < q, (N j).IsMatching)
    (c : (Multigraph.ofSimpleGraph (afterDeletions G N q)).EdgeColoring k) :
    (Multigraph.ofSimpleGraph G).EdgeColoring (q + k) :=
  reassembledColoring (Multigraph.ofSimpleGraph G) (matchingFamilyCopies G N q)
    (fun j => matchingEdges_isMatching G (N j.val) (hmatch j.val j.isLt))
    (residualCopyColoring G N q c)

theorem restoredColoring_prefix (G : SimpleGraph V) (N : ℕ → G.Subgraph) (q : ℕ)
    (hmatch : ∀ j < q, (N j).IsMatching)
    (hpresent : ∀ j < q, (N j).spanningCoe ≤ afterDeletions G N j)
    (c : (Multigraph.ofSimpleGraph (afterDeletions G N q)).EdgeColoring k)
    (j : Fin q) (e : G.edgeSet) (he : e ∈ matchingFamilyCopies G N q j) :
    (restoredColoring G N q hmatch c).color e = prefixLabel k j :=
  reassembledColoring_prefix (Multigraph.ofSimpleGraph G) (matchingFamilyCopies G N q)
    (fun i => matchingEdges_isMatching G (N i.val) (hmatch i.val i.isLt))
    (matchingFamilyCopies_pairwise_disjoint G N q hpresent)
    (residualCopyColoring G N q c) j e he

theorem restoredColoring_residual (G : SimpleGraph V) (N : ℕ → G.Subgraph) (q : ℕ)
    (hmatch : ∀ j < q, (N j).IsMatching)
    (c : (Multigraph.ofSimpleGraph (afterDeletions G N q)).EdgeColoring k)
    (e : (afterDeletions G N q).edgeSet) :
    (restoredColoring G N q hmatch c).color (residualEdgeEmbedding G N q e) =
      residualLabel q (c.color e) :=
  reassembledColoring_residual (Multigraph.ofSimpleGraph G) (matchingFamilyCopies G N q)
    (fun i => matchingEdges_isMatching G (N i.val) (hmatch i.val i.isLt))
    (residualCopyColoring G N q c) ((residualEdgeEquiv G N q).symm e)

theorem restoredColorClass_prefix (G : SimpleGraph V) (N : ℕ → G.Subgraph) (q : ℕ)
    (hmatch : ∀ j < q, (N j).IsMatching)
    (hpresent : ∀ j < q, (N j).spanningCoe ≤ afterDeletions G N j)
    (c : (Multigraph.ofSimpleGraph (afterDeletions G N q)).EdgeColoring k) (j : Fin q) :
    (restoredColoring G N q hmatch c).colorClass (prefixLabel k j) =
      matchingFamilyCopies G N q j :=
  reassembledColorClass_prefix (Multigraph.ofSimpleGraph G) (matchingFamilyCopies G N q)
    (fun i => matchingEdges_isMatching G (N i.val) (hmatch i.val i.isLt))
    (matchingFamilyCopies_pairwise_disjoint G N q hpresent)
    (residualCopyColoring G N q c) j

theorem restoredColorClass_residual (G : SimpleGraph V) (N : ℕ → G.Subgraph) (q : ℕ)
    (hmatch : ∀ j < q, (N j).IsMatching)
    (c : (Multigraph.ofSimpleGraph (afterDeletions G N q)).EdgeColoring k) (j : Fin k) :
    (restoredColoring G N q hmatch c).colorClass (residualLabel q j) =
      (c.colorClass j).image (residualEdgeEmbedding G N q) := by
  rw [restoredColoring, reassembledColorClass_residual]
  convert residualCopyColoring_colorClass_image G N q c j using 1 <;>
    congr 1 <;> exact Subsingleton.elim _ _

/-- Exact one-factorization with the first `q` original-copy classes retained
verbatim and every later class equal to its original residual copies. -/
theorem exists_restored_one_factorization (G : SimpleGraph V)
    (N : ℕ → G.Subgraph) (q : ℕ)
    (hmatch : ∀ j < q, (N j).IsMatching)
    (hpresent : ∀ j < q, (N j).spanningCoe ≤ afterDeletions G N j)
    (c : (Multigraph.ofSimpleGraph (afterDeletions G N q)).EdgeColoring k)
    (hregular : ∀ v, G.degree v = q + k) :
    ∃ F : Fin (q + k) → Finset G.edgeSet,
      (∀ i, (Multigraph.ofSimpleGraph G).IsPerfectMatching (F i)) ∧
      Pairwise (fun i j => Disjoint (F i) (F j)) ∧
      univ.biUnion F = univ ∧
      (∀ i, F (prefixLabel k i) = matchingFamilyCopies G N q i) ∧
      (∀ j, F (residualLabel q j) =
        (c.colorClass j).image (residualEdgeEmbedding G N q)) := by
  let d := restoredColoring G N q hmatch c
  have hreg : ∀ v, (Multigraph.ofSimpleGraph G).degree v = q + k := by
    intro v
    rw [Multigraph.ofSimpleGraph_degree]
    exact hregular v
  refine ⟨d.colorClass, BoundedExterior.colorClass_isPerfectMatching d hreg,
    BoundedExterior.colorClasses_pairwise_disjoint d, ?_, ?_, ?_⟩
  · convert BoundedExterior.colorClasses_union d using 1
    congr
    exact Subsingleton.elim _ _
  · exact restoredColorClass_prefix G N q hmatch hpresent c
  · exact restoredColorClass_residual G N q hmatch c

variable {I : Type*} {G : SimpleGraph V} {U : I → Finset V}
variable {H : ∀ i, SimpleGraph (U i)} {F : ℕ → G.Subgraph}
variable {q h : ℕ} {a θ σ : ℝ}

/-- Boundary completion followed by an actual residual coloring restores
the original `h`-coloring. The sole palette arithmetic premise is `q ≤ h`. -/
theorem completion_restores_coloring (D : BoundaryCompletion G U H F q h a θ σ)
    (hqh : q ≤ h)
    (c : (Multigraph.ofSimpleGraph (afterDeletions G D.full q)).EdgeColoring (h - q)) :
    Nonempty ((Multigraph.ofSimpleGraph G).EdgeColoring h) := by
  have hc : Nonempty ((Multigraph.ofSimpleGraph G).EdgeColoring (q + (h - q))) :=
    ⟨restoredColoring G D.full q (fun j hj => (D.perfect j hj).1) c⟩
  simpa only [Nat.add_sub_of_le hqh] using hc

/-- The completed prefix and residual coloring yield exactly `h` disjoint
perfect matchings covering the original host copies. -/
theorem completion_restores_one_factorization
    (D : BoundaryCompletion G U H F q h a θ σ) (hqh : q ≤ h)
    (c : (Multigraph.ofSimpleGraph (afterDeletions G D.full q)).EdgeColoring (h - q)) :
    ∃ K : Fin h → Finset G.edgeSet,
      (∀ i, (Multigraph.ofSimpleGraph G).IsPerfectMatching (K i)) ∧
      Pairwise (fun i j => Disjoint (K i) (K j)) ∧ univ.biUnion K = univ := by
  have hregular : ∀ v, (Multigraph.ofSimpleGraph G).degree v = h := by
    intro v
    have hz := D.residual_regular 0 (Nat.zero_le q) v
    rw [ForeignPhase.afterDeletions_zero] at hz
    simpa only [Nat.sub_zero, Multigraph.ofSimpleGraph_degree] using hz
  obtain ⟨d⟩ := completion_restores_coloring D hqh c
  refine ⟨d.colorClass, BoundedExterior.colorClass_isPerfectMatching d hregular,
    BoundedExterior.colorClasses_pairwise_disjoint d, ?_⟩
  convert BoundedExterior.colorClasses_union d using 1
  congr
  exact Subsingleton.elim _ _

end Overfull.Terminal
