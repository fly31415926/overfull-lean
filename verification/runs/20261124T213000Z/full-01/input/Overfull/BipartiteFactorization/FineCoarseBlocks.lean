import Overfull.BipartiteFactorization.SimultaneousBlocks
import Overfull.Probability.UniformPositions

/-!
# Actual fine and coarse vertex partitions

The sampled blocks inherit exact component sizes and all partition relations
from the constructed position sets. This interface records only actual
vertex subsets; the position witnesses and shared permutations are hidden.
-/

noncomputable section

namespace Overfull.BipartiteFactorization.SimultaneousBlocks

open Finset Classical PartitionPermutation

variable {V ι : Type*} [Fintype ι]

/-- Two actual partitions of a sampled side, with each coarse block exactly
the union of its prescribed fine blocks. Every component cardinality is exact. -/
structure FineCoarseBlocks (D : ι → Finset V) (B : Finset V) (c t : ℕ)
    (T : ((Fin c × Fin t) ⊕ Fin c) → Finset V) : Prop where
  subset : ∀ j, T j ⊆ B
  fine_card : ∀ j i, (T (Sum.inl j) ∩ D i).card = (D i).card / (c * t)
  coarse_card : ∀ j i, (T (Sum.inr j) ∩ D i).card = (D i).card / c
  fine_disjoint : ∀ j l, j ≠ l → Disjoint (T (Sum.inl j)) (T (Sum.inl l))
  coarse_disjoint : ∀ j l, j ≠ l → Disjoint (T (Sum.inr j)) (T (Sum.inr l))
  fine_cover : univ.biUnion (fun j => T (Sum.inl j)) = B
  coarse_cover : univ.biUnion (fun j => T (Sum.inr j)) = B
  coarse_union : ∀ j, T (Sum.inr j) = univ.biUnion (fun l => T (Sum.inl (j, l)))

omit [Fintype ι] in
/-- Deterministic transfer from constructed equal positions to the actual
sampled vertex blocks. No probability hypothesis appears in this step. -/
theorem fineCoarseBlocks_of_realizes {c t : ℕ}
    (D : ι → Finset V) (B : Finset V)
    (S : (Fin c × Fin t) → ∀ i, Finset (D i))
    (T : ((Fin c × Fin t) ⊕ Fin c) → Finset V)
    (hcard : ∀ j i, (S j i).card = (D i).card / (c * t))
    (hdisj : ∀ j l, j ≠ l → ∀ i, Disjoint (S j i) (S l i))
    (hcover : ∀ i, univ.biUnion (fun j => S j i) = univ)
    (hcoarsecard : ∀ j i, (coarsePositions S j i).card = (D i).card / c)
    (hreal : RealizesPositions D B (combinedPositions S) T) :
    FineCoarseBlocks D B c t T := by
  refine ⟨hreal.subset, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j i
    exact (hreal.component_card (Sum.inl j) i).trans (hcard j i)
  · intro j i
    exact (hreal.component_card (Sum.inr j) i).trans (hcoarsecard j i)
  · intro j l hjl
    exact hreal.disjoint (Sum.inl j) (Sum.inl l) (hdisj j l hjl)
  · intro j l hjl
    exact hreal.disjoint (Sum.inr j) (Sum.inr l) (coarsePositions_disjoint S hdisj j l hjl)
  · have h := hreal.cover (fineLabels c t) (by
      intro i
      simpa only [Finset.ext_iff, mem_biUnion, mem_univ] using
        combined_fine_cover S (fun i => by
          simpa only [Finset.ext_iff, mem_biUnion, mem_univ] using hcover i) i)
    simpa [fineLabels, Finset.image_biUnion] using h
  · have h := hreal.cover (coarseLabels c t) (by
      intro i
      simpa only [Finset.ext_iff, mem_biUnion, mem_univ] using
        combined_coarse_cover S (fun i => by
          simpa only [Finset.ext_iff, mem_biUnion, mem_univ] using hcover i) i)
    simpa [coarseLabels, Finset.image_biUnion] using h
  · intro j
    have h := hreal.biUnion (Sum.inr j) (coarseFineLabels t j) (by
      intro i
      simpa only [Finset.ext_iff, mem_biUnion, mem_univ] using combined_coarse_union S j i)
    simpa [coarseFineLabels, Finset.image_biUnion] using h

end Overfull.BipartiteFactorization.SimultaneousBlocks
