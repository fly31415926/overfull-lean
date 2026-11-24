import Overfull.OrdinaryFactorization.Residual
import Mathlib.Data.Fintype.EquivFin

/-!
# The remaining palette and conditional host reconstruction

The original labels outside the selected embedding form a palette of exactly
`k - h` colors. Compression and restoration keep their identities explicit.
A supplied coloring of the whole actual residual graph can then be joined
with the completed classes to color the original host. This reconstruction
is conditional on that residual coloring, not an assertion of its existence.
-/

noncomputable section

namespace Overfull.OrdinaryFactorization

open Finset Classical SmallCuts

variable {k h : ℕ}

/-- The original labels not selected by the exterior palette embedding. -/
def remainingColors (l : Fin h ↪ Fin k) : Finset (Fin k) :=
  ((univ : Finset (Fin h)).map l)ᶜ

@[simp] theorem mem_remainingColors (l : Fin h ↪ Fin k) (j : Fin k) :
    j ∈ remainingColors l ↔ j ∉ Set.range l := by
  simp only [remainingColors, mem_compl, mem_map, mem_univ, true_and, Set.mem_range]

@[simp] theorem remainingColors_card (l : Fin h ↪ Fin k) :
    (remainingColors l).card = k - h := by
  simp only [remainingColors, card_compl, Fintype.card_fin, card_map, card_univ]

/-- Compress the unselected original labels to the exact residual palette size. -/
def remainingEquiv (l : Fin h ↪ Fin k) : ↥(remainingColors l) ≃ Fin (k - h) :=
  Finset.equivFinOfCardEq (remainingColors_card l)

/-- Restore a compressed residual label to its original label. -/
def remainingLabel (l : Fin h ↪ Fin k) : Fin (k - h) ↪ Fin k :=
  (remainingEquiv l).symm.toEmbedding.trans (Function.Embedding.subtype
    (fun j => j ∈ remainingColors l))

theorem remainingLabel_mem (l : Fin h ↪ Fin k) (j : Fin (k - h)) :
    remainingLabel l j ∈ remainingColors l := ((remainingEquiv l).symm j).property

theorem remainingLabel_not_selected (l : Fin h ↪ Fin k) (j : Fin (k - h)) :
    remainingLabel l j ∉ Set.range l :=
  (mem_remainingColors l _).mp (remainingLabel_mem l j)

@[simp] theorem remainingLabel_compress (l : Fin h ↪ Fin k) (j : remainingColors l) :
    remainingLabel l (remainingEquiv l j) = j.val := by
  change ((remainingEquiv l).symm (remainingEquiv l j)).val = j.val
  rw [Equiv.symm_apply_apply]

@[simp] theorem compress_remainingLabel (l : Fin h ↪ Fin k) (j : Fin (k - h)) :
    remainingEquiv l ⟨remainingLabel l j, remainingLabel_mem l j⟩ = j := by
  change remainingEquiv l ((remainingEquiv l).symm j) = j
  exact Equiv.apply_symm_apply _ _

theorem remainingLabel_range (l : Fin h ↪ Fin k) (j : Fin k) :
    j ∈ Set.range (remainingLabel l) ↔ j ∉ Set.range l := by
  constructor
  · rintro ⟨i, rfl⟩
    exact remainingLabel_not_selected l i
  · intro hj
    let a : remainingColors l := ⟨j, (mem_remainingColors l j).mpr hj⟩
    exact ⟨remainingEquiv l a, remainingLabel_compress l a⟩

theorem selectedLabel_ne_remainingLabel (l : Fin h ↪ Fin k)
    (i : Fin h) (j : Fin (k - h)) : l i ≠ remainingLabel l j := by
  intro hij
  exact remainingLabel_not_selected l j ⟨i, hij⟩

variable {V E : Type*} [Fintype E]
variable {G : Multigraph V E} {U : Finset V}
variable (C : Core G U)
variable (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k)
variable (l : Fin h ↪ Fin k) (N : Fin h → C.graph.Subgraph)

/-- The actual surviving original complement colored with exactly `k - h` labels. -/
def compressedResidualComplementColoring :
    ((residualGraph C c l N).restrictEdges (residualComplementEdges C c l N)).EdgeColoring
      (k - h) where
  color e := remainingEquiv l
    ⟨(residualComplementColoring C c l N).color e,
      (mem_remainingColors l _).mpr (residualComplementColoring_avoids_selected C c l N e)⟩
  proper := by
    intro e f v hef hev hfv
    have hcolor : (residualComplementColoring C c l N).color e =
        (residualComplementColoring C c l N).color f :=
      congrArg Subtype.val ((remainingEquiv l).injective hef)
    exact (residualComplementColoring C c l N).proper hcolor hev hfv

/-- Restoring a compressed complementary label gives its original prescribed color. -/
@[simp] theorem compressedResidualComplementColoring_restore
    (e : ↥(residualComplementEdges C c l N)) :
    remainingLabel l ((compressedResidualComplementColoring C c l N).color e) =
      c.color (residualComplementOriginal C c l N e) :=
  remainingLabel_compress l _

/-- Choose a completed class containing a deleted original edge copy. -/
def completedIndex (e : deleted C c l N) : Fin h :=
  Classical.choose ((mem_deleted C c l N e.val).mp e.property)

theorem completedIndex_mem (e : deleted C c l N) :
    e.val ∈ completedClass C c l N (completedIndex C c l N e) :=
  Classical.choose_spec ((mem_deleted C c l N e.val).mp e.property)

theorem completedIndex_eq
    (hdisj : Pairwise (fun i j => Disjoint (N i).spanningCoe (N j).spanningCoe))
    (e : deleted C c l N) (i : Fin h) (he : e.val ∈ completedClass C c l N i) :
    completedIndex C c l N e = i := by
  by_contra hne
  exact Finset.disjoint_left.mp (completedClass_pairwiseDisjoint C c l N hdisj hne)
    (completedIndex_mem C c l N e) he

variable [Fintype V]

/-- Reconstruct a proper host coloring from an explicitly supplied coloring of
the whole residual graph, using the two disjoint original-label palettes. -/
def reconstructColoring
    (hN : ∀ i, (N i).IsMatching)
    (hverts : ∀ i, (N i).verts = (selectedFootprint C c l i : Set U)ᶜ)
    (d : (residualGraph C c l N).EdgeColoring (k - h)) : G.EdgeColoring k where
  color e := if he : e ∈ deleted C c l N then
    l (completedIndex C c l N ⟨e, he⟩)
    else remainingLabel l (d.color ⟨e, mem_compl.mpr he⟩)
  proper := by
    intro e f v hef hev hfv
    by_cases heD : e ∈ deleted C c l N
    · by_cases hfD : f ∈ deleted C c l N
      · have hi : completedIndex C c l N ⟨e, heD⟩ =
            completedIndex C c l N ⟨f, hfD⟩ := by
          apply l.injective
          simpa only [dif_pos heD, dif_pos hfD] using hef
        have hf : f ∈ completedClass C c l N (completedIndex C c l N ⟨e, heD⟩) := by
          rw [hi]
          exact completedIndex_mem C c l N ⟨f, hfD⟩
        exact completedClass_isMatching C c l N hN hverts _
          e (completedIndex_mem C c l N ⟨e, heD⟩) f hf v hev hfv
      · have hp : l (completedIndex C c l N ⟨e, heD⟩) =
            remainingLabel l (d.color ⟨f, mem_compl.mpr hfD⟩) := by
          simpa only [dif_pos heD, dif_neg hfD] using hef
        exact (selectedLabel_ne_remainingLabel l _ _ hp).elim
    · by_cases hfD : f ∈ deleted C c l N
      · have hp : l (completedIndex C c l N ⟨f, hfD⟩) =
            remainingLabel l (d.color ⟨e, mem_compl.mpr heD⟩) := by
          simpa only [dif_neg heD, dif_pos hfD] using hef.symm
        exact (selectedLabel_ne_remainingLabel l _ _ hp).elim
      · have hd : d.color ⟨e, mem_compl.mpr heD⟩ =
            d.color ⟨f, mem_compl.mpr hfD⟩ := by
          apply (remainingLabel l).injective
          simpa only [dif_neg heD, dif_neg hfD] using hef
        exact congrArg Subtype.val (d.proper hd hev hfv)

theorem reconstructColoring_completedClass
    (hN : ∀ i, (N i).IsMatching)
    (hverts : ∀ i, (N i).verts = (selectedFootprint C c l i : Set U)ᶜ)
    (hdisj : Pairwise (fun i j => Disjoint (N i).spanningCoe (N j).spanningCoe))
    (d : (residualGraph C c l N).EdgeColoring (k - h))
    (i : Fin h) (e : E) (he : e ∈ completedClass C c l N i) :
    (reconstructColoring C c l N hN hverts d).color e = l i := by
  have heD : e ∈ deleted C c l N := (mem_deleted C c l N e).mpr ⟨i, he⟩
  simp only [reconstructColoring, dif_pos heD]
  exact congrArg l (completedIndex_eq C c l N hdisj ⟨e, heD⟩ i he)

theorem reconstructColoring_residual
    (hN : ∀ i, (N i).IsMatching)
    (hverts : ∀ i, (N i).verts = (selectedFootprint C c l i : Set U)ᶜ)
    (d : (residualGraph C c l N).EdgeColoring (k - h))
    (e : ↥((deleted C c l N)ᶜ)) :
    (reconstructColoring C c l N hN hverts d).color e.val = remainingLabel l (d.color e) := by
  simp only [reconstructColoring, dif_neg (mem_compl.mp e.property)]

/-- Conditional reconstruction with exact preservation of the selected labels. -/
theorem exists_coloring_of_residual
    (hN : ∀ i, (N i).IsMatching)
    (hverts : ∀ i, (N i).verts = (selectedFootprint C c l i : Set U)ᶜ)
    (hdisj : Pairwise (fun i j => Disjoint (N i).spanningCoe (N j).spanningCoe))
    (d : (residualGraph C c l N).EdgeColoring (k - h)) :
    ∃ b : G.EdgeColoring k,
      (∀ i e, e ∈ completedClass C c l N i → b.color e = l i) ∧
      (∀ e : ↥((deleted C c l N)ᶜ), b.color e.val = remainingLabel l (d.color e)) := by
  refine ⟨reconstructColoring C c l N hN hverts d, ?_, ?_⟩
  · exact reconstructColoring_completedClass C c l N hN hverts hdisj d
  · exact reconstructColoring_residual C c l N hN hverts d

theorem edgeColorable_of_residual
    (hN : ∀ i, (N i).IsMatching)
    (hverts : ∀ i, (N i).verts = (selectedFootprint C c l i : Set U)ᶜ)
    (hdisj : Pairwise (fun i j => Disjoint (N i).spanningCoe (N j).spanningCoe))
    (d : (residualGraph C c l N).EdgeColoring (k - h)) : Nonempty (G.EdgeColoring k) := by
  obtain ⟨b, _⟩ := exists_coloring_of_residual C c l N hN hverts hdisj d
  exact ⟨b⟩

end Overfull.OrdinaryFactorization
