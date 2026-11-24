import Overfull.CompatibleCircuits.FourAdmissibleTransfer
import Overfull.SparseColoring

/-!
# Restricting to the selected actual copies

Replacing an arbitrary ambient edge type by the finite selected-copy
subtype preserves every selected degree, cut, class-cut, and admissibility
inequality. A partition of the subtype maps back to precisely the original
selected copies. This permits finite whole-graph constructions to be used
on arbitrary residual copy sets.
-/

noncomputable section

namespace Overfull.Multigraph

open Finset Classical

variable {V E F K : Type*}

/-- Copy embeddings preserve each class-cut exactly, not only the total cut. -/
theorem copyEmbedding_classCut (G : Multigraph V E) (H : Multigraph V F)
    (ψ : E ↪ F) (hedge : ∀ e, H.edge (ψ e) = G.edge e)
    (classOf : V → F → K) (C : Finset E) (v : V) (k : K) (X : Finset V) :
    H.classCutOn classOf (C.map ψ) v k X =
      (G.classCutOn (fun v e => classOf v (ψ e)) C v k X).map ψ := by
  simp only [classCutOn, copyEmbedding_cut G H ψ hedge, filter_map,
    Function.comp_def, hedge]

variable (G : Multigraph V E)

/-- The selected subtype maps bijectively back to the actual selected set. -/
theorem restrictEdges_univ_map (C : Finset E) :
    (univ : Finset C).map (Function.Embedding.subtype (fun e => e ∈ C)) = C := by
  ext e
  simp

/-- Selected degrees survive restriction to the selected-copy subtype. -/
theorem restrictEdges_degreeOn_univ (C : Finset E) (v : V) :
    (G.restrictEdges C).degreeOn univ v = G.degreeOn C v := by
  let ψ := Function.Embedding.subtype (fun e => e ∈ C)
  have h := copyEmbedding_degree (G.restrictEdges C) G ψ (fun _ => rfl) univ v
  rw [restrictEdges_univ_map C] at h
  exact h.symm

/-- Cut cardinalities retain all selected parallel copies. -/
theorem restrictEdges_cutOn_univ_card (C : Finset E) (X : Finset V) :
    ((G.restrictEdges C).cutOn univ X).card = (G.cutOn C X).card := by
  let ψ := Function.Embedding.subtype (fun e => e ∈ C)
  have h := copyEmbedding_cut (G.restrictEdges C) G ψ (fun _ => rfl) univ X
  rw [restrictEdges_univ_map C] at h
  simpa only [card_map] using (congrArg Finset.card h).symm

/-- Every original incidence class retains its exact count on every cut. -/
theorem restrictEdges_classCutOn_univ_card
    (classOf : V → E → K) (C : Finset E) (v : V) (k : K) (X : Finset V) :
    ((G.restrictEdges C).classCutOn (fun v e => classOf v e.val) univ v k X).card =
      (G.classCutOn classOf C v k X).card := by
  let ψ := Function.Embedding.subtype (fun e => e ∈ C)
  have h := copyEmbedding_classCut (G.restrictEdges C) G ψ (fun _ => rfl)
    classOf univ v k X
  rw [restrictEdges_univ_map C] at h
  simpa only [card_map] using (congrArg Finset.card h).symm

/-- Original and selected-subtype admissibility are equivalent. -/
theorem restrictEdges_admissibleOn_univ_iff
    (classOf : V → E → K) (C : Finset E) :
    (G.restrictEdges C).AdmissibleOn (fun v e => classOf v e.val) univ ↔
      G.AdmissibleOn classOf C := by
  simp only [AdmissibleOn, G.restrictEdges_classCutOn_univ_card,
    G.restrictEdges_cutOn_univ_card]

/-- Lift a constructed finite-subtype partition to the exact original
copy set, without changing any incidence class or identifying any copies. -/
def CompatibleCircuitPartition.of_restrictEdges
    (classOf : V → E → K) (C : Finset E)
    (P : (G.restrictEdges C).CompatibleCircuitPartition
      (fun v e => classOf v e.val) univ) :
    G.CompatibleCircuitPartition classOf C := by
  let ψ := Function.Embedding.subtype (fun e => e ∈ C)
  let P' := P.map_copies (G.restrictEdges C) G ψ (fun _ => rfl) classOf
  exact restrictEdges_univ_map C ▸ P'

end Overfull.Multigraph
