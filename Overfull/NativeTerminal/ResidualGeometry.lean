import Overfull.NativeTerminal.ReserveGeometry
import Overfull.NativeCore.Incidence

/-!
# Transport of native reserve geometry to the actual residual

An injective original-copy map preserves endpoints exactly. An equality of
the surviving external-copy image with the selected reserve union then
determines all assigned-shore cuts and exceptional incidences. The copy
image is an exact equality, not a multiplicity-free support approximation.
-/

noncomputable section

namespace Overfull.NativeTerminal

open Finset Classical NativeReserve AssignedParts

variable {V E F : Type*}

/-- An original-copy embedding retains both endpoints and parallel-copy identity. -/
structure CopyEmbedding (G : Multigraph V E) (H : Multigraph V F) where
  map : F ↪ E
  edge_eq : ∀ e, H.edge e = G.edge (map e)

namespace CopyEmbedding
variable {G : Multigraph V E} {H : Multigraph V F} (ι : CopyEmbedding G H)

@[simp] theorem firstEnd (e : F) : H.firstEnd e = G.firstEnd (ι.map e) := by
  unfold Multigraph.firstEnd
  rw [ι.edge_eq]

@[simp] theorem secondEnd (e : F) : H.secondEnd e = G.secondEnd (ι.map e) := by
  unfold Multigraph.secondEnd
  rw [ι.edge_eq]

@[simp] theorem otherEnd (z : V) (e : F) : H.otherEnd z e = G.otherEnd z (ι.map e) := by
  simp only [Multigraph.otherEnd, ι.firstEnd, ι.secondEnd]

@[simp] theorem incident (z : V) (e : F) : z ∈ H.edge e ↔ z ∈ G.edge (ι.map e) := by
  rw [ι.edge_eq]

end CopyEmbedding

section Finite
variable [Fintype E] [Fintype F]

/-- All copies outside the internal edge sets of the two old cores. -/
def externalCopies (G : Multigraph V E) (U₀ U₁ : Finset V) : Finset E :=
  univ \ (G.internalEdges U₀ ∪ G.internalEdges U₁)

@[simp] theorem mem_externalCopies (G : Multigraph V E) (U₀ U₁ : Finset V) (e : E) :
    e ∈ externalCopies G U₀ U₁ ↔
      ¬ (G.firstEnd e ∈ U₀ ∧ G.secondEnd e ∈ U₀) ∧
      ¬ (G.firstEnd e ∈ U₁ ∧ G.secondEnd e ∈ U₁) := by
  simp [externalCopies]

namespace CopyEmbedding
variable {G : Multigraph V E} {H : Multigraph V F} (ι : CopyEmbedding G H)

@[simp] theorem mem_cut_iff (A : Finset V) (e : F) :
    e ∈ H.cutEdges A ↔ ι.map e ∈ G.cutEdges A := by
  simp only [Multigraph.mem_cutEdges, ι.firstEnd, ι.secondEnd]

@[simp] theorem mem_external_iff (U₀ U₁ : Finset V) (e : F) :
    e ∈ externalCopies H U₀ U₁ ↔ ι.map e ∈ externalCopies G U₀ U₁ := by
  simp only [mem_externalCopies, ι.firstEnd, ι.secondEnd]

/-- Every whole-core shore cut is determined by the exact surviving external image. -/
theorem cut_image_of_external_image (U₀ U₁ A : Finset V) (R : Finset E)
    (himage : (externalCopies H U₀ U₁).image ι.map = R)
    (hwhole : G.cutEdges A ⊆ externalCopies G U₀ U₁) :
    (H.cutEdges A).image ι.map = G.cutOn R A := by
  ext e
  constructor
  · rintro he
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    have hcut := (ι.mem_cut_iff A f).mp hf
    have hmem : ι.map f ∈ R := by
      rw [← himage]
      exact mem_image.mpr ⟨f,(ι.mem_external_iff U₀ U₁ f).mpr (hwhole hcut),rfl⟩
    exact (G.mem_cutOn R A _).mpr ⟨hmem,(G.mem_cutEdges A _).mp hcut⟩
  · intro he
    obtain ⟨heR,hecut⟩ := (G.mem_cutOn R A e).mp he
    rw [← himage] at heR
    obtain ⟨f,_hf,rfl⟩ := mem_image.mp heR
    exact mem_image.mpr ⟨f,(ι.mem_cut_iff A f).mpr
      ((G.mem_cutEdges A _).mpr hecut),rfl⟩

/-- Original-copy injection turns the image identity into an exact cut-size identity. -/
theorem cutSize_of_external_image (U₀ U₁ A : Finset V) (R : Finset E)
    (himage : (externalCopies H U₀ U₁).image ι.map = R)
    (hwhole : G.cutEdges A ⊆ externalCopies G U₀ U₁) :
    H.cutSize A = (G.cutOn R A).card := by
  rw [← ι.cut_image_of_external_image U₀ U₁ A R himage hwhole,
    card_image_of_injective _ ι.map.injective]
  rfl

/-- Empty selected cuts give empty actual residual cuts. -/
theorem cut_empty_of_external_image (U₀ U₁ A : Finset V) (R : Finset E)
    (himage : (externalCopies H U₀ U₁).image ι.map = R)
    (hwhole : G.cutEdges A ⊆ externalCopies G U₀ U₁)
    (hzero : G.cutOn R A = ∅) : H.cutEdges A = ∅ := by
  have hc := ι.cutSize_of_external_image U₀ U₁ A R himage hwhole
  rw [hzero,card_empty] at hc
  exact card_eq_zero.mp hc

end CopyEmbedding

/-- A shore that contains or avoids each entire old core has no internal-core cut copy. -/
theorem whole_shore_cut_subset_external (G : Multigraph V E)
    (U₀ U₁ A : Finset V)
    (h₀ : U₀ ⊆ A ∨ Disjoint U₀ A) (h₁ : U₁ ⊆ A ∨ Disjoint U₁ A) :
    G.cutEdges A ⊆ externalCopies G U₀ U₁ := by
  intro e he
  have hcut := (G.mem_cutEdges A e).mp he
  apply (mem_externalCopies G U₀ U₁ e).mpr
  have hn (U : Finset V) (hU : U ⊆ A ∨ Disjoint U A) :
      ¬ (G.firstEnd e ∈ U ∧ G.secondEnd e ∈ U) := by
    rintro ⟨hx,hy⟩
    apply hcut
    rcases hU with hU | hU
    · exact propext (iff_of_true (hU hx) (hU hy))
    · exact propext (iff_of_false
        (fun h => disjoint_left.mp hU hx h) (fun h => disjoint_left.mp hU hy h))
  exact ⟨hn U₀ h₀,hn U₁ h₁⟩

/-- Any copy at a vertex outside both old cores is external. -/
theorem external_of_incident_outside (G : Multigraph V E) (U₀ U₁ : Finset V)
    {z : V} (hz₀ : z ∉ U₀) (hz₁ : z ∉ U₁) {e : E} (hze : z ∈ G.edge e) :
    e ∈ externalCopies G U₀ U₁ := by
  apply (mem_externalCopies G U₀ U₁ e).mpr
  rcases (G.incident_iff e z).mp hze with hx | hy
  · exact ⟨fun h => hz₀ (hx ▸ h.1), fun h => hz₁ (hx ▸ h.1)⟩
  · exact ⟨fun h => hz₀ (hy ▸ h.2), fun h => hz₁ (hy ▸ h.2)⟩

end Finite

end Overfull.NativeTerminal
