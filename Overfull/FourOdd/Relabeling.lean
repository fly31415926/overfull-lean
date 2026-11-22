import Overfull.FourOdd.Basic

/-!
# Relabeling the four odd parts

Relabeling changes only the four names of the parts. Original edge copies,
endpoints, matching conditions and exact decomposition counts are retained.
The seven allowable forest shapes reduce to one matching and one star.
-/

namespace Overfull.FourOdd

open Finset Compression CircuitPatterns

/-- The induced bijection on the six unordered pairs of distinct labels. -/
def relabelPair (σ : Equiv.Perm (Fin 4)) : LabelPair ≃ LabelPair where
  toFun p := ⟨p.val.map σ.toEmbedding, by simp [p.property]⟩
  invFun p := ⟨p.val.map σ.symm.toEmbedding, by simp [p.property]⟩
  left_inv p := by
    apply Subtype.ext
    ext i
    simp
  right_inv p := by
    apply Subtype.ext
    ext i
    simp

@[simp] theorem mem_relabelPair (σ : Equiv.Perm (Fin 4)) (p : LabelPair)
    (i : Fin 4) : i ∈ (relabelPair σ p).val ↔ σ.symm i ∈ p.val := by
  change i ∈ p.val.map σ.toEmbedding ↔ _
  simp

@[simp] theorem relabelPair_symm (σ : Equiv.Perm (Fin 4)) :
    (relabelPair σ).symm = relabelPair σ.symm := rfl

/-- The fixed canonical matching used by the matching-case construction. -/
def canonicalMatching : Finset LabelPair :=
  {⟨{0, 1}, by decide⟩, ⟨{2, 3}, by decide⟩}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- A permutation preserves precisely the allowed projected forest shapes.
This finite check enumerates the actual six label pairs. -/
theorem relabelPair_forestShape :
    ∀ (σ : Equiv.Perm (Fin 4)) (F : Finset LabelPair),
      LabelForestShape (F.image (relabelPair σ)) ↔ LabelForestShape F := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Any prescribed allowable forest can be renamed to the canonical
matching or the star with center zero. -/
theorem exists_canonical_relabeling :
    ∀ F : Finset LabelPair, LabelForestShape F →
      ∃ σ : Equiv.Perm (Fin 4),
        F.image (relabelPair σ) = canonicalMatching ∨
        F.image (relabelPair σ) = labelStar 0 := by
  decide

noncomputable section

open Classical

variable {V E : Type*}

/-- Relabel a decomposition without changing any actual piece. -/
def Decomposition.relabel {G : Multigraph V E} {label : E → LabelPair}
    {C : Finset E} {h : ℕ} (P : Decomposition G label C h)
    (σ : Equiv.Perm (Fin 4)) :
    Decomposition G (fun e => relabelPair σ (label e)) C h where
  parts := P.parts
  primary := P.primary
  primary_subset := P.primary_subset
  primary_card := P.primary_card
  nonempty := P.nonempty
  matching := P.matching
  primary_shape := by
    intro M hM
    obtain ⟨hi, hs⟩ := P.primary_shape M hM
    refine ⟨fun e he f hf h => hi he hf ((relabelPair σ).injective h), ?_⟩
    have hp := (relabelPair_forestShape σ (M.image label)).mpr hs
    simpa only [Finset.image_image] using hp
  surplus_shape := by
    intro M hM hn
    obtain ⟨hc, hp⟩ := P.surplus_shape M hM hn
    exact ⟨hc, fun e he f hf => congrArg (relabelPair σ) (hp e he f hf)⟩
  disjoint := P.disjoint
  cover := P.cover

/-- Relabeling vertices induces exactly the same relabeling of the
unordered projected endpoint pair of each original copy. -/
theorem labelQuotient_edgeLabelPair_relabel (G : Multigraph V E)
    (label : V → Fin 4) (σ : Equiv.Perm (Fin 4))
    (hjoin : ∀ e, label (G.firstEnd e) ≠ label (G.secondEnd e))
    (hjoin' : ∀ e, σ (label (G.firstEnd e)) ≠ σ (label (G.secondEnd e))) (e : E) :
    (G.labelQuotient (fun v => σ (label v)) hjoin').edgeLabelPair e =
      relabelPair σ ((G.labelQuotient label hjoin).edgeLabelPair e) := by
  apply Subtype.ext
  ext i
  rw [mem_relabelPair]
  simp only [Multigraph.mem_edgeLabelPair, Multigraph.labelQuotient_incident_iff]
  exact or_congr σ.apply_eq_iff_eq_symm_apply σ.apply_eq_iff_eq_symm_apply

end

end Overfull.FourOdd
