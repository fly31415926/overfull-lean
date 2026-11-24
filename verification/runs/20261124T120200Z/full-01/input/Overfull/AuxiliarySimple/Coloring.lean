import Overfull.AuxiliarySimple.Graph

/-! Colorings transported through the exact edge-copy equivalence. -/

noncomputable section

namespace Overfull.AuxiliarySimple

open Finset Classical Multigraph

variable {V E : Type*} (G : Multigraph V E) (hG : Function.Injective G.edge)

/-- Pull the simple-host coloring back to every original copy. -/
def originalColoring {k : ℕ}
    (c : (Multigraph.ofSimpleGraph (simpleGraph G)).EdgeColoring k) : G.EdgeColoring k where
  color e := c.color (edgeEquiv G hG e)
  proper := by
    intro e f v h he hf
    exact (edgeEquiv G hG).injective (c.proper h he hf)

/-- Push a coloring of original copies to the simple-host edge names. -/
def simpleColoring {k : ℕ} (c : G.EdgeColoring k) :
    (Multigraph.ofSimpleGraph (simpleGraph G)).EdgeColoring k where
  color e := c.color ((edgeEquiv G hG).symm e)
  proper := by
    intro e f v h he hf
    apply (edgeEquiv G hG).symm.injective
    exact c.proper h (by simpa using he) (by simpa using hf)

include hG in
theorem edgeColoring_iff (k : ℕ) :
    Nonempty ((Multigraph.ofSimpleGraph (simpleGraph G)).EdgeColoring k) ↔
      Nonempty (G.EdgeColoring k) :=
  ⟨fun ⟨c⟩ => ⟨originalColoring G hG c⟩, fun ⟨c⟩ => ⟨simpleColoring G hG c⟩⟩

variable [Fintype V] [Fintype E]

theorem originalColoring_colorClass_image {k : ℕ}
    (c : (Multigraph.ofSimpleGraph (simpleGraph G)).EdgeColoring k) (i : Fin k) :
    ((originalColoring G hG c).colorClass i).image (edgeEquiv G hG) = c.colorClass i := by
  ext e
  simp only [Finset.mem_image, Multigraph.EdgeColoring.colorClass, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact hf
  · intro he
    exact ⟨(edgeEquiv G hG).symm e, by simpa [originalColoring] using he,
      Equiv.apply_symm_apply _ _⟩

omit [Fintype V] [Fintype E] in
/-- Matching structure is preserved on arbitrary sets of original copies. -/
theorem isMatching_image_iff (M : Finset E) :
    (Multigraph.ofSimpleGraph (simpleGraph G)).IsMatching (M.image (edgeEquiv G hG)) ↔
      G.IsMatching M := by
  constructor
  · intro h e he f hf v hev hfv
    exact (edgeEquiv G hG).injective
      (h _ (mem_image.mpr ⟨e, he, rfl⟩) _ (mem_image.mpr ⟨f, hf, rfl⟩) v hev hfv)
  · intro h e he f hf v hev hfv
    obtain ⟨e', he', rfl⟩ := mem_image.mp he
    obtain ⟨f', hf', rfl⟩ := mem_image.mp hf
    exact congrArg (edgeEquiv G hG) (h e' he' f' hf' v hev hfv)

end Overfull.AuxiliarySimple
