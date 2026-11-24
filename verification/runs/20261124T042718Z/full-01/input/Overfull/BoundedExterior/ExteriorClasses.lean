import Overfull.BoundedExterior.MatchingSplit
import Overfull.OrdinaryFactorization.ExteriorSelection

/-!
# The exterior part of an actual complementary color class

The complement of an embedded simple core can contain additional copies
internal to the core vertex set.  The classes used to choose an exterior
bipartition retain precisely the copies having an endpoint outside that set.
The restriction does not change coverage at any exterior vertex.
-/

noncomputable section

namespace Overfull.BoundedExterior

open Finset Classical SmallCuts

variable {V E : Type*} [Fintype E]
variable {G : Multigraph V E} {F : Finset E} {k : ℕ}

/-- Original copies of one color having an endpoint outside `U`. -/
def exteriorClass (U : Finset V) (c : (G.restrictEdges F).EdgeColoring k)
    (i : Fin k) : Finset E :=
  ((c.colorClass i).map (Function.Embedding.subtype (fun e => e ∈ F))).filter
    (fun e => e ∉ G.internalEdges U)

@[simp] theorem mem_exteriorClass (U : Finset V)
    (c : (G.restrictEdges F).EdgeColoring k) (i : Fin k) (e : E) :
    e ∈ exteriorClass U c i ↔
      (∃ f : F, c.color f = i ∧ f.val = e) ∧ e ∉ G.internalEdges U := by
  simp only [exteriorClass, mem_filter, mem_map, Multigraph.EdgeColoring.colorClass,
    mem_univ, true_and, Function.Embedding.subtype_apply]

theorem exteriorClass_subset_outside (U : Finset V)
    (c : (G.restrictEdges F).EdgeColoring k) (i : Fin k) :
    exteriorClass U c i ⊆ (G.internalEdges U)ᶜ := by
  intro e he
  exact mem_compl.mpr ((mem_exteriorClass U c i e).mp he).2

theorem exteriorClass_isMatching (U : Finset V)
    (c : (G.restrictEdges F).EdgeColoring k) (i : Fin k) :
    G.IsMatching (exteriorClass U c i) := by
  intro e he f hf v hev hfv
  obtain ⟨⟨e', he', rfl⟩, _⟩ := (mem_exteriorClass U c i e).mp he
  obtain ⟨⟨f', hf', rfl⟩, _⟩ := (mem_exteriorClass U c i f).mp hf
  exact congrArg Subtype.val (c.proper (he'.trans hf'.symm) hev hfv)

/-- Coverage at an exterior vertex is retained by the exterior restriction. -/
theorem exteriorClass_covers_outside (U : Finset V)
    (c : (G.restrictEdges F).EdgeColoring k) (i : Fin k) (z : V)
    (hz : z ∉ U) (hcover : c.Covers i z) :
    ∃ e ∈ exteriorClass U c i, z ∈ G.edge e := by
  obtain ⟨f, hf, hzf⟩ := hcover
  refine ⟨f.val, (mem_exteriorClass U c i f.val).mpr ⟨⟨f, hf, rfl⟩, ?_⟩, hzf⟩
  intro hint
  obtain ⟨hfirst, hsecond⟩ := (G.mem_internalEdges U f.val).mp hint
  rcases (G.incident_iff f.val z).mp hzf with rfl | rfl
  · exact hz hfirst
  · exact hz hsecond

variable [Fintype V] {U : Finset V}

/-- Every exterior vertex has its original full degree in the core complement. -/
theorem coreComplement_exteriorClass_covers (C : Core G U)
    (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k)
    (hregular : ∀ v, G.degree v = k) (i : Fin k) :
    ∀ z ∈ Uᶜ, ∃ e ∈ exteriorClass U c i, z ∈ G.edge e := by
  intro z hz
  have hzU : z ∉ U := mem_compl.mp hz
  apply exteriorClass_covers_outside U c i z hzU
  exact c.covers_of_degree_eq z
    ((OrdinaryFactorization.complement_degree_outside C z hzU).trans (hregular z)) i

/-- Parity and the bounded exterior size apply to the actual exterior footprint. -/
theorem coreComplement_exteriorClass_footprint_bounds (C : Core G U)
    (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k)
    (hregular : ∀ v, G.degree v = k) (heven : Even Uᶜ.card) (i : Fin k) :
    Even (coreFootprintSubtype G U (exteriorClass U c i)).card ∧
      (coreFootprintSubtype G U (exteriorClass U c i)).card ≤ Uᶜ.card :=
  matching_footprintSubtype_bounds G U (exteriorClass U c i)
    (exteriorClass_isMatching U c i) (exteriorClass_subset_outside U c i)
    (coreComplement_exteriorClass_covers C c hregular i) heven

/-- A balanced exterior footprint extends to an actual balanced exterior split. -/
theorem coreComplement_exteriorClass_split (C : Core G U)
    (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k)
    (A B : Finset U) (hregular : ∀ v, G.degree v = k)
    (hAB : Disjoint A B) (hunion : A ∪ B = univ) (i : Fin k)
    (hbalance : (coreFootprintSubtype G U (exteriorClass U c i) ∩ A).card =
      (coreFootprintSubtype G U (exteriorClass U c i) ∩ B).card) :
    ∃ ZA ZB : Finset V, Disjoint ZA ZB ∧ ZA ∪ ZB = Uᶜ ∧ ZA.card = ZB.card ∧
      ∀ e ∈ exteriorClass U c i,
        e ∈ G.cutEdges (A.map (Function.Embedding.subtype (fun v => v ∈ U)) ∪ ZA) :=
  exists_balanced_exterior_split_subtype G U A B (exteriorClass U c i)
    (exteriorClass_isMatching U c i) (exteriorClass_subset_outside U c i)
    (coreComplement_exteriorClass_covers C c hregular i) hAB hunion hbalance

end Overfull.BoundedExterior
