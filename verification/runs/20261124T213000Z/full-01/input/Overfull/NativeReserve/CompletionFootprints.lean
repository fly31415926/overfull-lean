import Overfull.NativeReserve.Greedy
import Overfull.CircuitPatterns.IncidenceLoad
import Overfull.BoundaryExtension.Assembly

/-!
# Completion footprints inside the original simple cores

The forbidden vertices are precisely the endpoints already covered by the
actual boundary. Its load follows from original-copy disjointness and the
core-complement degree bound.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical

variable {V E J : Type*} (G : Multigraph V E)

def coreFootprint (U : Finset V) (F : Finset E) : Finset ↥U :=
  SmallCuts.shore U (G.edgeSupport F)

@[simp] theorem mem_coreFootprint (U : Finset V) (F : Finset E) (v : ↥U) :
    v ∈ coreFootprint G U F ↔ v.val ∈ G.edgeSupport F :=
  SmallCuts.mem_shore U (G.edgeSupport F) v

theorem coreFootprint_card (U : Finset V) (F : Finset E) :
    (coreFootprint G U F).card = (U ∩ G.edgeSupport F).card := by
  rw [coreFootprint, SmallCuts.shore_card, inter_comm]

theorem coreFootprint_compl_card (U : Finset V) (F : Finset E) :
    (coreFootprint G U F)ᶜ.card = (U \ G.edgeSupport F).card :=
  SmallCuts.shore_compl_card U (G.edgeSupport F)

theorem coreFootprint_card_le_six (U : Finset V) (F : Finset E) (hcard : F.card ≤ 3) :
    (coreFootprint G U F).card ≤ 6 := by
  rw [coreFootprint_card]
  exact (card_le_card inter_subset_right).trans (G.edgeSupport_card_le_six hcard)

theorem coreFootprint_parity (U : Finset V) (F : Finset E)
    (heven : Even (U \ G.edgeSupport F).card) :
    (coreFootprint G U F).card % 2 = Fintype.card ↥U % 2 := by
  have hsum := card_compl_add_card (coreFootprint G U F)
  rw [coreFootprint_compl_card] at hsum
  rw [Nat.even_iff] at heven
  omega

theorem coreFootprint_load_eq [Fintype J] (U : Finset V) (F : J → Finset E) (v : ↥U) :
    (univ.filter (fun j => v ∈ coreFootprint G U (F j))).card =
      (univ.filter (fun j => v.val ∈ G.edgeSupport (F j))).card := by
  simp only [mem_coreFootprint]

variable [Fintype E]

theorem boundary_disjoint_core (F : Finset E) (U₀ U₁ Z U : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hU : U = U₀ ∨ U = U₁) (C : SmallCuts.Core G U)
    (hpool : ∀ e ∈ F, ∃ p, e ∈ poolCopies G U₀ U₁ Z p) :
    Disjoint F (OneCore.coreEdges C) := by
  apply disjoint_left.mpr
  intro e he heC
  obtain ⟨p, hep⟩ := hpool e he
  exact disjoint_left.mp
    (poolCopies_disjoint_core G U₀ U₁ Z U h01 h0Z h1Z hU C p) hep heC

theorem coreFootprint_load_le_error [Fintype J] {U : Finset V}
    (C : SmallCuts.Core G U) (F : J → Finset E)
    (hdisj : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hout : ∀ j, Disjoint (F j) (OneCore.coreEdges C))
    (k : ℕ) (a : ℝ) (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ v, (k : ℝ)-a ≤ (C.graph.degree v : ℝ)) (v : ↥U) :
    ((univ.filter (fun j => v ∈ coreFootprint G U (F j))).card : ℝ) ≤ a := by
  let used := univ.biUnion F
  have hsubset (j : J) : F j ⊆ used := by
    intro e he
    exact mem_biUnion.mpr ⟨j, mem_univ _, he⟩
  have houtUsed : Disjoint used (OneCore.coreEdges C) := by
    apply disjoint_left.mpr
    intro e he heC
    obtain ⟨j, _, heF⟩ := mem_biUnion.mp he
    exact disjoint_left.mp (hout j) heF heC
  have hload := G.family_support_load_le_degreeOn F used hdisj hsubset v.val
  have hdegreeUsed := pool_core_incidence_le_error G C used houtUsed k a hregular hdegree v
  rw [coreFootprint_load_eq]
  exact (Nat.cast_le.mpr hload).trans hdegreeUsed

theorem coreFootprint_admissible [Fintype J] {U : Finset V}
    (C : SmallCuts.Core G U) (F : J → Finset E)
    (hdisj : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hout : ∀ j, Disjoint (F j) (OneCore.coreEdges C))
    (hcard : ∀ j, (F j).card ≤ 3)
    (heven : ∀ j, Even (U \ G.edgeSupport (F j)).card)
    (k : ℕ) (a ε : ℝ) (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ v, (k : ℝ)-a ≤ (C.graph.degree v : ℝ))
    (hsize : 6 ≤ ε * U.card) (herror : a ≤ ε * U.card) :
    (∀ j, (coreFootprint G U (F j)).card % 2 = Fintype.card ↥U % 2) ∧
      (∀ j, ((coreFootprint G U (F j)).card : ℝ) ≤ ε * Fintype.card ↥U) ∧
      (∀ v : ↥U, ((univ.filter (fun j => v ∈ coreFootprint G U (F j))).card : ℝ) ≤
        ε * Fintype.card ↥U) := by
  refine ⟨fun j => coreFootprint_parity G U (F j) (heven j), ?_, ?_⟩
  · intro j
    have hh : ((coreFootprint G U (F j)).card : ℝ) ≤ 6 := by
      exact_mod_cast coreFootprint_card_le_six G U (F j) (hcard j)
    simpa only [Fintype.card_coe] using hh.trans hsize
  · intro v
    simpa only [Fintype.card_coe] using
      (coreFootprint_load_le_error G C F hdisj hout k a hregular hdegree v).trans herror

end Overfull.NativeReserve
