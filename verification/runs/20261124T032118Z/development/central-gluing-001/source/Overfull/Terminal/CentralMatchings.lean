import Overfull.Terminal.Contraction
import Overfull.NativeTerminal.ColoringGlue

/-!
# Actual joining matchings in the two-apex host

Each original joining matching meets each contracted odd shore once.  It
therefore remains a matching after both contractions.  These matchings cover
every central copy outside the retained core, and their singleton cuts give
the exact degrees at both apices.
-/

noncomputable section

namespace Overfull.Terminal

open Finset Classical Multigraph SmallCuts BoundaryExtension

variable {V E : Type*} [Fintype E]

theorem cutSize_of_matching_partition (G : Multigraph V E) (A : Finset V) (k : ℕ)
    (M : Fin k → Finset E) (hdisj : Pairwise (fun i j => Disjoint (M i) (M j)))
    (hcover : ∀ e ∈ G.cutEdges A, ∃ i, e ∈ M i)
    (hcross : ∀ i, (M i ∩ G.cutEdges A).card = 1) : G.cutSize A = k := by
  have hparts : univ.biUnion (fun i => M i ∩ G.cutEdges A) = G.cutEdges A := by
    ext e
    simp only [mem_biUnion,mem_univ,true_and,mem_inter]
    constructor
    · rintro ⟨i,_,he⟩
      exact he
    · intro he
      obtain ⟨i,hi⟩ := hcover e he
      exact ⟨i,hi,he⟩
  have hp : (univ : Finset (Fin k)).toSet.PairwiseDisjoint (fun i => M i ∩ G.cutEdges A) := by
    intro i _ j _ hij
    exact (hdisj hij).mono inter_subset_left inter_subset_left
  change (G.cutEdges A).card = k
  rw [← hparts,card_biUnion hp]
  simp only [hcross,sum_const,card_univ,Fintype.card_fin,smul_eq_mul,mul_one]

def centralMatching (G : Multigraph V E) (U A : Finset V) (M : Finset E) :
    Finset (CentralEdge G U A) := univ.filter (fun e => e.val ∈ M)

@[simp] theorem mem_centralMatching (G : Multigraph V E) (U A : Finset V)
    (M : Finset E) (e : CentralEdge G U A) :
    e ∈ centralMatching G U A M ↔ e.val ∈ M := by simp [centralMatching]

theorem centralMatching_isMatching (G : Multigraph V E) (U A B : Finset V)
    (hUA : Disjoint U A) (hUB : Disjoint U B) (hAB : Disjoint A B)
    (hcover : ∀ v, v ∈ U ∨ v ∈ A ∨ v ∈ B)
    (M : Finset E) (hM : G.IsMatching M)
    (hA : (M ∩ G.cutEdges A).card ≤ 1) (hB : (M ∩ G.cutEdges B).card ≤ 1) :
    (centralGraph G U A).IsMatching (centralMatching G U A M) := by
  intro e he f hf v hev hfv
  have heM := (mem_centralMatching G U A M e).mp he
  have hfM := (mem_centralMatching G U A M f).mp hf
  apply Subtype.ext
  rcases v with u | i
  · exact hM e.val heM f.val hfM u.val
      ((central_incident_inl_iff G U A e u).mp hev)
      ((central_incident_inl_iff G U A f u).mp hfv)
  · fin_cases i
    · exact Finset.card_le_one.mp hA _
        (mem_inter.mpr ⟨heM,(central_incident_first_apex_iff G U A hUA e).mp hev⟩) _
        (mem_inter.mpr ⟨hfM,(central_incident_first_apex_iff G U A hUA f).mp hfv⟩)
    · exact Finset.card_le_one.mp hB _
        (mem_inter.mpr ⟨heM,(central_incident_second_apex_iff G U A B hUB hAB hcover e).mp hev⟩) _
        (mem_inter.mpr ⟨hfM,(central_incident_second_apex_iff G U A B hUB hAB hcover f).mp hfv⟩)

theorem central_external_incident_apex (G : Multigraph V E) (U A : Finset V)
    (e : CentralEdge G U A)
    (he : e ∉ (centralGraph G U A).internalEdges (centralCoreVertices U)) :
    ∃ i : Fin 2, Sum.inr i ∈ (centralGraph G U A).edge e := by
  let H := centralGraph G U A
  cases hf : H.firstEnd e with
  | inr i =>
      refine ⟨i,?_⟩
      rw [← H.edge_eq e,hf]
      simp
  | inl u =>
      cases hs : H.secondEnd e with
      | inr i =>
          refine ⟨i,?_⟩
          rw [← H.edge_eq e,hs]
          simp
      | inl v =>
          exact (he ((H.mem_internalEdges (centralCoreVertices U) e).mpr (by
            simp [hf,hs]))).elim

theorem centralMatching_external_cover (G : Multigraph V E) (U A B : Finset V)
    (hUA : Disjoint U A) (hUB : Disjoint U B) (hAB : Disjoint A B)
    (hcover : ∀ v, v ∈ U ∨ v ∈ A ∨ v ∈ B)
    (k : ℕ) (M : Fin k → Finset E)
    (hM : univ.biUnion M = G.cutEdges A ∪ G.cutEdges B) :
    ∀ e, e ∉ (centralGraph G U A).internalEdges (centralCoreVertices U) →
      ∃ i, e ∈ centralMatching G U A (M i) := by
  intro e he
  obtain ⟨j,hj⟩ := central_external_incident_apex G U A e he
  have hcut : e.val ∈ G.cutEdges A ∪ G.cutEdges B := by
    fin_cases j
    · exact mem_union_left _ ((central_incident_first_apex_iff G U A hUA e).mp hj)
    · exact mem_union_right _ ((central_incident_second_apex_iff G U A B hUB hAB hcover e).mp hj)
  rw [← hM] at hcut
  obtain ⟨i,_,hi⟩ := mem_biUnion.mp hcut
  exact ⟨i,(mem_centralMatching G U A (M i) e).mpr hi⟩

def centralRetainedLift (G : Multigraph V E) (U A : Finset V)
    (e : RetainedEdge G U) : CentralEdge G U A :=
  ⟨e.val,by
    obtain ⟨u,hu⟩ := e.property
    exact central_retained_of_core_incident G U A u.property hu⟩

/-- Central colors also form a proper coloring at original outside vertices. -/
def centralColoringToRetained (G : Multigraph V E) (U A : Finset V) (k : ℕ)
    (c : (centralGraph G U A).EdgeColoring k) :
    PaletteColoring (retainedGraph G U) (Fin k) where
  color e := c.color (centralRetainedLift G U A e)
  proper := by
    intro e f v hc hev hfv
    apply Subtype.ext
    exact congrArg Subtype.val (c.proper hc
      (central_incident_of_original G U A (centralRetainedLift G U A e) hev)
      (central_incident_of_original G U A (centralRetainedLift G U A f) hfv))

def centralBoundaryLabels (G : Multigraph V E) (U A X : Finset V) (k : ℕ)
    (z : CentralVertex U) (hfiber : ∀ v, centralMap U A v = z ↔ v ∈ X)
    (c : (centralGraph G U A).EdgeColoring k) (e : G.cutEdges X) : Fin k :=
  c.color (centralBoundaryLift G U A X z hfiber e)

theorem centralBoundaryLabels_injective (G : Multigraph V E) (U A X : Finset V) (k : ℕ)
    (z : CentralVertex U) (hfiber : ∀ v, centralMap U A v = z ↔ v ∈ X)
    (c : (centralGraph G U A).EdgeColoring k) :
    Function.Injective (centralBoundaryLabels G U A X k z hfiber c) := by
  intro e f h
  apply Subtype.ext
  exact congrArg Subtype.val (c.proper h
    ((central_incident_fiber_iff G U A X z hfiber _).mpr e.property)
    ((central_incident_fiber_iff G U A X z hfiber _).mpr f.property))

end Overfull.Terminal
