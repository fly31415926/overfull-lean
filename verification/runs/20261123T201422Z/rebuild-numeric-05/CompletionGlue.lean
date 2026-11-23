import Overfull.NativeReserve.CompletionFootprints

/-!
# Gluing the two original embedded-core packings

Each completed matching contains its actual selected boundary and the
specified original copies of both local core matchings. The gluing retains
copy disjointness, the reserve, and all native boundary-pool counts.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical SmallCuts BoundaryExtension

variable {V E J : Type*} {G : Multigraph V E} {U₀ U₁ U : Finset V}

theorem coreEdges_disjoint_of_vertices (C₀ : Core G U₀) (C₁ : Core G U₁)
    (h01 : Disjoint U₀ U₁) : Disjoint (OneCore.coreEdges C₀) (OneCore.coreEdges C₁) := by
  apply disjoint_left.mpr
  intro e he hf
  have hv : G.firstEnd e ∈ G.edge e := (G.incident_iff e _).mpr (Or.inl rfl)
  exact disjoint_left.mp h01 (OneCore.coreEdges_endpoint C₀ he hv)
    (OneCore.coreEdges_endpoint C₁ hf hv)

def completedBoundary (C₀ : Core G U₀) (C₁ : Core G U₁) (F : Finset E)
    (N₀ : C₀.graph.Subgraph) (N₁ : C₁.graph.Subgraph) : Finset E :=
  F ∪ coreMatchingCopies C₀ N₀ ∪ coreMatchingCopies C₁ N₁

theorem completedBoundary_contains (C₀ : Core G U₀) (C₁ : Core G U₁) (F : Finset E)
    (N₀ : C₀.graph.Subgraph) (N₁ : C₁.graph.Subgraph) :
    F ⊆ completedBoundary C₀ C₁ F N₀ N₁ :=
  subset_union_left.trans subset_union_left

private theorem boundary_core_no_common (C : Core G U) (F : Finset E)
    (N : C.graph.Subgraph) (hverts : N.verts = (coreFootprint G U F : Set U)ᶜ)
    {e f : E} (he : e ∈ F) (hf : f ∈ coreMatchingCopies C N)
    {v : V} (hev : v ∈ G.edge e) (hfv : v ∈ G.edge f) : False := by
  have hvU := OneCore.coreEdges_endpoint C (coreMatchingCopies_subset_core C N hf) hfv
  let u : U := ⟨v,hvU⟩
  have hfoot : u ∈ coreFootprint G U F := (mem_coreFootprint G U F u).mpr
    ((G.mem_edgeSupport F v).mpr ⟨e,he,hev⟩)
  have hver := coreMatchingCopies_incident_verts C N hf u hfv
  rw [hverts] at hver
  exact hver hfoot

private theorem two_core_no_common (C₀ : Core G U₀) (C₁ : Core G U₁)
    (h01 : Disjoint U₀ U₁) (N₀ : C₀.graph.Subgraph) (N₁ : C₁.graph.Subgraph)
    {e f : E} (he : e ∈ coreMatchingCopies C₀ N₀) (hf : f ∈ coreMatchingCopies C₁ N₁)
    {v : V} (hev : v ∈ G.edge e) (hfv : v ∈ G.edge f) : False :=
  disjoint_left.mp h01
    (OneCore.coreEdges_endpoint C₀ (coreMatchingCopies_subset_core C₀ N₀ he) hev)
    (OneCore.coreEdges_endpoint C₁ (coreMatchingCopies_subset_core C₁ N₁ hf) hfv)

theorem completedBoundary_isMatching (C₀ : Core G U₀) (C₁ : Core G U₁)
    (h01 : Disjoint U₀ U₁) (F : Finset E) (hF : G.IsMatching F)
    (N₀ : C₀.graph.Subgraph) (N₁ : C₁.graph.Subgraph)
    (hN₀ : N₀.IsMatching) (hN₁ : N₁.IsMatching)
    (hverts₀ : N₀.verts = (coreFootprint G U₀ F : Set U₀)ᶜ)
    (hverts₁ : N₁.verts = (coreFootprint G U₁ F : Set U₁)ᶜ) :
    G.IsMatching (completedBoundary C₀ C₁ F N₀ N₁) := by
  intro e he f hf v hev hfv
  simp only [completedBoundary, mem_union] at he hf
  rcases he with (he | he) | he <;> rcases hf with (hf | hf) | hf
  · exact hF e he f hf v hev hfv
  · exact (boundary_core_no_common C₀ F N₀ hverts₀ he hf hev hfv).elim
  · exact (boundary_core_no_common C₁ F N₁ hverts₁ he hf hev hfv).elim
  · exact (boundary_core_no_common C₀ F N₀ hverts₀ hf he hfv hev).elim
  · exact coreMatchingCopies_isMatching C₀ N₀ hN₀ e he f hf v hev hfv
  · exact (two_core_no_common C₀ C₁ h01 N₀ N₁ he hf hev hfv).elim
  · exact (boundary_core_no_common C₁ F N₁ hverts₁ hf he hfv hev).elim
  · exact (two_core_no_common C₀ C₁ h01 N₀ N₁ hf he hfv hev).elim
  · exact coreMatchingCopies_isMatching C₁ N₁ hN₁ e he f hf v hev hfv

theorem completedBoundary_isPerfectMatching (C₀ : Core G U₀) (C₁ : Core G U₁)
    (Z : Finset V) (h01 : Disjoint U₀ U₁)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (F : Finset E) (hF : G.IsMatching F) (hZ : Z ⊆ G.edgeSupport F)
    (N₀ : C₀.graph.Subgraph) (N₁ : C₁.graph.Subgraph)
    (hN₀ : N₀.IsMatching) (hN₁ : N₁.IsMatching)
    (hverts₀ : N₀.verts = (coreFootprint G U₀ F : Set U₀)ᶜ)
    (hverts₁ : N₁.verts = (coreFootprint G U₁ F : Set U₁)ᶜ) :
    G.IsPerfectMatching (completedBoundary C₀ C₁ F N₀ N₁) := by
  apply G.isPerfectMatching_iff.mpr
  refine ⟨completedBoundary_isMatching C₀ C₁ h01 F hF N₀ N₁ hN₀ hN₁ hverts₀ hverts₁, ?_⟩
  intro v
  by_cases hvF : v ∈ G.edgeSupport F
  · obtain ⟨e, he, hev⟩ := (G.mem_edgeSupport F v).mp hvF
    exact ⟨e, completedBoundary_contains C₀ C₁ F N₀ N₁ he, hev⟩
  · rcases hcover v with hv | hv | hv
    · have hver : (⟨v,hv⟩ : U₀) ∈ N₀.verts := by
        rw [hverts₀]
        exact fun hh => hvF ((mem_coreFootprint G U₀ F ⟨v,hv⟩).mp hh)
      obtain ⟨e, he, hev⟩ := coreMatchingCopies_covers C₀ N₀ hN₀ ⟨v,hv⟩ hver
      exact ⟨e, mem_union_left _ (mem_union_right _ he), hev⟩
    · have hver : (⟨v,hv⟩ : U₁) ∈ N₁.verts := by
        rw [hverts₁]
        exact fun hh => hvF ((mem_coreFootprint G U₁ F ⟨v,hv⟩).mp hh)
      obtain ⟨e, he, hev⟩ := coreMatchingCopies_covers C₁ N₁ hN₁ ⟨v,hv⟩ hver
      exact ⟨e, mem_union_right _ he, hev⟩
    · exact (hvF (hZ hv)).elim

theorem completedBoundary_pairwiseDisjoint (C₀ : Core G U₀) (C₁ : Core G U₁)
    (h01 : Disjoint U₀ U₁) (F : J → Finset E)
    (N₀ : J → C₀.graph.Subgraph) (N₁ : J → C₁.graph.Subgraph)
    (hdisj : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hout₀ : ∀ j, Disjoint (F j) (OneCore.coreEdges C₀))
    (hout₁ : ∀ j, Disjoint (F j) (OneCore.coreEdges C₁))
    (hN₀ : Pairwise (fun i j => Disjoint (N₀ i).spanningCoe (N₀ j).spanningCoe))
    (hN₁ : Pairwise (fun i j => Disjoint (N₁ i).spanningCoe (N₁ j).spanningCoe)) :
    Pairwise (fun i j => Disjoint (completedBoundary C₀ C₁ (F i) (N₀ i) (N₁ i))
      (completedBoundary C₀ C₁ (F j) (N₀ j) (N₁ j))) := by
  intro i j hij
  have hF₀ (r s : J) : Disjoint (F r) (coreMatchingCopies C₀ (N₀ s)) :=
    (hout₀ r).mono_right (coreMatchingCopies_subset_core C₀ (N₀ s))
  have hF₁ (r s : J) : Disjoint (F r) (coreMatchingCopies C₁ (N₁ s)) :=
    (hout₁ r).mono_right (coreMatchingCopies_subset_core C₁ (N₁ s))
  have hcores (r s : J) : Disjoint (coreMatchingCopies C₀ (N₀ r)) (coreMatchingCopies C₁ (N₁ s)) :=
    (coreEdges_disjoint_of_vertices C₀ C₁ h01).mono
      (coreMatchingCopies_subset_core C₀ (N₀ r)) (coreMatchingCopies_subset_core C₁ (N₁ s))
  simp only [completedBoundary, disjoint_union_left, disjoint_union_right]
  exact ⟨⟨⟨hdisj hij, hF₀ i j⟩, hF₁ i j⟩,
    ⟨⟨(hF₀ j i).symm, coreMatchingCopies_disjoint C₀ _ _ (hN₀ hij)⟩, hcores i j⟩⟩,
    ⟨⟨(hF₁ j i).symm, (hcores j i).symm⟩,
      coreMatchingCopies_disjoint C₁ _ _ (hN₁ hij)⟩⟩

theorem completedBoundary_avoids (C₀ : Core G U₀) (C₁ : Core G U₁)
    (F A : Finset E) (hFA : Disjoint F A)
    (hA₀ : Disjoint A (OneCore.coreEdges C₀))
    (hA₁ : Disjoint A (OneCore.coreEdges C₁))
    (N₀ : C₀.graph.Subgraph) (N₁ : C₁.graph.Subgraph) :
    Disjoint (completedBoundary C₀ C₁ F N₀ N₁) A := by
  simp only [completedBoundary, disjoint_union_left]
  exact ⟨⟨hFA, (hA₀.mono_right (coreMatchingCopies_subset_core C₀ N₀)).symm⟩,
    (hA₁.mono_right (coreMatchingCopies_subset_core C₁ N₁)).symm⟩

theorem mem_coreMatchingCopies_of_embedded (C : Core G U) (N : C.graph.Subgraph)
    (e : C.graph.edgeSet) :
    C.edgeMap e ∈ coreMatchingCopies C N ↔ e.val ∈ N.edgeSet := by
  constructor
  · intro he
    obtain ⟨f, hf, hfe⟩ := (mem_coreMatchingCopies C N _).mp he
    have hfe' : f = e := C.edgeMap.injective hfe
    subst f
    exact (mem_filter.mp hf).2
  · intro he
    exact (mem_coreMatchingCopies C N _).mpr ⟨e, mem_filter.mpr ⟨mem_univ _,he⟩,rfl⟩

theorem completedBoundary_core₀_copy_iff (C₀ : Core G U₀) (C₁ : Core G U₁)
    (h01 : Disjoint U₀ U₁) (F : Finset E) (hout : Disjoint F (OneCore.coreEdges C₀))
    (N₀ : C₀.graph.Subgraph) (N₁ : C₁.graph.Subgraph) (e : C₀.graph.edgeSet) :
    C₀.edgeMap e ∈ completedBoundary C₀ C₁ F N₀ N₁ ↔ e.val ∈ N₀.edgeSet := by
  have heC : C₀.edgeMap e ∈ OneCore.coreEdges C₀ := (OneCore.mem_coreEdges C₀ _).mpr ⟨e,rfl⟩
  have hnotF : C₀.edgeMap e ∉ F := fun he => disjoint_left.mp hout he heC
  have hnot₁ : C₀.edgeMap e ∉ coreMatchingCopies C₁ N₁ := by
    intro he
    exact disjoint_left.mp (coreEdges_disjoint_of_vertices C₀ C₁ h01) heC
      (coreMatchingCopies_subset_core C₁ N₁ he)
  simp only [completedBoundary, mem_union, hnotF, false_or, hnot₁, or_false]
  exact mem_coreMatchingCopies_of_embedded C₀ N₀ e

theorem completedBoundary_core₁_copy_iff (C₀ : Core G U₀) (C₁ : Core G U₁)
    (h01 : Disjoint U₀ U₁) (F : Finset E) (hout : Disjoint F (OneCore.coreEdges C₁))
    (N₀ : C₀.graph.Subgraph) (N₁ : C₁.graph.Subgraph) (e : C₁.graph.edgeSet) :
    C₁.edgeMap e ∈ completedBoundary C₀ C₁ F N₀ N₁ ↔ e.val ∈ N₁.edgeSet := by
  have heC : C₁.edgeMap e ∈ OneCore.coreEdges C₁ := (OneCore.mem_coreEdges C₁ _).mpr ⟨e,rfl⟩
  have hnotF : C₁.edgeMap e ∉ F := fun he => disjoint_left.mp hout he heC
  have hnot₀ : C₁.edgeMap e ∉ coreMatchingCopies C₀ N₀ := by
    intro he
    exact disjoint_left.mp (coreEdges_disjoint_of_vertices C₀ C₁ h01)
      (coreMatchingCopies_subset_core C₀ N₀ he) heC
  simp only [completedBoundary, mem_union, hnotF, false_or, hnot₀]
  exact mem_coreMatchingCopies_of_embedded C₁ N₁ e

variable [Fintype E]

theorem completedBoundary_added_internal (C₀ : Core G U₀) (C₁ : Core G U₁)
    (F : Finset E) (N₀ : C₀.graph.Subgraph) (N₁ : C₁.graph.Subgraph)
    (e : E) (he : e ∈ completedBoundary C₀ C₁ F N₀ N₁) :
    e ∈ F ∨ e ∈ G.internalOn univ U₀ ∨ e ∈ G.internalOn univ U₁ := by
  have hinside (U : Finset V) (C : Core G U) (N : C.graph.Subgraph)
      (heN : e ∈ coreMatchingCopies C N) : e ∈ G.internalOn univ U := by
    have h := OneCore.coreEdges_subset_internal C (coreMatchingCopies_subset_core C N heN)
    exact mem_filter.mpr ⟨mem_univ _, (G.mem_internalEdges U e).mp h⟩
  rcases mem_union.mp he with he | he
  · rcases mem_union.mp he with he | he
    · exact Or.inl he
    · exact Or.inr (Or.inl (hinside U₀ C₀ N₀ he))
  · exact Or.inr (Or.inr (hinside U₁ C₁ N₁ he))

theorem completedBoundary_pool_eq (C₀ : Core G U₀) (C₁ : Core G U₁)
    (Z : Finset V) (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (F : Finset E) (N₀ : C₀.graph.Subgraph) (N₁ : C₁.graph.Subgraph) (p : PoolKind Z) :
    completedBoundary C₀ C₁ F N₀ N₁ ∩ poolCopies G U₀ U₁ Z p =
      F ∩ poolCopies G U₀ U₁ Z p := by
  ext e
  constructor
  · intro he
    obtain ⟨he, hep⟩ := mem_inter.mp he
    rcases mem_union.mp he with he | he
    · rcases mem_union.mp he with he | he
      · exact mem_inter.mpr ⟨he,hep⟩
      · exact (disjoint_left.mp
          (poolCopies_disjoint_core G U₀ U₁ Z U₀ h01 h0Z h1Z (Or.inl rfl) C₀ p)
          hep (coreMatchingCopies_subset_core C₀ N₀ he)).elim
    · exact (disjoint_left.mp
        (poolCopies_disjoint_core G U₀ U₁ Z U₁ h01 h0Z h1Z (Or.inr rfl) C₁ p)
        hep (coreMatchingCopies_subset_core C₁ N₁ he)).elim
  · intro he
    obtain ⟨he, hep⟩ := mem_inter.mp he
    exact mem_inter.mpr ⟨completedBoundary_contains C₀ C₁ F N₀ N₁ he,hep⟩

theorem glue_two_core_packings {q : ℕ} {θ₀ θ₁ σ : ℝ}
    (C₀ : Core G U₀) (C₁ : Core G U₁) (Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (F : Fin q → Finset E) (hF : ∀ j, G.IsMatching (F j))
    (hdisj : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hZ : ∀ j, Z ⊆ G.edgeSupport (F j))
    (hpool : ∀ j, ∀ e ∈ F j, ∃ p, e ∈ poolCopies G U₀ U₁ Z p)
    (A : Finset E) (havoid : ∀ j, Disjoint (F j) A)
    (hApool : ∀ e ∈ A, ∃ p, e ∈ poolCopies G U₀ U₁ Z p)
    (P₀ : BoundaryExtension.CorePacking C₀.graph q
      (fun j => coreFootprint G U₀ (F j)) θ₀ σ)
    (P₁ : BoundaryExtension.CorePacking C₁.graph q
      (fun j => coreFootprint G U₁ (F j)) θ₁ σ) :
    let N := fun j => completedBoundary C₀ C₁ (F j) (P₀.matching j) (P₁.matching j)
    (∀ j, G.IsPerfectMatching (N j)) ∧
      Pairwise (fun i j => Disjoint (N i) (N j)) ∧
      (∀ j, Disjoint (N j) A) ∧
      (∀ j, F j ⊆ N j) ∧
      (∀ j, ∀ e ∈ N j,
        e ∈ F j ∨ e ∈ G.internalOn univ U₀ ∨ e ∈ G.internalOn univ U₁) ∧
      (∀ j p, N j ∩ poolCopies G U₀ U₁ Z p = F j ∩ poolCopies G U₀ U₁ Z p) := by
  dsimp only
  have hout₀ (j : Fin q) := boundary_disjoint_core G (F j) U₀ U₁ Z U₀
    h01 h0Z h1Z (Or.inl rfl) C₀ (hpool j)
  have hout₁ (j : Fin q) := boundary_disjoint_core G (F j) U₀ U₁ Z U₁
    h01 h0Z h1Z (Or.inr rfl) C₁ (hpool j)
  have hA₀ := boundary_disjoint_core G A U₀ U₁ Z U₀ h01 h0Z h1Z (Or.inl rfl) C₀ hApool
  have hA₁ := boundary_disjoint_core G A U₀ U₁ Z U₁ h01 h0Z h1Z (Or.inr rfl) C₁ hApool
  refine ⟨?_, completedBoundary_pairwiseDisjoint C₀ C₁ h01 F P₀.matching P₁.matching
    hdisj hout₀ hout₁ P₀.disjoint P₁.disjoint, ?_, ?_, ?_, ?_⟩
  · intro j
    exact completedBoundary_isPerfectMatching C₀ C₁ Z h01 hcover (F j) (hF j) (hZ j)
      (P₀.matching j) (P₁.matching j) (P₀.isMatching j) (P₁.isMatching j) (P₀.verts j) (P₁.verts j)
  · intro j
    exact completedBoundary_avoids C₀ C₁ (F j) A (havoid j) hA₀ hA₁ (P₀.matching j) (P₁.matching j)
  · exact fun j => completedBoundary_contains C₀ C₁ (F j) (P₀.matching j) (P₁.matching j)
  · exact fun j e he => completedBoundary_added_internal C₀ C₁ (F j)
      (P₀.matching j) (P₁.matching j) e he
  · exact fun j p => completedBoundary_pool_eq C₀ C₁ Z h01 h0Z h1Z (F j)
      (P₀.matching j) (P₁.matching j) p

end Overfull.NativeReserve
