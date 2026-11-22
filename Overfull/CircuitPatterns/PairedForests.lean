import Overfull.CircuitPatterns.Pairing
import Overfull.CircuitPatterns.Forest

/-!
# Actual matching forests from paired path families

The retained forests are subsets of the original edge copies. Their label
maps are injective, their projections are explicit perfect matchings or
three-edge stars, and the discarded copies have even degree at each label.

The final pairing theorem assumes the stated matching, endpoint-load, and
projected-parity properties of its input families. It does not assume or
construct a compatible-circuit decomposition.
-/

noncomputable section

namespace Overfull.CircuitPatterns

open Finset Classical Compression

variable {V E I J : Type*}

/-- An injective projection preserves every actual incidence count. -/
theorem pairDegree_image_of_injOn (M : Finset E) (label : E → LabelPair)
    (hinj : Set.InjOn label M) (i : Fin 4) :
    pairDegree (M.image label) i = copyDegree M label i := by
  have hfilter : (M.image label).filter (fun p => i ∈ p.val) =
      (M.filter (fun e => i ∈ (label e).val)).image label := by
    ext p
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨⟨e, he, rfl⟩, hi⟩
      exact ⟨e, ⟨he, hi⟩, rfl⟩
    · rintro ⟨e, ⟨he, hi⟩, rfl⟩
      exact ⟨⟨e, he, rfl⟩, hi⟩
  unfold pairDegree copyDegree
  rw [hfilter]
  exact card_image_of_injOn (hinj.mono (filter_subset _ _))

/-- Exact projected-degree accounting for a disjoint union of actual copies. -/
theorem copyDegree_union_of_disjoint (M N : Finset E) (label : E → LabelPair)
    (hdisjoint : Disjoint M N) (i : Fin 4) :
    copyDegree (M ∪ N) label i = copyDegree M label i + copyDegree N label i := by
  unfold copyDegree
  rw [filter_union]
  exact card_union_of_disjoint (hdisjoint.mono (filter_subset _ _) (filter_subset _ _))

/-- The retained and discarded copies account for the original degree exactly. -/
theorem copyDegree_sdiff_add (M T : Finset E) (label : E → LabelPair)
    (hT : T ⊆ M) (i : Fin 4) :
    copyDegree (M \ T) label i + copyDegree T label i = copyDegree M label i := by
  have hfilter : (M \ T).filter (fun e => i ∈ (label e).val) =
      (M.filter (fun e => i ∈ (label e).val)) \
        (T.filter (fun e => i ∈ (label e).val)) := by
    ext e
    simp only [mem_filter, mem_sdiff]
    tauto
  unfold copyDegree
  rw [hfilter]
  exact card_sdiff_add_card_eq_card (filter_subset_filter _ hT)

/-- Preserving a projected degree modulo two leaves an even discarded degree. -/
theorem copyDegree_sdiff_even (M T : Finset E) (label : E → LabelPair)
    (hT : T ⊆ M) (i : Fin 4)
    (hparity : copyDegree T label i % 2 = copyDegree M label i % 2) :
    Even (copyDegree (M \ T) label i) := by
  apply Nat.even_iff.mpr
  have hsum := copyDegree_sdiff_add M T label hT i
  omega

/-- Extract an actual matching forest from an all-odd projected matching.
The selected copies project injectively, and every discarded projected
degree is even. -/
theorem exists_odd_matching_forest (G : Multigraph V E) (M : Finset E)
    (label : E → LabelPair) (hM : G.IsMatching M)
    (hodd : ∀ i : Fin 4, Odd (copyDegree M label i)) :
    ∃ T : Finset E, T ⊆ M ∧ G.IsMatching T ∧ Set.InjOn label T ∧
      LabelForestShape (T.image label) ∧ T.card ≤ 3 ∧
      ∀ i : Fin 4, Even (copyDegree (M \ T) label i) := by
  obtain ⟨T, hTM, hTcard, hparity, hinj, hforest⟩ := exists_parity_subset M label
  refine ⟨T, hTM, ?_, hinj, ?_, hTcard, ?_⟩
  · intro e he f hf v hev hfv
    exact hM e (hTM he) f (hTM hf) v hev hfv
  · apply odd_leafForest_classification (T.image label) hforest
    intro i
    rw [pairDegree_image_of_injOn T label hinj i, hparity i]
    exact Nat.odd_iff.mp (hodd i)
  · intro i
    exact copyDegree_sdiff_even M T label hTM i (hparity i)

/-- Disjoint endpoint supports exclude a shared actual edge copy. -/
theorem disjoint_copies_of_disjoint_support (G : Multigraph V E)
    (M N : Finset E) (hdisjoint : Disjoint (G.edgeSupport M) (G.edgeSupport N)) :
    Disjoint M N := by
  apply Finset.disjoint_left.mpr
  intro e heM heN
  have hv : G.firstEnd e ∈ G.edge e := (G.incident_iff e _).mpr (Or.inl rfl)
  exact Finset.disjoint_left.mp hdisjoint
    ((G.mem_edgeSupport M _).mpr ⟨e, heM, hv⟩)
    ((G.mem_edgeSupport N _).mpr ⟨e, heN, hv⟩)

/-- Hall pairing followed by actual parity-forest extraction. The odd-sum
hypothesis allows every pairing, as for the two fixed-endpoint path families
in the four-odd-parts argument. -/
theorem exists_paired_matching_forests (G : Multigraph V E) (u a : ℕ)
    (M N : Fin u → Finset E) (label : E → LabelPair)
    (hM : ∀ i, G.IsMatching (M i)) (hN : ∀ i, G.IsMatching (N i))
    (hsizeM : ∀ i, (G.edgeSupport (M i)).card ≤ 6)
    (hsizeN : ∀ i, (G.edgeSupport (N i)).card ≤ 6)
    (hloadM : ∀ v, (univ.filter (fun i => v ∈ G.edgeSupport (M i))).card ≤ a)
    (hloadN : ∀ v, (univ.filter (fun i => v ∈ G.edgeSupport (N i))).card ≤ a)
    (hsize : 12 * a < u)
    (hodd : ∀ i j (k : Fin 4), Odd (copyDegree (M i) label k + copyDegree (N j) label k)) :
    ∃ f : Equiv.Perm (Fin u), ∃ T : Fin u → Finset E,
      (∀ i, Disjoint (G.edgeSupport (M i)) (G.edgeSupport (N (f i)))) ∧
      (∀ i, G.IsMatching (M i ∪ N (f i))) ∧
      ∀ i, T i ⊆ M i ∪ N (f i) ∧ G.IsMatching (T i) ∧
        Set.InjOn label (T i) ∧ LabelForestShape ((T i).image label) ∧
        (T i).card ≤ 3 ∧ G.IsMatching ((M i ∪ N (f i)) \ T i) ∧
        (∀ k : Fin 4, Even (copyDegree ((M i ∪ N (f i)) \ T i) label k)) := by
  obtain ⟨f, hsupports, hmatching⟩ := exists_six_endpoint_pairing G u a M N
    hM hN hsizeM hsizeN hloadM hloadN hsize
  have hoddUnion (i : Fin u) (k : Fin 4) : Odd (copyDegree (M i ∪ N (f i)) label k) := by
    rw [copyDegree_union_of_disjoint (M i) (N (f i)) label
      (disjoint_copies_of_disjoint_support G _ _ (hsupports i)) k]
    exact hodd i (f i) k
  have hex (i : Fin u) := exists_odd_matching_forest G (M i ∪ N (f i))
    label (hmatching i) (hoddUnion i)
  choose T hTsub hTmatching hinj hshape hTcard heven using hex
  refine ⟨f, T, hsupports, hmatching, fun i =>
    ⟨hTsub i, hTmatching i, hinj i, hshape i, hTcard i, ?_, heven i⟩⟩
  intro e he g hg v hev hgv
  exact hmatching i e (mem_sdiff.mp he).1 g (mem_sdiff.mp hg).1 v hev hgv

/-- Reindexing the second family by a bijection preserves all original copies. -/
theorem paired_unions_cover [Fintype I] [Fintype J]
    (M : I → Finset E) (N : J → Finset E) (f : I ≃ J) :
    univ.biUnion (fun i => M i ∪ N (f i)) = univ.biUnion M ∪ univ.biUnion N := by
  ext e
  simp only [mem_biUnion, mem_univ, true_and, mem_union]
  constructor
  · rintro ⟨i, hi | hi⟩
    · exact Or.inl ⟨i, hi⟩
    · exact Or.inr ⟨f i, hi⟩
  · rintro (⟨i, hi⟩ | ⟨j, hj⟩)
    · exact ⟨i, Or.inl hi⟩
    · exact ⟨f.symm j, Or.inr (by simpa only [f.apply_symm_apply] using hj)⟩

/-- Pairing preserves edge disjointness when the two original families
jointly consist of disjoint edge-copy sets. -/
theorem paired_unions_pairwise_disjoint (M : I → Finset E) (N : J → Finset E)
    (f : I ↪ J)
    (hM : Pairwise (fun i j => Disjoint (M i) (M j)))
    (hN : Pairwise (fun i j => Disjoint (N i) (N j)))
    (hcross : ∀ i j, Disjoint (M i) (N j)) :
    Pairwise (fun i j => Disjoint (M i ∪ N (f i)) (M j ∪ N (f j))) := by
  intro i j hij
  rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
  exact ⟨⟨hM hij, hcross i (f j)⟩,
    ⟨(hcross j (f i)).symm, hN (fun h => hij (f.injective h))⟩⟩

/-- Selecting a subset in each indexed part preserves that family's edge
disjointness. The same statement applies to the actual remainders. -/
theorem selected_family_pairwise_disjoint (P T : I → Finset E)
    (hP : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hT : ∀ i, T i ⊆ P i) : Pairwise (fun i j => Disjoint (T i) (T j)) := by
  intro i j hij
  exact (hP hij).mono (hT i) (hT j)

/-- The retained copies and actual set-difference remainders cover the
original indexed family exactly. -/
theorem selected_family_remainders_cover [Fintype I] (P T : I → Finset E)
    (hT : ∀ i, T i ⊆ P i) :
    univ.biUnion T ∪ univ.biUnion (fun i => P i \ T i) = univ.biUnion P := by
  ext e
  simp only [mem_union, mem_biUnion, mem_univ, true_and, mem_sdiff]
  constructor
  · rintro (⟨i, hi⟩ | ⟨i, hi, _⟩)
    · exact ⟨i, hT i hi⟩
    · exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    by_cases he : e ∈ T i
    · exact Or.inl ⟨i, he⟩
    · exact Or.inr ⟨i, hi, he⟩

/-- No original copy is counted both as a retained forest edge and as a
remainder edge when the original family is edge-disjoint. -/
theorem selected_family_remainders_disjoint [Fintype I] (P T : I → Finset E)
    (hP : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hT : ∀ i, T i ⊆ P i) :
    Disjoint (univ.biUnion T) (univ.biUnion (fun i => P i \ T i)) := by
  apply Finset.disjoint_left.mpr
  intro e heT heR
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp heT
  obtain ⟨j, _, hj⟩ := mem_biUnion.mp heR
  obtain ⟨hjP, hjT⟩ := mem_sdiff.mp hj
  by_cases hij : i = j
  · subst j
    exact hjT hi
  · exact Finset.disjoint_left.mp (hP hij) (hT i hi) hjP

end Overfull.CircuitPatterns
