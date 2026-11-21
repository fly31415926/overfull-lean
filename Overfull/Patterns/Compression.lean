import Overfull.Compression.Matching

namespace Overfull.Compression

open Finset Classical FractionalMatching MatchingProbability
open scoped BigOperators

variable {V I : Type*} [Fintype V] [DecidableEq V]

/-- The joining forest with one fixed embedding of the core labels.  Using
one embedding for every compressed matching makes patterns comparable. -/
noncomputable def JoiningForestWithCode (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4) (F : G.Subgraph) : Prop :=
  ∃ label : G.edgeSet → LabelPair,
    (nonexceptionalEdges G F Z).card ≤ 3 ∧
    (∀ e ∈ nonexceptionalEdges G F Z,
      (label e).val = {coreLabel U code (firstEnd e), coreLabel U code (secondEnd e)}) ∧
    Set.InjOn label (nonexceptionalEdges G F Z) ∧
    LeafForest ((nonexceptionalEdges G F Z).image label)

/-- Compress an actual perfect matching to its exceptional edges and an
actual parity-equivalent forest of at most three joining edges. -/
theorem exists_compressed_matching_fixed_code (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (M : G.Subgraph) (hM : M.IsPerfectMatching) :
    ∃ F : G.Subgraph, F.IsMatching ∧ F ≤ M ∧
      (∀ u v, M.Adj u v → u ∈ Z ∨ v ∈ Z → F.Adj u v) ∧
      (Z : Set V) ⊆ F.verts ∧ F.edgeSet.ncard ≤ Z.card + 3 ∧
      F.verts.ncard ≤ 2 * Z.card + 6 ∧
      (∀ i, (F.verts.toFinset ∩ U i).card ≤ 2 * Z.card + 6) ∧
      (∀ i, Even (((U i : Set V) \ F.verts).ncard)) ∧
      (∀ i u v, u ∈ U i → v ∈ U i → ¬ F.Adj u v) ∧
      JoiningForestWithCode G U Z code F := by
  let J := joiningEdges G M U Z code
  let B := exceptionalEdges G M Z
  obtain ⟨T, label, hTJ, hTcard, hpar, hlabel, hinj, hforest⟩ :=
    exists_endpoint_parity_forest J (fun e => coreLabel U code (firstEnd e))
      (fun e => coreLabel U code (secondEnd e))
      (fun e he => (Finset.mem_filter.mp he).2.2.2)
  let A := B ∪ T
  have hBM : B ⊆ matchingEdges M := Finset.filter_subset _ _
  have hJM : J ⊆ matchingEdges M := Finset.filter_subset _ _
  have hAM : A ⊆ matchingEdges M := Finset.union_subset hBM (hTJ.trans hJM)
  have hBcard : B.card ≤ Z.card :=
    selected_edges_card_le_of_endpoint G M hM.1 B hBM Z
      (fun _ he => (Finset.mem_filter.mp he).2)
  have hAcard : A.card ≤ Z.card + 3 := by
    have hle := Finset.card_union_le B T
    dsimp only [A]
    omega
  obtain ⟨F, hF, hFM, hEdges, hEdgeCard, hVertCard, hIncident⟩ :=
    exists_selected_matching G M hM.1 A hAM
  have hretain : ∀ u v, M.Adj u v → u ∈ Z ∨ v ∈ Z → F.Adj u v := by
    intro u v huv hZ
    let e : G.edgeSet := ⟨s(u, v), M.adj_sub huv⟩
    have heM : e ∈ matchingEdges M := by
      simpa only [matchingEdges, Finset.mem_filter, Finset.mem_univ, true_and] using huv
    have heZ : firstEnd e ∈ Z ∨ secondEnd e ∈ Z := by
      have heq : s(firstEnd e, secondEnd e) = s(u, v) := edge_eq e
      rcases Sym2.eq_iff.mp heq with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · simpa only [ha, hb] using hZ
      · simpa only [ha, hb, or_comm] using hZ
    have heA : e ∈ A := Finset.mem_union_left T (Finset.mem_filter.mpr ⟨heM, heZ⟩)
    have heF : e ∈ matchingEdges F := hEdges.symm ▸ heA
    simpa only [matchingEdges, Finset.mem_filter, Finset.mem_univ, true_and] using heF
  have hZcovered : (Z : Set V) ⊆ F.verts := by
    intro v hv
    obtain ⟨w, hvw, _⟩ := hM.1 (hM.2 v)
    exact F.edge_vert (hretain v w hvw (Or.inl hv))
  have hVbound : F.verts.ncard ≤ 2 * Z.card + 6 := by
    rw [hVertCard]
    omega
  have hcorebound (i : I) : (F.verts.toFinset ∩ U i).card ≤ 2 * Z.card + 6 := by
    calc
      _ ≤ F.verts.toFinset.card := Finset.card_le_card Finset.inter_subset_left
      _ = F.verts.ncard := (Set.ncard_eq_toFinset_card' _).symm
      _ ≤ _ := hVbound
  have heven (i : I) : Even (((U i : Set V) \ F.verts).ncard) := by
    have hp := selected_core_cut_parity G M hM U Z code hdisjoint hcover T hTJ hpar i
    have hi := selected_insideCount_eq_zero G M U Z code hdisjoint hUZ T hTJ i
    have hs := cut_handshake A (U i)
    have hc := covered_count_of_incident G F A hIncident (U i)
    have hAdef : A = exceptionalEdges G M Z ∪ T := rfl
    rw [hAdef, hi, Nat.mul_zero, Nat.add_zero] at hs
    have hdiff : ((U i : Set V) \ F.verts).ncard = (U i \ F.verts.toFinset).card := by
      have heq : (U i : Set V) \ F.verts = ((U i \ F.verts.toFinset : Finset V) : Set V) := by
        ext v
        simp
      rw [heq, Set.ncard_coe_finset]
    have hcard := Finset.card_sdiff_add_card_inter (U i) F.verts.toFinset
    rw [Finset.inter_comm (U i) F.verts.toFinset] at hcard
    apply Nat.even_iff.mpr
    rw [hdiff]
    change (F.verts.toFinset ∩ U i).card = ∑ v ∈ U i, incidentCount A v at hc
    rw [hAdef] at hc
    omega
  have hnointernal : ∀ i u v, u ∈ U i → v ∈ U i → ¬ F.Adj u v := by
    intro i u v hu hv huv
    let e : G.edgeSet := ⟨s(u, v), F.adj_sub huv⟩
    have heF : e ∈ matchingEdges F := by
      simpa only [matchingEdges, Finset.mem_filter, Finset.mem_univ, true_and] using huv
    have heA : e ∈ exceptionalEdges G M Z ∪ T := by simpa only [hEdges] using heF
    have hends : firstEnd e ∈ U i ∧ secondEnd e ∈ U i := by
      have heq : s(firstEnd e, secondEnd e) = s(u, v) := edge_eq e
      rcases Sym2.eq_iff.mp heq with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · simpa only [ha, hb] using And.intro hu hv
      · simpa only [ha, hb] using And.intro hv hu
    exact selected_edge_not_internal G M U Z code hdisjoint hUZ T hTJ e heA i hends
  have hnon : nonexceptionalEdges G F Z = T := by
    ext e
    simp only [nonexceptionalEdges, hEdges, A, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨heB | heT, ha, hb⟩
      · exact False.elim (((Finset.mem_filter.mp heB).2).elim ha hb)
      · exact heT
    · intro heT
      have heJ := (Finset.mem_filter.mp (hTJ heT)).2
      exact ⟨Or.inr heT, heJ.1, heJ.2.1⟩
  have hForest : JoiningForestWithCode G U Z code F := by
    refine ⟨label, ?_⟩
    rw [hnon]
    exact ⟨hTcard, fun e he => hlabel e (hTJ he), hinj, hforest⟩
  exact ⟨F, hF, hFM, hretain, hZcovered, hEdgeCard ▸ hAcard, hVbound,
    hcorebound, heven, hnointernal, hForest⟩

end Overfull.Compression
