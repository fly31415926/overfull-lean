import Overfull.SafePrescription.Sampling
import Overfull.SafePrescription.Counting
import Overfull.SafePrescription.Construction
import Overfull.SafePrescription.Classification
import Overfull.SafePrescription.Residual
import Overfull.SafePrescription.Parameters
import Overfull.ForceMatching.Assembly
import Overfull.ForceMatching.Parameters

/-!
# Prescribing exceptional edges while preserving the odd-set inequalities

This proves manuscript Lemma 4.9. The error tolerance and order threshold
are uniform in the exceptional order. The witnesses retain the sampled
boundary and the actual partial matching before its core completion.
-/

namespace Overfull

open Finset Classical MatchingProbability ForceMatching SafePrescription

set_option maxHeartbeats 800000 in
/-- **Manuscript Lemma 4.9.** The prescribed matching can be retained
apart from the stated constant number of edges, and the completed perfect
matching leaves no overfull set. The marked-set bound is fixed before the
error tolerance and order threshold; the full exceptional order may grow
linearly with the graph order. -/
theorem safe_prescription (α ν τ : ℝ) (t0 : ℕ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν)
    (hντ : ν ≤ τ) (hτ : τ ≤ α/1000) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ (V I : Type*) [Fintype V] [Fintype I]
        (G : SimpleGraph V) (U : I → Finset V) (Z Z0 : Finset V)
        (c : V → Fin 4) (p : I → Fin 4) (H : ∀ i, SimpleGraph (U i))
        (h k0 : ℕ) (a : ℝ) (M : G.Subgraph),
        n₀ ≤ Fintype.card V → Fintype.card I ≤ 4 →
        Pairwise (fun i j => Disjoint (U i) (U j)) →
        (∀ i, Disjoint (U i) Z) → Z0 ⊆ Z → Z0.card ≤ t0 →
        (∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) →
        (∀ i v, v ∈ U i → c v = p i) →
        (∀ v, G.degree v = h) → α*Fintype.card V ≤ h →
        h ≤ k0 → (k0 : ℝ)/1024 < h →
        (∀ X : Finset V, ¬ IsOverfull G h X) →
        0 ≤ a → a+(Z.card : ℝ)+1 ≤ ε*Fintype.card V →
        (∀ i, α*Fintype.card V ≤ ((U i).card : ℝ)) →
        (∀ i, H i ≤ G.induce (U i : Set V)) →
        (∀ i v, (h : ℝ)-a ≤ ((H i).degree v : ℝ)) →
        (∀ i, IsRobustExpander (H i) ν τ) →
        (clusterCrossingEdges G c Z0).card ≤ 6*k0 →
        (∀ v ∈ Z, v ∉ Z0 →
          (((G.neighborFinset v).filter (fun w => w ∉ Z0 ∧ c w ≠ c v)).card : ℝ) ≤
            (k0 : ℝ)/1024000) →
        (∀ X : Finset V, X.card % 2 = 1 →
          (cutCount (univ : Finset G.edgeSet) X : ℝ) ≤
            h+((2*(Z.card+t0+4096*(t0+6)+30) : ℕ) : ℝ) →
          ∀ i j, p i = p j → (coreMajority U X i ↔ coreMajority U X j)) →
        M.IsMatching →
        (∀ u v, M.Adj u v → u ∈ Z ∨ v ∈ Z) →
        (∀ u v, M.Adj u v → c u = c v) →
        ∃ K B F N : G.Subgraph,
          K.IsPerfectMatching ∧ ¬ FamilyFailure K h (wholeUnions (clusterSets c Z0) Z0) ∧
          B.IsMatching ∧ B ≤ K ∧ B.edgeSet.ncard ≤ 4096*(t0+6) ∧
          (∀ u v, B.Adj u v ↔ K.Adj u v ∧ (u ∈ Z0 ∨ v ∈ Z0 ∨ c u ≠ c v)) ∧
          F.IsMatching ∧ B ≤ F ∧ (Z : Set V) ⊆ F.verts ∧
          F.edgeSet.ncard ≤ 4096*(t0+6)+Z.card+3 ∧
          (∀ i, Even (((U i : Set V) \ F.verts).ncard)) ∧
          (∀ u v, F.Adj u v → B.Adj u v ∨ (u ∉ Z0 ∧ v ∉ Z0 ∧ c u = c v)) ∧
          (M.edgeSet \ F.edgeSet).ncard ≤ 2*(4096*(t0+6))+135720 ∧
          N.IsPerfectMatching ∧ F ≤ N ∧
          (∀ v w, N.Adj v w → F.Adj v w ∨
            ∃ i, ∃ hv : v ∈ U i, ∃ hw : w ∈ U i, (H i).Adj ⟨v,hv⟩ ⟨w,hw⟩) ∧
          (M.edgeSet \ N.edgeSet).ncard ≤ 2*(4096*(t0+6))+4*135720 ∧
          (∀ X : Finset V, ¬ IsOverfull (G \ N.spanningCoe) (h-1) X) := by
  obtain ⟨hαhalf,hτpos,_hνone,hτsmall,hτdegree,_hνhalf,hτα⟩ :=
    range_bounds α ν τ hα hα1 hν hντ hτ
  obtain ⟨η,hη,nCore,hcomplete⟩ := exists_compressed_completion_parameters
    (α/2) ν τ hαhalf hν hντ hτsmall hτdegree
  let q : ℕ := 4096*(t0+6)
  obtain ⟨ε,hε,n₀,hparameters⟩ := exists_prescription_parameters α ν η hα hν hη nCore t0 q
  refine ⟨ε,hε,max n₀ 1,?_⟩
  intro V I _ _ G U Z Z0 c p H h k0 a M hn hI hdisj hUZ hZ0 hZ0card hcover hcolor
    hregular hdensity hhk0 hscale hno ha haε hsize hH hdegree hrobust hcross hforeign
    hgroup hM hMZ hMc
  classical
  have hnpos : 0 < Fintype.card V := by omega
  obtain ⟨v₀⟩ := Fintype.card_pos_iff.mp hnpos
  have hhn : h ≤ Fintype.card V := by
    simpa only [hregular v₀] using (G.degree_lt_card_verts v₀).le
  have hk0 : (k0 : ℝ) ≤ 1024*h := by linarith
  obtain ⟨_hnpos,hhpos,hprob,hreslo,hhhi,hreshi,haSmall,hbSmall,hb,hlarge,
      haBoundary,hmarkedBoundary,hneighborMargin,hcores⟩ :=
    hparameters (Fintype.card V) h k0 Z.card a ((le_max_left _ _).trans hn)
      hhn hdensity hk0 ha haε
  let b : ℝ := ((2*(Z.card+t0+q+30) : ℕ) : ℝ)
  let 𝓧 := wholeUnions (clusterSets c Z0) Z0
  have hfamily : 44*𝓧.card < h := by
    have hh := wholeUnions_card_le (clusterSets c Z0) Z0 t0 (by simp) hZ0card
    exact (Nat.mul_le_mul_left 44 hh).trans_lt hprob
  have hboundaryCount := boundaryEdges_card_bound G c Z0 h k0 t0 hregular hhk0 hZ0card hcross
  obtain ⟨K,B,hK,hsafe,hB,hBK,hBedges,hBverts,_hBexact,_hBselected,hBadj⟩ :=
    exists_sampled_boundary G c Z0 h k0 t0 hregular hno 𝓧 hfamily hscale hboundaryCount
  have hcorebounds (i : I) := hcores (U i).card (card_le_univ _) (hsize i)
  have hneighbors : ∀ v ∈ Z, v ∉ Z0 →
      2*Z.card+4+2*q < (clusterCoreNeighbors G Z c v).ncard := by
    intro v hv hv0
    have hcount := same_cluster_neighbors_lower G Z Z0 hZ0 c v
    rw [hregular v] at hcount
    have hcount' : h ≤ (clusterCoreNeighbors G Z c v).ncard+Z.card+
        ((G.neighborFinset v).filter (fun w => w ∉ Z0 ∧ c w ≠ c v)).card := by
      convert hcount using 1
      congr 2
      ext w
      simp only [Finset.mem_filter,SimpleGraph.mem_neighborFinset]
    have hcountR : (h : ℝ) ≤ ((clusterCoreNeighbors G Z c v).ncard : ℝ)+Z.card+
        (((G.neighborFinset v).filter (fun w => w ∉ Z0 ∧ c w ≠ c v)).card : ℝ) := by
      exact_mod_cast hcount'
    have hf := hforeign v hv hv0
    have hh : 2*(Z.card : ℝ)+4+2*q < (clusterCoreNeighbors G Z c v).ncard := by linarith
    exact_mod_cast hh
  obtain ⟨F,hF,hBF,hZF,hFloss,hFedges,hFverts,_hFcore,heven,_hInternal,hFlocation⟩ :=
    exists_retained_partial_matching G U Z Z0 c hI (fun i j hij => hdisj hij)
      hUZ hZ0 hcover (fun i u v hu hv => (hcolor i u hu).trans (hcolor i v hv).symm)
      K B M hK hB hBK hBadj q hBedges hBverts hM hMZ hMc
      (fun i => (hcorebounds i).2.1) hneighbors
  have hlocaldegree (i : I) (v : U i) :
      (α/2)*(U i).card ≤ ((H i).degree v : ℝ) :=
    (hcorebounds i).2.2.2.trans (hdegree i v)
  have hlocalload (i : I) :
      ((F.verts.toFinset ∩ U i).card : ℝ) ≤ η*(U i).card := by
    have hnat : (F.verts.toFinset ∩ U i).card ≤ 2*(q+Z.card+3) := by
      calc
        _ ≤ F.verts.toFinset.card := card_le_card inter_subset_left
        _ = F.verts.ncard := (Set.ncard_eq_toFinset_card' _).symm
        _ ≤ _ := hFverts
    have hreal : ((F.verts.toFinset ∩ U i).card : ℝ) ≤ ((2*(q+Z.card+3) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    exact hreal.trans (hcorebounds i).2.2.1
  obtain ⟨N,hN,hFN,hEdges,hResidualLe,hResidualRobust,hDegreeLoss⟩ :=
    hcomplete V I G U Z H F (fun i j hij => hdisj hij) hcover hF hZF hH
      hlocaldegree hrobust (fun i => (hcorebounds i).1) hlocalload heven
  have hboundary : ∀ X ∈ 𝓧, ∀ v ∉ Z0,
      (incidentCount (cutEdges (univ : Finset G.edgeSet) X) v : ℝ) ≤ (h : ℝ)/20 := by
    intro X hX v hv0
    rcases hcover v with hvZ | ⟨i,hi⟩
    · have hc := cut_incident_cluster_bound G c Z0 X v hv0
        (family_same_label c Z0 X hX)
      have hcR : (incidentCount (cutEdges (univ : Finset G.edgeSet) X) v : ℝ) ≤
          Z0.card+(((G.neighborFinset v).filter (fun w => w ∉ Z0 ∧ c w ≠ c v)).card : ℝ) := by
        have hc' : incidentCount (cutEdges (univ : Finset G.edgeSet) X) v ≤
            Z0.card+((G.neighborFinset v).filter (fun w => w ∉ Z0 ∧ c w ≠ c v)).card := by
          convert hc using 1
          congr 2
          ext w
          simp only [Finset.mem_filter,SimpleGraph.mem_neighborFinset]
        exact_mod_cast hc'
      have hf := hforeign v hvZ hv0
      have hz : (Z0.card : ℝ) ≤ t0 := by exact_mod_cast hZ0card
      linarith
    · have hc := cut_incident_core_bound G (U i) X (H i) (hH i)
        (family_whole_cores U Z Z0 c p hZ0 hUZ hcolor X hX i)
        h a hregular (hdegree i) ⟨v,hi⟩
      exact hc.trans haBoundary
  have hZb : (2 : ℝ)*Z.card ≤ b := by
    change (2 : ℝ)*Z.card ≤ ((2*(Z.card+t0+q+30) : ℕ) : ℝ)
    exact_mod_cast (show 2*Z.card ≤ 2*(Z.card+t0+q+30) by omega)
  have hlargeOriginal : 3 < ν^2*α^2*(Fintype.card V : ℝ) := by
    nlinarith only [hlarge]
  have hdensityHalf : (α/2)*Fintype.card V ≤ h := by
    have hnR : (0 : ℝ) ≤ Fintype.card V := by positivity
    nlinarith only [hdensity,mul_nonneg hα.le hnR]
  have hclass : ∀ X : Finset V, X.card % 2 = 1 →
      (cutCount (univ : Finset G.edgeSet) X : ℝ) ≤ h+b →
      X ∈ 𝓧 ∨ ∃ Y ∈ 𝓧, ∃ v, X = toggle Y v := by
    intro X hodd hcut
    exact classified_robust_small_cut G U Z Z0 X c p h H hZ0 hdisj hUZ hcover hcolor
      hregular hH (α/2) α ν τ a b hαhalf hα hν hτpos.le hτα
      hdensityHalf hhhi haSmall hbSmall hlargeOriginal hsize hrobust hdegree
      (hgroup X hodd hcut) hboundary hZb hb hcut
  have hEdgesCore : ∀ u v, N.Adj u v → F.Adj u v ∨ ∃ i, u ∈ U i ∧ v ∈ U i := by
    intro u v huv
    rcases hEdges u v huv with hf | ⟨i,hi,hj,_⟩
    · exact Or.inl hf
    · exact Or.inr ⟨i,hi,hj⟩
  have hEdgesCluster : ∀ u v, N.Adj u v → B.Adj u v ∨
      ∃ j, u ∈ clusterSets c Z0 j ∧ v ∈ clusterSets c Z0 j := by
    intro u v huv
    rcases hEdgesCore u v huv with hf | ⟨i,hi,hj⟩
    · rcases hFlocation u v hf with hb | ⟨hu,hv,hc⟩
      · exact Or.inl hb
      · exact Or.inr ⟨c u,(mem_clusterSets c Z0 (c u) u).mpr ⟨hu,rfl⟩,
          (mem_clusterSets c Z0 (c u) v).mpr ⟨hv,hc.symm⟩⟩
    · have hu : u ∉ Z0 := fun hh => disjoint_left.mp (hUZ i) hi (hZ0 hh)
      have hv : v ∉ Z0 := fun hh => disjoint_left.mp (hUZ i) hj (hZ0 hh)
      exact Or.inr ⟨p i,(mem_clusterSets c Z0 (p i) u).mpr ⟨hu,hcolor i u hi⟩,
        (mem_clusterSets c Z0 (p i) v).mpr ⟨hv,hcolor i v hj⟩⟩
  have hwhole : ∀ X ∈ 𝓧, ∀ i, clusterSets c Z0 i ⊆ X ∨ Disjoint (clusterSets c Z0 i) X := by
    intro X hX
    exact wholeUnions_whole (clusterSets c Z0) Z0 X (clusterSets_disjoint c Z0)
      (clusterSets_disjoint_marked c Z0) hX
  have hsafeN := family_safe_after_completion (clusterSets c Z0) K B N hK hN hBK
    (hBF.trans hFN) hEdgesCluster h 𝓧 hwhole hsafe
  have hexterior := exteriorEdges_card_le G U F N (q+Z.card+3) hEdgesCore hFedges
  have hLb : ((q+Z.card+3 : ℕ) : ℝ) ≤ b := by
    change ((q+Z.card+3 : ℕ) : ℝ) ≤ ((2*(Z.card+t0+q+30) : ℕ) : ℝ)
    exact_mod_cast (show q+Z.card+3 ≤ 2*(Z.card+t0+q+30) by omega)
  have hsub : ((h-1 : ℕ) : ℝ)+1 = h := by
    exact_mod_cast Nat.sub_add_cancel (show 1 ≤ h by omega)
  have hResidualDegree (i : I) (v : U i) :
      ((h-1 : ℕ) : ℝ)-a ≤ ((residualCore G (U i) (H i) N).degree v : ℝ) := by
    have hbefore := hdegree i v
    have hloss : ((H i).degree v : ℝ) ≤
        ((residualCore G (U i) (H i) N).degree v : ℝ)+1 := by exact_mod_cast hDegreeLoss i v
    linarith
  have hResidual := residual_no_overfull_of_small_cut_classification G U Z hdisj hUZ hcover
    h hregular N hN (q+Z.card+3) b hexterior hLb 𝓧 hsafeN hclass
    (fun i => residualCore G (U i) (H i) N) hResidualLe
    (α/2) α (ν/2) τ a hαhalf hα (by positivity) hτpos.le hτα
    hreslo hreshi haSmall hlarge hsize hResidualRobust hResidualDegree
  have hNloss : (M.edgeSet \ N.edgeSet).ncard ≤ 2*q+4*135720 := by
    have hle := PrescribedMatching.omitted_edges_le_of_extension G M F N hFN
    omega
  exact ⟨K,B,F,N,hK,hsafe,hB,hBK,hBedges,hBadj,hF,hBF,hZF,hFedges,heven,hFlocation,
    hFloss,hN,hFN,hEdges,hNloss,hResidual⟩

end Overfull
