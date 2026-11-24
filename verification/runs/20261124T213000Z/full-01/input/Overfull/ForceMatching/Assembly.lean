import Overfull.ForceMatching.CoreCompletion
import Overfull.SmallCuts

/-!
# Completing a compressed matching inside disjoint robust cores

Every local matching is embedded into the original graph. Their union
with the compressed matching is an actual perfect matching, and the
remaining core graphs retain half of their robust parameter.
-/

namespace Overfull.ForceMatching

open Finset Classical SimpleGraph
open OrdinaryPackingWorking

variable {V I : Type*}

noncomputable def coveredCore (U : Finset V) (G : SimpleGraph V) (F : G.Subgraph)
    [Fintype V] : Finset U := SmallCuts.shore U F.verts.toFinset

theorem mem_coveredCore [Fintype V] (U : Finset V) (G : SimpleGraph V)
    (F : G.Subgraph) (v : U) :
    v ∈ coveredCore U G F ↔ v.val ∈ F.verts := by
  simp [coveredCore,SmallCuts.mem_shore]

theorem coveredCore_card [Fintype V] [DecidableEq V] (U : Finset V)
    (G : SimpleGraph V) (F : G.Subgraph) :
    (coveredCore U G F).card = (F.verts.toFinset ∩ U).card := by
  convert SmallCuts.shore_card U F.verts.toFinset using 1
  congr 1
  ext v
  simp only [Finset.mem_inter]

theorem uncoveredCore_card [Fintype V] [DecidableEq V] (U : Finset V)
    (G : SimpleGraph V) (F : G.Subgraph) :
    (coveredCore U G F)ᶜ.card = ((U : Set V) \ F.verts).ncard := by
  have hsum := Finset.card_add_card_compl (coveredCore U G F)
  rw [Fintype.card_coe,coveredCore_card] at hsum
  have hdiff := Finset.card_sdiff_add_card_inter U F.verts.toFinset
  rw [Finset.inter_comm U F.verts.toFinset] at hdiff
  have heq : ((U \ F.verts.toFinset : Finset V) : Set V) = (U : Set V) \ F.verts := by
    ext v
    simp
  rw [← heq,Set.ncard_coe_finset]
  omega

def embedCoreMatching (G : SimpleGraph V) (U : Finset V) (H : SimpleGraph U)
    (hH : H ≤ G.induce (U : Set V)) (M : H.Subgraph) : G.Subgraph :=
  M.map (⟨Subtype.val,fun h => hH h⟩ : H →g G)

theorem embedCoreMatching_isMatching (G : SimpleGraph V) (U : Finset V)
    (H : SimpleGraph U) (hH : H ≤ G.induce (U : Set V))
    (M : H.Subgraph) (hM : M.IsMatching) :
    (embedCoreMatching G U H hH M).IsMatching :=
  hM.map _ Subtype.val_injective

theorem embedCoreMatching_verts [Fintype V] (G : SimpleGraph V) (U : Finset V)
    (H : SimpleGraph U) (hH : H ≤ G.induce (U : Set V))
    (F : G.Subgraph) (M : H.Subgraph)
    (hverts : M.verts = (coveredCore U G F : Set U)ᶜ) :
    (embedCoreMatching G U H hH M).verts = (U : Set V) \ F.verts := by
  ext v
  change (∃ w : U, w ∈ M.verts ∧ w.val = v) ↔ v ∈ U ∧ v ∉ F.verts
  constructor
  · rintro ⟨w,hw,rfl⟩
    refine ⟨w.property,?_⟩
    rw [hverts] at hw
    exact fun h => hw ((mem_coveredCore U G F w).mpr h)
  · rintro ⟨hv,hF⟩
    refine ⟨⟨v,hv⟩,?_,rfl⟩
    rw [hverts]
    exact fun h => hF ((mem_coveredCore U G F ⟨v,hv⟩).mp h)

theorem embedCoreMatching_edge (G : SimpleGraph V) (U : Finset V)
    (H : SimpleGraph U) (hH : H ≤ G.induce (U : Set V))
    (M : H.Subgraph) {v w : V} (h : (embedCoreMatching G U H hH M).Adj v w) :
    ∃ hv : v ∈ U, ∃ hw : w ∈ U, H.Adj ⟨v,hv⟩ ⟨w,hw⟩ := by
  obtain ⟨x,y,hxy,rfl,rfl⟩ := h
  exact ⟨x.property,y.property,M.adj_sub hxy⟩

def assembledMatching (G : SimpleGraph V) (F : G.Subgraph)
    (P : I → G.Subgraph) : G.Subgraph where
  verts := Set.univ
  Adj v w := F.Adj v w ∨ ∃ i, (P i).Adj v w
  adj_sub := by
    intro v w h
    rcases h with h | ⟨i,h⟩
    · exact F.adj_sub h
    · exact (P i).adj_sub h
  edge_vert := by intro _ _ _; trivial
  symm := by
    intro v w h
    rcases h with h | ⟨i,h⟩
    · exact Or.inl (F.symm h)
    · exact Or.inr ⟨i,(P i).symm h⟩

theorem assembledMatching_perfect (G : SimpleGraph V) (U : I → Finset V)
    (Z : Finset V) (F : G.Subgraph) (P : I → G.Subgraph)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hF : F.IsMatching) (hZ : (Z : Set V) ⊆ F.verts)
    (hP : ∀ i, (P i).IsMatching)
    (hverts : ∀ i, (P i).verts = (U i : Set V) \ F.verts) :
    (assembledMatching G F P).IsPerfectMatching := by
  rw [Subgraph.isPerfectMatching_iff]
  intro v
  by_cases hv : v ∈ F.verts
  · obtain ⟨w,hw,huniq⟩ := hF hv
    refine ⟨w,Or.inl hw,?_⟩
    intro z hz
    rcases hz with hz | ⟨i,hz⟩
    · exact huniq z hz
    · have hi := (P i).edge_vert hz
      rw [hverts i] at hi
      exact (hi.2 hv).elim
  · have hcore : ∃ i, v ∈ U i := by
      rcases hcover v with hz | hi
      · exact (hv (hZ hz)).elim
      · exact hi
    obtain ⟨i,hi⟩ := hcore
    have hvP : v ∈ (P i).verts := by rw [hverts i]; exact ⟨hi,hv⟩
    obtain ⟨w,hw,huniq⟩ := hP i hvP
    refine ⟨w,Or.inr ⟨i,hw⟩,?_⟩
    intro z hz
    rcases hz with hz | ⟨j,hz⟩
    · exact (hv (F.edge_vert hz)).elim
    · have hj := (P j).edge_vert hz
      rw [hverts j] at hj
      have hij : i = j := by
        by_contra h
        exact Finset.disjoint_left.mp (hdisjoint i j h) hi hj.1
      subst j
      exact huniq z hz

theorem assembledMatching_contains (G : SimpleGraph V) (F : G.Subgraph)
    (P : I → G.Subgraph) : F ≤ assembledMatching G F P :=
  ⟨Set.subset_univ _,fun _ _ h => Or.inl h⟩

def residualCore (G : SimpleGraph V) (U : Finset V) (H : SimpleGraph U)
    (N : G.Subgraph) : SimpleGraph U := H \ N.spanningCoe.induce (U : Set V)

theorem residualCore_le (G : SimpleGraph V) (U : Finset V) (H : SimpleGraph U)
    (hH : H ≤ G.induce (U : Set V)) (N : G.Subgraph) :
    residualCore G U H N ≤ (G \ N.spanningCoe).induce (U : Set V) := by
  intro v w h
  exact ⟨hH h.1,h.2⟩

theorem residualCore_degree_loss [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (H : SimpleGraph U)
    (N : G.Subgraph) (hN : N.IsMatching) (v : U) :
    H.degree v ≤ (residualCore G U H N).degree v + 1 := by
  have hid := BipartitePackingAccounting.degree_sdiff_add_degree_inf
    H (N.spanningCoe.induce (U : Set V)) v
  have hsub : H ⊓ N.spanningCoe.induce (U : Set V) ≤
      N.spanningCoe.induce (U : Set V) := inf_le_right
  have hinf := SimpleGraph.degree_le_of_le hsub (v := v)
  have hind := (OrdinaryRobustStability.induced_degree_bounds N.spanningCoe U v).1
  have hone := BipartitePackingAccounting.matching_degree_le_one G N hN v.val
  simp only [residualCore, ← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] at hid hinf hind hone ⊢
  omega

theorem residualCore_robust [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (H : SimpleGraph U)
    (N : G.Subgraph) (hN : N.IsMatching) (ν τ : ℝ)
    (hν : 0 ≤ ν) (hlarge : 2 ≤ ν*U.card) (hH : IsRobustExpander H ν τ) :
    IsRobustExpander (residualCore G U H N) (ν/2) τ := by
  have hh := IsRobustExpander.after_edge_deletion H (residualCore G U H N)
    hH (show residualCore G U H N ≤ H from sdiff_le)
    (μ := ν/2) (by positivity) (by
      intro v
      have hl := residualCore_degree_loss G U H N hN v
      have hlR : (H.degree v : ℝ) ≤ (residualCore G U H N).degree v + 1 := by
        exact_mod_cast hl
      rw [Fintype.card_coe]
      linarith)
  convert hh using 1
  ring

set_option maxHeartbeats 800000 in
/-- Uniform completion of an actual compressed matching. Every additional
edge is an edge of an embedded core, and the actual residual cores retain
robust expansion and lose at most one edge at each vertex. -/
theorem exists_compressed_completion_parameters (δ ν τ : ℝ)
    (hδ : 0 < δ) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ 1/16) (hτδ : 24*τ ≤ δ) :
    ∃ η : ℝ, 0 < η ∧ ∃ n₀ : ℕ,
      ∀ (V I : Type*) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) (U : I → Finset V) (Z : Finset V)
        (H : ∀ i, SimpleGraph (U i)) (F : G.Subgraph),
        (∀ i j, i ≠ j → Disjoint (U i) (U j)) →
        (∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) →
        F.IsMatching → (Z : Set V) ⊆ F.verts →
        (∀ i, H i ≤ G.induce (U i : Set V)) →
        (∀ i v, δ*(U i).card ≤ ((H i).degree v : ℝ)) →
        (∀ i, IsRobustExpander (H i) ν τ) →
        (∀ i, n₀ ≤ (U i).card) →
        (∀ i, ((F.verts.toFinset ∩ U i).card : ℝ) ≤ η*(U i).card) →
        (∀ i, Even (((U i : Set V) \ F.verts).ncard)) →
        ∃ N : G.Subgraph,
          N.IsPerfectMatching ∧ F ≤ N ∧
          (∀ v w, N.Adj v w → F.Adj v w ∨
            ∃ i, ∃ hv : v ∈ U i, ∃ hw : w ∈ U i, (H i).Adj ⟨v,hv⟩ ⟨w,hw⟩) ∧
          (∀ i, residualCore G (U i) (H i) N ≤
            (G \ N.spanningCoe).induce (U i : Set V)) ∧
          (∀ i, IsRobustExpander (residualCore G (U i) (H i) N) (ν/2) τ) ∧
          (∀ i v, (H i).degree v ≤ (residualCore G (U i) (H i) N).degree v+1) := by
  obtain ⟨η,hη,n₀,hlarge,hcomplete⟩ :=
    exists_core_completion_parameters δ ν τ hδ hν hντ hτ hτδ
  refine ⟨η,hη,n₀,?_⟩
  intro V I _ _ G U Z H F hdisjoint hcover hF hZ hH hdegree hrobust hn hcovered heven
  have hlocal (i : I) : ∃ M : (H i).Subgraph,
      M.IsMatching ∧ M.verts = (coveredCore (U i) G F : Set (U i))ᶜ := by
    apply hcomplete (U i) (H i) (coveredCore (U i) G F)
    · simpa only [Fintype.card_coe] using hn i
    · simpa only [Fintype.card_coe,coveredCore_card] using hcovered i
    · have hh := heven i
      rw [← uncoveredCore_card (U i) G F] at hh
      simpa only [Finset.card_compl] using hh
    · simpa only [Fintype.card_coe] using hdegree i
    · exact hrobust i
  choose M hM hverts using hlocal
  let P (i : I) := embedCoreMatching G (U i) (H i) (hH i) (M i)
  have hP (i : I) : (P i).IsMatching :=
    embedCoreMatching_isMatching G (U i) (H i) (hH i) (M i) (hM i)
  have hPverts (i : I) : (P i).verts = (U i : Set V) \ F.verts :=
    embedCoreMatching_verts G (U i) (H i) (hH i) F (M i) (hverts i)
  let N := assembledMatching G F P
  have hN : N.IsPerfectMatching :=
    assembledMatching_perfect G U Z F P hdisjoint hcover hF hZ hP hPverts
  refine ⟨N,hN,assembledMatching_contains G F P,?_,?_,?_,?_⟩
  · intro v w h
    rcases h with h | ⟨i,h⟩
    · exact Or.inl h
    · exact Or.inr ⟨i,embedCoreMatching_edge G (U i) (H i) (hH i) (M i) h⟩
  · intro i
    exact residualCore_le G (U i) (H i) (hH i) N
  · intro i
    exact residualCore_robust G (U i) (H i) N hN.1 ν τ hν.le
      (hlarge (U i).card (hn i)) (hrobust i)
  · intro i v
    exact residualCore_degree_loss G (U i) (H i) N hN.1 v

end Overfull.ForceMatching
