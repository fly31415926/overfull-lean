import Overfull.ForceMatching.Assembly
import Overfull.ForceMatching.Cuts
import Overfull.ForceMatching.Residual
import Overfull.ForceMatching.Parameters

namespace Overfull.ForceMatching

open Finset Classical MatchingProbability

/-- Completing a bounded partial matching inside the actual robust cores
preserves all odd-set inequalities. The error tolerance is chosen before
the bound on the exceptional set. -/
theorem exists_safe_completion_parameters (α ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν)
    (hντ : ν ≤ τ) (hτ : τ ≤ α/1000) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℕ, ∃ n₀ : ℕ,
      ∀ (V I : Type*) [Fintype V] [Fintype I]
        (G : SimpleGraph V) [DecidableRel G.Adj]
        (U : I → Finset V) (Z : Finset V) (H : ∀ i, SimpleGraph (U i))
        (h : ℕ) (a : ℝ) (M F : G.Subgraph),
        n₀ ≤ Fintype.card V →
        Pairwise (fun i j => Disjoint (U i) (U j)) →
        (∀ i, Disjoint (U i) Z) →
        (∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) →
        (∀ v, G.degree v = h) → α*Fintype.card V ≤ h →
        0 ≤ a → a ≤ ε*Fintype.card V →
        (∀ i, α*Fintype.card V ≤ ((U i).card : ℝ)) →
        (∀ i, H i ≤ G.induce (U i : Set V)) →
        (∀ i v, (h : ℝ)-a ≤ ((H i).degree v : ℝ)) →
        (∀ i, IsRobustExpander (H i) ν τ) →
        M.IsPerfectMatching → F.IsMatching → F ≤ M → (Z : Set V) ⊆ F.verts →
        (∀ i, (F.verts.toFinset ∩ U i).card ≤ 2*t+6) →
        (∀ i, Even (((U i : Set V) \ F.verts).ncard)) →
        ¬ FamilyFailure M h (wholeUnions U Z) →
        ∃ N : G.Subgraph,
          N.IsPerfectMatching ∧ F ≤ N ∧
          (∀ v w, N.Adj v w → F.Adj v w ∨
            ∃ i, ∃ hv : v ∈ U i, ∃ hw : w ∈ U i, (H i).Adj ⟨v,hv⟩ ⟨w,hw⟩) ∧
          (∀ X : Finset V, ¬ IsOverfull (G \ N.spanningCoe) (h-1) X) := by
  obtain ⟨hαhalf,hτpos,_hνone,hτsmall,hτdegree,_hνhalf,hτα⟩ :=
    range_bounds α ν τ hα hα1 hν hντ hτ
  obtain ⟨η,hη,nCore,hcomplete⟩ := exists_compressed_completion_parameters
    (α/2) ν τ hαhalf hν hντ hτsmall hτdegree
  have hden : 0 < (ν/2)^2*α^2 := by positivity
  obtain ⟨nSmall,hnSmall⟩ := exists_nat_gt (3/((ν/2)^2*α^2))
  obtain ⟨ε,hε,horder⟩ := uniform_order_threshold α ν η hα hν hη nCore nSmall
  refine ⟨ε,hε,?_⟩
  intro t
  obtain ⟨n₀,hn₀⟩ := horder t
  refine ⟨max n₀ 1,?_⟩
  intro V I _ _ G _ U Z H h a M F hn hdisj hZ hcover hregular hdensity
    ha haε hsize hH hdegree hrobust hM hF hFM hZF hload heven hsafe
  classical
  have hnpos : 0 < Fintype.card V := by omega
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp hnpos
  have hhn : h ≤ Fintype.card V := by
    simpa only [hregular v] using (G.degree_lt_card_verts v).le
  obtain ⟨_hnpos,hhpos,hnSmallV,hreslo,hreshi,haSmall,hcores⟩ :=
    hn₀ (Fintype.card V) h a ((le_max_left _ _).trans hn)
      hdensity hhn ha haε
  have hcorebounds (i : I) := hcores (U i).card (card_le_univ _) (hsize i)
  have hlocaldegree (i : I) (v : U i) :
      (α/2)*(U i).card ≤ ((H i).degree v : ℝ) :=
    (hcorebounds i).2.2.2.trans (hdegree i v)
  have hlocalorder (i : I) : nCore ≤ (U i).card := by
    have hh := (hcorebounds i).1
    omega
  have hlocalload (i : I) :
      ((F.verts.toFinset ∩ U i).card : ℝ) ≤ η*(U i).card :=
    (by exact_mod_cast hload i :
      ((F.verts.toFinset ∩ U i).card : ℝ) ≤ ((2*t+6 : ℕ) : ℝ)).trans
      (hcorebounds i).2.1
  obtain ⟨N,hN,hFN,hEdges,hResidualLe,hResidualRobust,hDegreeLoss⟩ :=
    hcomplete V I G U Z H F (fun i j hij => hdisj hij) hcover hF hZF hH
      hlocaldegree hrobust hlocalorder hlocalload heven
  have hwhole : ∀ X ∈ wholeUnions U Z, ∀ i, U i ⊆ X ∨ Disjoint (U i) X := by
    intro X hX
    exact wholeUnions_whole U Z X hdisj hZ hX
  have hEdgesCore : ∀ u v, N.Adj u v → F.Adj u v ∨ ∃ i, u ∈ U i ∧ v ∈ U i := by
    intro u v huv
    rcases hEdges u v huv with hf | ⟨i,hi,hj,_⟩
    · exact Or.inl hf
    · exact Or.inr ⟨i,hi,hj⟩
  have hsafeN := family_safe_after_completion U M F N hM hN hFM hFN hEdgesCore
    h (wholeUnions U Z) hwhole hsafe
  have hlarge : 3 < (ν/2)^2*α^2*(Fintype.card V : ℝ) := by
    have hdiv : 3/((ν/2)^2*α^2) < (Fintype.card V : ℝ) :=
      hnSmall.trans_le (by exact_mod_cast hnSmallV)
    have hh := (div_lt_iff₀ hden).mp hdiv
    simpa only [mul_comm] using hh
  have hsub : ((h-1 : ℕ) : ℝ)+1 = h := by
    exact_mod_cast Nat.sub_add_cancel (show 1 ≤ h by omega)
  have hResidualDegree (i : I) (v : U i) :
      ((h-1 : ℕ) : ℝ)-a ≤ ((residualCore G (U i) (H i) N).degree v : ℝ) := by
    have hbefore := hdegree i v
    have hloss : ((H i).degree v : ℝ) ≤
        ((residualCore G (U i) (H i) N).degree v : ℝ)+1 := by
      exact_mod_cast hDegreeLoss i v
    linarith
  refine ⟨N,hN,hFN,hEdges,?_⟩
  exact residual_no_overfull G U Z hdisj hZ hcover h hregular N hN hsafeN
    (fun i => residualCore G (U i) (H i) N) hResidualLe
    (α/2) α (ν/2) τ a hαhalf hα (by positivity) hτpos.le hτα
    hreslo hreshi haSmall hlarge hsize hResidualRobust hResidualDegree

end Overfull.ForceMatching
