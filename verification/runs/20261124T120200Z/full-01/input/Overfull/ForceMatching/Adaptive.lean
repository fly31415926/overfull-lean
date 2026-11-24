import Overfull.ForceMatching

/-!
# Forced-star preparation for one fixed adaptive phase

The sampled and compressed matching is chosen before any internal core
completion.  Its safety clause applies to every compatible completion with
the stated actual residual cores.  Thus a fixed packing rule can supply all
successive completions without repeatedly weakening robust parameters.
-/

namespace Overfull

open Finset Classical MatchingProbability ForceMatching

/-- Preparation with explicit scalar bounds.  This form is used inside a
fixed phase: all bounds are inherited from its entry state, while the
current host and target star may change at every round. -/
theorem prepare_forced_star_of_bounds
    {V I : Type*} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (U : I → Finset V) (Z : Finset V)
    (h t : ℕ) (a α μ τ η : ℝ) (S : Finset G.edgeSet) (z : V)
    (hI : Fintype.card I ≤ 4) (hZcard : Z.card ≤ t)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hregular : ∀ v, G.degree v = h) (hhpos : 0 < h)
    (hno : ∀ X : Finset V, ¬ IsOverfull G h X)
    (hα : 0 < α) (hμ : 0 < μ) (hτ : 0 ≤ τ) (hτα : τ ≤ α/10)
    (hreslo : α*Fintype.card V ≤ ((h-1 : ℕ) : ℝ))
    (hreshi : ((h-1 : ℕ) : ℝ) ≤ 2*Fintype.card V)
    (ha : a ≤ α*Fintype.card V/10)
    (hlarge : 3 < μ^2*α^2*(Fintype.card V : ℝ))
    (hsize : ∀ i, α*Fintype.card V ≤ ((U i).card : ℝ))
    (hload : ∀ i, ((2*t+6 : ℕ) : ℝ) ≤ η*(U i).card)
    (hz : z ∈ Z) (hstar : ∀ e ∈ S, z ∈ e.val) (hstarsize : 11*2^(t+4) < S.card) :
    ∃ F : G.Subgraph,
      F.IsMatching ∧ (Z : Set V) ⊆ F.verts ∧
      F.edgeSet.ncard ≤ Z.card+3 ∧
      (∀ i, Even (((U i : Set V) \ F.verts).ncard)) ∧
      (∀ i, ((coveredCore (U i) G F).card : ℝ) ≤ η*(U i).card) ∧
      (∀ i u v, u ∈ U i → v ∈ U i → ¬ F.Adj u v) ∧
      StarHit F S ∧
      ∀ (N : G.Subgraph) (R : ∀ i, SimpleGraph (U i)),
        N.IsPerfectMatching → F ≤ N →
        (∀ u v, N.Adj u v → F.Adj u v ∨ ∃ i, u ∈ U i ∧ v ∈ U i) →
        (∀ i, R i ≤ (G \ N.spanningCoe).induce (U i : Set V)) →
        (∀ i, IsRobustExpander (R i) μ τ) →
        (∀ i v, ((h-1 : ℕ) : ℝ)-a ≤ ((R i).degree v : ℝ)) →
        StarHit N S ∧
        (∀ X : Finset V, ¬ IsOverfull (G \ N.spanningCoe) (h-1) X) := by
  classical
  obtain ⟨M,hM,hMstar,hsafe⟩ :=
    exists_star_matching U Z t h hI hZcard hhpos hregular hno S z hstar hstarsize
  obtain ⟨F,hF,hFM,hretain,hZF,hFedges,_hFvertices,hFcore,heven,hinternal,_hforest⟩ :=
    Compression.exists_compressed_matching G U Z hI
      (fun i j hij => hdisj hij) hUZ hcover M hM
  have hfoot (i : I) : ((coveredCore (U i) G F).card : ℝ) ≤ η*(U i).card := by
    have hl : (F.verts.toFinset ∩ U i).card ≤ 2*t+6 :=
      (hFcore i).trans (by omega)
    rw [coveredCore_card]
    exact (by exact_mod_cast hl :
      ((F.verts.toFinset ∩ U i).card : ℝ) ≤ ((2*t+6 : ℕ) : ℝ)).trans (hload i)
  have hFstar := starHit_of_exceptional_retention M F Z hretain S z hz hstar hMstar
  refine ⟨F,hF,hZF,hFedges,heven,hfoot,hinternal,hFstar,?_⟩
  intro N R hN hFN hEdges hRle hRrobust hRdegree
  have hwhole : ∀ X ∈ wholeUnions U Z, ∀ i, U i ⊆ X ∨ Disjoint (U i) X := by
    intro X hX
    exact wholeUnions_whole U Z X hdisj hUZ hX
  have hsafeN := family_safe_after_completion U M F N hM hN hFM hFN hEdges
    h (wholeUnions U Z) hwhole hsafe
  exact ⟨starHit_mono F N hFN S hFstar,
    residual_no_overfull G U Z hdisj hUZ hcover h hregular N hN hsafeN R hRle
      α α μ τ a hα hα hμ hτ hτα hreslo hreshi ha hlarge hsize hRrobust hRdegree⟩

set_option maxHeartbeats 800000 in
/-- A bounded partial matching meets the requested exceptional star and
admits every compatible robust completion.  The tolerance is fixed before
the exceptional-set bound; only the order threshold depends on that bound.
The footprint tolerance is selected before both of them. -/
theorem prepare_forced_star (α ν τ η : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν)
    (hντ : ν ≤ τ) (hτ : τ ≤ α/1000) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℕ, ∃ n₀ : ℕ,
      ∀ (V I : Type*) [Fintype V] [Fintype I]
        (G : SimpleGraph V) (U : I → Finset V) (Z : Finset V)
        (h : ℕ) (a : ℝ) (S : Finset G.edgeSet) (z : V),
        n₀ ≤ Fintype.card V → Fintype.card I ≤ 4 → Z.card ≤ t →
        Pairwise (fun i j => Disjoint (U i) (U j)) →
        (∀ i, Disjoint (U i) Z) →
        (∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) →
        (∀ v, G.degree v = h) → α*Fintype.card V ≤ h →
        (∀ X : Finset V, ¬ IsOverfull G h X) →
        0 ≤ a → a ≤ ε*Fintype.card V →
        (∀ i, α*Fintype.card V ≤ ((U i).card : ℝ)) →
        z ∈ Z → (∀ e ∈ S, z ∈ e.val) → 11*2^(t+4) < S.card →
        ∃ M F : G.Subgraph,
          M.IsPerfectMatching ∧ ¬ FamilyFailure M h (wholeUnions U Z) ∧
          F.IsMatching ∧ F ≤ M ∧ (Z : Set V) ⊆ F.verts ∧
          F.edgeSet.ncard ≤ Z.card+3 ∧
          (∀ i, Even (((U i : Set V) \ F.verts).ncard)) ∧
          (∀ i, ((coveredCore (U i) G F).card : ℝ) ≤ η*(U i).card) ∧
          (∀ i u v, u ∈ U i → v ∈ U i → ¬ F.Adj u v) ∧
          StarHit F S ∧
          ∀ (N : G.Subgraph) (R : ∀ i, SimpleGraph (U i)),
            N.IsPerfectMatching → F ≤ N →
            (∀ u v, N.Adj u v → F.Adj u v ∨ ∃ i, u ∈ U i ∧ v ∈ U i) →
            (∀ i, R i ≤ (G \ N.spanningCoe).induce (U i : Set V)) →
            (∀ i, IsRobustExpander (R i) (ν/2) τ) →
            (∀ i v, ((h-1 : ℕ) : ℝ)-a ≤ ((R i).degree v : ℝ)) →
            StarHit N S ∧
            (∀ X : Finset V, ¬ IsOverfull (G \ N.spanningCoe) (h-1) X) := by
  obtain ⟨hαhalf,hτpos,_hνone,_hτsmall,_hτdegree,_hνhalf,hτα⟩ :=
    range_bounds α ν τ hα hα1 hν hντ hτ
  have hden : 0 < (ν/2)^2*α^2 := by positivity
  obtain ⟨nSmall,hnSmall⟩ := exists_nat_gt (3/((ν/2)^2*α^2))
  obtain ⟨ε,hε,horder⟩ := uniform_order_threshold α ν η hα hν hη 0 nSmall
  refine ⟨ε,hε,?_⟩
  intro t
  obtain ⟨n₀,hn₀⟩ := horder t
  refine ⟨max n₀ 1,?_⟩
  intro V I _ _ G U Z h a S z hn hI hZcard hdisj hUZ hcover hregular hdensity
    hno ha haε hsize hz hstar hstarsize
  classical
  have hnpos : 0 < Fintype.card V := by omega
  obtain ⟨v₀⟩ := Fintype.card_pos_iff.mp hnpos
  have hhn : h ≤ Fintype.card V := by
    simpa only [hregular v₀] using (G.degree_lt_card_verts v₀).le
  obtain ⟨_hnpos,hhpos,hnSmallV,hreslo,hreshi,haSmall,hcores⟩ :=
    hn₀ (Fintype.card V) h a ((le_max_left _ _).trans hn)
      hdensity hhn ha haε
  obtain ⟨M,hM,hMstar,hsafe⟩ :=
    exists_star_matching U Z t h hI hZcard hhpos hregular hno S z hstar hstarsize
  obtain ⟨F,hF,hFM,hretain,hZF,hFedges,_hFvertices,hFcore,heven,hinternal,_hforest⟩ :=
    Compression.exists_compressed_matching G U Z hI
      (fun i j hij => hdisj hij) hUZ hcover M hM
  have hfoot (i : I) : ((coveredCore (U i) G F).card : ℝ) ≤ η*(U i).card := by
    have hc := hcores (U i).card (card_le_univ _) (hsize i)
    have hl : (F.verts.toFinset ∩ U i).card ≤ 2*t+6 :=
      (hFcore i).trans (by omega)
    rw [coveredCore_card]
    exact (by exact_mod_cast hl :
      ((F.verts.toFinset ∩ U i).card : ℝ) ≤ ((2*t+6 : ℕ) : ℝ)).trans hc.2.1
  have hFstar := starHit_of_exceptional_retention M F Z hretain S z hz hstar hMstar
  refine ⟨M,F,hM,hsafe,hF,hFM,hZF,hFedges,heven,hfoot,hinternal,hFstar,?_⟩
  intro N R hN hFN hEdges hRle hRrobust hRdegree
  have hwhole : ∀ X ∈ wholeUnions U Z, ∀ i, U i ⊆ X ∨ Disjoint (U i) X := by
    intro X hX
    exact wholeUnions_whole U Z X hdisj hUZ hX
  have hsafeN := family_safe_after_completion U M F N hM hN hFM hFN hEdges
    h (wholeUnions U Z) hwhole hsafe
  have hlarge : 3 < (ν/2)^2*α^2*(Fintype.card V : ℝ) := by
    have hdiv : 3/((ν/2)^2*α^2) < (Fintype.card V : ℝ) :=
      hnSmall.trans_le (by exact_mod_cast hnSmallV)
    have hh := (div_lt_iff₀ hden).mp hdiv
    simpa only [mul_comm] using hh
  exact ⟨starHit_mono F N hFN S hFstar,
    residual_no_overfull G U Z hdisj hUZ hcover h hregular N hN hsafeN R hRle
      (α/2) α (ν/2) τ a hαhalf hα (by positivity) hτpos.le hτα
      hreslo hreshi haSmall hlarge hsize hRrobust hRdegree⟩

end Overfull
