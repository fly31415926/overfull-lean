import Overfull.Compression.Matching
import Overfull.ForceMatching.SafeCompletion

/-!
# A perfect matching meeting an exceptional-centered star

This proves manuscript Lemma 4.11. The witnesses include the sampled
perfect matching, its actual compressed submatching with a forest on the
core labels, and its completion using edges of the robust cores. The
error tolerance precedes the bound on the exceptional set.
-/

namespace Overfull

open Finset Classical ForceMatching

/-- **Manuscript Lemma 4.11.** Every exceptional-centered star with more
than `11 * 2^(t+4)` edges is met by an actual perfect matching whose
deletion leaves no overfull set at the remaining degree. The compressed
matching and its projected forest are included in the conclusion.

The range `τ ≤ α/1000` is fixed before `t`. The error tolerance is also
chosen before `t`; only the order threshold may depend on `t`. -/
theorem force_exceptional_star (α ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν)
    (hντ : ν ≤ τ) (hτ : τ ≤ α/1000) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℕ, ∃ n₀ : ℕ,
      ∀ (V I : Type*) [Fintype V] [Fintype I]
        (G : SimpleGraph V) [DecidableRel G.Adj]
        (U : I → Finset V) (Z : Finset V) (H : ∀ i, SimpleGraph (U i))
        (h : ℕ) (a : ℝ) (S : Finset G.edgeSet) (z : V),
        n₀ ≤ Fintype.card V → Fintype.card I ≤ 4 → Z.card ≤ t →
        Pairwise (fun i j => Disjoint (U i) (U j)) →
        (∀ i, Disjoint (U i) Z) →
        (∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) →
        (∀ v, G.degree v = h) → α*Fintype.card V ≤ h →
        (∀ X : Finset V, ¬ IsOverfull G h X) →
        0 ≤ a → a ≤ ε*Fintype.card V →
        (∀ i, α*Fintype.card V ≤ ((U i).card : ℝ)) →
        (∀ i, H i ≤ G.induce (U i : Set V)) →
        (∀ i v, (h : ℝ)-a ≤ ((H i).degree v : ℝ)) →
        (∀ i, IsRobustExpander (H i) ν τ) →
        z ∈ Z → (∀ e ∈ S, z ∈ e.val) → 11*2^(t+4) < S.card →
        ∃ M F N : G.Subgraph,
          M.IsPerfectMatching ∧ StarHit M S ∧
          F.IsMatching ∧ F ≤ M ∧
          (∀ u v, M.Adj u v → u ∈ Z ∨ v ∈ Z → F.Adj u v) ∧
          (Z : Set V) ⊆ F.verts ∧ F.edgeSet.ncard ≤ Z.card+3 ∧
          (∀ i, Even (((U i : Set V) \ F.verts).ncard)) ∧
          (∀ i u v, u ∈ U i → v ∈ U i → ¬ F.Adj u v) ∧
          Compression.JoiningForest G U Z F ∧ StarHit F S ∧
          N.IsPerfectMatching ∧ F ≤ N ∧ StarHit N S ∧
          (∀ v w, N.Adj v w → F.Adj v w ∨
            ∃ i, ∃ hv : v ∈ U i, ∃ hw : w ∈ U i, (H i).Adj ⟨v,hv⟩ ⟨w,hw⟩) ∧
          (∀ X : Finset V, ¬ IsOverfull (G \ N.spanningCoe) (h-1) X) := by
  obtain ⟨ε,hε,hcomplete⟩ :=
    exists_safe_completion_parameters α ν τ hα hα1 hν hντ hτ
  refine ⟨ε,hε,?_⟩
  intro t
  obtain ⟨n₀,hn₀⟩ := hcomplete t
  refine ⟨max n₀ 1,?_⟩
  intro V I _ _ G _ U Z H h a S z hn hI hZcard hdisj hUZ hcover hregular
    hdensity hno ha haε hsize hH hdegree hrobust hz hstar hstarsize
  classical
  have hnpos : 0 < Fintype.card V := by omega
  have hnposR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hnpos
  have hhpos : 0 < h := by
    have hh : (0 : ℝ) < h := (mul_pos hα hnposR).trans_le hdensity
    exact_mod_cast hh
  obtain ⟨M,hM,hMstar,hsafe⟩ :=
    exists_star_matching U Z t h hI hZcard hhpos hregular hno S z hstar hstarsize
  obtain ⟨F,hF,hFM,hretain,hZF,hFedges,_hFvertices,hFcore,heven,hinternal,hforest⟩ :=
    Compression.exists_compressed_matching G U Z hI
      (fun i j hij => hdisj hij) hUZ hcover M hM
  have hload (i : I) : (F.verts.toFinset ∩ U i).card ≤ 2*t+6 :=
    (hFcore i).trans (by omega)
  obtain ⟨N,hN,hFN,hEdges,hResidual⟩ :=
    hn₀ V I G U Z H h a M F ((le_max_left _ _).trans hn)
      hdisj hUZ hcover hregular hdensity ha haε hsize hH hdegree hrobust
      hM hF hFM hZF hload heven hsafe
  have hFstar := starHit_of_exceptional_retention M F Z hretain S z hz hstar hMstar
  have hNstar := starHit_mono F N hFN S hFstar
  exact ⟨M,F,N,hM,hMstar,hF,hFM,hretain,hZF,hFedges,heven,hinternal,hforest,hFstar,
    hN,hFN,hNstar,hEdges,hResidual⟩

end Overfull
