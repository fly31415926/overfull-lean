import Overfull.ForeignEdges.Incidence
import Overfull.SafePrescription.Adaptive

/-!
# Safe completion using arbitrary actual core matchings

The core matchings may be outputs of a previously fixed adaptive rule.
Their exact unused cores, rather than a bound obtained by repeatedly
weakening robustness, are used by the safe-completion clause.
-/

namespace Overfull.ForeignCompletion

open Finset Classical SimpleGraph ForceMatching ForeignIncidence
open BipartitePackingAccounting

variable {V I : Type*}

/-- Assemble the given local matchings and identify every induced core
matching exactly. -/
theorem assemble_core_completions (G : SimpleGraph V) [Fintype V]
    (U : I → Finset V) (Z : Finset V) (H : ∀ i, SimpleGraph (U i))
    (hH : ∀ i, H i ≤ G.induce (U i : Set V))
    (F : G.Subgraph) (C : ∀ i, (H i).Subgraph)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hF : F.IsMatching) (hZ : (Z : Set V) ⊆ F.verts)
    (hno : ∀ i u v, u ∈ U i → v ∈ U i → ¬ F.Adj u v)
    (hC : ∀ i, (C i).IsMatching)
    (hverts : ∀ i, (C i).verts = (coveredCore (U i) G F : Set (U i))ᶜ) :
    ∃ N : G.Subgraph,
      N.IsPerfectMatching ∧ F ≤ N ∧
      (∀ u v, N.Adj u v → F.Adj u v ∨ ∃ i, u ∈ U i ∧ v ∈ U i) ∧
      (∀ i, N.spanningCoe.induce (U i : Set V) = (C i).spanningCoe) ∧
      (∀ i, H i \ (C i).spanningCoe ≤
        (G \ N.spanningCoe).induce (U i : Set V)) := by
  let P : I → G.Subgraph := fun i =>
    embedCoreMatching G (U i) (H i) (hH i) (C i)
  let N := assembledMatching G F P
  have hP (i : I) : (P i).IsMatching :=
    embedCoreMatching_isMatching G (U i) (H i) (hH i) (C i) (hC i)
  have hPverts (i : I) : (P i).verts = (U i : Set V) \ F.verts :=
    embedCoreMatching_verts G (U i) (H i) (hH i) F (C i) (hverts i)
  have hperfect := assembledMatching_perfect G U Z F P hdisjoint hcover hF hZ hP hPverts
  have hlocal (i : I) : N.spanningCoe.induce (U i : Set V) = (C i).spanningCoe :=
    assembledMatching_induce_eq G U H hH F C hdisjoint hno i
  refine ⟨N,hperfect,assembledMatching_contains G F P,?_,hlocal,?_⟩
  · intro u v huv
    rcases huv with hFuv | ⟨i,hi⟩
    · exact Or.inl hFuv
    · obtain ⟨hu,hv,_⟩ := embedCoreMatching_edge G (U i) (H i) (hH i) (C i) hi
      exact Or.inr ⟨i,hu,hv⟩
  · intro i u v huv
    refine ⟨hH i huv.1,?_⟩
    intro hNuv
    apply huv.2
    change (N.spanningCoe.induce (U i : Set V)).Adj u v at hNuv
    simpa only [hlocal i] using hNuv

/-- A local matching loses at most one from the whole-core degree, with
the error measured in real numbers and retained without rounding. -/
theorem core_remainder_degree_lower [Fintype V]
    (H : SimpleGraph V) (C : H.Subgraph) (hC : C.IsMatching)
    (d a : ℝ) (hdegree : ∀ v, d-a ≤ H.degree v) (v : V) :
    d-1-a ≤ ((H \ C.spanningCoe).degree v : ℝ) := by
  have hid := degree_sdiff_add_of_le H C.spanningCoe C.spanningCoe_le v
  have hone := matching_degree_le_one H C hC v
  have hidR : ((H \ C.spanningCoe).degree v : ℝ) + C.spanningCoe.degree v =
      H.degree v := by exact_mod_cast hid
  have honeR : (C.spanningCoe.degree v : ℝ) ≤ 1 := by exact_mod_cast hone
  have hd := hdegree v
  linarith

end Overfull.ForeignCompletion

namespace Overfull

open Finset Classical SimpleGraph MatchingProbability ForceMatching SafePrescription
open ForeignCompletion

set_option maxHeartbeats 800000 in
/-- Prepare a safe partial matching with a caller-selected footprint
tolerance. Any actual local matching family with robust exact residual
cores gives a safe ambient perfect matching. The local family is not
obtained by invoking a one-step robustness-loss completion theorem. -/
theorem safe_prescription_of_core_matchings (α ν τ η : ℝ) (t0 : ℕ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν)
    (hντ : ν ≤ τ) (hτ : τ ≤ α/1000) (hη : 0 < η) :
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
        ∃ F : G.Subgraph,
          F.IsMatching ∧ (Z : Set V) ⊆ F.verts ∧
          F.edgeSet.ncard ≤ 4096*(t0+6)+Z.card+3 ∧
          (∀ i, Even (((U i : Set V) \ F.verts).ncard)) ∧
          (M.edgeSet \ F.edgeSet).ncard ≤ 2*(4096*(t0+6))+135720 ∧
          F.verts.ncard ≤ 2*(4096*(t0+6)+Z.card+3) ∧
          (∀ i, ((coveredCore (U i) G F).card : ℝ) ≤ η*(U i).card) ∧
          (∀ i u v, u ∈ U i → v ∈ U i → ¬ F.Adj u v) ∧
          ∀ C : ∀ i, (H i).Subgraph,
            (∀ i, (C i).IsMatching) →
            (∀ i, (C i).verts = (coveredCore (U i) G F : Set (U i))ᶜ) →
            (∀ i, IsRobustExpander (H i \ (C i).spanningCoe) (ν/2) τ) →
            ∃ N : G.Subgraph,
              N.IsPerfectMatching ∧ F ≤ N ∧
              (∀ u v, N.Adj u v → F.Adj u v ∨ ∃ i, u ∈ U i ∧ v ∈ U i) ∧
              (∀ i, N.spanningCoe.induce (U i : Set V) = (C i).spanningCoe) ∧
              (∀ i, H i \ (C i).spanningCoe ≤
                (G \ N.spanningCoe).induce (U i : Set V)) ∧
              (∀ i v, ((h-1 : ℕ) : ℝ)-a ≤ ((H i \ (C i).spanningCoe).degree v : ℝ)) ∧
              (M.edgeSet \ N.edgeSet).ncard ≤ 2*(4096*(t0+6))+4*135720 ∧
              (∀ X : Finset V, ¬ IsOverfull (G \ N.spanningCoe) (h-1) X) := by
  obtain ⟨ε,hε,n₀,hprepare⟩ := prepare_safe_prescription α ν τ η t0
    hα hα1 hν hντ hτ hη
  refine ⟨ε,hε,n₀,?_⟩
  intro V I _ _ G U Z Z0 c p H h k0 a M hn hI hdisj hUZ hZ0 hZ0card hcover hcolor
    hregular hdensity hhk0 hscale hno ha haε hsize hH hdegree hrobust hcross hforeign
    hgroup hM hMZ hMc
  obtain ⟨K,B,F,_hK,_hfamily,_hB,_hBK,_hBsize,_hBcut,hF,_hBF,hZF,hFsize,heven,
      _hFloc,hFloss,hFverts,hfoot,hnoCore,hcompletion⟩ :=
    hprepare V I G U Z Z0 c p H h k0 a M hn hI hdisj hUZ hZ0 hZ0card hcover hcolor
      hregular hdensity hhk0 hscale hno ha haε hsize hH hdegree hrobust hcross hforeign
      hgroup hM hMZ hMc
  refine ⟨F,hF,hZF,hFsize,heven,hFloss,hFverts,hfoot,hnoCore,?_⟩
  intro C hC hCverts hCrobust
  obtain ⟨N,hN,hFN,hNedges,hNlocal,hRle⟩ :=
    assemble_core_completions G U Z H hH F C (fun i j hij => hdisj hij)
      hcover hF hZF hnoCore hC hCverts
  have hhpos : 0 < h := by
    have hk0 : (0 : ℝ) ≤ k0 := Nat.cast_nonneg _
    have hh : (0 : ℝ) < h := by linarith
    exact_mod_cast hh
  have hRdegree : ∀ i v,
      ((h-1 : ℕ) : ℝ)-a ≤ ((H i \ (C i).spanningCoe).degree v : ℝ) := by
    intro i v
    have hl := core_remainder_degree_lower (H i) (C i) (hC i) (h : ℝ) a
      (hdegree i) v
    simpa only [Nat.cast_sub (by omega : 1 ≤ h),Nat.cast_one] using hl
  obtain ⟨hloss,hresidual⟩ := hcompletion N (fun i => H i \ (C i).spanningCoe)
    hN hFN hNedges hRle (by intro i; convert hCrobust i using 1)
    (by
      intro i v
      simpa only [← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hRdegree i v)
  exact ⟨N,hN,hFN,hNedges,hNlocal,hRle,hRdegree,hloss,hresidual⟩

end Overfull
