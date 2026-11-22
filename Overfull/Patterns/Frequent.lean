import Overfull.Patterns.Parameters
import Overfull.Patterns.RealizedPlan
import Overfull.Patterns.Completion
import Overfull.Patterns.Safety
import Overfull.Patterns.CompletedCuts
import Overfull.Patterns.PairSupply
import Overfull.Patterns.Result

/-!
# Frequent boundary patterns

The surviving robust parameter is fixed before the requested final error.
All patterns, multiplicities, actual boundary matchings, completed perfect
matchings and final enlarged cores are constructed from the input graph.
Every prefix is proved to have no overfull set, using actual cut accounting.
-/

namespace Overfull

open Finset Classical SimpleGraph Patterns Compression MatchingProbability
open ForeignPackingSchedule ForeignRuleCompletion ForeignPhase ForeignIncidence
open scoped BigOperators

universe u v

set_option maxHeartbeats 1800000 in
/-- Lemma 4.13. A bounded exceptional set and three or four robust cores
reduce to a partition into robust cores, with arbitrarily small relative
error. The result records actual perfect-matching deletions, their exact
safe residual, a linear degree reserve, and the matching-or-star supply
in the four-odd-part case. -/
theorem frequent_boundary_patterns (t : ℕ) (α ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ α/(1000*patternBound t)) :
    ∃ νout : ℝ, 0 < νout ∧ νout ≤ τ ∧
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
        ∀ (V : Type u) (I : Type v) [Fintype V] [Fintype I]
          (G : SimpleGraph V) (U : I → Finset V) (H : ∀ i, SimpleGraph (U i))
          (Z : Finset V) (k : ℕ) (a : ℝ),
          n₀ ≤ Fintype.card V → 3 ≤ Fintype.card I → Fintype.card I ≤ 4 →
          Z.card ≤ t → (∀ x, G.degree x = k) → α*Fintype.card V ≤ k →
          (∀ X : Finset V, ¬ IsOverfull G k X) →
          Pairwise (fun i j => Disjoint (U i) (U j)) →
          (∀ i, Disjoint (U i) Z) → (∀ x, x ∈ Z ∨ ∃ i, x ∈ U i) →
          (∀ i, α*Fintype.card V ≤ ((U i).card : ℝ)) →
          (∀ i, H i ≤ G.induce (U i : Set V)) →
          (∀ i x, (k : ℝ)-a ≤ ((H i).degree x : ℝ)) →
          (∀ i, IsRobustExpander (H i) ν τ) →
          0 ≤ a → a+(Z.card : ℝ)+1 ≤ ε*Fintype.card V →
          Nonempty (FrequentPatternResult G U Z k (patternBound t) δ νout τ) := by
  classical
  have hB : 0 < patternBound t := patternBound_pos t
  have hBR : (0 : ℝ) < patternBound t := by exact_mod_cast hB
  have hτpos : 0 < τ := hν.trans_le hντ
  obtain ⟨Pack,hout,houtτ,hrange,hparams⟩ :=
    exists_frequent_pattern_parameters.{u} t (discardCoefficient t : ℝ) α ν τ
      (Nat.cast_nonneg _) hα hα1 hν hντ hτ
  refine ⟨Pack.output/4,hout,houtτ,?_⟩
  intro δ hδ
  obtain ⟨η,ε,hη,hη1,_hηδ,hε,n₀,hscalar⟩ := hparams δ hδ
  refine ⟨ε,hε,n₀,?_⟩
  intro V I _ _ G U H Z k a hn hI3 hI4 hZ hregular hdensity hsafe
    hdisjoint hUZ hcover hsize hembed hdegree hrobust ha hbudget
  let n := Fintype.card V
  have hαn : α*n ≤ (n : ℝ) :=
    mul_le_of_le_one_left (Nat.cast_nonneg _) hα1
  have scalar (m : ℕ) (hm : α*n ≤ (m : ℝ)) :
      PatternScalarBounds t (patternBound t) Pack.order α Pack.error Pack.output
        η δ (discardCoefficient t : ℝ) n k m a :=
    hscalar n k m Z.card a hn hdensity hm ha hbudget
  have ambient := scalar n hαn
  have coreScalar (i : I) := scalar (U i).card (hsize i)
  have hnpos : 0 < n := ambient.order_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hk : 0 < k :=
    (Nat.mul_pos (by decide) hB).trans_le ambient.degree_large
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨v₀⟩ := Fintype.card_pos_iff.mp hnpos
  have hkn : k ≤ n := by
    have hh := G.degree_lt_card_verts v₀
    rw [hregular v₀] at hh
    exact hh.le
  have hIpos : 0 < Fintype.card I := by omega
  letI : Nonempty I := Fintype.card_pos_iff.mp hIpos
  obtain ⟨code⟩ : Nonempty (I ↪ Fin 4) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hI4)
  obtain ⟨S,hS,⟨D⟩⟩ := exists_encoded_distribution G U Z code k hk hregular hsafe
    (fun i j h => hdisjoint h) hUZ hcover
  letI := hS
  obtain ⟨p₀,r,_hmax,_hweight,hlinear,_hrhalf,hrweight,hweightpos,hpairs,_hassigned⟩ :=
    D.exists_frequent_reserve t hZ ambient.degree_large
      (fun i j h => hdisjoint h) hcover
  obtain ⟨sample,_hsample,hencoding⟩ := D.positive_witness p₀ hweightpos
  let m := D.plannedMultiplicity η a t p₀ r
  let q : ℕ := ∑ p, m p
  let h : ℕ := k-q
  have hrounding := D.planned_residual_bounds hk η a t p₀ r hη hη1.le ha hrweight hZ
  change h+q = k ∧ r ≤ h ∧
    (h : ℝ) ≤ r+η*k+patternBound t+(discardCoefficient t : ℝ)*a/η at hrounding
  have hqk : q ≤ k := by omega
  have hqrk : q+r ≤ k := by omega
  have hrpos : 0 < r := by
    have hh : (0 : ℝ) < r :=
      (div_pos hkR (by positivity : (0 : ℝ) < 3*patternBound t)).trans_le hlinear
    exact_mod_cast hh
  obtain ⟨R⟩ := D.exists_planned_realization hk η a t p₀ r hη hη1.le ha hrweight hZ
    (fun i j hh => hdisjoint hh) hUZ hcover H hembed hregular hdegree
  have hupper (i : I) (v : U i) : ((H i).degree v : ℝ) ≤ k := by
    have hh := (Replacement.lift (U i) (H i)).degree_le_of_le (v := v.val)
      (Replacement.lift_le (U i) (H i) G (hembed i))
    rw [Replacement.lift_degree,hregular] at hh
    exact_mod_cast hh
  have hpackingDensity (i : I) : α*(U i).card ≤ (k : ℝ) :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast card_le_univ (U i)) hα.le).trans hdensity
  have hpackingDegree (i : I) (v : U i) :
      |((H i).degree v : ℝ)-(k : ℝ)| ≤ Pack.error*(U i).card := by
    rw [abs_of_nonpos (sub_nonpos.mpr (hupper i v))]
    have hl := hdegree i v
    have he := (coreScalar i).packing_error
    linarith only [hl,he]
  obtain ⟨rule,hcertificate⟩ := exists_certified_core_rules U H
    α (α/(4*patternBound t)) ν τ Pack.error Pack.output Pack.order Pack.rule (k : ℝ)
    (fun i => (coreScalar i).packing_order) hrobust hpackingDensity hpackingDegree
  have hlimit (i : I) : q ≤ Nat.floor ((k : ℝ)-(α/(4*patternBound t))*(U i).card) :=
    pattern_packing_horizon α (patternBound t) n k (U i).card q r
      hα hB (card_le_univ _) hdensity hlinear hqrk
  have hfootprint (j : ℕ) (hj : j < q) (i : I) :
      ((ForceMatching.coveredCore (U i) G (R.boundary j)).card : ℝ) ≤
        Pack.error*(U i).card := by
    have hh := RealizedPlan.core_footprint_bound G U Z code R hUZ j hj i
    have ht : Z.card+6 ≤ 2*t+6 := by omega
    have hb : ((ForceMatching.coveredCore (U i) G (R.boundary j)).card : ℝ) ≤
        ((2*t+6 : ℕ) : ℝ) := by exact_mod_cast hh.trans ht
    exact hb.trans (coreScalar i).footprint
  obtain ⟨C⟩ := exists_boundary_completion G U Z H hembed R.boundary q k a
    Pack.error Pack.output (τ/2) rule
    (fun i => Nat.floor ((k : ℝ)-(α/(4*patternBound t))*(U i).card))
    hcertificate hlimit (fun i j hh => hdisjoint hh) hcover
    (fun j hj => (R.realizes j hj).matching)
    (fun j hj => (R.realizes j hj).covered) R.disjoint
    (fun j hj => (R.realizes j hj).no_core_internal) hregular hdegree
    (fun i => (coreScalar i).packing_error)
    (fun j hj => (R.realizes j hj).even_uncovered) hfootprint
  have hcross (j : ℕ) (hj : j < q) (Q : Finset (Z ⊕ Fin 4)) :
      cutCount (matchingEdges (C.full j)) (wholeUnion U Z code Q) =
        (R.pattern j).cutCount Q :=
    completed_pattern_whole_cut hdisjoint hUZ hcover (R.boundary j) (C.full j)
      (R.pattern j) (R.realizes j hj) (C.contains j hj) (C.added_internal j hj) Q
  have hcounts (s : ℕ) (hs : s ≤ q) (p : Pattern Z) :
      prefixCount R.pattern s p ≤ m p := by
    exact RealizedPlan.prefix_count_le G U Z code R s hs p
  have hproposed (s : ℕ) (hs : s ≤ q) (p : Pattern Z) :
      prefixCount R.pattern s p ≤ proposedMultiplicity η D.weight p₀ r p :=
    (hcounts s hs p).trans (D.planned_le_proposed η a t p₀ p r)
  let HR : ℕ → ∀ i, SimpleGraph (U i) := fun s i =>
    remainingCore (U i) (H i) (C.core i) (range s)
  have hRdegree (s : ℕ) (hs : s ≤ q) (i : I) (v : U i) :
      ((k-s : ℕ) : ℝ)-a ≤ ((HR s i).degree v : ℝ) := by
    have hh := (C.core_degree s hs i v).1
    simpa only [Nat.cast_sub (hs.trans hqk)] using hh
  have hretainedDensity : (α/(4*patternBound t))*n ≤ (r : ℝ) := by
    have hr3 := (div_le_iff₀ (by positivity : (0 : ℝ) < 3*patternBound t)).mp hlinear
    have hBr : (0 : ℝ) ≤ (patternBound t : ℝ)*r :=
      mul_nonneg hBR.le (Nat.cast_nonneg _)
    have hh : α*n/(4*patternBound t) ≤ (r : ℝ) :=
      (div_le_iff₀ (by positivity : (0 : ℝ) < 4*patternBound t)).mpr
        (by nlinarith only [hr3,hdensity,hBr])
    convert hh using 1
    ring
  have hsafePrefix (s : ℕ) (hs : s ≤ q) :
      ∀ X : Finset V, ¬ IsOverfull (afterDeletions G C.full s) (k-s) X := by
    have hsK : s ≤ k := hs.trans hqk
    have hresLower : (r : ℝ) ≤ ((k-s : ℕ) : ℝ) := by
      have hh : r ≤ k-s := by omega
      exact_mod_cast hh
    have hresUpper : ((k-s : ℕ) : ℝ) ≤ 2*Fintype.card V := by
      have hh : k-s ≤ n := (Nat.sub_le _ _).trans hkn
      have hh' : ((k-s : ℕ) : ℝ) ≤ n := by exact_mod_cast hh
      change ((k-s : ℕ) : ℝ) ≤ 2*(n : ℝ)
      linarith only [hh',hnR]
    exact D.completed_prefix_safe C.full R.pattern s η a t p₀ r hk hsK hη hη1.le
      hrweight hregular hsafe hdisjoint hUZ hcover
      (fun j hj => C.present j (hj.trans_le hs))
      (fun j hj => hcross j (hj.trans_le hs)) (hcounts s hs)
      (C.residual_regular s hs) (HR s) (C.core_embedded s hs)
      (α/(4*patternBound t)) α Pack.output (τ/2)
      (by positivity) hα Pack.output_pos (by positivity) hrange
      (hretainedDensity.trans hresLower) hresUpper ambient.small_cut_error
      ambient.robust_cut hsize (C.core_robust s hs) (hRdegree s hs)
  have hpools (b : Finset (Z ⊕ Fin 4)) (hb : b ∈ p₀.boundaryEdges) :
      r ≤ (boundaryPool (afterDeletions G C.full q) U Z code b).card := by
    apply completed_pattern_pool_reserved (fun i j hh => hdisjoint hh) hUZ
      R.boundary C.full R.pattern q C.present R.realizes C.contains C.added_internal
      D.weight p₀ η r m hη.le hη1.le D.weight_nonneg hrweight
      (fun p => D.planned_le_proposed η a t p₀ p r) b
      (p₀.boundaryEdge_card b hb) hb (D.pair_capacity hk b)
    calc
      _ = ∑ p, prefixPatternCount R.pattern q p * pairUse b p :=
        (prefixPatternCount_statistic R.pattern q (pairUse b)).symm
      _ = _ := by
        apply sum_congr rfl
        intro p _
        exact congrArg (fun z : ℕ => z * pairUse b p) (R.total_count p)
  have hcuts := completed_pattern_cut_reserved C.full R.pattern q C.present hcross
    D.weight p₀ η r hη.le hη1.le D.weight_nonneg hrweight
    (hproposed q le_rfl) (D.whole_cut_capacity_actual hk)
  have herror : a+(h : ℝ)-r ≤ δ*h := by
    have hretained : (k : ℝ)/(3*patternBound t) ≤ h :=
      hlinear.trans (by exact_mod_cast hrounding.2.1)
    have hδh : δ*k/(3*patternBound t) ≤ δ*h := by
      calc
        _ = δ*((k : ℝ)/(3*patternBound t)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hretained hδ.le
    have he := ambient.final_error
    have hh := hrounding.2.2
    linarith only [he,hh,hδh]
  have hsmall (i : I) : (Z.card : ℝ) ≤ Pack.output*(U i).card/4 :=
    (show (Z.card : ℝ) ≤ t by exact_mod_cast hZ).trans (coreScalar i).absorption
  have hσ : τ/2 ≤ (1:ℝ)/4 := by
    have hh := (pattern_range_bounds α ν τ (patternBound t) hα hν hντ hB hτ).1
    linarith only [hh,hα1]
  have hresult := assemble_frequent_pattern_result G U Z code C.full q k h r
    (patternBound t) a δ Pack.output (τ/2) (HR q) (D.part sample) p₀
    rfl C.perfect C.present hsafePrefix (C.residual_regular q le_rfl)
    hB hrpos hrounding.2.1 hlinear ha herror hdisjoint hUZ hcover
    (C.core_embedded q le_rfl) (hRdegree q le_rfl) Pack.output_pos.le
    Pack.output_le hσ hsmall (C.core_robust q le_rfl)
    hencoding (D.parity sample) hpairs hpools hcuts
  have hτeq : (2 : ℝ)*(τ/2) = τ := by ring
  rw [hτeq] at hresult
  exact hresult

end Overfull
