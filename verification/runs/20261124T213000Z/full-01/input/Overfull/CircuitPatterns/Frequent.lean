import Overfull.CircuitPatterns.Result
import Overfull.CircuitPatterns.SelectedCompletion
import Overfull.CircuitPatterns.SelectedSafety
import Overfull.CircuitPatterns.Parameters

/-!
# The frequent boundary pattern reduction

The output robustness is fixed before the requested final error. All
matchings, residual graphs, assignments, enlarged robust cores, and
reserved joining edges are constructed from the original graph.
-/

noncomputable section
namespace Overfull

open Finset Classical SimpleGraph CircuitPatterns Compression Absorption
open ForeignPhase ForeignIncidence ForeignPackingSchedule ForeignRuleCompletion
open scoped BigOperators

universe u v

set_option maxHeartbeats 2400000 in
/-- Lemma 4.13, with an explicit retained fraction and actual forest supply.
The constants precede the graph, and the output robust parameter precedes
the arbitrary requested relative error. -/
theorem circuit_frequent_boundary_pattern (t : ℕ) (α ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ α/(1000*patternBound t)) :
    ∃ νout : ℝ, 0 < νout ∧ ∀ δ : ℝ, 0 < δ →
      ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
        ∀ (V : Type u) (I : Type v) [Fintype V] [Fintype I]
          (G : SimpleGraph V) (U : I → Finset V) (H : ∀ i, SimpleGraph (U i))
          (Z : Finset V) (k : ℕ) (a : ℝ),
          n₀ ≤ Fintype.card V → (Fintype.card I = 3 ∨ Fintype.card I = 4) →
          (∀ x, G.degree x = k) → α*Fintype.card V ≤ k →
          (∀ X : Finset V, ¬ IsOverfull G k X) →
          Pairwise (fun i j => Disjoint (U i) (U j)) →
          (∀ i, Disjoint (U i) Z) → (∀ x, x ∈ Z ∨ ∃ i, x ∈ U i) →
          Z.card ≤ t → (∀ i, α*Fintype.card V ≤ ((U i).card : ℝ)) →
          (∀ i, H i ≤ G.induce (U i : Set V)) →
          (∀ i x, (k : ℝ)-a ≤ ((H i).degree x : ℝ)) →
          (∀ i, IsRobustExpander (H i) ν τ) →
          0 ≤ a → a ≤ ε*Fintype.card V →
          Nonempty (FrequentPatternResult G U k t δ νout τ) := by
  let B : ℝ := patternBound t
  let C : ℝ := discardCoefficient t
  have hB : 0 < B := by
    dsimp [B]
    exact_mod_cast patternBound_pos t
  have hB1 : 1 ≤ B := by
    dsimp [B]
    exact_mod_cast patternBound_pos t
  have hC : 0 ≤ C := Nat.cast_nonneg _
  let γ := α/(4*B)
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hτpos : 0 < τ := hν.trans_le hντ
  have hτnum : τ*(1000*B) ≤ α :=
    (le_div_iff₀ (by positivity : 0 < 1000*B)).mp hτ
  have hτB : 0 ≤ τ*B := mul_nonneg hτpos.le hB.le
  have hτpack : τ ≤ α/8 := by
    have hh := mul_le_mul_of_nonneg_left hB1 hτpos.le
    nlinarith only [hτnum,hh,hτpos]
  have hτquarter : τ/2 ≤ 1/4 := by linarith only [hτpack,hα1]
  have hσsafe : τ/2 ≤ γ/10 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 10)).mpr
    apply (le_div_iff₀ (by positivity : 0 < 4*B)).mpr
    nlinarith only [hτnum,hτB]
  obtain ⟨Pack⟩ := exists_epoch_parameters.{u} α γ τ ν
    hα hα1 hγ hν hντ hτpack
  refine ⟨Pack.output/4,div_pos Pack.output_pos (by norm_num),?_⟩
  intro δ hδ
  obtain ⟨η,ε,hη,hη1,hε,n₀,hparameters⟩ :=
    exists_pattern_parameters α Pack.error Pack.output δ B C hα Pack.error_pos
      Pack.output_pos hδ hB hC Pack.order t
  refine ⟨ε,hε,n₀,?_⟩
  intro V I _ _ G U H Z k a hn hI hregular hdensity hno
    hdisj hUZ hcover ht hsize hembed hdegree hrobust ha herror
  let n := Fintype.card V
  have hIpos : 0 < Fintype.card I := by omega
  letI : Nonempty I := Fintype.card_pos_iff.mp hIpos
  have hIle : Fintype.card I ≤ 4 := by omega
  obtain ⟨code⟩ : Nonempty (I ↪ Fin 4) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hIle)
  have hαn : α*n ≤ (n : ℝ) := mul_le_of_le_one_left (Nat.cast_nonneg n) hα1
  have ambient := hparameters n k n Z.card a hn hdensity hαn le_rfl ht ha herror
  have scalar (i : I) := hparameters n k (U i).card Z.card a hn hdensity
    (hsize i) (card_le_univ _) ht ha herror
  have hnpos : 0 < n := ambient.order_pos
  have hk : 0 < k := ambient.degree_pos
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨v₀⟩ := Fintype.card_pos_iff.mp hnpos
  have hkn : k ≤ n := by
    have hh := G.degree_lt_card_verts v₀
    rw [hregular v₀] at hh
    exact hh.le
  have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hupper (i : I) (x : U i) : ((H i).degree x : ℝ) ≤ k := by
    have hh := SimpleGraph.degree_le_of_le
      (Replacement.lift_le (U i) (H i) G (hembed i)) (v := x.val)
    rw [Replacement.lift_degree (U i) (H i) x,hregular x.val] at hh
    exact_mod_cast hh
  have hpackingDegree (i : I) (x : U i) :
      |((H i).degree x : ℝ)-(k : ℝ)| ≤ Pack.error*(U i).card := by
    rw [abs_of_nonpos (sub_nonpos.mpr (hupper i x))]
    linarith only [hdegree i x,(scalar i).packing_error]
  have hpackingDensity (i : I) : α*(U i).card ≤ (k : ℝ) :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast card_le_univ (U i)) hα.le).trans hdensity
  obtain ⟨rule,hcertificate⟩ := exists_certified_core_rules U H
    α γ ν τ Pack.error Pack.output Pack.order Pack.rule (k : ℝ)
    (fun i => (scalar i).packing_order) hrobust hpackingDensity hpackingDegree
  obtain ⟨S,hS,⟨D⟩⟩ := exists_encoded_distribution G U Z code k hk hregular hno
    (fun i j hij => hdisj hij) hUZ hcover
  letI := hS
  obtain ⟨selection⟩ := exists_pattern_selection G U Z code k t D η a hk ht
    ambient.frequent_large hη hη1 ha
  let q := ∑ p, selection.multiplicity p
  let h := k-q
  have hqk : q ≤ k := selection.total_le
  have hcast : (h : ℝ) = (k : ℝ)-q := Nat.cast_sub hqk
  have hretained : (k : ℝ)/(3*B) ≤ (h : ℝ) :=
    selection.reserve_lower.trans (by exact_mod_cast selection.retained_lower)
  have hhpos : 0 < h := by
    have hh : (0 : ℝ) < h := (div_pos hkR (by positivity)).trans_le hretained
    exact_mod_cast hh
  have hlimit (i : I) : q ≤ Nat.floor ((k : ℝ)-γ*(U i).card) := by
    apply Nat.le_floor
    have hh := (scalar i).reserve.trans hretained
    change γ*(U i).card ≤ (h : ℝ) at hh
    rw [hcast] at hh
    linarith only [hh]
  obtain ⟨Family⟩ := exists_completed_pattern_family G U Z code H k t D
    η a Pack.error Pack.output (τ/2) selection hη ha ht
    (fun i j hij => hdisj hij) hUZ hcover hembed hregular hdegree
    (fun i => (scalar i).packing_error) (fun i => (scalar i).footprint)
    rule (fun i => Nat.floor ((k : ℝ)-γ*(U i).card)) hcertificate hlimit
  let Comp := Family.completion
  let R := afterDeletions G Comp.full q
  let K := fun i => remainingCore (U i) (H i) (Comp.core i) (range q)
  have hRregular : ∀ x, R.degree x = h := Comp.residual_regular q le_rfl
  have hKembed : ∀ i, K i ≤ R.induce (U i : Set V) := Comp.core_embedded q le_rfl
  have hKdegree (i : I) (x : U i) : (h : ℝ)-a ≤ ((K i).degree x : ℝ) := by
    rw [hcast]
    exact (Comp.core_degree q le_rfl i x).1
  have hKrobust : ∀ i, IsRobustExpander (K i) Pack.output (τ/2) :=
    Comp.core_robust q le_rfl
  have hsafe := Comp.safe_selected_prefixes G U Z code H k t D η a Pack.output (τ/2)
    selection Family.boundary hk hη.le hη1 hdisj hUZ hcover hregular hno
    Family.boundary_counts γ α hγ hα Pack.output_pos (by positivity) hσsafe
    (ambient.reserve.trans hretained)
    (by linarith only [hknR,show (0 : ℝ) ≤ n from Nat.cast_nonneg n])
    ambient.safe_error ambient.robust_cut hsize
  obtain ⟨s₀,_hs₀,henc₀⟩ := D.positive_witness selection.frequent selection.frequent_positive
  obtain ⟨assignment,hassignment⟩ := henc₀.exists_core_assignment
    selection.frequent_no_internal (fun i j hij => hdisj hij) hcover
  let A := enlargedSets U Z assignment
  let L := enlargedGraphs R U K Z assignment
  have hAold : ∀ i, U i ⊆ A i := old_subset_enlarged U Z assignment
  have hAdisj : Pairwise (fun i j => Disjoint (A i) (A j)) :=
    enlargedSets_pairwise_disjoint U Z Z assignment hdisj hUZ (subset_refl _)
  have hAcover (x : V) : ∃ i, x ∈ A i := by
    have hh := enlargedSets_cover U Z Z assignment hcover x
    simpa [A] using hh
  have hLembed : ∀ i, L i ≤ R.induce (A i : Set V) :=
    enlargedGraphs_le_ambient R U K Z assignment hKembed
  have hpool (b : BoundaryPair Z) (hb : boundaryPairLabels b ∈ selection.frequent.boundaryEdges) :
      selection.reserve ≤ (survivingPool G R U Z code b).card :=
    reserved_boundaryPool_card U Z code (fun i j hij => hdisj hij) hUZ
      Family.boundary Comp.full selection.multiplicity selection.frequent selection.reserve
      Comp.present Comp.contains Comp.added_internal Family.boundary_injective
      Family.boundary_image selection.pair_reserved b hb
  have hnew (z : Z) : selection.reserve ≤
      (R.neighborFinset z.val ∩ U (assignment z.val)).card := by
    have hb : boundaryPairLabels (Sum.inl (z,code (assignment z.val)) : BoundaryPair Z) ∈
        selection.frequent.boundaryEdges := by
      rw [boundaryPairLabels_exceptional,← hassignment z]
      exact assignment_edge_mem selection.frequent selection.frequent_no_internal z
    exact (hpool _ hb).trans (survivingPool_exceptional_card_le_neighbors R U Z code
      (fun i j hij => hdisj hij) hUZ hcover z (assignment z.val))
  let a₁ : ℝ := η*k+B+C*a/η
  have ha₁ : 0 ≤ a₁ := by dsimp [a₁]; positivity
  have hhr : (h : ℝ) ≤ selection.reserve+a₁ := by
    have hh := selection.retained_upper
    dsimp [a₁,B,C]
    linarith only [hh]
  have hLdegree : ∀ i x, (h : ℝ)-(a+a₁) ≤ ((L i).degree x : ℝ) := by
    apply enlargedGraphs_degree_error R U K Z assignment h a a₁ ha ha₁ hKdegree
    intro z hz
    have hh : (selection.reserve : ℝ) ≤ (R.neighborFinset z ∩ U (assignment z)).card := by
      exact_mod_cast hnew ⟨z,hz⟩
    linarith only [hh,hhr]
  have hLrobust : ∀ i, IsRobustExpander (L i) (Pack.output/4) τ := by
    intro i
    have hh := enlargedGraphs_robust R U K Z Z assignment Pack.output (τ/2)
      Pack.output_pos.le Pack.output_le hτquarter (subset_refl _)
      (fun i => (scalar i).addition) hKrobust i
    convert hh using 1
    ring
  have herrorFinal : a+a₁ ≤ δ*h :=
    ambient.final_error.trans (mul_le_mul_of_nonneg_left hretained hδ.le)
  have hpair : ∀ p ∈ selection.frequent.forest,
      selection.reserve ≤ (partPairEdges R A code p).card := by
    intro p hp
    have hb : boundaryPairLabels (Sum.inr p : BoundaryPair Z) ∈
        selection.frequent.boundaryEdges := by
      exact mem_union_right _ (mem_image.mpr ⟨p,hp,rfl⟩)
    exact (hpool _ hb).trans (survivingPool_joining_card_le R U A Z code
      (fun i j hij => hdisj hij) (fun i j hij => hAdisj hij) hAold hcover p)
  refine ⟨{
    G := R
    h := h
    N := Comp.full
    rounds := q
    graph_eq := rfl
    degree_eq := rfl
    perfect := Comp.perfect
    present := Comp.present
    regular := hRregular
    safe_prefixes := hsafe
    no_overfull := hsafe q le_rfl
    degree_positive := hhpos
    retained_degree := hretained
    U := A
    H := L
    core_enlargement := hAold
    core_disjoint := hAdisj
    cover := hAcover
    core_embed := hLembed
    error := a+a₁
    error_nonneg := add_nonneg ha ha₁
    error_bound := herrorFinal
    core_degree := hLdegree
    core_robust := hLrobust
    reserve := selection.reserve
    reserve_le := selection.retained_lower
    reserve_error := by linarith only [hhr,herrorFinal,ha]
    code := code
    forest := selection.frequent.forest
    forest_isForest := henc₀.forest
    forest_shape := by
      intro hfour hodd
      exact henc₀.forestShape_of_four_odd_enlarged selection.frequent_no_internal
        (fun i j hij => hdisj hij) hUZ hcover (D.parity s₀) assignment hassignment hfour hodd
    pair_supply := hpair
    cut_supply := forest_supply_of_pair_supply R A code selection.frequent.forest
      selection.reserve (fun i j hij => hAdisj hij) hAcover hpair
  }⟩

end Overfull
