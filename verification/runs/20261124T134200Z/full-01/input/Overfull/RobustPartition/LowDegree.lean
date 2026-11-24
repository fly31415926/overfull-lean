import Overfull.RobustPartition.CriticalConsequences
import Overfull.RobustPartition.Theorem

/-!
# Deleting the actual low-degree set before robust partitioning

This is the deterministic reduction in Proposition 2.24.  Its numerical
hypothesis is a small total degree deficiency in the original graph.  No
asymptotic average-degree theorem for critical graphs is postulated here.
-/

noncomputable section

universe u

namespace Overfull.RobustPartition

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

/-- Exactly the low-degree set in the manuscript. -/
def lowDegreeVertices (G : SimpleGraph V) (ζ : ℝ) : Finset V :=
  univ.filter (fun v => ζ * Fintype.card V < (G.maxDegree : ℝ) - G.degree v)

/-- The actual surviving original vertices. -/
def survivingVertices (G : SimpleGraph V) (ζ : ℝ) : Finset V :=
  (lowDegreeVertices G ζ)ᶜ

/-- The induced graph after deletion, with vertices retaining their original labels. -/
def survivingGraph (G : SimpleGraph V) (ζ : ℝ) :
    SimpleGraph (survivingVertices G ζ : Set V) :=
  G.induce (survivingVertices G ζ : Set V)

local instance (priority := 2000) survivingDecidableEq (G : SimpleGraph V) (ζ : ℝ) :
    DecidableEq (survivingVertices G ζ : Set V) := fun _ _ => Classical.propDecidable _

/-- The total-deficiency estimate gives a strict bound for the actual deleted set. -/
theorem lowDegreeVertices_card_lt (G : SimpleGraph V) (ζ : ℝ)
    (hζ : 0 < ζ) (hn : 0 < (Fintype.card V : ℝ))
    (hdef : (∑ v : V, ((G.maxDegree : ℝ) - G.degree v)) <
      ζ^3 * (Fintype.card V : ℝ)^2) :
    ((lowDegreeVertices G ζ).card : ℝ) < ζ^2 * Fintype.card V := by
  have hsum : ((lowDegreeVertices G ζ).card : ℝ) * (ζ * Fintype.card V) ≤
      ∑ v : V, ((G.maxDegree : ℝ) - G.degree v) := by
    calc
      _ = ∑ _v ∈ lowDegreeVertices G ζ, ζ * Fintype.card V := by simp
      _ ≤ ∑ v ∈ lowDegreeVertices G ζ, ((G.maxDegree : ℝ) - G.degree v) := by
        apply Finset.sum_le_sum
        intro v hv
        exact (Finset.mem_filter.mp hv).2.le
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun v _ _ => sub_nonneg.mpr (by exact_mod_cast G.degree_le_maxDegree v))
  have hprod : ζ^3 * (Fintype.card V : ℝ)^2 =
      (ζ^2 * Fintype.card V) * (ζ * Fintype.card V) := by ring
  rw [hprod] at hdef
  exact (mul_lt_mul_iff_left₀ (mul_pos hζ hn)).mp (hsum.trans_lt hdef)

/-- The surviving subtype has exactly the complement's cardinality. -/
theorem surviving_card_add_deleted (G : SimpleGraph V) (ζ : ℝ) :
    Fintype.card (survivingVertices G ζ : Set V) + (lowDegreeVertices G ζ).card =
      Fintype.card V := by
  have hc : Fintype.card (survivingVertices G ζ : Set V) = (survivingVertices G ζ).card := by
    simpa only [← Nat.card_eq_fintype_card] using Fintype.card_coe (survivingVertices G ζ)
  rw [hc]
  change ((lowDegreeVertices G ζ)ᶜ).card + (lowDegreeVertices G ζ).card = _
  rw [Finset.card_compl]
  exact Nat.sub_add_cancel (Finset.card_le_univ _)

/-- The actual surviving subtype has more than the required proportion of vertices. -/
theorem surviving_card_lower (G : SimpleGraph V) (ζ : ℝ)
    (hsmall : ((lowDegreeVertices G ζ).card : ℝ) < ζ^2 * Fintype.card V) :
    (1 - ζ^2) * Fintype.card V <
      (Fintype.card (survivingVertices G ζ : Set V) : ℝ) := by
  have hsum : (Fintype.card (survivingVertices G ζ : Set V) : ℝ) +
      (lowDegreeVertices G ζ).card = Fintype.card V := by
    exact_mod_cast surviving_card_add_deleted G ζ
  nlinarith

/-- A retained vertex has small original deficiency by the actual set definition. -/
theorem surviving_original_degree_lower (G : SimpleGraph V) (ζ : ℝ)
    (v : (survivingVertices G ζ : Set V)) :
    (G.maxDegree : ℝ) - ζ * Fintype.card V ≤ G.degree v.val := by
  have hnot : v.val ∉ lowDegreeVertices G ζ := Finset.mem_compl.mp v.property
  have h := (show ¬ ζ * Fintype.card V < (G.maxDegree : ℝ) - G.degree v.val by
    simpa only [lowDegreeVertices, Finset.mem_filter, Finset.mem_univ, true_and] using hnot)
  linarith

/-- Deletion removes at most the size of the actual deleted set from each degree. -/
theorem surviving_degree_bounds (G : SimpleGraph V) (ζ : ℝ)
    (hsmall : ((lowDegreeVertices G ζ).card : ℝ) ≤ ζ^2 * Fintype.card V)
    (v : (survivingVertices G ζ : Set V)) :
    (G.maxDegree : ℝ) - (ζ + ζ^2) * Fintype.card V ≤
        ((survivingGraph G ζ).degree v : ℝ) ∧
      ((survivingGraph G ζ).degree v : ℝ) ≤ G.maxDegree := by
  have hlocal : (survivingGraph G ζ).degree v =
      (G.neighborFinset v.val ∩ survivingVertices G ζ).card :=
    induced_degree_eq_local_count G (survivingVertices G ζ) v
  rw [hlocal]
  have hcount : ((G.neighborFinset v.val ∩ survivingVertices G ζ).card : ℝ) +
      (G.neighborFinset v.val ∩ lowDegreeVertices G ζ).card = G.degree v.val := by
    have h := Finset.card_inter_add_card_sdiff (G.neighborFinset v.val) (lowDegreeVertices G ζ)
    rw [Finset.sdiff_eq_inter_compl, SimpleGraph.card_neighborFinset_eq_degree] at h
    change _ + (G.neighborFinset v.val ∩ survivingVertices G ζ).card = _ at h
    exact_mod_cast (show (G.neighborFinset v.val ∩ survivingVertices G ζ).card +
      (G.neighborFinset v.val ∩ lowDegreeVertices G ζ).card = G.degree v.val by omega)
  have hlost : ((G.neighborFinset v.val ∩ lowDegreeVertices G ζ).card : ℝ) ≤
      (lowDegreeVertices G ζ).card := by
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_right :
      G.neighborFinset v.val ∩ lowDegreeVertices G ζ ⊆ lowDegreeVertices G ζ)
  have hretained := surviving_original_degree_lower G ζ v
  have hupper : (G.degree v.val : ℝ) ≤ G.maxDegree := by
    exact_mod_cast G.degree_le_maxDegree v.val
  have hnonneg : 0 ≤ ((G.neighborFinset v.val ∩ lowDegreeVertices G ζ).card : ℝ) :=
    Nat.cast_nonneg _
  constructor <;> nlinarith


/-- Choose the deletion threshold before any graph, with any prescribed upper bound. -/
theorem exists_deletion_scale (γ θ ζ₀ : ℝ) (hγ : 0 < γ) (hθ : 0 < θ)
    (hζ₀ : 0 < ζ₀) :
    ∃ ζ : ℝ, 0 < ζ ∧ ζ < ζ₀ ∧ ζ < 1 / 2 ∧
      ζ + ζ^2 < γ / 2 ∧ ζ + ζ^2 < θ := by
  let δ : ℝ := min γ (min θ (min ζ₀ 1))
  have hδ : 0 < δ := lt_min hγ (lt_min hθ (lt_min hζ₀ (by norm_num)))
  have hδγ : δ ≤ γ := min_le_left _ _
  have hδθ : δ ≤ θ := (min_le_right _ _).trans (min_le_left _ _)
  have hδζ : δ ≤ ζ₀ := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hsq : (δ / 8)^2 ≤ δ / 8 := by nlinarith
  exact ⟨δ / 8, by positivity, by linarith, by linarith, by nlinarith, by nlinarith⟩

/-- The actual robust partition after deletion, with the parameters and the
original-order transfer needed for every conclusion of Proposition 2.24. -/
structure SmallDeficiencyPartition (G : SimpleGraph V) (ζ γ θ τ : ℝ)
    (f : ℝ → ℝ) where
  rho : ℝ
  nu : ℝ
  gamma_le_rho : γ ≤ rho
  rho_pos : 0 < rho
  rho_le_nu : rho ≤ nu
  nu_le_range : nu ≤ τ
  rho_le_function : rho ≤ f nu
  rho_le_cubic : rho ≤ (θ / 100)^3
  deleted_small : ((lowDegreeVertices G ζ).card : ℝ) < ζ^2 * Fintype.card V
  surviving_order_lower : (1 - ζ^2) * Fintype.card V <
    (Fintype.card (survivingVertices G ζ : Set V) : ℝ)
  positive_order : 0 < (Fintype.card (survivingVertices G ζ : Set V) : ℝ)
  min_degree_lower : (G.maxDegree : ℝ) - (ζ + ζ^2) * Fintype.card V ≤
    (survivingGraph G ζ).minDegree
  min_degree_transfer : (G.maxDegree : ℝ) - rho * Fintype.card V ≤
    (survivingGraph G ζ).minDegree
  max_degree_le : ((survivingGraph G ζ).maxDegree : ℝ) ≤ G.maxDegree
  density : (1 / 4 : ℝ) * Fintype.card (survivingVertices G ζ : Set V) ≤
    (survivingGraph G ζ).minDegree
  almost_regular : ((survivingGraph G ζ).maxDegree : ℝ) ≤
    (survivingGraph G ζ).minDegree + γ * Fintype.card (survivingVertices G ζ : Set V)
  pieces : List (Piece (survivingVertices G ζ : Set V))
  partition : PartitionConclusion (survivingGraph G ζ)
    (survivingGraph G ζ).minDegree rho nu τ pieces
  five_cases :
    (ordinaryCount pieces = 1 ∧ bipartiteCount pieces = 0) ∨
    (ordinaryCount pieces = 0 ∧ bipartiteCount pieces = 1) ∨
    (ordinaryCount pieces = 2 ∧ bipartiteCount pieces = 0) ∨
    (ordinaryCount pieces = 3 ∧ bipartiteCount pieces = 0) ∨
    (ordinaryCount pieces = 1 ∧ bipartiteCount pieces = 1)

/-- All parameters precede the graph.  The hypothesis is an actual sum of
original degree deficiencies, and the output constructs the actual low-degree
deletion and a robust partition of its induced graph. -/
theorem exists_uniform_small_deficiency_partition (θ τ ζ₀ : ℝ) (f : ℝ → ℝ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 12) (hτ : 0 < τ) (hτ1 : τ < 1 / 2)
    (hζ₀ : 0 < ζ₀) (hf : ∀ x, 0 < x → x < 1 → 0 < f x) :
    ∃ ζ γ : ℝ, 0 < ζ ∧ ζ < ζ₀ ∧ 0 < γ ∧
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V),
        0 < (Fintype.card V : ℝ) →
        (1 / 4 + θ) * Fintype.card V ≤ (G.maxDegree : ℝ) →
        (∑ v : V, ((G.maxDegree : ℝ) - G.degree v)) <
          ζ^3 * (Fintype.card V : ℝ)^2 →
        Nonempty (SmallDeficiencyPartition G ζ γ θ τ f) := by
  let f₀ : ℝ → ℝ := fun x => min (f x) ((θ / 100)^3)
  have hf₀ : ∀ x, 0 < x → x < 1 → 0 < f₀ x := by
    intro x hx hx1
    exact lt_min (hf x hx hx1) (by positivity)
  obtain ⟨γ, hγ, hpartition⟩ :=
    exists_uniform_partition (1 / 4 : ℝ) τ f₀ (by norm_num) hτ hτ1 hf₀
  obtain ⟨ζ, hζ, hζζ₀, hζhalf, hζγ, hζθ⟩ := exists_deletion_scale γ θ ζ₀ hγ hθ hζ₀
  refine ⟨ζ, γ, hζ, hζζ₀, hγ, ?_⟩
  intro V _ G hn hdensity hdef
  let H := survivingGraph G ζ
  let m : ℝ := Fintype.card (survivingVertices G ζ : Set V)
  let n : ℝ := Fintype.card V
  have hzsmall := lowDegreeVertices_card_lt G ζ hζ hn hdef
  have hm : (1 - ζ^2) * n < m := surviving_card_lower G ζ hzsmall
  have hmle : m ≤ n := by
    have hnat := surviving_card_add_deleted G ζ
    have hcard : Fintype.card (survivingVertices G ζ : Set V) ≤ Fintype.card V := by omega
    have hcast : (Fintype.card (survivingVertices G ζ : Set V) : ℝ) ≤ Fintype.card V := by
      exact_mod_cast hcard
    simpa only [m, n, ← Nat.card_eq_fintype_card] using hcast
  have hζsq : ζ^2 < 1 / 4 := by nlinarith
  have hmhalf : n / 2 < m := by nlinarith
  have hmpos : 0 < m := by nlinarith
  have hpositive : (0 : ℕ) < Fintype.card (survivingVertices G ζ : Set V) := by
    have hcast : (0 : ℝ) < Fintype.card (survivingVertices G ζ : Set V) := by
      simpa only [m, ← Nat.card_eq_fintype_card] using hmpos
    exact_mod_cast hcast
  haveI : Nonempty (survivingVertices G ζ : Set V) :=
    Fintype.card_pos_iff.mp hpositive
  have hmin : (G.maxDegree : ℝ) - (ζ + ζ^2) * n ≤ H.minDegree := by
    obtain ⟨v, hv⟩ := H.exists_minimal_degree_vertex
    rw [hv]
    exact (surviving_degree_bounds G ζ hzsmall.le v).1
  have hmax : (H.maxDegree : ℝ) ≤ G.maxDegree := by
    obtain ⟨v, hv⟩ := H.exists_maximal_degree_vertex
    rw [hv]
    exact (surviving_degree_bounds G ζ hzsmall.le v).2
  have had : (1 / 4 : ℝ) * m ≤ H.minDegree := by
    have hmul := mul_lt_mul_of_pos_right hζθ hn
    dsimp [n] at *
    nlinarith
  have halmost : (H.maxDegree : ℝ) ≤ (H.minDegree : ℝ) + γ * m := by
    have herror := mul_lt_mul_of_pos_right hζγ hn
    have hmass := mul_lt_mul_of_pos_left hmhalf hγ
    nlinarith
  obtain ⟨ρ, ν, L, hγρ, hρν, hντ, hρf₀, hL⟩ :=
    hpartition (survivingVertices G ζ : Set V) H H.minDegree hmpos had
      (fun v => by exact_mod_cast H.minDegree_le_degree v)
      (fun v => (show (H.degree v : ℝ) ≤ H.maxDegree by
        exact_mod_cast H.degree_le_maxDegree v).trans halmost)
  have hρ : 0 < ρ := hγ.trans_le hγρ
  have hρf : ρ ≤ f ν := hρf₀.trans (min_le_left _ _)
  have hρsmall : ρ ≤ (θ / 100)^3 := hρf₀.trans (min_le_right _ _)
  have htransfer : (G.maxDegree : ℝ) - ρ * n ≤ H.minDegree := by
    have herror : ζ + ζ^2 ≤ ρ := by linarith
    have hmul := mul_le_mul_of_nonneg_right herror hn.le
    linarith
  refine ⟨{
    rho := ρ, nu := ν, gamma_le_rho := hγρ, rho_pos := hρ,
    rho_le_nu := hρν, nu_le_range := hντ, rho_le_function := hρf,
    rho_le_cubic := hρsmall, deleted_small := hzsmall,
    surviving_order_lower := hm, positive_order := hmpos,
    min_degree_lower := hmin, min_degree_transfer := htransfer,
    max_degree_le := hmax, density := had, almost_regular := halmost,
    pieces := L, partition := hL,
    five_cases := hL.five_cases n G.maxDegree θ hmpos hmle hθ hθ1 hρ hρsmall
      hdensity htransfer }⟩


/-- Deletion never increases the actual vertex count. -/
theorem surviving_card_le (G : SimpleGraph V) (ζ : ℝ) :
    (Fintype.card (survivingVertices G ζ : Set V) : ℝ) ≤ Fintype.card V := by
  have h := surviving_card_add_deleted G ζ
  exact_mod_cast (show Fintype.card (survivingVertices G ζ : Set V) ≤ Fintype.card V by omega)

/-- The ordinary conclusions of Proposition 2.24, for the actual constructed
partition and its surviving original labels. -/
theorem SmallDeficiencyPartition.ordinary_bounds
    {G : SimpleGraph V} {ζ γ θ τ : ℝ} {f : ℝ → ℝ}
    (R : SmallDeficiencyPartition G ζ γ θ τ f)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 12)
    (U : Finset (survivingVertices G ζ : Set V)) (hU : Piece.ordinary U ∈ R.pieces) :
    (G.maxDegree : ℝ) - 2 * R.rho * Fintype.card V + 1 ≤ (U.card : ℝ) ∧
      ∃ Z : Finset (survivingVertices G ζ : Set V), Z ⊆ U ∧
        (Z.card : ℝ) ≤ R.rho * Fintype.card V ∧
        ∀ v ∈ U, v ∉ Z → (G.maxDegree : ℝ) - 2 * R.rho * Fintype.card V ≤
          (((survivingGraph G ζ).neighborFinset v ∩ U).card : ℝ) := by
  have hρ1 := (cubic_error_bounds θ R.rho hθ hθ1 R.rho_pos R.rho_le_cubic).1
  exact R.partition.ordinary_transferred_bounds R.rho_pos hρ1 R.positive_order
    (Fintype.card V) G.maxDegree (surviving_card_le G ζ) R.min_degree_transfer U hU

/-- The two shore-size bounds and one actual opposite-degree exceptional set. -/
theorem SmallDeficiencyPartition.bipartite_bounds
    {G : SimpleGraph V} {ζ γ θ τ : ℝ} {f : ℝ → ℝ}
    (R : SmallDeficiencyPartition G ζ γ θ τ f)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 12)
    (A B : Finset (survivingVertices G ζ : Set V))
    (hAB : Piece.bipartite A B ∈ R.pieces) :
    (G.maxDegree : ℝ) - 3 * Real.sqrt R.rho * Fintype.card V ≤ (A.card : ℝ) ∧
    (G.maxDegree : ℝ) - 3 * Real.sqrt R.rho * Fintype.card V ≤ (B.card : ℝ) ∧
    ∃ Z : Finset (survivingVertices G ζ : Set V), Z ⊆ A ∪ B ∧
      (Z.card : ℝ) ≤ 2 * Real.sqrt R.rho * Fintype.card V ∧
      (∀ v ∈ A, v ∉ Z →
        (G.maxDegree : ℝ) - 2 * Real.sqrt R.rho * Fintype.card V ≤
          (((survivingGraph G ζ).neighborFinset v ∩ B).card : ℝ)) ∧
      (∀ v ∈ B, v ∉ Z →
        (G.maxDegree : ℝ) - 2 * Real.sqrt R.rho * Fintype.card V ≤
          (((survivingGraph G ζ).neighborFinset v ∩ A).card : ℝ)) := by
  have hρ1 := (cubic_error_bounds θ R.rho hθ hθ1 R.rho_pos R.rho_le_cubic).1
  exact R.partition.bipartite_transferred_bounds
    (fun v => by exact_mod_cast (survivingGraph G ζ).minDegree_le_degree v)
    R.rho_pos hρ1 R.positive_order (Fintype.card V) G.maxDegree
    (surviving_card_le G ζ) R.min_degree_transfer A B hAB

/-- The exact lower and upper original-order estimates when three shores remain. -/
theorem SmallDeficiencyPartition.three_shore_bounds
    {G : SimpleGraph V} {ζ γ θ τ : ℝ} {f : ℝ → ℝ}
    (R : SmallDeficiencyPartition G ζ γ θ τ f)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 12)
    (hthree : ordinaryCount R.pieces + 2 * bipartiteCount R.pieces = 3) :
    ∀ X ∈ shoreList R.pieces,
      (G.maxDegree : ℝ) - 3 * Real.sqrt R.rho * Fintype.card V ≤ (X.card : ℝ) ∧
      (X.card : ℝ) ≤ Fintype.card V - 2 * (G.maxDegree : ℝ) +
        6 * Real.sqrt R.rho * Fintype.card V := by
  have hρ1 := (cubic_error_bounds θ R.rho hθ hθ1 R.rho_pos R.rho_le_cubic).1
  exact R.partition.three_shore_transferred_bounds
    (fun v => by exact_mod_cast (survivingGraph G ζ).minDegree_le_degree v)
    R.rho_pos hρ1 R.positive_order (Fintype.card V) G.maxDegree
    (surviving_card_le G ζ) R.min_degree_transfer hthree


/-- Convert the normalized average-degree estimate into the exact total-deficiency
hypothesis used by the actual deletion construction. -/
theorem total_deficiency_lt_of_average_degree (G : SimpleGraph V) (ζ : ℝ)
    (hζ : 0 < ζ) (hn : 0 < (Fintype.card V : ℝ))
    (haverage : (1 - ζ^3 / 2) * (G.maxDegree : ℝ) ≤
      (∑ v : V, (G.degree v : ℝ)) / Fintype.card V) :
    (∑ v : V, ((G.maxDegree : ℝ) - G.degree v)) <
      ζ^3 * (Fintype.card V : ℝ)^2 := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by exact_mod_cast hn)
  have hmax : (G.maxDegree : ℝ) ≤ Fintype.card V := by
    exact_mod_cast G.maxDegree_lt_card_verts.le
  have hsum : (∑ v : V, ((G.maxDegree : ℝ) - G.degree v)) =
      (Fintype.card V : ℝ) * G.maxDegree - ∑ v : V, (G.degree v : ℝ) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have haverage' := (le_div_iff₀ hn).mp haverage
  have hmul := mul_le_mul_of_nonneg_right hmax
    (by positivity : 0 ≤ ζ^3 / 2 * (Fintype.card V : ℝ))
  have hpositive : 0 < ζ^3 * (Fintype.card V : ℝ)^2 := by positivity
  rw [hsum]
  nlinarith

/-- The full deterministic critical-partition construction from the average-degree
estimate, with every constant chosen before the graph.  The implication from
criticality to that average-degree estimate is the separate missing input. -/
theorem exists_uniform_partition_of_average_degree (θ τ ζ₀ : ℝ) (f : ℝ → ℝ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 12) (hτ : 0 < τ) (hτ1 : τ < 1 / 2)
    (hζ₀ : 0 < ζ₀) (hf : ∀ x, 0 < x → x < 1 → 0 < f x) :
    ∃ ζ γ : ℝ, 0 < ζ ∧ ζ < ζ₀ ∧ 0 < γ ∧
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V),
        0 < (Fintype.card V : ℝ) →
        (1 / 4 + θ) * Fintype.card V ≤ (G.maxDegree : ℝ) →
        (1 - ζ^3 / 2) * (G.maxDegree : ℝ) ≤
          (∑ v : V, (G.degree v : ℝ)) / Fintype.card V →
        Nonempty (SmallDeficiencyPartition G ζ γ θ τ f) := by
  obtain ⟨ζ, γ, hζ, hζζ₀, hγ, hconstruct⟩ :=
    exists_uniform_small_deficiency_partition θ τ ζ₀ f hθ hθ1 hτ hτ1 hζ₀ hf
  refine ⟨ζ, γ, hζ, hζζ₀, hγ, ?_⟩
  intro V _ G hn hdensity haverage
  exact hconstruct V G hn hdensity (total_deficiency_lt_of_average_degree G ζ hζ hn haverage)

end Overfull.RobustPartition
