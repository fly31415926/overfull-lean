import Overfull.MatchingPolytope
import Overfull.MatchingProbability

/-!
# Matching-deletion probabilities for loopless multigraphs

Every parallel edge copy remains a separate element of the edge type.
The three cut-failure bounds apply to the regular multigraphs used in the
completion arguments, with a distribution supplied by the proved matching
polytope theorem.
-/

namespace Overfull.MultigraphMatchingProbability

open Finset Classical
open Overfull.Multigraph (matchingIndicator)
open Overfull.MatchingProbability (probability probability_nonneg probability_mono
  probability_union_le probability_exists_le_sum probability_markov toggle toggle_odd)
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] {G : Multigraph V E}

noncomputable def cutEdges (F : Finset E) (X : Finset V) : Finset E :=
  Lovasz.BMatch.cut G.firstEnd G.secondEnd F X

noncomputable def cutCount (F : Finset E) (X : Finset V) : ℕ :=
  (cutEdges (G := G) F X).card

noncomputable def incidentCount (F : Finset E) (v : V) : ℕ :=
  (F.filter (fun e => G.firstEnd e = v ∨ G.secondEnd e = v)).card

noncomputable def insideCount (F : Finset E) (X : Finset V) : ℕ :=
  (Lovasz.BMatch.inside G.firstEnd G.secondEnd F X).card

noncomputable def matchingEdges (M : Finset E) : Finset E :=
  univ.filter (fun e => e ∈ M)

noncomputable def remainingEdges (M : Finset E) : Finset E :=
  univ.filter (fun e => e ∉ M)

/-- The actual loopless multigraph obtained by deleting the selected edge
copies. Its edge type retains exactly the original copies outside `M`. -/
def remainingGraph (G : Multigraph V E) (M : Finset E) :
    Multigraph V {e : E // e ∉ M} where
  edge e := G.edge e.val
  loopless e := G.loopless e.val

/-- The remaining cut has fewer than `k-1` edges. The `+1<k` form avoids
truncated subtraction and is equivalent for every positive `k`. -/
noncomputable def CutFailure (M : Finset E) (k : ℕ) (X : Finset V) : Prop :=
  cutCount (G := G) (remainingEdges M) X + 1 < k

omit [Fintype V] in
private theorem matching_cut_filter (M : Finset E) (X : Finset V) :
    cutEdges (G := G) (matchingEdges M) X =
      (cutEdges (G := G) univ X).filter (fun e => e ∈ M) := by
  ext e
  simp only [cutEdges, matchingEdges, Lovasz.BMatch.cut,
    Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

omit [Fintype V] in
private theorem remaining_cut_filter (M : Finset E) (X : Finset V) :
    cutEdges (G := G) (remainingEdges M) X =
      (cutEdges (G := G) univ X).filter (fun e => e ∉ M) := by
  ext e
  simp only [cutEdges, remainingEdges, Lovasz.BMatch.cut,
    Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

omit [Fintype V] in
theorem cut_partition (M : Finset E) (X : Finset V) :
    cutCount (G := G) (matchingEdges M) X + cutCount (G := G) (remainingEdges M) X =
      cutCount (G := G) (univ : Finset E) X := by
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := cutEdges (G := G) univ X) (fun e : E => e ∈ M)
  rw [← matching_cut_filter, ← remaining_cut_filter] at h
  exact h

omit [Fintype V] in
theorem matching_cut_le (M : Finset E) (X : Finset V) :
    cutCount (G := G) (matchingEdges M) X ≤ cutCount (G := G) (univ : Finset E) X := by
  have h := cut_partition (G := G) M X
  omega

omit [Fintype E] in
/-- The handshaking identity restricted to any finite set of actual edges. -/
theorem cut_handshake (F : Finset E) (X : Finset V) :
    (∑ v ∈ X, incidentCount (G := G) F v) = cutCount (G := G) F X + 2 * insideCount (G := G) F X := by
  have h := Lovasz.BMatch.handshake G.firstEnd G.secondEnd F
    (fun e _ => G.endpoints_distinct e) X (fun _ => (1 : ℝ))
  simp only [Lovasz.BMatch.dsum, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

omit [Fintype E] in
theorem total_incidence (F : Finset E) :
    (∑ v : V, incidentCount (G := G) F v) = 2 * F.card := by
  have h := cut_handshake (G := G) F univ
  simpa [cutCount, cutEdges, insideCount, Lovasz.BMatch.cut, Lovasz.BMatch.inside] using h

omit [Fintype V] in
theorem incidentCount_univ (v : V) :
    incidentCount (G := G) (univ : Finset E) v = G.degree v := by
  simp only [incidentCount, Multigraph.degree, Multigraph.incidenceEdges, G.incident_iff]

omit [Fintype V] in
theorem incidentCount_matching (M : Finset E) (hM : G.IsPerfectMatching M) (v : V) :
    incidentCount (G := G) (matchingEdges M) v = 1 := by
  have h := hM v
  simpa [incidentCount, matchingEdges, G.incident_iff,
    Finset.filter_filter, and_comm] using h

theorem matching_cut_handshake (M : Finset E) (hM : G.IsPerfectMatching M)
    (X : Finset V) :
    X.card = cutCount (G := G) (matchingEdges M) X + 2 * insideCount (G := G) (matchingEdges M) X := by
  simpa [incidentCount_matching (G := G) M hM] using cut_handshake (G := G) (matchingEdges M) X

theorem matching_odd_cut (M : Finset E) (hM : G.IsPerfectMatching M)
    (X : Finset V) (hX : X.card % 2 = 1) :
    cutCount (G := G) (matchingEdges M) X % 2 = 1 ∧ 1 ≤ cutCount (G := G) (matchingEdges M) X := by
  have h := matching_cut_handshake (G := G) M hM X
  omega

theorem regular_cut_handshake {k : ℕ} (hregular : ∀ v, G.degree v = k)
    (X : Finset V) :
    k * X.card = cutCount (G := G) (univ : Finset E) X + 2 * (G.internalEdges X).card := by
  have h := cut_handshake (G := G) (univ : Finset E) X
  have hins : insideCount (G := G) univ X = (G.internalEdges X).card := by
    unfold insideCount Lovasz.BMatch.inside
    congr 1
    ext e
    simp
  simpa [incidentCount_univ, hregular, hins, Nat.mul_comm] using h

theorem regular_odd_cut {k : ℕ} (hregular : ∀ v, G.degree v = k)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull k X)
    (X : Finset V) (hX : X.card % 2 = 1) :
    ∃ σ : ℕ, cutCount (G := G) (univ : Finset E) X = k + σ ∧ σ % 2 = 0 := by
  have h := regular_cut_handshake (G := G) hregular X
  have hcard : X.card = 2 * (X.card / 2) + 1 := by omega
  have hi : (G.internalEdges X).card ≤ k * (X.card / 2) := Nat.not_lt.mp (hno X)
  have hk : k ≤ cutCount (G := G) (univ : Finset E) X := by
    rw [hcard] at h
    nlinarith
  have hmod := congrArg (fun a : ℕ => a % 2) h
  simp [Nat.add_mod, Nat.mul_mod, hX] at hmod
  refine ⟨cutCount (G := G) (univ : Finset E) X - k, by omega, ?_⟩
  omega

theorem odd_failure_threshold {k σ : ℕ}
    (M : Finset E) (hM : G.IsPerfectMatching M)
    (X : Finset V) (hX : X.card % 2 = 1)
    (hcut : cutCount (G := G) (univ : Finset E) X = k + σ) (hσ : σ % 2 = 0)
    (hfail : CutFailure (G := G) M k X) : σ + 3 ≤ cutCount (G := G) (matchingEdges M) X := by
  have hpart := cut_partition (G := G) M X
  have hc := (matching_odd_cut (G := G) M hM X hX).1
  unfold CutFailure at hfail
  omega

omit [Fintype V] [Fintype E] in
/-- This proves both toggle formulas directly from actual edges. -/
theorem cut_toggle (F : Finset E) (X : Finset V) (v : V) :
    cutCount (G := G) F (toggle X v) + 2 * incidentCount (G := G) (cutEdges (G := G) F X) v =
      cutCount (G := G) F X + incidentCount (G := G) F v := by
  simp only [cutCount, cutEdges, incidentCount, Lovasz.BMatch.cut,
    Finset.filter_filter, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have hne := G.endpoints_distinct e
  by_cases hv : v ∈ X <;>
    by_cases h1 : G.firstEnd e = v <;> by_cases h2 : G.secondEnd e = v <;>
    by_cases hx : G.firstEnd e ∈ X <;> by_cases hy : G.secondEnd e ∈ X <;>
    simp_all [toggle]

omit [Fintype V] in
theorem light_toggle_failure {k : ℕ} (hregular : ∀ v, G.degree v = k)
    (M : Finset E) (hM : G.IsPerfectMatching M) (Y : Finset V) (v : V)
    (hlight : 4 * incidentCount (G := G) (cutEdges (G := G) (univ : Finset E) Y) v ≤
      cutCount (G := G) (univ : Finset E) Y)
    (hfail : CutFailure (G := G) M k (toggle Y v)) :
    cutCount (G := G) (univ : Finset E) Y < 2 * cutCount (G := G) (matchingEdges M) Y := by
  have hG := cut_toggle (G := G) (univ : Finset E) Y v
  have hM' := cut_toggle (G := G) (matchingEdges M) Y v
  have hp := cut_partition (G := G) M (toggle Y v)
  rw [incidentCount_univ (G := G), hregular] at hG
  rw [incidentCount_matching (G := G) M hM] at hM'
  unfold CutFailure at hfail
  omega

noncomputable def heavyVertices (Y : Finset V) : Finset V :=
  univ.filter (fun v => cutCount (G := G) (univ : Finset E) Y <
    4 * incidentCount (G := G) (cutEdges (G := G) (univ : Finset E) Y) v)

/-- Fewer than eight vertices meet more than one quarter of a fixed cut. -/
theorem heavyVertices_card (Y : Finset V) : (heavyVertices (G := G) Y).card < 8 := by
  let b := cutCount (G := G) (univ : Finset E) Y
  let p := fun v => incidentCount (G := G) (cutEdges (G := G) (univ : Finset E) Y) v
  let S := heavyVertices (G := G) Y
  have hsum : (∑ v : V, p v) = 2 * b := total_incidence (G := G) (cutEdges (G := G) univ Y)
  have hpart : (∑ v ∈ S, p v) ≤ ∑ v : V, p v := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun _ _ _ => Nat.zero_le _)
  have hsmall : S.card * (b + 1) ≤ 4 * ∑ v ∈ S, p v := by
    calc
      _ = ∑ _v ∈ S, (b + 1) := by simp
      _ ≤ ∑ v ∈ S, 4 * p v := by
        apply Finset.sum_le_sum
        intro v hv
        have hv' : b < 4 * p v := (Finset.mem_filter.mp hv).2
        omega
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hbound : S.card * (b + 1) ≤ 8 * b := by
    nlinarith
  change S.card < 8
  by_contra hnot
  have hlarge : 8 ≤ S.card := by omega
  have hmul := Nat.mul_le_mul_right (b + 1) hlarge
  nlinarith

omit [Fintype V] in
/-- The cut counted using the original edge copies is the actual cut of the
multigraph after deletion. -/
theorem remaining_cut_count (M : Finset E) (X : Finset V) :
    cutCount (G := G) (remainingEdges M) X = (remainingGraph G M).cutSize X := by
  have himage : ((remainingGraph G M).cutEdges X).image Subtype.val =
      cutEdges (G := G) (remainingEdges M) X := by
    ext e
    simp only [Finset.mem_image, Multigraph.mem_cutEdges, cutEdges, remainingEdges,
      Lovasz.BMatch.cut, Finset.mem_filter, Finset.mem_univ, true_and]
    change (∃ a : {e : E // e ∉ M},
      ((G.firstEnd a.val ∈ X) ≠ (G.secondEnd a.val ∈ X)) ∧ a.val = e) ↔
        e ∉ M ∧ ((G.firstEnd e ∈ X) ≠ (G.secondEnd e ∈ X))
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.property, ha⟩
    · rintro ⟨he, hcross⟩
      exact ⟨⟨e, he⟩, hcross, rfl⟩
  rw [Multigraph.cutSize, ← Finset.card_image_of_injective _ Subtype.val_injective,
    himage]
  rfl

omit [Fintype V] in
/-- Failure means that the actual residual cut is smaller than its new
regular degree. -/
theorem cutFailure_iff_actual_cut (M : Finset E) (k : ℕ) (X : Finset V) :
    CutFailure (G := G) M k X ↔ (remainingGraph G M).cutSize X < k - 1 := by
  rw [CutFailure, remaining_cut_count]
  omega

omit [Fintype V] in
theorem remaining_degree (M : Finset E) (v : V) :
    (remainingGraph G M).degree v = incidentCount (G := G) (remainingEdges M) v := by
  have himage : ((remainingGraph G M).incidenceEdges v).image Subtype.val =
      (remainingEdges M).filter (fun e => G.firstEnd e = v ∨ G.secondEnd e = v) := by
    ext e
    simp only [Finset.mem_image, Multigraph.mem_incidenceEdges, remainingEdges,
      Finset.mem_filter, Finset.mem_univ, true_and]
    change (∃ a : {e : E // e ∉ M}, v ∈ G.edge a.val ∧ a.val = e) ↔
      e ∉ M ∧ (G.firstEnd e = v ∨ G.secondEnd e = v)
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.property, (G.incident_iff _ _).mp ha⟩
    · rintro ⟨he, hv⟩
      exact ⟨⟨e, he⟩, (G.incident_iff _ _).mpr hv, rfl⟩
  rw [Multigraph.degree, ← Finset.card_image_of_injective _ Subtype.val_injective,
    himage]
  rfl

omit [Fintype V] in
theorem incident_partition (M : Finset E) (v : V) :
    incidentCount (G := G) (matchingEdges M) v +
        incidentCount (G := G) (remainingEdges M) v = G.degree v := by
  have hmatch : (G.incidenceEdges v).filter (fun e => e ∈ M) =
      (matchingEdges M).filter (fun e => G.firstEnd e = v ∨ G.secondEnd e = v) := by
    ext e
    simp only [Multigraph.mem_incidenceEdges, matchingEdges, Finset.mem_filter,
      Finset.mem_univ, true_and, G.incident_iff]
    tauto
  have hremain : (G.incidenceEdges v).filter (fun e => e ∉ M) =
      (remainingEdges M).filter (fun e => G.firstEnd e = v ∨ G.secondEnd e = v) := by
    ext e
    simp only [Multigraph.mem_incidenceEdges, remainingEdges, Finset.mem_filter,
      Finset.mem_univ, true_and, G.incident_iff]
    tauto
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := G.incidenceEdges v) (fun e : E => e ∈ M)
  rw [hmatch, hremain] at h
  exact h

omit [Fintype V] in
/-- Every selected edge copy removes one incidence at each of its endpoints. -/
theorem remaining_degree_add_selected (M : Finset E) (v : V) :
    (remainingGraph G M).degree v + (M.filter (fun e => v ∈ G.edge e)).card =
      G.degree v := by
  have hselected : incidentCount (G := G) (matchingEdges M) v =
      (M.filter (fun e => v ∈ G.edge e)).card := by
    simp [incidentCount, matchingEdges, G.incident_iff]
  have h := incident_partition (G := G) M v
  rw [hselected, ← remaining_degree] at h
  omega

omit [Fintype V] in
/-- Deleting a perfect matching from a `k`-regular multigraph makes it
`(k-1)`-regular, counting every remaining parallel copy. -/
theorem remaining_regular {k : ℕ} (hregular : ∀ v, G.degree v = k)
    (M : Finset E) (hM : G.IsPerfectMatching M) (v : V) :
    (remainingGraph G M).degree v = k - 1 := by
  have h := incident_partition (G := G) M v
  rw [incidentCount_matching (G := G) M hM, hregular] at h
  rw [remaining_degree]
  omega

/-- A finite distribution on actual perfect matchings, with uniform edge-copy marginals. -/
structure Distribution (G : Multigraph V E) (k : ℕ) (ι : Type*) [Fintype ι] where
  weight : ι → ℝ
  matching : ι → Finset E
  nonneg : ∀ i, 0 ≤ weight i
  sum_one : ∑ i, weight i = 1
  perfect : ∀ i, G.IsPerfectMatching (matching i)
  marginal : ∀ e : E,
    ∑ i ∈ univ.filter (fun i => e ∈ matching i), weight i = 1 / (k : ℝ)

omit [Fintype V] in
theorem matching_cut_indicator_sum (M : Finset E) (X : Finset V) :
    (cutCount (G := G) (matchingEdges M) X : ℝ) =
      ∑ e ∈ cutEdges (G := G) (univ : Finset E) X, matchingIndicator M e := by
  rw [cutCount, matching_cut_filter]
  simp only [matchingIndicator, Finset.sum_boole]

namespace Distribution

variable {ι : Type*} [Fintype ι] {k : ℕ} (D : Distribution G k ι)

omit [Fintype V] in
theorem expected_cut (X : Finset V) :
    (∑ i, D.weight i * (cutCount (G := G) (matchingEdges (D.matching i)) X : ℝ)) =
      (cutCount (G := G) (univ : Finset E) X : ℝ) / k := by
  calc
    _ = ∑ e ∈ cutEdges (G := G) (univ : Finset E) X,
        ∑ i ∈ univ.filter (fun i => e ∈ D.matching i), D.weight i := by
      simp only [matching_cut_indicator_sum (G := G), Finset.mul_sum, matchingIndicator,
        mul_ite, mul_one, mul_zero]
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ = ∑ _e ∈ cutEdges (G := G) (univ : Finset E) X, (1 : ℝ) / k := by
      apply Finset.sum_congr rfl
      intro e _
      exact D.marginal e
    _ = _ := by simp [cutCount, div_eq_mul_inv]

/-- A fixed odd set fails with probability strictly smaller than `1/k`. -/
theorem odd_failure_probability (hk : 0 < k) (hregular : ∀ v, G.degree v = k)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull k X)
    (X : Finset V) (hX : X.card % 2 = 1) :
    probability D.weight (fun i => CutFailure (G := G) (D.matching i) k X) < 1 / (k : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨σ, hcut, hσ⟩ := regular_odd_cut (G := G) hregular hno X hX
  have hnonneg (i : ι) : 0 ≤ (cutCount (G := G) (matchingEdges (D.matching i)) X : ℝ) - 1 := by
    have hc := (matching_odd_cut (G := G) (D.matching i) (D.perfect i) X hX).2
    have hcR : (1 : ℝ) ≤ (cutCount (G := G) (matchingEdges (D.matching i)) X : ℝ) := by
      exact_mod_cast hc
    linarith
  have hthreshold (i : ι) (hi : CutFailure (G := G) (D.matching i) k X) :
      (σ : ℝ) + 2 ≤ (cutCount (G := G) (matchingEdges (D.matching i)) X : ℝ) - 1 := by
    have h := odd_failure_threshold (G := G) (D.matching i) (D.perfect i) X hX hcut hσ hi
    have hR : (σ : ℝ) + 3 ≤ (cutCount (G := G) (matchingEdges (D.matching i)) X : ℝ) := by
      exact_mod_cast h
    linarith
  have hexpect :
      (∑ i, D.weight i * ((cutCount (G := G) (matchingEdges (D.matching i)) X : ℝ) - 1)) =
        (σ : ℝ) / k := by
    simp_rw [mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, D.expected_cut X, D.sum_one, hcut, Nat.cast_add, add_div,
      div_self hkR.ne']
    ring
  have hmark := probability_markov D.weight D.nonneg
    (fun i => (cutCount (G := G) (matchingEdges (D.matching i)) X : ℝ) - 1)
    hnonneg ((σ : ℝ) + 2) (fun i => CutFailure (G := G) (D.matching i) k X) hthreshold
  rw [hexpect] at hmark
  by_contra hn
  have hp : (1 : ℝ) / k ≤ probability D.weight (fun i => CutFailure (G := G) (D.matching i) k X) :=
    le_of_not_gt hn
  have hbound := (mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ σ + 2 by positivity)).trans hmark
  have hdiv : ((σ : ℝ) + 2) / k ≤ (σ : ℝ) / k := by simpa [mul_one_div] using hbound
  have hbad := (div_le_div_iff_of_pos_right hkR).mp hdiv
  linarith

omit [Fintype V] in
theorem large_matching_cut_probability (hk : 0 < k) (Y : Finset V) :
    probability D.weight (fun i => cutCount (G := G) (univ : Finset E) Y <
      2 * cutCount (G := G) (matchingEdges (D.matching i)) Y) ≤ 2 / (k : ℝ) := by
  let b := cutCount (G := G) (univ : Finset E) Y
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  by_cases hb : 0 < b
  · have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    have hmark := probability_markov D.weight D.nonneg
      (fun i => 2 * (cutCount (G := G) (matchingEdges (D.matching i)) Y : ℝ))
      (fun _ => by positivity) (b : ℝ)
      (fun i => b < 2 * cutCount (G := G) (matchingEdges (D.matching i)) Y)
      (fun i hi => by dsimp only; exact_mod_cast Nat.le_of_lt hi)
    apply (mul_le_mul_iff_right₀ hbR).mp
    calc
      _ ≤ ∑ i, D.weight i * (2 * (cutCount (G := G) (matchingEdges (D.matching i)) Y : ℝ)) := hmark
      _ = 2 * ∑ i, D.weight i * (cutCount (G := G) (matchingEdges (D.matching i)) Y : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (b : ℝ) * (2 / k) := by rw [D.expected_cut Y]; dsimp [b]; ring
  · have hb0 : b = 0 := by omega
    have hempty (i : ι) : ¬ b < 2 * cutCount (G := G) (matchingEdges (D.matching i)) Y := by
      have hle := matching_cut_le (G := G) (D.matching i) Y
      change cutCount (G := G) (matchingEdges (D.matching i)) Y ≤ b at hle
      omega
    change probability D.weight (fun i => b < 2 * cutCount (G := G) (matchingEdges (D.matching i)) Y) ≤ _
    simp only [probability, hempty, Finset.filter_false, Finset.sum_empty]
    positivity

/-- All one-vertex changes of one even set have total failure probability at
most `10/k`, independently of the number of vertices. -/
theorem even_toggles_failure_probability (hk : 0 < k)
    (hregular : ∀ v, G.degree v = k)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull k X)
    (Y : Finset V) (hY : Y.card % 2 = 0) :
    probability D.weight (fun i => ∃ v : V, CutFailure (G := G) (D.matching i) k (toggle Y v)) ≤
      10 / (k : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  let S := heavyVertices (G := G) Y
  let P := fun i => ∃ v ∈ S, CutFailure (G := G) (D.matching i) k (toggle Y v)
  let Q := fun i => cutCount (G := G) (univ : Finset E) Y <
    2 * cutCount (G := G) (matchingEdges (D.matching i)) Y
  have hheavy : probability D.weight P ≤ 8 / (k : ℝ) := by
    calc
      _ ≤ ∑ v ∈ S, probability D.weight
          (fun i => CutFailure (G := G) (D.matching i) k (toggle Y v)) :=
        probability_exists_le_sum D.weight D.nonneg S _
      _ ≤ ∑ _v ∈ S, (1 : ℝ) / k := by
        apply Finset.sum_le_sum
        intro v _
        exact (D.odd_failure_probability hk hregular hno (toggle Y v) (toggle_odd hY v)).le
      _ = (S.card : ℝ) * (1 / k) := by simp
      _ ≤ 8 * (1 / k) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hS : S.card ≤ 8 := (heavyVertices_card (G := G) Y).le
        exact_mod_cast hS
      _ = _ := by ring
  have hlarge : probability D.weight Q ≤ 2 / (k : ℝ) := D.large_matching_cut_probability hk Y
  have hcontained (i : ι) (hi : ∃ v : V, CutFailure (G := G) (D.matching i) k (toggle Y v)) :
      P i ∨ Q i := by
    obtain ⟨v, hv⟩ := hi
    by_cases hS : v ∈ S
    · exact Or.inl ⟨v, hS, hv⟩
    · apply Or.inr
      apply light_toggle_failure (G := G) hregular (D.matching i) (D.perfect i) Y v _ hv
      have hS' : ¬ cutCount (G := G) (univ : Finset E) Y <
          4 * incidentCount (G := G) (cutEdges (G := G) (univ : Finset E) Y) v := by
        simpa [S, heavyVertices] using hS
      omega
  calc
    _ ≤ probability D.weight (fun i => P i ∨ Q i) :=
      probability_mono D.weight D.nonneg hcontained
    _ ≤ probability D.weight P + probability D.weight Q :=
      probability_union_le D.weight D.nonneg P Q
    _ ≤ 8 / (k : ℝ) + 2 / k := add_le_add hheavy hlarge
    _ = _ := by ring

end Distribution

/-- Failure for an odd member, or for a one-vertex change of an even member,
of the specified family. Even members themselves impose no odd-cut condition. -/
noncomputable def FamilyFailure (M : Finset E) (k : ℕ) (𝓧 : Finset (Finset V)) : Prop :=
  ∃ X ∈ 𝓧, (X.card % 2 = 1 ∧ CutFailure (G := G) M k X) ∨
    (X.card % 2 = 0 ∧ ∃ v : V, CutFailure (G := G) M k (toggle X v))

namespace Distribution

variable {ι : Type*} [Fintype ι] {k : ℕ} (D : Distribution G k ι)

/-- The union bound requested in the manuscript for a family of vertex sets. -/
theorem family_failure_probability (hk : 0 < k) (hregular : ∀ v, G.degree v = k)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull k X) (𝓧 : Finset (Finset V)) :
    probability D.weight (fun i => FamilyFailure (G := G) (D.matching i) k 𝓧) ≤
      11 * (𝓧.card : ℝ) / k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  unfold FamilyFailure
  calc
    _ ≤ ∑ X ∈ 𝓧, probability D.weight (fun i =>
        (X.card % 2 = 1 ∧ CutFailure (G := G) (D.matching i) k X) ∨
          (X.card % 2 = 0 ∧ ∃ v : V, CutFailure (G := G) (D.matching i) k (toggle X v))) :=
      probability_exists_le_sum D.weight D.nonneg 𝓧 _
    _ ≤ ∑ _X ∈ 𝓧, (11 : ℝ) / k := by
      apply Finset.sum_le_sum
      intro X _
      by_cases hX : X.card % 2 = 1
      · simp only [hX, one_ne_zero, false_and, or_false, true_and]
        calc
          _ ≤ 1 / (k : ℝ) := (D.odd_failure_probability hk hregular hno X hX).le
          _ ≤ 11 / k := div_le_div_of_nonneg_right (by norm_num) hkR.le
      · have hX0 : X.card % 2 = 0 := by omega
        simp only [hX0, zero_ne_one, false_and, false_or, true_and]
        calc
          _ ≤ 10 / (k : ℝ) := D.even_toggles_failure_probability hk hregular hno X hX0
          _ ≤ 11 / k := div_le_div_of_nonneg_right (by norm_num) hkR.le
    _ = _ := by simp; ring

end Distribution

/-- The required distribution exists for every positive regular loopless
multigraph without an overfull set. -/
theorem exists_distribution {k : ℕ} (hk : 0 < k) (hregular : ∀ v, G.degree v = k)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull k X) :
    ∃ (ι : Type) (_ : Fintype ι), Nonempty (Distribution G k ι) := by
  obtain ⟨ι, hι, w, M, hw, hsum, hM, hmarginal⟩ :=
    G.exists_perfectMatching_distribution hk hregular hno
  letI := hι
  exact ⟨ι, hι, ⟨⟨w, M, (fun i => (hw i).le), hsum, hM, hmarginal⟩⟩⟩

end Overfull.MultigraphMatchingProbability
