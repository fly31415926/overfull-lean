import Overfull.FractionalMatching

/-!
Failure probabilities for odd cuts after deleting an actual perfect matching.
All cut counts are finsets of the original simple graph's unordered edges;
the chosen endpoint orientation is used only to test whether an edge crosses.
-/

namespace Overfull.MatchingProbability

open Finset Classical FractionalMatching
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def cutEdges (F : Finset G.edgeSet) (X : Finset V) : Finset G.edgeSet :=
  Lovasz.BMatch.cut firstEnd secondEnd F X

noncomputable def cutCount (F : Finset G.edgeSet) (X : Finset V) : ℕ :=
  (cutEdges F X).card

noncomputable def incidentCount (F : Finset G.edgeSet) (v : V) : ℕ :=
  (F.filter (fun e => firstEnd e = v ∨ secondEnd e = v)).card

noncomputable def insideCount (F : Finset G.edgeSet) (X : Finset V) : ℕ :=
  (Lovasz.BMatch.inside firstEnd secondEnd F X).card

noncomputable def matchingEdges (M : G.Subgraph) : Finset G.edgeSet :=
  univ.filter (fun e => e.val ∈ M.edgeSet)

noncomputable def remainingEdges (M : G.Subgraph) : Finset G.edgeSet :=
  univ.filter (fun e => e.val ∉ M.edgeSet)

/-- The remaining cut has fewer than `k-1` edges. The `+1<k` form avoids
truncated subtraction and is equivalent for every positive `k`. -/
noncomputable def CutFailure (M : G.Subgraph) (k : ℕ) (X : Finset V) : Prop :=
  cutCount (remainingEdges M) X + 1 < k

theorem cut_partition (M : G.Subgraph) (X : Finset V) :
    cutCount (matchingEdges M) X + cutCount (remainingEdges M) X =
      cutCount (univ : Finset G.edgeSet) X := by
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := cutEdges univ X) (fun e : G.edgeSet => e.val ∈ M.edgeSet)
  simpa [cutCount, cutEdges, matchingEdges, remainingEdges, Lovasz.BMatch.cut,
    Finset.filter_filter, and_comm] using h

theorem matching_cut_le (M : G.Subgraph) (X : Finset V) :
    cutCount (matchingEdges M) X ≤ cutCount (univ : Finset G.edgeSet) X := by
  have h := cut_partition M X
  omega

omit [DecidableRel G.Adj] in
/-- The handshaking identity restricted to any finite set of actual edges. -/
theorem cut_handshake (F : Finset G.edgeSet) (X : Finset V) :
    (∑ v ∈ X, incidentCount F v) = cutCount F X + 2 * insideCount F X := by
  have h := Lovasz.BMatch.handshake firstEnd secondEnd F
    (fun e _ => endpoints_distinct e) X (fun _ => (1 : ℝ))
  simp only [Lovasz.BMatch.dsum, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

omit [DecidableRel G.Adj] in
theorem total_incidence (F : Finset G.edgeSet) :
    (∑ v : V, incidentCount F v) = 2 * F.card := by
  have h := cut_handshake F univ
  simpa [cutCount, cutEdges, insideCount, Lovasz.BMatch.cut, Lovasz.BMatch.inside] using h

theorem incidentCount_univ (v : V) :
    incidentCount (univ : Finset G.edgeSet) v = G.degree v := incident_card v

theorem incidentCount_matching (M : G.Subgraph) (hM : M.IsPerfectMatching) (v : V) :
    incidentCount (matchingEdges M) v = 1 := by
  have h := perfectMatching_indicator_degree M hM v
  simp only [Lovasz.BMatch.dsum, matchingIndicator, Finset.sum_boole] at h
  have heq : incidentCount (matchingEdges M) v =
      ((univ.filter (fun e : G.edgeSet => firstEnd e = v ∨ secondEnd e = v)).filter
        (fun e => e.val ∈ M.edgeSet)).card := by
    simp [incidentCount, matchingEdges, Finset.filter_filter, and_comm]
  rw [← heq] at h
  exact_mod_cast h

theorem matching_cut_handshake (M : G.Subgraph) (hM : M.IsPerfectMatching)
    (X : Finset V) :
    X.card = cutCount (matchingEdges M) X + 2 * insideCount (matchingEdges M) X := by
  simpa [incidentCount_matching M hM] using cut_handshake (matchingEdges M) X

theorem matching_odd_cut (M : G.Subgraph) (hM : M.IsPerfectMatching)
    (X : Finset V) (hX : X.card % 2 = 1) :
    cutCount (matchingEdges M) X % 2 = 1 ∧ 1 ≤ cutCount (matchingEdges M) X := by
  have h := matching_cut_handshake M hM X
  omega

theorem regular_cut_handshake {k : ℕ} (hregular : ∀ v, G.degree v = k)
    (X : Finset V) :
    k * X.card = cutCount (univ : Finset G.edgeSet) X + 2 * (internalEdges G X).card := by
  have h := cut_handshake (univ : Finset G.edgeSet) X
  simpa [incidentCount_univ, hregular, insideCount, inside_eq, Nat.mul_comm] using h

theorem regular_odd_cut {k : ℕ} (hregular : ∀ v, G.degree v = k)
    (hno : ∀ X : Finset V, ¬ IsOverfull G k X)
    (X : Finset V) (hX : X.card % 2 = 1) :
    ∃ σ : ℕ, cutCount (univ : Finset G.edgeSet) X = k + σ ∧ σ % 2 = 0 := by
  have h := regular_cut_handshake hregular X
  have hcard : X.card = 2 * (X.card / 2) + 1 := by omega
  have hi : (internalEdges G X).card ≤ k * (X.card / 2) := Nat.not_lt.mp (hno X)
  have hk : k ≤ cutCount (univ : Finset G.edgeSet) X := by
    rw [hcard] at h
    nlinarith
  have hmod := congrArg (fun a : ℕ => a % 2) h
  simp [Nat.add_mod, Nat.mul_mod, hX] at hmod
  refine ⟨cutCount (univ : Finset G.edgeSet) X - k, by omega, ?_⟩
  omega

theorem odd_failure_threshold {k σ : ℕ}
    (M : G.Subgraph) (hM : M.IsPerfectMatching)
    (X : Finset V) (hX : X.card % 2 = 1)
    (hcut : cutCount (univ : Finset G.edgeSet) X = k + σ) (hσ : σ % 2 = 0)
    (hfail : CutFailure M k X) : σ + 3 ≤ cutCount (matchingEdges M) X := by
  have hpart := cut_partition M X
  have hc := (matching_odd_cut M hM X hX).1
  unfold CutFailure at hfail
  omega

/-- Toggling membership of one vertex is symmetric difference with its singleton. -/
noncomputable def toggle (X : Finset V) (v : V) : Finset V :=
  if v ∈ X then X.erase v else insert v X

omit [Fintype V] in
theorem toggle_odd {X : Finset V} (hX : X.card % 2 = 0) (v : V) :
    (toggle X v).card % 2 = 1 := by
  by_cases hv : v ∈ X
  · have hp : 0 < X.card := Finset.card_pos.mpr ⟨v, hv⟩
    simp only [toggle, if_pos hv, Finset.card_erase_of_mem hv]
    omega
  · simp only [toggle, if_neg hv, Finset.card_insert_of_notMem hv]
    omega

omit [Fintype V] [DecidableRel G.Adj] in
/-- This proves both toggle formulas directly from actual edges. -/
theorem cut_toggle (F : Finset G.edgeSet) (X : Finset V) (v : V) :
    cutCount F (toggle X v) + 2 * incidentCount (cutEdges F X) v =
      cutCount F X + incidentCount F v := by
  simp only [cutCount, cutEdges, incidentCount, Lovasz.BMatch.cut,
    Finset.filter_filter, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have hne := endpoints_distinct e
  by_cases hv : v ∈ X <;>
    by_cases h1 : firstEnd e = v <;> by_cases h2 : secondEnd e = v <;>
    by_cases hx : firstEnd e ∈ X <;> by_cases hy : secondEnd e ∈ X <;>
    simp_all [toggle]

theorem light_toggle_failure {k : ℕ} (hregular : ∀ v, G.degree v = k)
    (M : G.Subgraph) (hM : M.IsPerfectMatching) (Y : Finset V) (v : V)
    (hlight : 4 * incidentCount (cutEdges (univ : Finset G.edgeSet) Y) v ≤
      cutCount (univ : Finset G.edgeSet) Y)
    (hfail : CutFailure M k (toggle Y v)) :
    cutCount (univ : Finset G.edgeSet) Y < 2 * cutCount (matchingEdges M) Y := by
  have hG := cut_toggle (univ : Finset G.edgeSet) Y v
  have hM' := cut_toggle (matchingEdges M) Y v
  have hp := cut_partition M (toggle Y v)
  rw [incidentCount_univ, hregular] at hG
  rw [incidentCount_matching M hM] at hM'
  unfold CutFailure at hfail
  omega

noncomputable def heavyVertices (Y : Finset V) : Finset V :=
  univ.filter (fun v => cutCount (univ : Finset G.edgeSet) Y <
    4 * incidentCount (cutEdges (univ : Finset G.edgeSet) Y) v)

/-- Fewer than eight vertices meet more than one quarter of a fixed cut. -/
theorem heavyVertices_card (Y : Finset V) : (heavyVertices (G := G) Y).card < 8 := by
  let b := cutCount (univ : Finset G.edgeSet) Y
  let p := fun v => incidentCount (cutEdges (univ : Finset G.edgeSet) Y) v
  let S := heavyVertices (G := G) Y
  have hsum : (∑ v : V, p v) = 2 * b := total_incidence (cutEdges univ Y)
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

/-- An unordered edge crosses a vertex set when it has one end on each side. -/
def Crosses (X : Finset V) (e : Sym2 V) : Prop :=
  ∃ v w, e = s(v, w) ∧ v ∈ X ∧ w ∉ X

omit [Fintype V] in
theorem crosses_pair (X : Finset V) (v w : V) :
    Crosses X s(v, w) ↔ (v ∈ X ∧ w ∉ X) ∨ (w ∈ X ∧ v ∉ X) := by
  constructor
  · rintro ⟨a, b, he, ha, hb⟩
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨ha, hb⟩
  · rintro (⟨hv, hw⟩ | ⟨hw, hv⟩)
    · exact ⟨v, w, rfl, hv, hw⟩
    · exact ⟨w, v, Sym2.eq_swap, hw, hv⟩

omit [Fintype V] [DecidableRel G.Adj] in
theorem crosses_iff_endpoints (X : Finset V) (e : G.edgeSet) :
    Crosses X e.val ↔ (firstEnd e ∈ X) ≠ (secondEnd e ∈ X) := by
  rw [← edge_eq e, crosses_pair]
  simp only [ne_eq, eq_iff_iff]
  tauto

noncomputable def graphCutEdges (H : SimpleGraph V) (X : Finset V) : Finset (Sym2 V) :=
  H.edgeFinset.filter (Crosses X)

noncomputable def graphCutCount (H : SimpleGraph V) (X : Finset V) : ℕ :=
  (graphCutEdges H X).card

omit [Fintype V] [DecidableRel G.Adj] in
theorem cutEdges_image (F : Finset G.edgeSet) (X : Finset V) :
    (cutEdges F X).image Subtype.val = (F.image Subtype.val).filter (Crosses X) := by
  ext e
  constructor
  · intro he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨haF, haX⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨a, haF, rfl⟩,
      (crosses_iff_endpoints X a).mpr haX⟩
  · intro he
    obtain ⟨ha, hcross⟩ := Finset.mem_filter.mp he
    obtain ⟨a, haF, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_image.mpr ⟨a,
      Finset.mem_filter.mpr ⟨haF, (crosses_iff_endpoints X a).mp hcross⟩, rfl⟩

/-- Deleting the selected edges really produces `G \ M.spanningCoe`. -/
theorem remainingEdges_image (M : G.Subgraph) :
    (remainingEdges M).image Subtype.val = (G \ M.spanningCoe).edgeFinset := by
  ext e
  have hMset : M.spanningCoe.edgeSet = M.edgeSet := rfl
  simp only [Finset.mem_image, SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_sdiff,
    Set.mem_diff, hMset]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.property, (Finset.mem_filter.mp ha).2⟩
  · rintro ⟨heG, heM⟩
    exact ⟨⟨e, heG⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heM⟩, rfl⟩

theorem remaining_cut_count (M : G.Subgraph) (X : Finset V) :
    cutCount (remainingEdges M) X = graphCutCount (G \ M.spanningCoe) X := by
  change (cutEdges (remainingEdges M) X).card = _
  rw [← Finset.card_image_of_injective _ Subtype.val_injective,
    cutEdges_image, remainingEdges_image]
  unfold graphCutCount graphCutEdges
  congr 1
  ext e
  simp

theorem cutFailure_iff_actual_cut (M : G.Subgraph) (k : ℕ) (X : Finset V) :
    CutFailure M k X ↔ graphCutCount (G \ M.spanningCoe) X < k - 1 := by
  rw [CutFailure, remaining_cut_count]
  omega

theorem remaining_regular {k : ℕ} (hregular : ∀ v, G.degree v = k)
    (M : G.Subgraph) (hM : M.IsPerfectMatching) (v : V) :
    (G \ M.spanningCoe).degree v = k - 1 := by
  have hN : (G \ M.spanningCoe).neighborFinset v =
      G.neighborFinset v \ M.spanningCoe.neighborFinset v := by
    ext w
    simp
  have hsub : M.spanningCoe.neighborFinset v ⊆ G.neighborFinset v := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw ⊢
    exact M.adj_sub hw
  have hdegree : M.spanningCoe.degree v = 1 := by
    rw [SimpleGraph.Subgraph.degree_spanningCoe]
    exact SimpleGraph.Subgraph.isPerfectMatching_iff_forall_degree.mp hM v
  rw [SimpleGraph.degree, hN, Finset.card_sdiff_of_subset hsub]
  change G.degree v - M.spanningCoe.degree v = _
  rw [hregular, hdegree]

/-- A finite probability distribution on actual perfect matchings, with the
uniform edge marginals used in the manuscript. -/
structure Distribution (G : SimpleGraph V) (k : ℕ) (ι : Type*) [Fintype ι] where
  weight : ι → ℝ
  matching : ι → G.Subgraph
  nonneg : ∀ i, 0 ≤ weight i
  sum_one : ∑ i, weight i = 1
  perfect : ∀ i, (matching i).IsPerfectMatching
  marginal : ∀ e : G.edgeSet,
    ∑ i ∈ univ.filter (fun i => e.val ∈ (matching i).edgeSet), weight i = 1 / (k : ℝ)

noncomputable def probability {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (P : ι → Prop) : ℝ :=
  ∑ i ∈ univ.filter P, w i

theorem probability_nonneg {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (P : ι → Prop) : 0 ≤ probability w P := by
  exact Finset.sum_nonneg (fun i _ => hw i)

theorem probability_mono {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) {P Q : ι → Prop} (hPQ : ∀ i, P i → Q i) :
    probability w P ≤ probability w Q := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hPQ i hi
  · intro i _ _
    exact hw i

theorem probability_union_le {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (P Q : ι → Prop) :
    probability w (fun i => P i ∨ Q i) ≤ probability w P + probability w Q := by
  simp only [probability, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases hP : P i <;> by_cases hQ : Q i <;> simp [hP, hQ, hw i]

theorem probability_exists_le_sum {ι J : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (S : Finset J) (P : J → ι → Prop) :
    probability w (fun i => ∃ j ∈ S, P j i) ≤ ∑ j ∈ S, probability w (P j) := by
  calc
    _ ≤ ∑ i : ι, ∑ j ∈ S, if P j i then w i else 0 := by
      simp only [probability, Finset.sum_filter]
      apply Finset.sum_le_sum
      intro i _
      have hwi := hw i
      by_cases hi : ∃ j ∈ S, P j i
      · obtain ⟨j, hj, hji⟩ := hi
        rw [if_pos ⟨j, hj, hji⟩]
        have h := Finset.single_le_sum
          (fun a (_ : a ∈ S) => by split_ifs <;> positivity :
            ∀ a ∈ S, 0 ≤ if P a i then w i else 0) hj
        simpa only [if_pos hji] using h
      · rw [if_neg hi]
        exact Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [probability, Finset.sum_filter]

/-- The elementary weighted Markov bound, proved as a finite sum inequality. -/
theorem probability_markov {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (F : ι → ℝ) (hF : ∀ i, 0 ≤ F i)
    (a : ℝ) (P : ι → Prop) (hP : ∀ i, P i → a ≤ F i) :
    a * probability w P ≤ ∑ i, w i * F i := by
  simp only [probability, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : P i
  · simp only [if_pos hi]
    simpa only [mul_comm a] using mul_le_mul_of_nonneg_left (hP i hi) (hw i)
  · simp only [if_neg hi, mul_zero]
    exact mul_nonneg (hw i) (hF i)

theorem matching_cut_indicator_sum (M : G.Subgraph) (X : Finset V) :
    (cutCount (matchingEdges M) X : ℝ) =
      ∑ e ∈ cutEdges (univ : Finset G.edgeSet) X, matchingIndicator M e := by
  simp [cutCount, cutEdges, matchingEdges, Lovasz.BMatch.cut,
    matchingIndicator, Finset.sum_boole, Finset.filter_filter, and_comm]

namespace Distribution

variable {ι : Type*} [Fintype ι] {k : ℕ} (D : Distribution G k ι)

theorem expected_cut (X : Finset V) :
    (∑ i, D.weight i * (cutCount (matchingEdges (D.matching i)) X : ℝ)) =
      (cutCount (univ : Finset G.edgeSet) X : ℝ) / k := by
  calc
    _ = ∑ e ∈ cutEdges (univ : Finset G.edgeSet) X,
        ∑ i ∈ univ.filter (fun i => e.val ∈ (D.matching i).edgeSet), D.weight i := by
      simp only [matching_cut_indicator_sum, Finset.mul_sum, matchingIndicator,
        mul_ite, mul_one, mul_zero]
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ = ∑ _e ∈ cutEdges (univ : Finset G.edgeSet) X, (1 : ℝ) / k := by
      apply Finset.sum_congr rfl
      intro e _
      exact D.marginal e
    _ = _ := by simp [cutCount, div_eq_mul_inv]

/-- A fixed odd set fails with probability strictly smaller than `1/k`. -/
theorem odd_failure_probability (hk : 0 < k) (hregular : ∀ v, G.degree v = k)
    (hno : ∀ X : Finset V, ¬ IsOverfull G k X)
    (X : Finset V) (hX : X.card % 2 = 1) :
    probability D.weight (fun i => CutFailure (D.matching i) k X) < 1 / (k : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨σ, hcut, hσ⟩ := regular_odd_cut hregular hno X hX
  have hnonneg (i : ι) : 0 ≤ (cutCount (matchingEdges (D.matching i)) X : ℝ) - 1 := by
    have hc := (matching_odd_cut (D.matching i) (D.perfect i) X hX).2
    have hcR : (1 : ℝ) ≤ (cutCount (matchingEdges (D.matching i)) X : ℝ) := by
      exact_mod_cast hc
    linarith
  have hthreshold (i : ι) (hi : CutFailure (D.matching i) k X) :
      (σ : ℝ) + 2 ≤ (cutCount (matchingEdges (D.matching i)) X : ℝ) - 1 := by
    have h := odd_failure_threshold (D.matching i) (D.perfect i) X hX hcut hσ hi
    have hR : (σ : ℝ) + 3 ≤ (cutCount (matchingEdges (D.matching i)) X : ℝ) := by
      exact_mod_cast h
    linarith
  have hexpect :
      (∑ i, D.weight i * ((cutCount (matchingEdges (D.matching i)) X : ℝ) - 1)) =
        (σ : ℝ) / k := by
    simp_rw [mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, D.expected_cut X, D.sum_one, hcut, Nat.cast_add, add_div,
      div_self hkR.ne']
    ring
  have hmark := probability_markov D.weight D.nonneg
    (fun i => (cutCount (matchingEdges (D.matching i)) X : ℝ) - 1)
    hnonneg ((σ : ℝ) + 2) (fun i => CutFailure (D.matching i) k X) hthreshold
  rw [hexpect] at hmark
  by_contra hn
  have hp : (1 : ℝ) / k ≤ probability D.weight (fun i => CutFailure (D.matching i) k X) :=
    le_of_not_gt hn
  have hbound := (mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ σ + 2 by positivity)).trans hmark
  have hdiv : ((σ : ℝ) + 2) / k ≤ (σ : ℝ) / k := by simpa [mul_one_div] using hbound
  have hbad := (div_le_div_iff_of_pos_right hkR).mp hdiv
  linarith

theorem large_matching_cut_probability (hk : 0 < k) (Y : Finset V) :
    probability D.weight (fun i => cutCount (univ : Finset G.edgeSet) Y <
      2 * cutCount (matchingEdges (D.matching i)) Y) ≤ 2 / (k : ℝ) := by
  let b := cutCount (univ : Finset G.edgeSet) Y
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  by_cases hb : 0 < b
  · have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    have hmark := probability_markov D.weight D.nonneg
      (fun i => 2 * (cutCount (matchingEdges (D.matching i)) Y : ℝ))
      (fun _ => by positivity) (b : ℝ)
      (fun i => b < 2 * cutCount (matchingEdges (D.matching i)) Y)
      (fun i hi => by dsimp only; exact_mod_cast Nat.le_of_lt hi)
    apply (mul_le_mul_iff_right₀ hbR).mp
    calc
      _ ≤ ∑ i, D.weight i * (2 * (cutCount (matchingEdges (D.matching i)) Y : ℝ)) := hmark
      _ = 2 * ∑ i, D.weight i * (cutCount (matchingEdges (D.matching i)) Y : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (b : ℝ) * (2 / k) := by rw [D.expected_cut Y]; dsimp [b]; ring
  · have hb0 : b = 0 := by omega
    have hempty (i : ι) : ¬ b < 2 * cutCount (matchingEdges (D.matching i)) Y := by
      have hle := matching_cut_le (D.matching i) Y
      change cutCount (matchingEdges (D.matching i)) Y ≤ b at hle
      omega
    change probability D.weight (fun i => b < 2 * cutCount (matchingEdges (D.matching i)) Y) ≤ _
    simp only [probability, hempty, Finset.filter_false, Finset.sum_empty]
    positivity

/-- All one-vertex changes of one even set have total failure probability at
most `10/k`, independently of the number of vertices. -/
theorem even_toggles_failure_probability (hk : 0 < k)
    (hregular : ∀ v, G.degree v = k)
    (hno : ∀ X : Finset V, ¬ IsOverfull G k X)
    (Y : Finset V) (hY : Y.card % 2 = 0) :
    probability D.weight (fun i => ∃ v : V, CutFailure (D.matching i) k (toggle Y v)) ≤
      10 / (k : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  let S := heavyVertices (G := G) Y
  let P := fun i => ∃ v ∈ S, CutFailure (D.matching i) k (toggle Y v)
  let Q := fun i => cutCount (univ : Finset G.edgeSet) Y <
    2 * cutCount (matchingEdges (D.matching i)) Y
  have hheavy : probability D.weight P ≤ 8 / (k : ℝ) := by
    calc
      _ ≤ ∑ v ∈ S, probability D.weight
          (fun i => CutFailure (D.matching i) k (toggle Y v)) :=
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
  have hcontained (i : ι) (hi : ∃ v : V, CutFailure (D.matching i) k (toggle Y v)) :
      P i ∨ Q i := by
    obtain ⟨v, hv⟩ := hi
    by_cases hS : v ∈ S
    · exact Or.inl ⟨v, hS, hv⟩
    · apply Or.inr
      apply light_toggle_failure hregular (D.matching i) (D.perfect i) Y v _ hv
      have hS' : ¬ cutCount (univ : Finset G.edgeSet) Y <
          4 * incidentCount (cutEdges (univ : Finset G.edgeSet) Y) v := by
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
noncomputable def FamilyFailure (M : G.Subgraph) (k : ℕ) (𝓧 : Finset (Finset V)) : Prop :=
  ∃ X ∈ 𝓧, (X.card % 2 = 1 ∧ CutFailure M k X) ∨
    (X.card % 2 = 0 ∧ ∃ v : V, CutFailure M k (toggle X v))

namespace Distribution

variable {ι : Type*} [Fintype ι] {k : ℕ} (D : Distribution G k ι)

/-- The union bound requested in the manuscript for a family of vertex sets. -/
theorem family_failure_probability (hk : 0 < k) (hregular : ∀ v, G.degree v = k)
    (hno : ∀ X : Finset V, ¬ IsOverfull G k X) (𝓧 : Finset (Finset V)) :
    probability D.weight (fun i => FamilyFailure (D.matching i) k 𝓧) ≤
      11 * (𝓧.card : ℝ) / k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  unfold FamilyFailure
  calc
    _ ≤ ∑ X ∈ 𝓧, probability D.weight (fun i =>
        (X.card % 2 = 1 ∧ CutFailure (D.matching i) k X) ∨
          (X.card % 2 = 0 ∧ ∃ v : V, CutFailure (D.matching i) k (toggle X v))) :=
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

/-- The required distributions exist under the graph hypotheses, using the
proved perfect-matching polytope theorem and its actual-graph interpretation. -/
theorem exists_distribution {k : ℕ} (hk : 0 < k) (hregular : ∀ v, G.degree v = k)
    (hno : ∀ X : Finset V, ¬ IsOverfull G k X) :
    ∃ (ι : Type) (_ : Fintype ι), Nonempty (Distribution G k ι) := by
  obtain ⟨ι, hι, w, M, hw, hsum, hM, hmarginal⟩ :=
    exists_perfectMatching_distribution hk hregular hno
  letI := hι
  exact ⟨ι, hι, ⟨⟨w, M, hw, hsum, hM, hmarginal⟩⟩⟩

end Overfull.MatchingProbability
