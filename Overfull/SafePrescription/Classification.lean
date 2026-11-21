import Overfull.ForceMatching.Family
import Overfull.ForceMatching.Residual
import Mathlib.Data.Finset.SymmDiff

namespace Overfull.SafePrescription

open Finset Classical MatchingProbability FractionalMatching ForceMatching
open scoped BigOperators symmDiff

variable {V I : Type*} [Fintype V] [Fintype I]

/-- The actual clusters consist of all unmarked vertices with a fixed label. -/
noncomputable def clusterSets (c : V → Fin 4) (Z0 : Finset V) : Fin 4 → Finset V :=
  fun j => univ.filter (fun v => v ∉ Z0 ∧ c v = j)

@[simp] theorem mem_clusterSets (c : V → Fin 4) (Z0 : Finset V) (j : Fin 4) (v : V) :
    v ∈ clusterSets c Z0 j ↔ v ∉ Z0 ∧ c v = j := by
  simp [clusterSets]

theorem clusterSets_disjoint (c : V → Fin 4) (Z0 : Finset V) :
    Pairwise (fun i j => Disjoint (clusterSets c Z0 i) (clusterSets c Z0 j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro v hv hw
  exact hij (((mem_clusterSets c Z0 i v).mp hv).2.symm.trans
    ((mem_clusterSets c Z0 j v).mp hw).2)

theorem clusterSets_disjoint_marked (c : V → Fin 4) (Z0 : Finset V) (j : Fin 4) :
    Disjoint (clusterSets c Z0 j) Z0 := by
  apply disjoint_left.mpr
  intro v hv hz
  exact ((mem_clusterSets c Z0 j v).mp hv).1 hz

theorem clusterSets_cover (c : V → Fin 4) (Z0 : Finset V) (v : V) :
    v ∈ Z0 ∨ ∃ j, v ∈ clusterSets c Z0 j := by
  by_cases h : v ∈ Z0
  · exact Or.inl h
  · exact Or.inr ⟨c v, (mem_clusterSets c Z0 (c v) v).mpr ⟨h, rfl⟩⟩

/-- Unmarked vertices with the same cluster label have the same membership
in every tested family shore. -/
theorem family_same_label (c : V → Fin 4) (Z0 X : Finset V)
    (hX : X ∈ wholeUnions (clusterSets c Z0) Z0)
    (u v : V) (hu : u ∉ Z0) (hv : v ∉ Z0) (hc : c u = c v) :
    u ∈ X ↔ v ∈ X := by
  have hwhole := wholeUnions_whole (clusterSets c Z0) Z0 X
    (clusterSets_disjoint c Z0) (clusterSets_disjoint_marked c Z0) hX
  exact same_core_membership (clusterSets c Z0) X hwhole
    ((mem_clusterSets c Z0 (c u) u).mpr ⟨hu, rfl⟩)
    ((mem_clusterSets c Z0 (c u) v).mpr ⟨hv, hc.symm⟩)

omit [Fintype I] in
/-- Every original core is contained wholly in or wholly outside a tested
cluster union, because all its vertices carry the same unmarked label. -/
theorem family_whole_cores (U : I → Finset V) (Z Z0 : Finset V)
    (c : V → Fin 4) (p : I → Fin 4)
    (hZ0 : Z0 ⊆ Z) (hUZ : ∀ i, Disjoint (U i) Z)
    (hcolor : ∀ i v, v ∈ U i → c v = p i)
    (X : Finset V) (hX : X ∈ wholeUnions (clusterSets c Z0) Z0) :
    ∀ i, U i ⊆ X ∨ Disjoint (U i) X := by
  have hwhole := wholeUnions_whole (clusterSets c Z0) Z0 X
    (clusterSets_disjoint c Z0) (clusterSets_disjoint_marked c Z0) hX
  intro i
  have hsub : U i ⊆ clusterSets c Z0 (p i) := by
    intro v hv
    exact (mem_clusterSets c Z0 (p i) v).mpr
      ⟨fun hz => disjoint_left.mp (hUZ i) hv (hZ0 hz), hcolor i v hv⟩
  rcases hwhole (p i) with hi | hi
  · exact Or.inl (hsub.trans hi)
  · exact Or.inr (hi.mono_left hsub)

/-- The chosen shore contains strictly more than half of a core. -/
def coreMajority (U : I → Finset V) (X : Finset V) (i : I) : Prop :=
  (U i \ X).card < (X ∩ U i).card

/-- Agreement of the core majorities within each group produces an actual
cluster union. Its difference from the given set contains no marked vertex
and has size at most the exceptional order plus the total core minority. -/
theorem cluster_union_approximation (U : I → Finset V) (Z Z0 X : Finset V)
    (c : V → Fin 4) (p : I → Fin 4)
    (hZ0 : Z0 ⊆ Z) (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hcolor : ∀ i v, v ∈ U i → c v = p i)
    (hagreement : ∀ i j, p i = p j → (coreMajority U X i ↔ coreMajority U X j)) :
    ∃ Y ∈ wholeUnions (clusterSets c Z0) Z0,
      (X ∆ Y).card ≤ Z.card + ∑ i, min (X ∩ U i).card (U i \ X).card ∧
      Disjoint (X ∆ Y) Z0 := by
  let A : Finset I := univ.filter (coreMajority U X)
  let B : Finset (Fin 4) := A.image p
  let Y := B.biUnion (clusterSets c Z0) ∪ (X ∩ Z0)
  let T : I → Finset V := fun i =>
    if coreMajority U X i then U i \ X else X ∩ U i
  have hB (i : I) : p i ∈ B ↔ coreMajority U X i := by
    constructor
    · intro hi
      obtain ⟨j, hj, hji⟩ := mem_image.mp hi
      exact (hagreement j i hji).mp ((mem_filter.mp hj).2)
    · intro hi
      exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ i, hi⟩, rfl⟩
  have hYcore (i : I) (v : V) (hv : v ∈ U i) : v ∈ Y ↔ coreMajority U X i := by
    have hvZ : v ∉ Z := fun h => disjoint_left.mp (hUZ i) hv h
    have hvZ0 : v ∉ Z0 := fun h => hvZ (hZ0 h)
    have hcv := hcolor i v hv
    change v ∈ B.biUnion (clusterSets c Z0) ∪ (X ∩ Z0) ↔ _
    simp only [mem_union, mem_inter, hvZ0, and_false, or_false, mem_biUnion,
      mem_clusterSets, not_false_eq_true, true_and, hcv]
    constructor
    · rintro ⟨j, hj, hij⟩
      exact (hB i).mp (hij.symm ▸ hj)
    · intro hi
      exact ⟨p i, (hB i).mpr hi, rfl⟩
  have hTcard (i : I) : (T i).card = min (X ∩ U i).card (U i \ X).card := by
    dsimp only [T]
    split_ifs with h
    · exact (min_eq_right (Nat.le_of_lt h)).symm
    · exact (min_eq_left (Nat.le_of_not_gt h)).symm
  have hsub : X ∆ Y ⊆ Z ∪ univ.biUnion T := by
    intro v hv
    by_cases hvZ : v ∈ Z
    · exact mem_union_left _ hvZ
    obtain ⟨i, hi⟩ := (hcover v).resolve_left hvZ
    have hcore := hYcore i v hi
    have hv' := mem_symmDiff.mp hv
    have hvT : v ∈ T i := by
      by_cases hm : coreMajority U X i
      · have hy : v ∈ Y := hcore.mpr hm
        have hx : v ∉ X := by tauto
        simp [T, hm, hi, hx]
      · have hy : v ∉ Y := fun h => hm (hcore.mp h)
        have hx : v ∈ X := by tauto
        simp [T, hm, hi, hx]
    exact mem_union_right _ (mem_biUnion.mpr ⟨i, mem_univ i, hvT⟩)
  have hmarked : Disjoint (X ∆ Y) Z0 := by
    apply disjoint_left.mpr
    intro v hv hz
    have hYn : v ∈ Y ↔ v ∈ X := by
      have hn : v ∉ B.biUnion (clusterSets c Z0) := by
        intro h
        obtain ⟨j, _, hj⟩ := mem_biUnion.mp h
        exact ((mem_clusterSets c Z0 j v).mp hj).1 hz
      simp [Y, hn, hz]
    have hd := mem_symmDiff.mp hv
    tauto
  refine ⟨Y, (mem_wholeUnions (clusterSets c Z0) Z0 Y).mpr
    ⟨B, X ∩ Z0, inter_subset_right, rfl⟩, ?_, hmarked⟩
  calc
    (X ∆ Y).card ≤ (Z ∪ univ.biUnion T).card := card_le_card hsub
    _ ≤ Z.card + (univ.biUnion T).card := card_union_le _ _
    _ ≤ Z.card + ∑ i, (T i).card := Nat.add_le_add_left card_biUnion_le _
    _ = _ := by simp_rw [hTcard]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem cutCount_univ_eq_cutSize (X : Finset V) :
    cutCount (univ : Finset G.edgeSet) X = (Multigraph.ofSimpleGraph G).cutSize X := by
  rfl

omit [Fintype V] [DecidableRel G.Adj] in
/-- The symmetric-difference identity counts actual edges of the host. -/
theorem cut_symmDiff_identity (F : Finset G.edgeSet) (X W : Finset V) :
    cutCount F (X ∆ W) + 2 * cutCount (cutEdges F X) W =
      cutCount F X + cutCount F W := by
  simp only [cutCount, cutEdges, Lovasz.BMatch.cut, filter_filter,
    card_eq_sum_ones, sum_filter, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro e _
  by_cases hx : firstEnd e ∈ X <;> by_cases hy : secondEnd e ∈ X <;>
    by_cases hw : firstEnd e ∈ W <;> by_cases hz : secondEnd e ∈ W <;>
    simp_all [mem_symmDiff]

omit [Fintype I] in
/-- A simultaneous change of vertex memberships has the required cut lower
bound. Simplicity is used through the proved degree lower bound on a cut. -/
theorem cut_symmDiff_lower_bound (d : ℝ)
    (hdegree : ∀ v, d ≤ (G.degree v : ℝ)) (X W : Finset V) :
    (cutCount (univ : Finset G.edgeSet) X : ℝ) +
      (W.card : ℝ) * (d - W.card + 1) -
        2 * ∑ v ∈ W, (incidentCount (cutEdges (univ : Finset G.edgeSet) X) v : ℝ) ≤
      cutCount (univ : Finset G.edgeSet) (X ∆ W) := by
  have hcut := SmallCuts.cut_lower_bound_degree G d hdegree W
  rw [← cutCount_univ_eq_cutSize G W] at hcut
  have hidentity : (cutCount (univ : Finset G.edgeSet) (X ∆ W) : ℝ) +
      2 * cutCount (cutEdges (univ : Finset G.edgeSet) X) W =
      cutCount (univ : Finset G.edgeSet) X + cutCount (univ : Finset G.edgeSet) W := by
    exact_mod_cast cut_symmDiff_identity G (univ : Finset G.edgeSet) X W
  have hsumNat := cut_handshake (cutEdges (univ : Finset G.edgeSet) X) W
  have hsum : (cutCount (cutEdges (univ : Finset G.edgeSet) X) W : ℝ) ≤
      ∑ v ∈ W, (incidentCount (cutEdges (univ : Finset G.edgeSet) X) v : ℝ) := by
    exact_mod_cast (show cutCount (cutEdges (univ : Finset G.edgeSet) X) W ≤
      ∑ v ∈ W, incidentCount (cutEdges (univ : Finset G.edgeSet) X) v by omega)
  linarith

set_option maxHeartbeats 1000000 in
/-- A small cut whose core majorities agree within groups is one of the
actual tested cluster unions or a single-vertex change of one. -/
theorem classified_small_cut (U : I → Finset V) (Z Z0 X : Finset V)
    (c : V → Fin 4) (p : I → Fin 4) (h : ℕ) (b : ℝ)
    (hZ0 : Z0 ⊆ Z) (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hcolor : ∀ i v, v ∈ U i → c v = p i)
    (hregular : ∀ v, G.degree v = h)
    (hminority : (∑ i, min (X ∩ U i).card (U i \ X).card) ≤ 1)
    (hagreement : ∀ i j, p i = p j → (coreMajority U X i ↔ coreMajority U X j))
    (hboundary : ∀ Y ∈ wholeUnions (clusterSets c Z0) Z0, ∀ v ∉ Z0,
      (incidentCount (cutEdges (univ : Finset G.edgeSet) Y) v : ℝ) ≤ (h : ℝ)/20)
    (hZbound : (2 : ℝ) * Z.card ≤ b) (hb : b < (h : ℝ)/10)
    (hcut : (cutCount (univ : Finset G.edgeSet) X : ℝ) ≤ h+b) :
    X ∈ wholeUnions (clusterSets c Z0) Z0 ∨
      ∃ Y ∈ wholeUnions (clusterSets c Z0) Z0, ∃ v, X = toggle Y v := by
  obtain ⟨Y, hY, hcard, hmarked⟩ :=
    cluster_union_approximation U Z Z0 X c p hZ0 hUZ hcover hcolor hagreement
  have hdiffcard : (X ∆ Y).card ≤ Z.card+1 := by omega
  let W := X ∆ Y
  have hXY : X = Y ∆ W := by
    ext v
    simp only [W, mem_symmDiff]
    tauto
  have hWcard : W.card ≤ 1 := by
    by_contra hnot
    have htwo : (2 : ℝ) ≤ W.card := by exact_mod_cast (show 2 ≤ W.card by omega)
    have hWbound : (W.card : ℝ) ≤ Z.card+1 := by exact_mod_cast hdiffcard
    have hsum : (∑ v ∈ W, (incidentCount (cutEdges (univ : Finset G.edgeSet) Y) v : ℝ)) ≤
        (W.card : ℝ) * ((h : ℝ)/20) := by
      calc
        _ ≤ ∑ _v ∈ W, (h : ℝ)/20 := by
          apply sum_le_sum
          intro v hv
          exact hboundary Y hY v (fun hz => disjoint_left.mp hmarked hv hz)
        _ = _ := by simp
    have hlow := cut_symmDiff_lower_bound G (h : ℝ)
      (fun v => by rw [hregular v]) Y W
    rw [← hXY] at hlow
    have hzsmall : (Z.card : ℝ) < (h : ℝ)/20 := by linarith
    have hcoef : (4 : ℝ)/5*h ≤ (h : ℝ)-W.card+1-(h : ℝ)/10 := by linarith
    have hscale := mul_le_mul_of_nonneg_left hcoef (Nat.cast_nonneg W.card)
    have htwoScale := mul_le_mul_of_nonneg_right htwo
      (by positivity : (0 : ℝ) ≤ (4 : ℝ)/5*h)
    have hnonneg : (0 : ℝ) ≤ cutCount (univ : Finset G.edgeSet) Y := Nat.cast_nonneg _
    nlinarith
  have hclose : ((X \ Y) ∪ (Y \ X)).card ≤ 1 := hWcard
  rcases eq_or_toggle_of_difference_card_le_one X Y hclose with hEq | ⟨v, hv⟩
  · exact Or.inl (hEq ▸ hY)
  · exact Or.inr ⟨Y, hY, v, hv⟩

/-- The classification follows from the actual embedded robust cores.
Only agreement of the larger shores is supplied by the group hypothesis. -/
theorem classified_robust_small_cut (U : I → Finset V) (Z Z0 X : Finset V)
    (c : V → Fin 4) (p : I → Fin 4) (h : ℕ)
    (H : ∀ i, SimpleGraph (U i))
    (hZ0 : Z0 ⊆ Z) (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hcolor : ∀ i v, v ∈ U i → c v = p i)
    (hregular : ∀ v, G.degree v = h)
    (hH : ∀ i, H i ≤ G.induce (U i : Set V))
    (α κ ν τ a b : ℝ)
    (hα : 0 < α) (hκ : 0 < κ) (hν : 0 < ν) (hτ : 0 ≤ τ)
    (hτα : τ ≤ α/10)
    (hhlo : α*Fintype.card V ≤ h) (hhhi : (h : ℝ) ≤ 2*Fintype.card V)
    (ha : a ≤ α*Fintype.card V/10) (hbsmall : b ≤ α*Fintype.card V/10)
    (hlarge : 3 < ν^2*κ^2*(Fintype.card V : ℝ))
    (hsize : ∀ i, κ*Fintype.card V ≤ ((U i).card : ℝ))
    (hrobust : ∀ i, IsRobustExpander (H i) ν τ)
    (hdegree : ∀ i v, (h : ℝ)-a ≤ ((H i).degree v : ℝ))
    (hagreement : ∀ i j, p i = p j → (coreMajority U X i ↔ coreMajority U X j))
    (hboundary : ∀ Y ∈ wholeUnions (clusterSets c Z0) Z0, ∀ v ∉ Z0,
      (incidentCount (cutEdges (univ : Finset G.edgeSet) Y) v : ℝ) ≤ (h : ℝ)/20)
    (hZbound : (2 : ℝ)*Z.card ≤ b) (hb : b < (h : ℝ)/10)
    (hcut : (cutCount (univ : Finset G.edgeSet) X : ℝ) ≤ h+b) :
    X ∈ wholeUnions (clusterSets c Z0) Z0 ∨
      ∃ Y ∈ wholeUnions (clusterSets c Z0) Z0, ∃ v, X = toggle Y v := by
  let C : ∀ i, SmallCuts.Core (Multigraph.ofSimpleGraph G) (U i) :=
    fun i => embeddedCore G (U i) (H i) (hH i)
  have hcut' : ((Multigraph.ofSimpleGraph G).cutSize X : ℝ) ≤ (h : ℝ)+b := by
    simpa only [cutCount_univ_eq_cutSize] using hcut
  have hminority := SmallCuts.minority_sum_le_one (Multigraph.ofSimpleGraph G) U C hdisj
    α κ ν τ a b h hα hκ hν hτ hτα hhlo hhhi ha hbsmall hlarge
    hsize hrobust hdegree X hcut'
  exact classified_small_cut G U Z Z0 X c p h b hZ0 hUZ hcover hcolor hregular
    hminority hagreement hboundary hZbound hb hcut

end Overfull.SafePrescription
