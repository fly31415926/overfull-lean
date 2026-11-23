import Overfull.NativeReserve.Residual
import Overfull.OneCore.Complement
import Overfull.CircuitPatterns.Safety

/-!
# Whole-cut safety for the actual multigraph residual

All incidences count original edge copies. The retained simple cores are
embedded in that same residual. Whole cuts and their one-vertex toggles
then close the proved small-cut classification.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical ForceMatching MatchingProbability
open scoped BigOperators

variable {V E I J : Type*} [Fintype E]

/-- The number of actual crossing copies incident with a vertex. -/
def cutIncidence (G : Multigraph V E) (X : Finset V) (v : V) : ℕ :=
  (G.cutEdges X ∩ G.incidenceEdges v).card

theorem cut_toggle (G : Multigraph V E) (X : Finset V) (v : V) :
    G.cutSize (toggle X v) + 2 * cutIncidence G X v =
      G.cutSize X + G.degree v := by
  have h := MultigraphMatchingProbability.cut_toggle (G := G) univ X v
  rw [MultigraphMatchingProbability.incidentCount_univ] at h
  have hi : MultigraphMatchingProbability.incidentCount (G := G) (G.cutEdges X) v =
      cutIncidence G X v := by
    unfold MultigraphMatchingProbability.incidentCount cutIncidence
    congr 1
    ext e
    simp [G.incident_iff]
  change G.cutSize (toggle X v) +
    2 * MultigraphMatchingProbability.incidentCount (G := G) (G.cutEdges X) v =
      G.cutSize X + G.degree v at h
  rwa [hi] at h

theorem regular_odd_cut_lower (G : Multigraph V E) (k : ℕ)
    (hregular : ∀ v, G.degree v = k)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull k X)
    (X : Finset V) (hodd : X.card % 2 = 1) : k ≤ G.cutSize X := by
  have hsum := G.degree_sum_on X
  simp only [hregular, sum_const, smul_eq_mul] at hsum
  have hcard : X.card = 2 * (X.card / 2) + 1 := by omega
  have hi : (G.internalEdges X).card ≤ k * (X.card / 2) := Nat.not_lt.mp (hno X)
  rw [hcard] at hsum
  nlinarith

theorem toggle_safe_of_incidence (G : Multigraph V E) (k : ℕ)
    (hregular : ∀ v, G.degree v = k) (X : Finset V) (v : V)
    (hinc : 2 * cutIncidence G X v ≤ G.cutSize X) :
    k ≤ G.cutSize (toggle X v) := by
  have h := cut_toggle G X v
  rw [hregular] at h
  omega

/-- A shore containing all or none of a core gives its vertices the same
membership, independently of the chosen internal edge. -/
theorem whole_core_membership_iff (U X : Finset V)
    (hwhole : U ⊆ X ∨ Disjoint U X) {u v : V} (hu : u ∈ U) (hv : v ∈ U) :
    u ∈ X ↔ v ∈ X := by
  rcases hwhole with hwhole | hwhole
  · exact iff_of_true (hwhole hu) (hwhole hv)
  · exact iff_of_false (fun hx => disjoint_left.mp hwhole hu hx)
      (fun hx => disjoint_left.mp hwhole hv hx)

theorem whole_cut_core_incidence (G : Multigraph V E) (U X : Finset V)
    (C : SmallCuts.Core G U) (hwhole : U ⊆ X ∨ Disjoint U X)
    (k : ℕ) (a : ℝ) (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ)) (v : U) :
    (cutIncidence G X v.val : ℝ) ≤ a := by
  have hbound : cutIncidence G X v.val ≤
      (G.restrictEdges (OneCore.coreEdges C)ᶜ).degree v.val := by
    rw [Multigraph.restrictEdges_degree]
    apply card_le_card
    intro e he
    obtain ⟨heX, hev⟩ := mem_inter.mp he
    refine mem_inter.mpr ⟨mem_compl.mpr ?_, hev⟩
    intro heC
    have hends := (G.mem_internalEdges U e).mp (OneCore.coreEdges_subset_internal C heC)
    exact (G.mem_cutEdges X e).mp heX
      (propext (whole_core_membership_iff U X hwhole hends.1 hends.2))
  have hboundR : (cutIncidence G X v.val : ℝ) ≤
      ((G.restrictEdges (OneCore.coreEdges C)ᶜ).degree v.val : ℝ) := by exact_mod_cast hbound
  exact hboundR.trans (OneCore.complement_degree_le_error C k a hregular hdegree v)

theorem residual_cutIncidence (G : Multigraph V E) (N : J → Finset E) (T : Finset J)
    (X : Finset V) (v : V) :
    cutIncidence (residualGraph G N T) X v =
      ((G.cutEdges X \ removedCopies N T) ∩ G.incidenceEdges v).card := by
  have himage :
      (((residualGraph G N T).cutEdges X ∩
        (residualGraph G N T).incidenceEdges v).image Subtype.val) =
          (G.cutEdges X \ removedCopies N T) ∩ G.incidenceEdges v := by
    ext e
    simp only [mem_image, mem_inter, Multigraph.mem_cutEdges,
      Multigraph.mem_incidenceEdges, mem_sdiff]
    change (∃ a : {e : E // e ∉ removedCopies N T},
      (((G.firstEnd a.val ∈ X) ≠ (G.secondEnd a.val ∈ X)) ∧
        v ∈ G.edge a.val) ∧ a.val = e) ↔
      (((G.firstEnd e ∈ X) ≠ (G.secondEnd e ∈ X)) ∧
        e ∉ removedCopies N T) ∧ v ∈ G.edge e
    constructor
    · rintro ⟨a, ⟨ha, hv⟩, rfl⟩
      exact ⟨⟨ha, a.property⟩, hv⟩
    · rintro ⟨⟨hcross, he⟩, hv⟩
      exact ⟨⟨e, he⟩, ⟨hcross, hv⟩, rfl⟩
  rw [cutIncidence, ← card_image_of_injective _ Subtype.val_injective]
  exact congrArg card himage

theorem toggle_safe_of_preserved_cut (G : Multigraph V E)
    (N : J → Finset E) (T : Finset J) (k h : ℕ)
    (hregularG : ∀ v, G.degree v = k)
    (hregularR : ∀ v, (residualGraph G N T).degree v = h)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull k X)
    (X : Finset V) (heven : X.card % 2 = 0)
    (hcut : G.cutEdges X \ removedCopies N T = G.cutEdges X) (v : V) :
    h ≤ (residualGraph G N T).cutSize (toggle X v) := by
  have hsafe := regular_odd_cut_lower G k hregularG hno
    (toggle X v) (toggle_odd heven v)
  have htoggle := cut_toggle G X v
  rw [hregularG] at htoggle
  apply toggle_safe_of_incidence (residualGraph G N T) h hregularR X v
  rw [residual_cutIncidence, residual_cutSize, hcut]
  change 2 * cutIncidence G X v ≤ G.cutSize X
  omega

variable [Fintype V] [Fintype I]

theorem no_overfull_of_whole_cut_bounds (G : Multigraph V E)
    (U : I → Finset V) (Z : Finset V)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hZ : ∀ i, Disjoint (U i) Z) (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (k : ℕ) (hregular : ∀ v, G.degree v = k)
    (C : ∀ i, SmallCuts.Core G (U i))
    (α c ν τ a : ℝ)
    (hα : 0 < α) (hc : 0 < c) (hν : 0 < ν) (hτ : 0 ≤ τ)
    (hτα : τ ≤ α / 10)
    (hklo : α * Fintype.card V ≤ (k : ℝ))
    (hkhi : (k : ℝ) ≤ 2 * Fintype.card V)
    (ha : a ≤ α * Fintype.card V / 10)
    (hlarge : 3 < ν ^ 2 * c ^ 2 * (Fintype.card V : ℝ))
    (hsize : ∀ i, c * Fintype.card V ≤ ((U i).card : ℝ))
    (hrobust : ∀ i, IsRobustExpander (C i).graph ν τ)
    (hdegree : ∀ i v, (k : ℝ) - a ≤ ((C i).graph.degree v : ℝ))
    (hwhole : ∀ X ∈ wholeUnions U Z, X.card % 2 = 1 → k ≤ G.cutSize X)
    (htoggle : ∀ X ∈ wholeUnions U Z, X.card % 2 = 0 →
      ∀ v, k ≤ G.cutSize (toggle X v)) :
    ∀ X, ¬ G.IsOverfull k X := by
  apply OneCore.no_overfull_of_odd_cuts G k hregular
  intro X hodd
  by_contra h
  have hcut : G.cutSize X < k := Nat.lt_of_not_ge h
  have hcutR : (G.cutSize X : ℝ) ≤ (k : ℝ) + 0 := by exact_mod_cast hcut.le
  have hb : (0 : ℝ) ≤ α * Fintype.card V / 10 := by positivity
  have hminority := SmallCuts.minority_sum_le_one G U C hdisj
    α c ν τ a 0 k hα hc hν hτ hτα hklo hkhi ha hb hlarge
    hsize hrobust hdegree X hcutR
  have hsafe : k ≤ G.cutSize X := by
    rcases classified_of_minority U Z X hZ hcover hminority with hX | ⟨Y, hY, v, rfl⟩
    · exact hwhole X hX hodd
    · exact htoggle Y hY (even_of_toggle_odd Y v hodd) v
  omega

omit [Fintype V] in
theorem residual_whole_toggles_safe (G : Multigraph V E)
    (N : J → Finset E) (T : Finset J) (U : I → Finset V) (Z : Finset V)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hZ : ∀ i, Disjoint (U i) Z) (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (k h : ℕ) (hregularG : ∀ v, G.degree v = k)
    (hregularR : ∀ v, (residualGraph G N T).degree v = h)
    (hnoG : ∀ X, ¬ G.IsOverfull k X)
    (C : ∀ i, SmallCuts.Core (residualGraph G N T) (U i))
    (a : ℝ) (hdegree : ∀ i v, (h : ℝ) - a ≤ ((C i).graph.degree v : ℝ))
    (hwhole : ∀ X ∈ wholeUnions U Z, X.card % 2 = 1 → h ≤ (residualGraph G N T).cutSize X)
    (hcases : ∀ X ∈ wholeUnions U Z, X.card % 2 = 0 →
      2 * a ≤ ((residualGraph G N T).cutSize X : ℝ) ∨
        G.cutEdges X \ removedCopies N T = G.cutEdges X) :
    ∀ X ∈ wholeUnions U Z, X.card % 2 = 0 →
      ∀ v, h ≤ (residualGraph G N T).cutSize (toggle X v) := by
  intro X hX heven v
  by_cases hvZ : v ∈ Z
  · exact hwhole (toggle X v)
      (CircuitPatterns.wholeUnions_toggle_exceptional U Z X hZ hX v hvZ)
      (toggle_odd heven v)
  · obtain ⟨i, hvi⟩ := (hcover v).resolve_left hvZ
    rcases hcases X hX heven with hlargeCut | hpreserved
    · have hinc := whole_cut_core_incidence (residualGraph G N T) (U i) X (C i)
        (wholeUnions_whole U Z X hdisj hZ hX i) h a hregularR (hdegree i) ⟨v, hvi⟩
      apply toggle_safe_of_incidence (residualGraph G N T) h hregularR X v
      have hincR : 2 * (cutIncidence (residualGraph G N T) X v : ℝ) ≤
          (residualGraph G N T).cutSize X := by linarith only [hinc, hlargeCut]
      exact_mod_cast hincR
    · exact toggle_safe_of_preserved_cut G N T k h hregularG hregularR hnoG
        X heven hpreserved v

theorem residual_no_overfull (G : Multigraph V E)
    (N : J → Finset E) (T : Finset J)
    (hNdisj : (T : Set J).Pairwise (fun i j => Disjoint (N i) (N j)))
    (hperfect : ∀ j ∈ T, G.IsPerfectMatching (N j))
    (U : I → Finset V) (Z : Finset V)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hZ : ∀ i, Disjoint (U i) Z) (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (k : ℕ) (hregularG : ∀ v, G.degree v = k) (hnoG : ∀ X, ¬ G.IsOverfull k X)
    (C : ∀ i, SmallCuts.Core (residualGraph G N T) (U i))
    (α c ν τ a : ℝ)
    (hα : 0 < α) (hc : 0 < c) (hν : 0 < ν) (hτ : 0 ≤ τ) (hτα : τ ≤ α / 10)
    (hklo : α * Fintype.card V ≤ ((k - T.card : ℕ) : ℝ))
    (hkhi : ((k - T.card : ℕ) : ℝ) ≤ 2 * Fintype.card V)
    (ha : a ≤ α * Fintype.card V / 10)
    (hlarge : 3 < ν ^ 2 * c ^ 2 * (Fintype.card V : ℝ))
    (hsize : ∀ i, c * Fintype.card V ≤ ((U i).card : ℝ))
    (hrobust : ∀ i, IsRobustExpander (C i).graph ν τ)
    (hdegree : ∀ i v, ((k - T.card : ℕ) : ℝ) - a ≤ ((C i).graph.degree v : ℝ))
    (hwhole : ∀ X ∈ wholeUnions U Z, X.card % 2 = 1 →
      k - T.card ≤ (residualGraph G N T).cutSize X)
    (hcases : ∀ X ∈ wholeUnions U Z, X.card % 2 = 0 →
      2 * a ≤ ((residualGraph G N T).cutSize X : ℝ) ∨
        G.cutEdges X \ removedCopies N T = G.cutEdges X) :
    ∀ X, ¬ (residualGraph G N T).IsOverfull (k - T.card) X := by
  have hregular := residual_regular G hregularG N T hNdisj hperfect
  exact no_overfull_of_whole_cut_bounds (residualGraph G N T) U Z hdisj hZ hcover
    (k - T.card) hregular C α c ν τ a hα hc hν hτ hτα hklo hkhi ha hlarge
    hsize hrobust hdegree hwhole
    (residual_whole_toggles_safe G N T U Z hdisj hZ hcover k (k - T.card)
      hregularG hregular hnoG C a hdegree hwhole hcases)

end Overfull.NativeReserve
