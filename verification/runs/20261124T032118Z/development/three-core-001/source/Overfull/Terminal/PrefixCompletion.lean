import Overfull.Terminal.Palette
import Overfull.Terminal.SimpleBridge
import Overfull.CircuitPatterns.SelectedCompletion
import Overfull.ForeignEdges.ColorClasses
import Overfull.ForeignEdges.PackingSchedule

/-! Completing a terminal joining palette in every original simple core. -/

noncomputable section

namespace Overfull.Terminal

open Finset Classical SimpleGraph Compression MatchingProbability ForeignPhase
open ForeignPackingSchedule ForeignRuleCompletion ForceMatching CircuitPatterns FourOdd

universe u v
variable {V : Type u} {I : Type v} [Fintype V] [Fintype I] [DecidableEq I]

def PrefixPalette.simpleBoundary (G : SimpleGraph V) {label : V → I} {r L : ℕ}
    {p : I → ℕ} (B : PrefixPalette (Multigraph.ofSimpleGraph G) label r L p) :
    ℕ → G.Subgraph :=
  extendBoundary G r (fun j => selectedMatching G (B.boundary j))

omit [Fintype I] in
@[simp] theorem PrefixPalette.simpleBoundary_lt (G : SimpleGraph V)
    {label : V → I} {r L : ℕ} {p : I → ℕ}
    (B : PrefixPalette (Multigraph.ofSimpleGraph G) label r L p)
    (j : ℕ) (hj : j < r) :
    B.simpleBoundary G j = selectedMatching G (B.boundary ⟨j,hj⟩) := by
  simp only [PrefixPalette.simpleBoundary, extendBoundary_lt G r _ j hj]

theorem selectedMatching_verts_toFinset (G : SimpleGraph V) (M : Finset G.edgeSet) :
    (selectedMatching G M).verts.toFinset = (Multigraph.ofSimpleGraph G).edgeSupport M := by
  ext v
  simp only [Set.mem_toFinset, selectedMatching_mem_verts, Multigraph.mem_edgeSupport]
  rfl

theorem selectedMatching_uncovered_card (G : SimpleGraph V) (M : Finset G.edgeSet)
    (U : Finset V) :
    ((U : Set V) \ (selectedMatching G M).verts).ncard =
      (U \ (Multigraph.ofSimpleGraph G).edgeSupport M).card := by
  have heq : (U : Set V) \ (selectedMatching G M).verts =
      (↑(U \ (Multigraph.ofSimpleGraph G).edgeSupport M) : Set V) := by
    rw [← selectedMatching_verts_toFinset]
    ext v
    simp
  rw [heq, Set.ncard_coe_finset]

omit [Fintype I] in
theorem joining_not_internal (G : SimpleGraph V) (label : V → I)
    (U : I → Finset V) (hparts : ∀ i, labelShore label {i} = U i)
    {u v : V} (huv : G.Adj u v) {i : I} (hu : u ∈ U i) (hv : v ∈ U i) :
    (⟨s(u,v),huv⟩ : G.edgeSet) ∉ joiningCopies (Multigraph.ofSimpleGraph G) label := by
  let e : G.edgeSet := ⟨s(u,v),huv⟩
  have hlu : label u = i := by
    rw [← hparts i] at hu
    simpa only [mem_labelShore, mem_singleton] using hu
  have hlv : label v = i := by
    rw [← hparts i] at hv
    simpa only [mem_labelShore, mem_singleton] using hv
  have hlabel : ∀ w, w ∈ (Multigraph.ofSimpleGraph G).edge e → label w = i := by
    intro w hw
    change w ∈ s(u,v) at hw
    rcases Sym2.mem_iff.mp hw with rfl | rfl
    · exact hlu
    · exact hlv
  intro he
  apply (mem_joiningCopies (Multigraph.ofSimpleGraph G) label e).mp he
  exact (hlabel _ ((Multigraph.ofSimpleGraph G).incident_iff e _ |>.mpr (Or.inl rfl))).trans
    (hlabel _ ((Multigraph.ofSimpleGraph G).incident_iff e _ |>.mpr (Or.inr rfl))).symm

set_option maxHeartbeats 800000 in
/-- The proved adaptive rules complete the actual small joining classes.
All graph-specific rule admissibility is derived by the existing arbitrary-core
boundary completion theorem. -/
theorem exists_prefix_completion (α γ ν τ : ℝ) (P : EpochParameters.{u} α γ τ ν)
    (G : SimpleGraph V) (U : I → Finset V) (H : ∀ i, SimpleGraph (U i))
    (label : V → I) (hparts : ∀ i, labelShore label {i} = U i)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hcover : ∀ v, ∃ i, v ∈ U i)
    (hH : ∀ i, H i ≤ G.induce (U i : Set V))
    (h r L : ℕ) (a : ℝ) (p : I → ℕ)
    (B : PrefixPalette (Multigraph.ofSimpleGraph G) label r L p)
    (hregular : ∀ v, G.degree v = h)
    (hrobust : ∀ i, IsRobustExpander (H i) ν τ)
    (hdegree : ∀ i v, (h : ℝ)-a ≤ (H i).degree v)
    (hm : ∀ i, P.order ≤ (U i).card)
    (hdensity : ∀ i, α*(U i).card ≤ (h : ℝ))
    (ha : ∀ i, a ≤ P.error*(U i).card)
    (hlimit : ∀ i, r ≤ ⌊(h : ℝ)-γ*(U i).card⌋₊)
    (hsize : ∀ i, (6*L : ℕ) ≤ P.error*(U i).card)
    (hparity : ∀ i, (U i).card % 2 = p i) :
    Nonempty (BoundaryCompletion G U H (B.simpleBoundary G) r h a P.output (τ/2)) := by
  have hdegrees (i : I) (v : U i) :
      |((H i).degree v : ℝ)-(h : ℝ)| ≤ P.error*(U i).card := by
    have hu := SimpleGraph.degree_le_of_le
      (Replacement.lift_le (U i) (H i) G (hH i)) (v := v.val)
    rw [Replacement.lift_degree] at hu
    have hu' : ((H i).degree v : ℝ) ≤ h := by exact_mod_cast hu.trans_eq (hregular v.val)
    rw [abs_of_nonpos (sub_nonpos.mpr hu')]
    linarith only [hdegree i v, ha i]
  obtain ⟨rule, hcertificate⟩ := exists_certified_core_rules U H
    α γ ν τ P.error P.output P.order P.rule (h : ℝ) hm hrobust hdensity hdegrees
  apply exists_boundary_completion G U ∅ H hH (B.simpleBoundary G) r h a
    P.error P.output (τ/2) rule (fun i => ⌊(h : ℝ)-γ*(U i).card⌋₊)
    hcertificate
    hlimit hdisj (fun v => Or.inr (hcover v))
  · intro j hj
    rw [B.simpleBoundary_lt G j hj]
    exact ForeignColoring.selectedMatching_isMatching_of_edge_copies G _ (B.matching ⟨j,hj⟩)
  · simp
  · intro j hj k hk hjk
    rw [B.simpleBoundary_lt G j hj, B.simpleBoundary_lt G k hk]
    exact ForeignColoring.selectedMatching_spanning_disjoint G _ _
      (B.disjoint (fun he => hjk (congrArg Fin.val he)))
  · intro j hj i u v hu hv hF
    rw [B.simpleBoundary_lt G j hj] at hF
    obtain ⟨huv, he⟩ := hF
    exact joining_not_internal G label U hparts huv hu hv (B.boundary_subset ⟨j,hj⟩ he)
  · exact hregular
  · exact hdegree
  · exact ha
  · intro j hj i
    rw [B.simpleBoundary_lt G j hj, selectedMatching_uncovered_card]
    have hh := B.uncovered_even (fun i => by rw [hparts]; exact hparity i) ⟨j,hj⟩ i
    simpa only [hparts] using hh
  · intro j hj i
    rw [B.simpleBoundary_lt G j hj, coveredCore_card, selectedMatching_verts_toFinset]
    exact (Nat.cast_le.mpr ((card_le_card inter_subset_left).trans
      (B.support_card_le ⟨j,hj⟩))).trans (hsize i)

omit [Fintype I] in
/-- A completed class removes exactly its prescribed original joining copies.
The adaptive completion can add only edges internal to a core. -/
theorem completed_joining_copies (G : SimpleGraph V) (U : I → Finset V)
    (H : ∀ i, SimpleGraph (U i)) (label : V → I)
    (hparts : ∀ i, labelShore label {i} = U i)
    {h r L : ℕ} {a θ σ : ℝ} {p : I → ℕ}
    (B : PrefixPalette (Multigraph.ofSimpleGraph G) label r L p)
    (C : BoundaryCompletion G U H (B.simpleBoundary G) r h a θ σ)
    (j : Fin r) :
    matchingEdges (C.full j.val) ∩ joiningCopies (Multigraph.ofSimpleGraph G) label =
      B.boundary j := by
  ext e
  constructor
  · intro he
    obtain ⟨heN, heJ⟩ := mem_inter.mp he
    have heN' := (mem_filter.mp heN).2
    obtain ⟨⟨u,v⟩, heG⟩ := e
    rcases C.added_internal j.val j.isLt u v heN' with heF | ⟨i, hu, hv⟩
    · rw [B.simpleBoundary_lt G j.val j.isLt] at heF
      exact heF.choose_spec
    · exact (joining_not_internal G label U hparts heG hu hv heJ).elim
  · intro he
    refine mem_inter.mpr ⟨?_, B.boundary_subset j he⟩
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    apply Subgraph.edgeSet_mono (C.contains j.val j.isLt)
    rw [B.simpleBoundary_lt G j.val j.isLt]
    exact (selectedMatching_mem_edge G _ e).mpr he

omit [Fintype I] in
/-- The complement of the completed classes within the original joining set
is exactly the union of the unselected primary pieces. -/
theorem remaining_joining_copies (G : SimpleGraph V) (U : I → Finset V)
    (H : ∀ i, SimpleGraph (U i)) (label : V → I)
    (hparts : ∀ i, labelShore label {i} = U i)
    {h r L : ℕ} {a θ σ : ℝ} {p : I → ℕ}
    (B : PrefixPalette (Multigraph.ofSimpleGraph G) label r L p)
    (C : BoundaryCompletion G U H (B.simpleBoundary G) r h a θ σ) :
    joiningCopies (Multigraph.ofSimpleGraph G) label \
      NativeReserve.removedCopies (matchingFamilyCopies G C.full r) univ =
        B.remaining.biUnion id := by
  have hremaining : B.remaining.biUnion id = joiningCopies (Multigraph.ofSimpleGraph G) label \
      univ.biUnion B.boundary := by
    convert B.remaining_eq_joining_sdiff using 1
    all_goals
      ext e
      simp only [mem_biUnion, mem_sdiff, mem_univ, true_and]
  rw [hremaining]
  ext e
  simp only [mem_sdiff]
  constructor
  · rintro ⟨he, hn⟩
    refine ⟨he, ?_⟩
    intro hb
    obtain ⟨j, _, hej⟩ := mem_biUnion.mp hb
    have heN := (mem_inter.mp (show e ∈ matchingEdges (C.full j.val) ∩
      joiningCopies (Multigraph.ofSimpleGraph G) label by
      rw [completed_joining_copies G U H label hparts B C j]
      exact hej)).1
    exact hn ((mem_removedFamilyCopies G C.full r e).mpr
      ⟨j.val, j.isLt, (mem_filter.mp heN).2⟩)
  · rintro ⟨he, hn⟩
    refine ⟨he, ?_⟩
    intro hb
    obtain ⟨j, hj, hej⟩ := (mem_removedFamilyCopies G C.full r e).mp hb
    apply hn
    refine mem_biUnion.mpr ⟨⟨j,hj⟩, mem_univ _, ?_⟩
    rw [← completed_joining_copies G U H label hparts B C ⟨j,hj⟩]
    exact mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hej⟩, he⟩

end Overfull.Terminal
