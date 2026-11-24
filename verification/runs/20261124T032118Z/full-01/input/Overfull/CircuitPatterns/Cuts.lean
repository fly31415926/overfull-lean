import Overfull.ForeignEdges.Phase
import Overfull.ForceMatching.Residual

/-!
# Actual cuts during a pattern deletion sequence

The identities use the edges of the actual residual graph. Numerical
remaining pattern weights need not be a fractional decomposition of that
residual.
-/

namespace Overfull.CircuitPatterns

open Finset Classical SimpleGraph MatchingProbability FractionalMatching
open ForeignPhase ForceMatching
open scoped BigOperators

variable {V : Type*} [Fintype V]

theorem matchingEdges_image_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : G.Subgraph) :
    (matchingEdges M).image Subtype.val = M.spanningCoe.edgeFinset := by
  classical
  ext e
  constructor
  · rintro he
    obtain ⟨f, hf, rfl⟩ := mem_image.mp he
    exact mem_edgeFinset.mpr (mem_filter.mp hf).2
  · intro he
    have hm : e ∈ M.edgeSet := mem_edgeFinset.mp he
    exact mem_image.mpr ⟨⟨e, M.edgeSet_subset hm⟩,
      mem_filter.mpr ⟨mem_univ _, hm⟩, rfl⟩

theorem matching_cut_eq_graph (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : G.Subgraph) (X : Finset V) :
    cutCount (matchingEdges M) X = graphCutCount M.spanningCoe X := by
  unfold cutCount
  rw [← card_image_of_injective _ Subtype.val_injective, cutEdges_image,
    matchingEdges_image_eq]
  rfl

theorem graphCutEdges_mono (G R : SimpleGraph V) (hRG : R ≤ G) (X : Finset V) :
    graphCutEdges R X ⊆ graphCutEdges G X := by
  classical
  intro e he
  exact mem_filter.mpr ⟨mem_edgeFinset.mpr
    (SimpleGraph.edgeSet_mono hRG (mem_edgeFinset.mp (mem_filter.mp he).1)),
    (mem_filter.mp he).2⟩

theorem graphCutEdges_sdiff (G H : SimpleGraph V) (X : Finset V) :
    graphCutEdges (G \ H) X = graphCutEdges G X \ graphCutEdges H X := by
  classical
  ext e
  simp only [graphCutEdges, mem_filter, mem_edgeFinset, edgeSet_sdiff,
    Set.mem_diff, mem_sdiff]
  tauto

/-- A deletion partitions the current cut into the surviving and deleted
actual cut edges. -/
theorem graphCutCount_partition (G H : SimpleGraph V) (hHG : H ≤ G) (X : Finset V) :
    graphCutCount (G \ H) X + graphCutCount H X = graphCutCount G X := by
  unfold graphCutCount
  rw [graphCutEdges_sdiff]
  exact card_sdiff_add_card_eq_card (graphCutEdges_mono G H hHG X)

/-- Exact cut subtraction over every prefix of an original-host sequence. -/
theorem afterDeletions_cut_accounting (G : SimpleGraph V) [DecidableRel G.Adj]
    (N : ℕ → G.Subgraph) (s : ℕ)
    (hpresent : ∀ j < s, (N j).spanningCoe ≤ afterDeletions G N j)
    (X : Finset V) :
    graphCutCount (afterDeletions G N s) X +
      (∑ j ∈ range s, cutCount (matchingEdges (N j)) X) = graphCutCount G X := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hh := ih (fun j hj => hpresent j (Nat.lt_succ_of_lt hj))
    have hstep := graphCutCount_partition (afterDeletions G N s)
      (N s).spanningCoe (hpresent s (Nat.lt_succ_self s)) X
    rw [← afterDeletions_succ, ← matching_cut_eq_graph] at hstep
    rw [sum_range_succ]
    omega

/-- If no processed pattern crosses a protected cut, all its original
cut edges survive, including their original incidences. -/
theorem afterDeletions_cut_unchanged (G : SimpleGraph V) [DecidableRel G.Adj]
    (N : ℕ → G.Subgraph) (s : ℕ)
    (hpresent : ∀ j < s, (N j).spanningCoe ≤ afterDeletions G N j)
    (X : Finset V) (hzero : ∀ j < s, cutCount (matchingEdges (N j)) X = 0) :
    graphCutEdges (afterDeletions G N s) X = graphCutEdges G X := by
  have hh := afterDeletions_cut_accounting G N s hpresent X
  have hz : (∑ j ∈ range s, cutCount (matchingEdges (N j)) X) = 0 :=
    sum_eq_zero (fun j hj => hzero j (mem_range.mp hj))
  rw [hz, Nat.add_zero] at hh
  exact eq_of_subset_of_card_le
    (graphCutEdges_mono G (afterDeletions G N s) sdiff_le X) hh.symm.le

/-- Actual incidence of a cut at one vertex, independent of the host. -/
noncomputable def graphCutIncidence (G : SimpleGraph V) (X : Finset V) (v : V) : ℕ :=
  ((graphCutEdges G X).filter (fun e => v ∈ e)).card

theorem univ_edges_image (G : SimpleGraph V) [DecidableRel G.Adj] :
    (univ : Finset G.edgeSet).image Subtype.val = G.edgeFinset := by
  classical
  ext e
  simp

theorem univ_cut_eq_graph (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) :
    cutCount (univ : Finset G.edgeSet) X = graphCutCount G X := by
  unfold cutCount
  rw [← card_image_of_injective _ Subtype.val_injective, cutEdges_image, univ_edges_image]
  unfold graphCutCount graphCutEdges
  congr 2
  ext e
  simp only [mem_edgeFinset]

theorem univ_cut_incidence_eq_graph (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (v : V) :
    incidentCount (cutEdges (univ : Finset G.edgeSet) X) v =
      graphCutIncidence G X v := by
  classical
  have himage : ((cutEdges (univ : Finset G.edgeSet) X).filter
      (fun e => firstEnd e = v ∨ secondEnd e = v)).image Subtype.val =
        (graphCutEdges G X).filter (fun e => v ∈ e) := by
    ext e
    constructor
    · intro he
      obtain ⟨f, hf, rfl⟩ := mem_image.mp he
      obtain ⟨hc, hi⟩ := mem_filter.mp hf
      obtain ⟨_, hx⟩ := mem_filter.mp hc
      exact mem_filter.mpr ⟨mem_filter.mpr
        ⟨by simpa only [mem_edgeFinset] using f.property,
          (crosses_iff_endpoints X f).mpr hx⟩,
        (incident_iff f v).mpr hi⟩
    · intro he
      obtain ⟨hc, hi⟩ := mem_filter.mp he
      obtain ⟨hg, hx⟩ := mem_filter.mp hc
      let f : G.edgeSet := ⟨e, by simpa only [mem_edgeFinset] using hg⟩
      exact mem_image.mpr ⟨f, mem_filter.mpr ⟨mem_filter.mpr
        ⟨mem_univ _, (crosses_iff_endpoints X f).mp hx⟩,
        (incident_iff f v).mp hi⟩, rfl⟩
  unfold incidentCount graphCutIncidence
  rw [← card_image_of_injective _ Subtype.val_injective, himage]

/-- The graph form of the exact one-vertex toggle identity. -/
theorem graphCut_toggle (G : SimpleGraph V) (X : Finset V) (v : V) :
    graphCutCount G (toggle X v) + 2 * graphCutIncidence G X v =
      graphCutCount G X + G.degree v := by
  classical
  have h := cut_toggle (univ : Finset G.edgeSet) X v
  simpa only [univ_cut_eq_graph, univ_cut_incidence_eq_graph, incidentCount_univ] using h

theorem regular_odd_graphCut_lower (G : SimpleGraph V) (k : ℕ)
    (hregular : ∀ v, G.degree v = k) (hno : ∀ X : Finset V, ¬ IsOverfull G k X)
    (X : Finset V) (hodd : X.card % 2 = 1) : k ≤ graphCutCount G X := by
  classical
  obtain ⟨s, hs, _⟩ := regular_odd_cut hregular hno X hodd
  rw [univ_cut_eq_graph] at hs
  omega

/-- A cut of size at least twice its vertex incidences has safe toggles. -/
theorem toggle_safe_of_incidence (G : SimpleGraph V) (k : ℕ)
    (hregular : ∀ v, G.degree v = k) (X : Finset V) (v : V)
    (hinc : 2 * graphCutIncidence G X v ≤ graphCutCount G X) :
    k ≤ graphCutCount G (toggle X v) := by
  have h := graphCut_toggle G X v
  rw [hregular] at h
  omega

/-- An even original cut with all its edges retained has safe toggles at
the current regular degree. -/
theorem toggle_safe_of_preserved_cut (G R : SimpleGraph V) (k h : ℕ)
    (hregularG : ∀ v, G.degree v = k) (hregularR : ∀ v, R.degree v = h)
    (hno : ∀ X : Finset V, ¬ IsOverfull G k X)
    (X : Finset V) (heven : X.card % 2 = 0)
    (hcut : graphCutEdges R X = graphCutEdges G X) (v : V) :
    h ≤ graphCutCount R (toggle X v) := by
  have hsafe := regular_odd_graphCut_lower G k hregularG hno
    (toggle X v) (toggle_odd heven v)
  have htoggle := graphCut_toggle G X v
  rw [hregularG] at htoggle
  apply toggle_safe_of_incidence R h hregularR X v
  unfold graphCutIncidence graphCutCount
  rw [hcut]
  change 2 * graphCutIncidence G X v ≤ graphCutCount G X
  omega

variable {I : Type*} [Fintype I]

/-- The proved small-cut classification closes the no-overfull conclusion
from actual cut inequalities for the finite whole-union family. -/
theorem no_overfull_of_whole_cut_bounds (G : SimpleGraph V)
    (U : I → Finset V) (Z : Finset V)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hZ : ∀ i, Disjoint (U i) Z) (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (k : ℕ) (hregular : ∀ v, G.degree v = k)
    (H : ∀ i, SimpleGraph (U i)) (hH : ∀ i, H i ≤ G.induce (U i : Set V))
    (α c ν τ a : ℝ) (hα : 0 < α) (hc : 0 < c) (hν : 0 < ν) (hτ : 0 ≤ τ)
    (hτα : τ ≤ α / 10)
    (hklo : α * Fintype.card V ≤ (k : ℝ)) (hkhi : (k : ℝ) ≤ 2 * Fintype.card V)
    (ha : a ≤ α * Fintype.card V / 10)
    (hlarge : 3 < ν ^ 2 * c ^ 2 * (Fintype.card V : ℝ))
    (hsize : ∀ i, c * Fintype.card V ≤ ((U i).card : ℝ))
    (hrobust : ∀ i, IsRobustExpander (H i) ν τ)
    (hdegree : ∀ i v, (k : ℝ) - a ≤ ((H i).degree v : ℝ))
    (hwhole : ∀ X ∈ wholeUnions U Z, X.card % 2 = 1 → k ≤ graphCutCount G X)
    (htoggle : ∀ X ∈ wholeUnions U Z, X.card % 2 = 0 →
      ∀ v, k ≤ graphCutCount G (toggle X v)) :
    ∀ X : Finset V, ¬ IsOverfull G k X := by
  classical
  let C : ∀ i, SmallCuts.Core (Multigraph.ofSimpleGraph G) (U i) :=
    fun i => embeddedCore G (U i) (H i) (hH i)
  intro X hOver
  have hodd : X.card % 2 = 1 := by
    by_contra h
    exact not_overfull_of_even_card G X k (fun v => (hregular v).le) (by omega) hOver
  have hcut := regular_overfull_cut G k hregular X hodd hOver
  have hcutR : ((Multigraph.ofSimpleGraph G).cutSize X : ℝ) ≤ (k : ℝ) + 0 := by
    simp only [add_zero]
    exact_mod_cast hcut.le
  have hb : (0 : ℝ) ≤ α * Fintype.card V / 10 := by positivity
  have hminority := SmallCuts.minority_sum_le_one (Multigraph.ofSimpleGraph G) U C hdisj
    α c ν τ a 0 (k : ℝ) hα hc hν hτ hτα hklo hkhi ha hb hlarge
    hsize hrobust hdegree X hcutR
  have hsafe : k ≤ graphCutCount G X := by
    rcases classified_of_minority U Z X hZ hcover hminority with hX | ⟨Y, hY, v, rfl⟩
    · exact hwhole X hX hodd
    · exact htoggle Y hY (even_of_toggle_odd Y v hodd) v
  rw [graphCutCount_eq_cutSize] at hsafe
  omega

end Overfull.CircuitPatterns
