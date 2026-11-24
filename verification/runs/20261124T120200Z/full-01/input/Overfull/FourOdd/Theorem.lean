import Overfull.FourOdd.MatchingPreprocessing
import Overfull.FourOdd.Star
import Overfull.FourOdd.RelabelGraph
import Overfull.FourOdd.Quantitative

/-!
# Lemma 4.15: decomposition of the joining edges of four odd parts

The complete proof starts with the actual regular, non-overfull graph and
its four odd label fibers. It constructs exactly `h` original matchings
projecting to perfect matchings or three-edge stars, and partitions every
remaining joining copy into an actual matching whose quotient is a
two-edge circuit. The fixed error constant `1/1000` makes the manuscript's
two sufficiently-small conditions explicit.

The argument uses König coloring, equitable balancing and finite Hall
pairing. It does not assume the general compatible-circuit theorem.
-/

noncomputable section

namespace Overfull.FourOdd

open Finset Classical Compression CircuitPatterns

variable {V E : Type*} [Fintype V] [Fintype E]

/-- Compose the two actual finite constructions for an arbitrary allowed
prescribed forest, with a permutation of the part names chosen internally. -/
theorem exists_joining_decomposition
    (G : Multigraph V E) (label : V → Fin 4)
    (hjoin : ∀ e, label (G.firstEnd e) ≠ label (G.secondEnd e))
    (h D r0 : ℕ) (hD : 0 < D)
    (hsmall : 1000 * D ≤ h) (hnearly : 999 * h ≤ 1000 * r0)
    (hdegree : ∀ v, G.degree v ≤ D)
    (hlower : ∀ i, h ≤ (G.labelQuotient label hjoin).degree i)
    (hparity : ∀ i, (G.labelQuotient label hjoin).degree i % 2 = h % 2)
    (F0 : Finset LabelPair) (hF0 : LabelForestShape F0)
    (hsupply : ∀ p ∈ F0, r0 ≤ (pairPool (G.labelQuotient label hjoin) p).card)
    (hcut_even : ∀ i j : Fin 4, i ≠ j →
      ((G.labelQuotient label hjoin).cutOn univ {i, j}).card % 2 = 0)
    (hcut_half : ∀ i j : Fin 4, i ≠ j → ∀ v,
      G.degreeOn ((G.labelQuotient label hjoin).cutOn univ {i, j}) v ≤
        ((G.labelQuotient label hjoin).cutOn univ {i, j}).card / 2) :
    Nonempty (Decomposition G (G.labelQuotient label hjoin).edgeLabelPair univ h) := by
  obtain ⟨σ, hcanonical⟩ := exists_canonical_relabeling F0 hF0
  let L := fun v => σ (label v)
  let hj := relabel_join G label hjoin σ
  let Q := G.labelQuotient L hj
  let F := F0.image (relabelPair σ)
  have hlower' (i : Fin 4) : h ≤ Q.degree i := by
    rw [relabel_quotient_degree G label hjoin σ]
    exact hlower _
  have hparity' (i : Fin 4) : Q.degree i % 2 = h % 2 := by
    rw [relabel_quotient_degree G label hjoin σ]
    exact hparity _
  have hsupply' : ∀ p ∈ F, r0 ≤ (pairPool Q p).card := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    rw [relabel_quotient_pairPool G label hjoin σ]
    have heq : relabelPair σ.symm (relabelPair σ q) = q :=
      (relabelPair σ).symm_apply_apply q
    rw [heq]
    exact hsupply q hq
  have hne : σ.symm (0 : Fin 4) ≠ σ.symm 1 :=
    fun heq => (by decide : (0 : Fin 4) ≠ 1) (σ.symm.injective heq)
  have heven : (Q.cutOn univ {0, 1}).card % 2 = 0 := by
    rw [relabel_quotient_cut_pair G label hjoin σ]
    exact hcut_even _ _ hne
  have hhalf (v : V) : G.degreeOn (Q.cutOn univ {0, 1}) v ≤
      (Q.cutOn univ {0, 1}).card / 2 := by
    rw [relabel_quotient_cut_pair G label hjoin σ]
    exact hcut_half _ _ hne v
  have hresult : Nonempty (Decomposition G Q.edgeLabelPair univ h) := by
    rcases hcanonical with hm | hs
    · have hleft : r0 ≤ (pairPool Q matchingLeftPair).card := by
        apply hsupply'
        change matchingLeftPair ∈ F0.image (relabelPair σ)
        rw [hm]
        simp [canonicalMatching, matchingLeftPair]
      have hright : r0 ≤ (pairPool Q matchingRightPair).card := by
        apply hsupply'
        change matchingRightPair ∈ F0.image (relabelPair σ)
        rw [hm]
        simp [canonicalMatching, matchingRightPair]
      exact exists_matching_decomposition G L hj hD hsmall hnearly hdegree
        hlower' hparity' hleft hright heven hhalf
    · have hstar : ∀ i : Fin 3, r0 ≤ (pairPool Q (starPair i)).card := by
        intro i
        apply hsupply'
        change starPair i ∈ F0.image (relabelPair σ)
        rw [hs]
        revert i
        decide
      exact exists_star_decomposition G L hj h D r0 (by omega) hD hsmall hnearly
        hdegree hlower' hparity' hstar
  obtain ⟨P⟩ := hresult
  exact ⟨P.unrelabel G label hjoin σ⟩

/-- Complete four-odd-parts decomposition with integer boundary bounds.
All quotient and even-cut inputs are derived from the actual graph. -/
theorem four_odd_decomposition_nat (G : Multigraph V E) (label : V → Fin 4)
    (h D r0 : ℕ) (hregular : ∀ v, G.degree v = h)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull h X)
    (hodd : ∀ i : Fin 4, (univ.filter (fun v => label v = i)).card % 2 = 1)
    (hdegree : ∀ v, G.degreeOn (joiningCopies G label) v ≤ D)
    (F0 : Finset LabelPair) (hF0 : LabelForestShape F0)
    (hsupply : ∀ p ∈ F0, r0 ≤ (pairPool (joiningQuotient G label) p).card)
    (hsmall : 1000 * D ≤ h) (hnearly : 999 * h ≤ 1000 * r0) :
    Nonempty (Decomposition (joiningGraph G label)
      (joiningQuotient G label).edgeLabelPair univ h) := by
  by_cases hh : h = 0
  · subst h
    letI : IsEmpty E := edge_type_empty_of_zero_regular G hregular
    have hc : (univ : Finset (joiningCopies G label)) = ∅ := by simp
    exact ⟨(Decomposition.empty (joiningGraph G label)
      (joiningQuotient G label).edgeLabelPair).cast hc.symm rfl⟩
  · have hh' : 0 < h := Nat.pos_of_ne_zero hh
    have hD : 0 < D := four_odd_joining_degree_bound_pos G label
      hh' hregular hno hodd hdegree
    apply exists_joining_decomposition (joiningGraph G label) label
      (joiningGraph_join G label) h D r0 hD hsmall hnearly
      (joiningGraph_degree_le G label hdegree)
      (joiningQuotient_degree_lower G label hregular hno hodd)
      (joiningQuotient_degree_parity G label hregular hodd) F0 hF0 hsupply
    · intro i j hij
      exact joiningCut_pair_parity G label hregular hodd hij
    · intro i j hij v
      exact joiningCut_pair_degree_le_half G label hregular hno hodd hij v

/-- The explicit real-bound version. The proof needs only the pair supply,
so the manuscript's extra forest-cut supply is a redundant hypothesis. -/
theorem four_odd_decomposition_real (G : Multigraph V E) (label : V → Fin 4)
    (h r0 : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (hregular : ∀ v, G.degree v = h)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull h X)
    (hodd : ∀ i : Fin 4, (univ.filter (fun v => label v = i)).card % 2 = 1)
    (hdegree : ∀ v, (G.degreeOn (joiningCopies G label) v : ℝ) ≤ a)
    (F0 : Finset LabelPair) (hF0 : LabelForestShape F0)
    (hsupply : ∀ p ∈ F0, r0 ≤ (pairPool (joiningQuotient G label) p).card)
    (hsmall : 1000 * a ≤ h) (hnearly : 999 * h ≤ 1000 * r0) :
    Nonempty (Decomposition (joiningGraph G label)
      (joiningQuotient G label).edgeLabelPair univ h) :=
  four_odd_decomposition_nat G label h ⌊a⌋₊ r0 hregular hno hodd
    (joining_degree_le_floor G label hdegree) F0 hF0 hsupply
    (floor_boundary_small ha hsmall) hnearly

/-- Full Lemma 4.15, with the absolute sufficient constant `1/1000` for
both ratios. The conclusion retains every actual joining edge copy. -/
theorem four_odd_parts_decomposition (G : Multigraph V E) (label : V → Fin 4)
    (h r0 : ℕ) (a : ℝ) (hh : 0 < h) (ha : 0 ≤ a)
    (hregular : ∀ v, G.degree v = h)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull h X)
    (hodd : ∀ i : Fin 4, (univ.filter (fun v => label v = i)).card % 2 = 1)
    (hdegree : ∀ v, (G.degreeOn (joiningCopies G label) v : ℝ) ≤ a)
    (F0 : Finset LabelPair) (hF0 : LabelForestShape F0)
    (_hforestSupply : ∀ A : Finset (Fin 4),
      r0 * forestCutCount F0 A ≤ (joiningCut G label A).card)
    (hsupply : ∀ p ∈ F0, r0 ≤ (pairPool (joiningQuotient G label) p).card)
    (hsmall : a / h ≤ (1 : ℝ) / 1000)
    (hnearly : ((h : ℝ) - r0) / h ≤ (1 : ℝ) / 1000) :
    Nonempty (Decomposition (joiningGraph G label)
      (joiningQuotient G label).edgeLabelPair univ h) :=
  four_odd_decomposition_real G label h r0 a ha hregular hno hodd hdegree
    F0 hF0 hsupply (ratio_boundary_small hh hsmall) (ratio_supply_nearly hh hnearly)

omit [Fintype V] [Fintype E] in
/-- Every surplus part is an actual quotient circuit of length at most
four; the construction proves the stronger exact length two. -/
theorem Decomposition.surplus_circuit {G : Multigraph V E}
    {Q : Multigraph (Fin 4) E} {C : Finset E} {h : ℕ}
    (P : Decomposition G Q.edgeLabelPair C h)
    {M : Finset E} (hM : M ∈ P.parts) (hn : M ∉ P.primary) :
    Q.IsCircuit M ∧ M.card = 2 ∧ M.card ≤ 4 := by
  have hp := P.surplus_shape M hM hn
  exact ⟨hp.isCircuit Q, hp.1, by rw [hp.1]; decide⟩

end Overfull.FourOdd
