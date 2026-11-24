import Overfull.FourOdd.PairPools

/-!
# Pairing a bipartite boundary with two labels on each side

The smaller refinement class on each side is contracted to one vertex, while
all other original vertices and every actual edge copy are retained.  König's
theorem and equitable balancing then produce exact two-edge matchings.  Each
edge in a minority class has a partner in the other class on that side.
Consequently the number of pairs crossing a refinement equals the smaller
of its two edge-copy totals.
-/

noncomputable section

namespace Overfull.FourOdd

open Finset Classical
open scoped BigOperators

variable {V E : Type*}

/-- The original endpoint of an edge on the specified side of a bipartition. -/
def sideEndpoint (G : Multigraph V E) (side : V → Bool) (s : Bool) (e : E) : V :=
  if side (G.firstEnd e) = s then G.firstEnd e else G.secondEnd e

theorem sideEndpoint_mem (G : Multigraph V E) (side : V → Bool) (s : Bool) (e : E) :
    sideEndpoint G side s e ∈ G.edge e := by
  rw [G.incident_iff]
  unfold sideEndpoint
  split_ifs <;> simp

theorem sideEndpoint_side (G : Multigraph V E) (side : V → Bool)
    (hside : ∀ e, side (G.firstEnd e) ≠ side (G.secondEnd e)) (s : Bool) (e : E) :
    side (sideEndpoint G side s e) = s := by
  have h := hside e
  cases h₁ : side (G.firstEnd e) <;> cases h₂ : side (G.secondEnd e) <;>
    cases s <;> simp_all [sideEndpoint]

theorem sideEndpoint_eq_of_incident (G : Multigraph V E) (side : V → Bool)
    (hside : ∀ e, side (G.firstEnd e) ≠ side (G.secondEnd e))
    {e : E} {v : V} (hv : v ∈ G.edge e) :
    sideEndpoint G side (side v) e = v := by
  rcases (G.incident_iff e v).mp hv with h | h
  · rw [← h]
    simp [sideEndpoint]
  · rw [← h]
    simp [sideEndpoint, hside e]

/-- The refinement label of an edge at one side of the bipartition. -/
def sideLabel (G : Multigraph V E) (side refinement : V → Bool)
    (s : Bool) (e : E) : Bool :=
  refinement (sideEndpoint G side s e)

variable [Fintype E]

/-- Actual edge copies incident with one refinement class on one side. -/
def sideEdges (G : Multigraph V E) (side refinement : V → Bool)
    (s b : Bool) : Finset E :=
  univ.filter (fun e => sideLabel G side refinement s e = b)

@[simp] theorem mem_sideEdges (G : Multigraph V E) (side refinement : V → Bool)
    (s b : Bool) (e : E) :
    e ∈ sideEdges G side refinement s b ↔ sideLabel G side refinement s e = b := by
  simp [sideEdges]

theorem sideEdges_card_add (G : Multigraph V E) (side refinement : V → Bool)
    (s : Bool) :
    (sideEdges G side refinement s false).card +
      (sideEdges G side refinement s true).card = Fintype.card E := by
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (univ : Finset E)) (fun e => sideLabel G side refinement s e = false)
  simpa [sideEdges] using h

/-- Ties are resolved toward `false`; only the minimum cardinality is relevant. -/
def minorityLabel (G : Multigraph V E) (side refinement : V → Bool) (s : Bool) : Bool :=
  if (sideEdges G side refinement s false).card ≤
      (sideEdges G side refinement s true).card then false else true

theorem minorityLabel_card (G : Multigraph V E) (side refinement : V → Bool)
    (s : Bool) :
    (sideEdges G side refinement s (minorityLabel G side refinement s)).card =
      min (sideEdges G side refinement s false).card
        (sideEdges G side refinement s true).card := by
  unfold minorityLabel
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h))).symm

theorem minorityLabel_card_le (G : Multigraph V E) (side refinement : V → Bool)
    {k : ℕ} (hcard : Fintype.card E = 2 * k) (s : Bool) :
    (sideEdges G side refinement s (minorityLabel G side refinement s)).card ≤ k := by
  rw [minorityLabel_card]
  have hsum := sideEdges_card_add G side refinement s
  rw [hcard] at hsum
  omega

private def contractedEnd (G : Multigraph V E) (side refinement : V → Bool)
    (minority : Bool → Bool) (s : Bool) (e : E) : Bool × Option V :=
  (s, if sideLabel G side refinement s e = minority s
    then none else some (sideEndpoint G side s e))

private def contractedGraph (G : Multigraph V E) (side refinement : V → Bool)
    (minority : Bool → Bool) : Multigraph (Bool × Option V) E where
  edge e := s(contractedEnd G side refinement minority false e,
    contractedEnd G side refinement minority true e)
  loopless e := by simp [contractedEnd]

omit [Fintype E] in
private theorem contractedGraph_bipartite (G : Multigraph V E)
    (side refinement : V → Bool) (minority : Bool → Bool) :
    (contractedGraph G side refinement minority).IsBipartite := by
  refine ⟨Prod.fst, ?_⟩
  intro e
  have h := (contractedGraph G side refinement minority).edge_eq e
  change s((contractedGraph G side refinement minority).firstEnd e,
      (contractedGraph G side refinement minority).secondEnd e) =
    s(contractedEnd G side refinement minority false e,
      contractedEnd G side refinement minority true e) at h
  rcases Sym2.eq_iff.mp h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
    simp [h₁, h₂, contractedEnd]

omit [Fintype E] in
private theorem contractedGraph_none_incident (G : Multigraph V E)
    (side refinement : V → Bool) (minority : Bool → Bool) (s : Bool) (e : E) :
    (s, none) ∈ (contractedGraph G side refinement minority).edge e ↔
      sideLabel G side refinement s e = minority s := by
  cases s <;>
    simp [contractedGraph, contractedEnd, Sym2.mem_iff]

omit [Fintype E] in
private theorem contractedGraph_some_incident (G : Multigraph V E)
    (side refinement : V → Bool) (minority : Bool → Bool) (s : Bool) (v : V) (e : E) :
    (s, some v) ∈ (contractedGraph G side refinement minority).edge e ↔
      sideLabel G side refinement s e ≠ minority s ∧ sideEndpoint G side s e = v := by
  cases s <;> simp [contractedGraph, contractedEnd, Sym2.mem_iff, eq_comm]

private theorem contractedGraph_none_degree (G : Multigraph V E)
    (side refinement : V → Bool) (minority : Bool → Bool) (s : Bool) :
    (contractedGraph G side refinement minority).degree (s, none) =
      (sideEdges G side refinement s (minority s)).card := by
  unfold Multigraph.degree
  congr 1
  ext e
  simp [contractedGraph_none_incident]

private theorem contractedGraph_some_degree_le (G : Multigraph V E)
    (side refinement : V → Bool) (minority : Bool → Bool) (s : Bool) (v : V) :
    (contractedGraph G side refinement minority).degree (s, some v) ≤ G.degree v := by
  apply Finset.card_le_card
  intro e he
  have h := (contractedGraph_some_incident G side refinement minority s v e).mp
    ((contractedGraph G side refinement minority).mem_incidenceEdges (s, some v) e |>.mp he)
  apply (G.mem_incidenceEdges v e).mpr
  rw [← h.2]
  exact sideEndpoint_mem G side s e

omit [Fintype E] in
private theorem contraction_incident (G : Multigraph V E)
    (side refinement : V → Bool)
    (hside : ∀ e, side (G.firstEnd e) ≠ side (G.secondEnd e))
    (minority : Bool → Bool) {e : E} {v : V} (hv : v ∈ G.edge e) :
    (side v, if refinement v = minority (side v) then none else some v) ∈
      (contractedGraph G side refinement minority).edge e := by
  have he := sideEndpoint_eq_of_incident G side hside hv
  have hvertex : contractedEnd G side refinement minority (side v) e =
      (side v, if refinement v = minority (side v) then none else some v) := by
    simp only [contractedEnd, sideLabel, he]
  rw [← hvertex]
  cases side v <;> simp [contractedGraph]

/-- An exact two-copy coloring with no repeated minority class in one pair. -/
structure MinorityPairing (G : Multigraph V E) (side refinement : V → Bool) (k : ℕ) where
  coloring : G.EdgeColoring k
  class_card_two : ∀ i, (coloring.colorClass i).card = 2
  minority_unique : ∀ (s : Bool) (e f : E),
    sideLabel G side refinement s e = minorityLabel G side refinement s →
    sideLabel G side refinement s f = minorityLabel G side refinement s →
    coloring.color e = coloring.color f → e = f

/-- Contracting just the two minority classes gives the required actual pairs.
The hypotheses concern the original graph's degrees and the exact number of
edge copies; no compatible-circuit theorem or desired partition is assumed. -/
theorem exists_minorityPairing [Fintype V] (G : Multigraph V E)
    (side refinement : V → Bool)
    (hside : ∀ e, side (G.firstEnd e) ≠ side (G.secondEnd e))
    (k : ℕ) (hcard : Fintype.card E = 2 * k) (hdegree : ∀ v, G.degree v ≤ k) :
    Nonempty (MinorityPairing G side refinement k) := by
  let minority := minorityLabel G side refinement
  let C := contractedGraph G side refinement minority
  have hCdegree : ∀ w, C.degree w ≤ k := by
    rintro ⟨s, _ | v⟩
    · rw [contractedGraph_none_degree]
      exact minorityLabel_card_le G side refinement hcard s
    · exact (contractedGraph_some_degree_le G side refinement minority s v).trans (hdegree v)
  obtain ⟨c₀⟩ := C.exists_edgeColoring_of_bipartite
    (contractedGraph_bipartite G side refinement minority) k hCdegree
  obtain ⟨c, hspread⟩ := c₀.exists_equitable
  let d : G.EdgeColoring k :=
    { color := c.color
      proper := by
        intro e f v hef hev hfv
        exact c.proper hef
          (contraction_incident G side refinement hside minority hev)
          (contraction_incident G side refinement hside minority hfv) }
  refine ⟨{ coloring := d, class_card_two := ?_, minority_unique := ?_ }⟩
  · exact equitable_colorClass_card_two c hcard hspread
  · intro s e f he hf hcolor
    apply c.proper hcolor (v := (s, none))
    · exact (contractedGraph_none_incident G side refinement minority s e).mpr he
    · exact (contractedGraph_none_incident G side refinement minority s f).mpr hf

namespace MinorityPairing

variable {G : Multigraph V E} {side refinement : V → Bool} {k : ℕ}
    (P : MinorityPairing G side refinement k)

/-- The actual two-copy matching indexed by a color. -/
def pair (i : Fin k) : Finset E := P.coloring.colorClass i

@[simp] theorem mem_pair (i : Fin k) (e : E) :
    e ∈ P.pair i ↔ P.coloring.color e = i := by
  simp [pair, Multigraph.EdgeColoring.colorClass]

@[simp] theorem card_pair (i : Fin k) : (P.pair i).card = 2 :=
  P.class_card_two i

theorem pair_isMatching (i : Fin k) : G.IsMatching (P.pair i) :=
  P.coloring.colorClass_isMatching i

theorem pair_disjoint {i j : Fin k} (hij : i ≠ j) : Disjoint (P.pair i) (P.pair j) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  exact hij ((P.mem_pair i e).mp he |>.symm.trans ((P.mem_pair j e).mp hf))

theorem pair_cover : univ.biUnion P.pair = (univ : Finset E) := by
  ext e
  simp

theorem unique_pair (e : E) : ∃! i, e ∈ P.pair i := by
  refine ⟨P.coloring.color e, by simp, ?_⟩
  intro i hi
  exact ((P.mem_pair i e).mp hi).symm

theorem pair_injective : Function.Injective P.pair := by
  intro i j hij
  obtain ⟨e, he⟩ := Finset.card_pos.mp (show 0 < (P.pair i).card by simp)
  have hj : e ∈ P.pair j := by rw [← hij]; exact he
  exact ((P.mem_pair i e).mp he).symm.trans ((P.mem_pair j e).mp hj)

/-- Forget the indexing while retaining the exact actual-copy partition. -/
def toMatchingPairPartition : MatchingPairPartition G univ where
  parts := univ.image P.pair
  matching := by
    intro C hC
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hC
    exact P.pair_isMatching i
  card_two := by
    intro C hC
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hC
    exact P.card_pair i
  disjoint := by
    intro C hC D hD hne
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hD
    apply P.pair_disjoint
    intro hij
    exact hne (congrArg P.pair hij)
  cover := by
    rw [Finset.image_biUnion]
    exact P.pair_cover

theorem toMatchingPairPartition_card : P.toMatchingPairPartition.parts.card = k := by
  change (univ.image P.pair).card = k
  rw [Finset.card_image_of_injective _ P.pair_injective]
  simp

/-- A minority edge has a different-label partner on that side. -/
theorem minority_partner (s : Bool) (i : Fin k) (e : E) (he : e ∈ P.pair i)
    (hminority : sideLabel G side refinement s e = minorityLabel G side refinement s) :
    ∃ f ∈ P.pair i, f ≠ e ∧
      sideLabel G side refinement s f ≠ minorityLabel G side refinement s := by
  obtain ⟨f, hf, hfe⟩ := Finset.exists_mem_ne (s := P.pair i) (by simp) e
  refine ⟨f, hf, hfe, ?_⟩
  intro hfminority
  apply hfe
  exact P.minority_unique s f e hfminority hminority
    (((P.mem_pair i f).mp hf).trans ((P.mem_pair i e).mp he).symm)

/-- A pair is mixed on a side if its two edges use different refinement labels. -/
def Mixed (s : Bool) (i : Fin k) : Prop :=
  ∃ e ∈ P.pair i, ∃ f ∈ P.pair i,
    sideLabel G side refinement s e ≠ sideLabel G side refinement s f

theorem mixed_iff_minority_member (s : Bool) (i : Fin k) :
    P.Mixed s i ↔ ∃ e ∈ P.pair i,
      sideLabel G side refinement s e = minorityLabel G side refinement s := by
  constructor
  · rintro ⟨e, he, f, hf, hlabels⟩
    by_cases hm : sideLabel G side refinement s e = minorityLabel G side refinement s
    · exact ⟨e, he, hm⟩
    · refine ⟨f, hf, ?_⟩
      cases h₁ : sideLabel G side refinement s e <;>
        cases h₂ : sideLabel G side refinement s f <;>
        cases h₃ : minorityLabel G side refinement s <;> simp_all
  · rintro ⟨e, he, hm⟩
    obtain ⟨f, hf, _hfe, hfm⟩ := P.minority_partner s i e he hm
    exact ⟨e, he, f, hf, by rw [hm]; exact hfm.symm⟩

/-- Mixed pair indices are precisely the colors used by the minority copies. -/
theorem mixed_eq_image (s : Bool) :
    univ.filter (P.Mixed s) =
      (sideEdges G side refinement s (minorityLabel G side refinement s)).image
        P.coloring.color := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  rw [P.mixed_iff_minority_member]
  constructor
  · rintro ⟨e, he, hm⟩
    exact ⟨e, (mem_sideEdges _ _ _ _ _ _).mpr hm, (P.mem_pair i e).mp he⟩
  · rintro ⟨e, he, hc⟩
    exact ⟨e, (P.mem_pair i e).mpr hc, (mem_sideEdges _ _ _ _ _ _).mp he⟩

/-- Exact saturation: mixed-row or mixed-column pairs are counted by the
smaller of the corresponding two original edge-copy totals. -/
theorem mixed_card (s : Bool) :
    (univ.filter (P.Mixed s)).card =
      min (sideEdges G side refinement s false).card
        (sideEdges G side refinement s true).card := by
  rw [P.mixed_eq_image]
  have hinj : Set.InjOn P.coloring.color
      (sideEdges G side refinement s (minorityLabel G side refinement s)) := by
    intro e he f hf hcolor
    exact P.minority_unique s e f ((mem_sideEdges _ _ _ _ _ _).mp he)
      ((mem_sideEdges _ _ _ _ _ _).mp hf) hcolor
  rw [Finset.card_image_iff.mpr hinj, minorityLabel_card]

/-- A concrete pair's two copies determine whether its side is mixed. -/
theorem mixed_iff_labels_ne (s : Bool) (i : Fin k) {e f : E}
    (he : e ∈ P.pair i) (hf : f ∈ P.pair i) (hef : e ≠ f) :
    P.Mixed s i ↔ sideLabel G side refinement s e ≠ sideLabel G side refinement s f := by
  have hpair : P.pair i = {e, f} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    · simp [hef]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    rw [hpair] at ha hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact False.elim (hab rfl)
    · exact hab
    · exact hab.symm
    · exact False.elim (hab rfl)
  · exact fun h => ⟨e, he, f, hf, h⟩

/-- Pair indices whose quotient labels differ on both sides. -/
def oppositePairs : Finset (Fin k) :=
  univ.filter (fun i => P.Mixed false i ∧ P.Mixed true i)

/-- Pair indices with equal row labels and different column labels. -/
def sameRowPairs : Finset (Fin k) :=
  univ.filter (fun i => ¬ P.Mixed false i ∧ P.Mixed true i)

/-- Pair indices with different row labels and equal column labels. -/
def sameColumnPairs : Finset (Fin k) :=
  univ.filter (fun i => P.Mixed false i ∧ ¬ P.Mixed true i)

/-- Pair indices with the same two quotient labels, hence parallel projection. -/
def parallelPairs : Finset (Fin k) :=
  univ.filter (fun i => ¬ P.Mixed false i ∧ ¬ P.Mixed true i)

/-- The four quotient shapes exhaust the pair indices. -/
theorem pair_shapes_cover :
    P.oppositePairs ∪ P.sameRowPairs ∪ P.sameColumnPairs ∪ P.parallelPairs = univ := by
  ext i
  simp only [oppositePairs, sameRowPairs, sameColumnPairs, parallelPairs,
    Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

/-- Mixed-row pairs are the opposite and same-column shapes. -/
theorem opposite_add_sameColumn_card :
    P.oppositePairs.card + P.sameColumnPairs.card =
      min (sideEdges G side refinement false false).card
        (sideEdges G side refinement false true).card := by
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := univ.filter (P.Mixed false)) (P.Mixed true)
  simpa only [Finset.filter_filter, oppositePairs, sameColumnPairs, P.mixed_card] using h

/-- Mixed-column pairs are the opposite and same-row shapes. -/
theorem opposite_add_sameRow_card :
    P.oppositePairs.card + P.sameRowPairs.card =
      min (sideEdges G side refinement true false).card
        (sideEdges G side refinement true true).card := by
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := univ.filter (P.Mixed true)) (P.Mixed false)
  simpa only [Finset.filter_filter, and_comm, oppositePairs, sameRowPairs,
    P.mixed_card] using h

/-- Every pair contributes exactly once to the four shape counts. -/
theorem pair_shapes_card :
    P.oppositePairs.card + P.sameRowPairs.card + P.sameColumnPairs.card +
      P.parallelPairs.card = k := by
  have hrow := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (univ : Finset (Fin k))) (P.Mixed false)
  have hyes := Finset.filter_card_add_filter_neg_card_eq_card
    (s := univ.filter (P.Mixed false)) (P.Mixed true)
  have hno := Finset.filter_card_add_filter_neg_card_eq_card
    (s := univ.filter (fun i => ¬ P.Mixed false i)) (P.Mixed true)
  simp only [Finset.card_univ, Fintype.card_fin] at hrow
  simp only [Finset.filter_filter] at hyes hno
  unfold oppositePairs sameColumnPairs sameRowPairs parallelPairs
  omega

end MinorityPairing

end Overfull.FourOdd
