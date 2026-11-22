import Overfull.Patterns.AssignedCuts
import Overfull.Patterns.BetweenSupply
import Overfull.Patterns.BoundaryRealization
import Overfull.Patterns.Cuts

/-!
# The actual frequent-pattern reduction result

This result records the exact original-host deletion sequence and the
final partition into enlarged robust cores. The finite-data assembly
below assumes already constructed completions, reserved actual pools,
and actual cut bounds. The uniform public theorem must supply these
inputs; this assembly alone is not the quantified manuscript lemma.
-/

noncomputable section
namespace Overfull.Patterns

open Finset Classical SimpleGraph Compression MatchingProbability ForeignPhase
open scoped BigOperators

variable {V I : Type*} [Fintype V] [Fintype I]

/-- The crossing count of an actual forest on the four core labels. -/
def labelForestCutCount (F : Finset LabelPair) (L : Finset (Fin 4)) : ℕ :=
  (F.filter (fun p => (p.val.filter (fun i => i ∈ L)).card = 1)).card

/-- The graph-level conclusion of the frequent-pattern reduction. The
ambient graph is exactly the residual of the recorded matchings, and the
final core sets cover every vertex, with no exceptional set left over. -/
structure FrequentPatternResult (G₀ : SimpleGraph V) (U₀ : I → Finset V)
    (Z₀ : Finset V) (k B : ℕ) (δ νout τout : ℝ) where
  G : SimpleGraph V
  h : ℕ
  r : ℕ
  N : ℕ → G₀.Subgraph
  rounds : ℕ
  graph_eq : G = afterDeletions G₀ N rounds
  degree_eq : h = k-rounds
  perfect : ∀ s < rounds, (N s).IsPerfectMatching
  present : ∀ s < rounds, (N s).spanningCoe ≤ afterDeletions G₀ N s
  safe_prefix : ∀ s ≤ rounds, ∀ X : Finset V,
    ¬ IsOverfull (afterDeletions G₀ N s) (k-s) X
  regular : ∀ v, G.degree v = h
  no_overfull : ∀ X : Finset V, ¬ IsOverfull G h X
  degree_positive : 0 < h
  pattern_bound_positive : 0 < B
  reserve_positive : 0 < r
  reserve_le_degree : r ≤ h
  reserve_linear : (k : ℝ)/(3*B) ≤ r
  retained_degree : (k : ℝ)/(3*B) ≤ h
  reserve_gap : (h : ℝ)-r ≤ δ*h
  A : I → Finset V
  H : ∀ i, SimpleGraph (A i)
  error : ℝ
  error_nonneg : 0 ≤ error
  error_bound : error ≤ δ*h
  core_enlargement : ∀ i, U₀ i ⊆ A i
  core_subset : ∀ i, A i ⊆ U₀ i ∪ Z₀
  core_disjoint : Pairwise (fun i j => Disjoint (A i) (A j))
  cover : ∀ v, ∃ i, v ∈ A i
  core_embed : ∀ i, H i ≤ G.induce (A i : Set V)
  core_degree : ∀ i v, (h : ℝ)-error ≤ ((H i).degree v : ℝ)
  core_robust : ∀ i, IsRobustExpander (H i) νout τout
  code : I ↪ Fin 4
  forest : Finset LabelPair
  forest_valid : LeafForest forest
  forest_card : forest.card ≤ 3
  forest_labels : ∀ p ∈ forest, ∀ j ∈ p.val, ∃ i, code i = j
  part_parity : ∀ i, (A i).card % 2 = pairDegree forest (code i) % 2
  pair_supply : ∀ p ∈ forest, ∀ i j, p.val = {code i,code j} →
    r ≤ (graphEdgesBetween G (A i) (A j)).card
  cut_supply : ∀ J : Finset I,
    r*labelForestCutCount forest (J.image code) ≤ graphCutCount G (J.biUnion A)
  four_odd_shape : Fintype.card I = 4 → (∀ i, (A i).card % 2 = 1) →
    (forest.card = 2 ∧ ∀ j : Fin 4, pairDegree forest j = 1) ∨
      ∃ center : Fin 4, forest.card = 3 ∧
        ∀ p : LabelPair, p ∈ forest ↔ center ∈ p.val

namespace FrequentPatternResult

variable {G₀ : SimpleGraph V} {U₀ : I → Finset V} {Z₀ : Finset V}
variable {k B : ℕ} {δ νout τout : ℝ}

theorem graph_le_original (R : FrequentPatternResult G₀ U₀ Z₀ k B δ νout τout) :
    R.G ≤ G₀ := by
  rw [R.graph_eq]
  exact sdiff_le

theorem pairwise_disjoint (R : FrequentPatternResult G₀ U₀ Z₀ k B δ νout τout) :
    ∀ s ∈ range R.rounds, ∀ t ∈ range R.rounds, s ≠ t →
      Disjoint (R.N s).spanningCoe (R.N t).spanningCoe :=
  ForeignIncidence.deletion_sequence_pairwise G₀ R.N R.rounds R.present

theorem core_order_le (R : FrequentPatternResult G₀ U₀ Z₀ k B δ νout τout) (i : I) :
    (U₀ i).card ≤ (R.A i).card := card_le_card (R.core_enlargement i)

end FrequentPatternResult

set_option maxHeartbeats 800000 in
/-- Assemble the actual final result from an already completed matching
sequence and actual reserved pools and cuts. The only new graph
construction is the proved enlargement of the distinguished cores. -/
theorem assemble_frequent_pattern_result [Nonempty I]
    (G₀ : SimpleGraph V) [DecidableRel G₀.Adj]
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (N : ℕ → G₀.Subgraph) (q k h r B : ℕ) (a δ θ σ : ℝ)
    (H : ∀ i, SimpleGraph (U i)) (F₀ : G₀.Subgraph) (P₀ : Pattern Z)
    (hdegree_eq : h = k-q)
    (hperfect : ∀ j < q, (N j).IsPerfectMatching)
    (hpresent : ∀ j < q, (N j).spanningCoe ≤ afterDeletions G₀ N j)
    (hsafe : ∀ s ≤ q, ∀ X : Finset V, ¬ IsOverfull (afterDeletions G₀ N s) (k-s) X)
    (hregular : ∀ v, (afterDeletions G₀ N q).degree v = h)
    (hB : 0 < B) (hrpos : 0 < r) (hrh : r ≤ h)
    (hlinear : (k : ℝ)/(3*B) ≤ r)
    (ha : 0 ≤ a) (herror : a+(h : ℝ)-r ≤ δ*h)
    (hdisjoint : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hembed : ∀ i, H i ≤ (afterDeletions G₀ N q).induce (U i : Set V))
    (hdegree : ∀ i v, (h : ℝ)-a ≤ ((H i).degree v : ℝ))
    (hθ : 0 ≤ θ) (hθσ : θ ≤ σ) (hσ : σ ≤ 1/4)
    (hsmall : ∀ i, (Z.card : ℝ) ≤ θ*(U i).card/4)
    (hrobust : ∀ i, IsRobustExpander (H i) θ σ)
    (hencoding : Encodes G₀ U Z code F₀ P₀)
    (hparity : ∀ i, Even (((U i : Set V) \ F₀.verts).ncard))
    (hpairs : P₀.internalPairs = ∅)
    (hpools : ∀ b ∈ P₀.boundaryEdges,
      r ≤ (boundaryPool (afterDeletions G₀ N q) U Z code b).card)
    (hcuts : ∀ Q : Finset (Z ⊕ Fin 4), r*P₀.cutCount Q ≤
      cutCount (univ : Finset (afterDeletions G₀ N q).edgeSet) (wholeUnion U Z code Q)) :
    Nonempty (FrequentPatternResult G₀ U Z k B δ (θ/4) (2*σ)) := by
  classical
  let R := afterDeletions G₀ N q
  obtain ⟨assignment,hassignment⟩ := hencoding.exists_total_assignment
    (fun i j hh => hdisjoint hh) hcover hpairs
  have hneighbors : ∀ z ∈ Z, r ≤ (R.neighborFinset z ∩ U (assignment z)).card := by
    apply reserved_pairs_give_neighbors R U Z code P₀ assignment r
      (fun i j hh => hdisjoint hh) hUZ hcover hassignment
    intro z
    exact hpools _ (assignment_edge_mem P₀ hpairs z)
  let a₁ : ℝ := (h : ℝ)-r
  have ha₁ : 0 ≤ a₁ := sub_nonneg.mpr (by exact_mod_cast hrh)
  have herror' : a+a₁ ≤ δ*h := by dsimp only [a₁]; linarith only [herror]
  obtain ⟨hAdisjoint,hAcover,hAold,hKembed,hKdegree,hKrobust⟩ :=
    absorb_all_with_reserved_neighbors R U H Z assignment h r a a₁ θ σ
      ha ha₁ le_rfl hdisjoint hUZ hcover hembed hdegree hneighbors
      hθ hθσ hσ hsmall hrobust
  let A := Absorption.enlargedSets U Z assignment
  let K := Absorption.enlargedGraphs R U H Z assignment
  have hAsubset (i : I) : A i ⊆ U i ∪ Z := by
    intro v hv
    rcases mem_union.mp hv with hv | hv
    · exact mem_union_left _ hv
    · exact mem_union_right _ (Absorption.absorbedAt_subset Z assignment i hv)
  have hforestlabels (p : LabelPair) (hp : p ∈ P₀.forest)
      (j : Fin 4) (hj : j ∈ p.val) : ∃ i, code i = j := by
    obtain ⟨label,hlabel,_hinj,hforest⟩ := hencoding.projection
    rw [hforest] at hp
    obtain ⟨e,he,heq⟩ := mem_image.mp hp
    have hends := hlabel e he
    rw [heq] at hends
    rw [hends] at hj
    obtain ⟨_heM,haZ,hbZ⟩ := mem_filter.mp he
    have hj' : j = coreLabel U code (FractionalMatching.firstEnd e) ∨
        j = coreLabel U code (FractionalMatching.secondEnd e) := by
      simpa using hj
    rcases hj' with hj' | hj'
    · obtain ⟨i,hi⟩ := (hcover (FractionalMatching.firstEnd e)).resolve_left haZ
      exact ⟨i,(coreLabel_of_mem U code (fun i j hh => hdisjoint hh) hi).symm.trans hj'.symm⟩
    · obtain ⟨i,hi⟩ := (hcover (FractionalMatching.secondEnd e)).resolve_left hbZ
      exact ⟨i,(coreLabel_of_mem U code (fun i j hh => hdisjoint hh) hi).symm.trans hj'.symm⟩
  have hpairsupply (p : LabelPair) (hp : p ∈ P₀.forest)
      (i j : I) (hends : p.val = {code i,code j}) :
      r ≤ (graphEdgesBetween R (A i) (A j)).card := by
    apply reserved_forest_pair_enlarged R U Z code assignment r
      (fun i j hh => hdisjoint hh) hUZ hcover p i j hends
    exact hpools _ (mem_union_right _ (mem_image.mpr ⟨p,hp,rfl⟩))
  have hcutsupply (J : Finset I) :
      r*labelForestCutCount P₀.forest (J.image code) ≤ graphCutCount R (J.biUnion A) := by
    have hh := forest_supply_on_enlarged_parts R U Z code P₀ assignment r
      (fun i j hh => hdisjoint hh) hUZ hcover hpairs hassignment hcuts J
    rw [univ_cut_eq_graph] at hh
    exact hh
  have hsafeR : ∀ X : Finset V, ¬ IsOverfull R h X := by
    intro X
    rw [hdegree_eq]
    exact hsafe q le_rfl X
  refine ⟨{
    G := R
    h := h
    r := r
    N := N
    rounds := q
    graph_eq := rfl
    degree_eq := hdegree_eq
    perfect := hperfect
    present := hpresent
    safe_prefix := hsafe
    regular := hregular
    no_overfull := hsafeR
    degree_positive := hrpos.trans_le hrh
    pattern_bound_positive := hB
    reserve_positive := hrpos
    reserve_le_degree := hrh
    reserve_linear := hlinear
    retained_degree := hlinear.trans (by exact_mod_cast hrh)
    reserve_gap := by linarith only [herror,ha]
    A := A
    H := K
    error := a+a₁
    error_nonneg := add_nonneg ha ha₁
    error_bound := herror'
    core_enlargement := hAold
    core_subset := hAsubset
    core_disjoint := hAdisjoint
    cover := hAcover
    core_embed := hKembed
    core_degree := hKdegree
    core_robust := hKrobust
    code := code
    forest := P₀.forest
    forest_valid := hencoding.forest
    forest_card := label_forest_card P₀.forest hencoding.forest
    forest_labels := hforestlabels
    part_parity := hencoding.enlarged_part_parity assignment hdisjoint hUZ hcover
      hparity hpairs hassignment
    pair_supply := hpairsupply
    cut_supply := hcutsupply
    four_odd_shape := fun hI hodd => hencoding.enlarged_four_odd_forest assignment hI
      hdisjoint hUZ hcover hparity hpairs hassignment hodd
  }⟩

end Overfull.Patterns
