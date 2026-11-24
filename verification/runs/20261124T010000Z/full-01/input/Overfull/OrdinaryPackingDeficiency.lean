import Overfull.TutteBerge
import Overfull.MatchingExtension
import Overfull.BipartitePackingStep

/-!
# Maximum-matching deficiency in an ordinary graph

The Tutte–Berge witness and the connected components are those of the
actual graph after vertex deletion. Counting neighbors of one vertex in
each component gives the degree-and-load estimate used in Lemma 2.20.
-/

set_option maxHeartbeats 800000

namespace Overfull.OrdinaryPackingDeficiency

open Finset Classical SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V]

private noncomputable def representative (G : SimpleGraph V)
    (C : G.ConnectedComponent) : V := C.nonempty_supp.choose

omit [Fintype V] in
private theorem representative_mem (G : SimpleGraph V) (C : G.ConnectedComponent) :
    representative G C ∈ C.supp := C.nonempty_supp.choose_spec

omit [Fintype V] in
private theorem representative_injective (G : SimpleGraph V) :
    Function.Injective (representative G) := by
  intro C D h
  exact ConnectedComponent.eq_of_common_vertex (representative_mem G C)
    (h ▸ representative_mem G D)

/-- The actual connected-component orders sum to the graph order. -/
theorem sum_component_orders (G : SimpleGraph V) [Fintype G.ConnectedComponent] :
    ∑ C : G.ConnectedComponent, C.supp.ncard = Fintype.card V := by
  classical
  have hdisj : (univ : Finset G.ConnectedComponent).toSet.PairwiseDisjoint
      (fun C => C.supp.toFinset) := by
    intro C _ D _ hCD
    exact Set.disjoint_toFinset.mpr (G.pairwise_disjoint_supp_connectedComponent hCD)
  have hcover : (univ : Finset G.ConnectedComponent).biUnion
      (fun C => C.supp.toFinset) = univ := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_univ, Set.mem_toFinset, true_and,
      iff_true]
    exact ⟨G.connectedComponentMk v, rfl⟩
  calc
    _ = ∑ C : G.ConnectedComponent, C.supp.toFinset.card := by simp only [Set.toFinset_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    _ = ((univ : Finset G.ConnectedComponent).biUnion
        (fun C => C.supp.toFinset)).card := (Finset.card_biUnion hdisj).symm
    _ = Fintype.card V := by rw [hcover, Finset.card_univ]

/-- A component contains a vertex and every neighbor of that vertex. -/
theorem degree_add_one_le_component_order (G : SimpleGraph V)
    (C : G.ConnectedComponent) (v : V) (hv : v ∈ C.supp) :
    G.degree v + 1 ≤ C.supp.ncard := by
  classical
  have hsub : insert v (G.neighborFinset v) ⊆ C.supp.toFinset := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact Set.mem_toFinset.mpr hv
    · exact Set.mem_toFinset.mpr
        ((C.mem_supp_congr_adj (by simpa using hw)).mp hv)
  have hnot : v ∉ G.neighborFinset v := by simp
  have hcard := Finset.card_le_card hsub
  simpa only [Finset.card_insert_of_notMem hnot,
    SimpleGraph.card_neighborFinset_eq_degree, Set.toFinset_card,
    ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using hcard

private abbrev remainingGraph (G : SimpleGraph V) (X : Set V) :=
  ((⊤ : G.Subgraph).deleteVerts X).coe

omit [Fintype V] in
private theorem remaining_adj (G : SimpleGraph V) (X : Set V)
    (v w : ((⊤ : G.Subgraph).deleteVerts X).verts) :
    (remainingGraph G X).Adj v w ↔ G.Adj v.val w.val := by
  change (v.val ∈ Set.univ \ X ∧ w.val ∈ Set.univ \ X ∧ G.Adj v.val w.val) ↔ _
  exact and_iff_right v.property |>.trans (and_iff_right w.property)

/-- The neighbors lost by vertex deletion are precisely the neighbors
in the deleted set. -/
theorem deleted_degree_add_neighbors (G : SimpleGraph V) (X : Set V)
    (v : ((⊤ : G.Subgraph).deleteVerts X).verts) :
    (remainingGraph G X).degree v +
      (X.toFinset.filter (fun x => G.Adj v.val x)).card = G.degree v.val := by
  classical
  have himage : ((remainingGraph G X).neighborFinset v).image Subtype.val =
      G.neighborFinset v.val \ X.toFinset := by
    ext w
    simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset, Finset.mem_sdiff,
      Set.mem_toFinset]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(remaining_adj G X v z).mp hz, z.property.2⟩
    · rintro ⟨hw, hwX⟩
      exact ⟨⟨w, ⟨Set.mem_univ _, hwX⟩⟩,
        (remaining_adj G X v _).mpr hw, rfl⟩
  have hcard : (remainingGraph G X).degree v =
      (G.neighborFinset v.val \ X.toFinset).card := by
    rw [← himage, Finset.card_image_of_injective _ Subtype.val_injective]
    rfl
  have hfilter : X.toFinset.filter (fun x => G.Adj v.val x) =
      G.neighborFinset v.val ∩ X.toFinset := by
    ext w
    simp only [Finset.mem_filter, Set.mem_toFinset, Finset.mem_inter,
      SimpleGraph.mem_neighborFinset, and_comm]
  rw [hcard, hfilter]
  exact Finset.card_sdiff_add_card_inter _ _

/-- Distinct components have distinct chosen vertices, so their incident
edges into a deleted set use at most the degree sum on that set. -/
theorem representative_boundary_sum_le (G : SimpleGraph V) (X : Set V)
    [Fintype (remainingGraph G X).ConnectedComponent] :
    (∑ C : (remainingGraph G X).ConnectedComponent,
      (X.toFinset.filter (fun x => G.Adj (representative (remainingGraph G X) C).val x)).card)
      ≤ ∑ x ∈ X.toFinset, G.degree x := by
  classical
  let r : (remainingGraph G X).ConnectedComponent → V :=
    fun C => (representative (remainingGraph G X) C).val
  have hr : Function.Injective r := Subtype.val_injective.comp
    (representative_injective (remainingGraph G X))
  let rel := fun C x => G.Adj (r C) x
  calc
    _ = ∑ C : (remainingGraph G X).ConnectedComponent,
        (Finset.bipartiteAbove rel X.toFinset C).card := rfl
    _ = ∑ x ∈ X.toFinset,
        (Finset.bipartiteBelow rel univ x).card :=
      Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow rel
    _ ≤ ∑ x ∈ X.toFinset, G.degree x := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.card_le_card_of_injOn r
      · intro C hC
        have h : G.Adj x (r C) := (Finset.mem_filter.mp hC).2.symm
        simpa using h
      · intro C _ D _ hCD
        exact hr hCD

/-- Counting one representative from every component after deletion. -/
theorem component_count_degree_bound (G : SimpleGraph V) (X : Set V)
    (d a t : ℝ) (u : V → ℝ)
    (hu : ∀ v, 0 ≤ u v)
    (hlower : ∀ v, d - a ≤ (G.degree v : ℝ))
    (hupper : ∀ v, (G.degree v : ℝ) ≤ d + a + u v)
    (hload : ∑ v, u v ≤ t) :
    (Nat.card (remainingGraph G X).ConnectedComponent : ℝ) * (d - a + 1) ≤
      Fintype.card V + (d + a - 1) * X.ncard + t := by
  classical
  let W := ((⊤ : G.Subgraph).deleteVerts X).verts
  let D := remainingGraph G X
  letI : Fintype D.ConnectedComponent := Fintype.ofFinite _
  have hlocal (C : D.ConnectedComponent) :
      d - a + 1 ≤ (C.supp.ncard : ℝ) +
        (X.toFinset.filter (fun x => G.Adj (representative D C).val x)).card := by
    have heq := deleted_degree_add_neighbors G X (representative D C)
    have hdeg := degree_add_one_le_component_order D C
      (representative D C) (representative_mem D C)
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at heq hdeg
    have heqR : ((Nat.card (D.neighborSet (representative D C)) : ℝ) +
        (X.toFinset.filter (fun x => G.Adj (representative D C).val x)).card) =
        Nat.card (G.neighborSet (representative D C).val) := by exact_mod_cast heq
    have hdegR : (Nat.card (D.neighborSet (representative D C)) : ℝ) + 1 ≤ C.supp.ncard := by
      exact_mod_cast hdeg
    have hlow := hlower (representative D C).val
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hlow
    linarith
  have hsum := Finset.sum_le_sum (s := (univ : Finset D.ConnectedComponent))
    (fun C _ => hlocal C)
  have horders : (∑ C : D.ConnectedComponent, (C.supp.ncard : ℝ)) = Fintype.card W := by
    exact_mod_cast sum_component_orders D
  have hboundary : (∑ C : D.ConnectedComponent,
      ((X.toFinset.filter (fun x => G.Adj (representative D C).val x)).card : ℝ)) ≤
      ∑ x ∈ X.toFinset, (G.degree x : ℝ) := by
    exact_mod_cast representative_boundary_sum_le G X
  have hloadX : ∑ x ∈ X.toFinset, u x ≤ t :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun x _ _ => hu x)).trans hload
  have hdegreesX : ∑ x ∈ X.toFinset, (G.degree x : ℝ) ≤
      (d + a) * X.ncard + t := by
    calc
      _ ≤ ∑ x ∈ X.toFinset, (d + a + u x) :=
        Finset.sum_le_sum (fun x _ => hupper x)
      _ = (d + a) * X.ncard + ∑ x ∈ X.toFinset, u x := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card']
        ring
      _ ≤ _ := add_le_add_left hloadX _
  have horder : (Fintype.card W : ℝ) + X.ncard = Fintype.card V := by
    exact_mod_cast (by simpa only [Nat.card_eq_fintype_card] using
      TutteBerge.deleted_order_add G X)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hsum
  rw [horders] at hsum
  simp only [← Nat.card_eq_fintype_card] at hsum horder ⊢
  nlinarith

/-- A maximum matching in an ordinary graph has small actual deficiency
under lower and upper degree bounds and a bound on the total nonnegative load. -/
theorem maximum_matching_deficiency (G : SimpleGraph V)
    (M : G.Subgraph) (hM : TutteBerge.IsMaximumMatching G M)
    (m : ℕ) (d a t : ℝ) (u : V → ℝ)
    (hd : 0 < d - a + 1) (ha : 0 ≤ a) (hu : ∀ v, 0 ≤ u v)
    (horder : Fintype.card V ≤ m)
    (hlower : ∀ v, d - a ≤ (G.degree v : ℝ))
    (hupper : ∀ v, (G.degree v : ℝ) ≤ d + a + u v)
    (hload : ∑ v, u v ≤ t) :
    (M.vertsᶜ.ncard : ℝ) ≤ (m + 2 * a * m + t) / (d - a + 1) := by
  classical
  have hmiss := TutteBerge.tutte_berge G M hM
  obtain ⟨X, hX⟩ := TutteBerge.deficiency_attained G
  rw [← hmiss] at hX
  have hXr : (TutteBerge.oddCount G X : ℝ) = X.ncard + M.vertsᶜ.ncard := by
    exact_mod_cast hX
  have hodd : TutteBerge.oddCount G X ≤
      Nat.card (remainingGraph G X).ConnectedComponent := by
    simpa only [TutteBerge.oddCount] using
      Set.ncard_le_card (remainingGraph G X).oddComponents
  have hoddR : (TutteBerge.oddCount G X : ℝ) ≤
      Nat.card (remainingGraph G X).ConnectedComponent := by exact_mod_cast hodd
  have hcomponent := component_count_degree_bound G X d a t u hu hlower hupper hload
  have hXsize : (X.ncard : ℝ) ≤ m := by
    have hXnat : X.ncard ≤ Fintype.card V := by
      simpa only [Nat.card_eq_fintype_card] using Set.ncard_le_card X
    exact_mod_cast hXnat.trans horder
  have hn : (Fintype.card V : ℝ) ≤ m := by exact_mod_cast horder
  have hXnonneg : (0 : ℝ) ≤ X.ncard := Nat.cast_nonneg _
  have hbound := mul_le_mul_of_nonneg_right hoddR hd.le
  have haX := mul_le_mul_of_nonneg_left hXsize (by positivity : 0 ≤ 2 * a)
  apply (le_div_iff₀ hd).mpr
  nlinarith

/-- The numerical form used in the ordinary adaptive packing argument. -/
theorem deficiency_scale (h m : ℕ) (d ε γ t : ℝ)
    (hm : 0 < m) (hε : 0 ≤ ε) (hγ : 0 < γ) (ht : 0 ≤ t)
    (hεγ : ε ≤ γ / 40) (hεm : 1 ≤ ε * m)
    (hdlower : γ * m / 2 ≤ d)
    (hbound : (h : ℝ) ≤ (m + 8 * ε * (m : ℝ) ^ 2 + t) / (d - 4 * ε * m + 1)) :
    (h : ℝ) ≤ 30 / γ * (ε * m + t / m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hden : 2 * γ * m / 5 ≤ d - 4 * ε * m + 1 := by
    have hsmall := mul_le_mul_of_nonneg_right hεγ hmR.le
    nlinarith
  have hdenpos : 0 < d - 4 * ε * m + 1 :=
    (by positivity : (0 : ℝ) < 2 * γ * m / 5).trans_le hden
  have hmul := (le_div_iff₀ hdenpos).mp hbound
  have hlow := mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg h : (0 : ℝ) ≤ h)
  have hmε := mul_le_mul_of_nonneg_right hεm hmR.le
  have hεm2 : 0 ≤ ε * (m : ℝ) ^ 2 := by positivity
  have hfinal : (h : ℝ) * (γ * m) ≤ 30 * (ε * (m : ℝ) ^ 2 + t) := by
    nlinarith
  have heq : 30 / γ * (ε * m + t / m) =
      (30 * (ε * (m : ℝ) ^ 2 + t)) / (γ * m) := by
    field_simp
  rw [heq]
  exact (le_div_iff₀ (mul_pos hγ hmR)).mpr hfinal

/-- Maximum matching selection preserving a small prescribed covered set,
with the ordinary-graph deficiency bound. -/
theorem exists_maximum_matching_with_deficiency (G : SimpleGraph V)
    (Z : Finset V) (m : ℕ) (d a t : ℝ) (u : V → ℝ)
    (hd : 0 < d - a + 1) (ha : 0 ≤ a) (hu : ∀ v, 0 ≤ u v)
    (horder : Fintype.card V ≤ m)
    (hlower : ∀ v, d - a ≤ (G.degree v : ℝ))
    (hupper : ∀ v, (G.degree v : ℝ) ≤ d + a + u v)
    (hload : ∑ v, u v ≤ t) (hsmall : (2 : ℝ) * Z.card < d - a) :
    ∃ M : G.Subgraph, TutteBerge.IsMaximumMatching G M ∧
      (↑Z : Set V) ⊆ M.verts ∧
      (M.vertsᶜ.ncard : ℝ) ≤ (m + 2 * a * m + t) / (d - a + 1) := by
  classical
  have hdegreeZ : ∀ v ∈ Z, 2 * Z.card < G.degree v := by
    intro v _
    exact_mod_cast hsmall.trans_le (hlower v)
  obtain ⟨M, hM, hcover, hmax⟩ :=
    MatchingExtension.exists_maximum_covering_small_set G Z hdegreeZ
  refine ⟨M, ⟨hM, hmax⟩, hcover, ?_⟩
  exact maximum_matching_deficiency G M ⟨hM, hmax⟩ m d a t u hd ha hu horder
    hlower hupper hload

/-- The actual set of vertices at capacity is small enough to be covered
by the selected maximum matching. -/
theorem exists_matching_covering_saturated_load (G : SimpleGraph V)
    (m : ℕ) (d a r t : ℝ) (u : V → ℝ)
    (hd : 0 < d - a + 1) (ha : 0 ≤ a) (hr : 0 < r) (hu : ∀ v, 0 ≤ u v)
    (horder : Fintype.card V ≤ m)
    (hlower : ∀ v, d - a ≤ (G.degree v : ℝ))
    (hupper : ∀ v, (G.degree v : ℝ) ≤ d + a + u v)
    (hload : ∑ v, u v ≤ t) (hbudget : 2 * t < r * (d - a)) :
    ∃ M : G.Subgraph, TutteBerge.IsMaximumMatching G M ∧
      (∀ v, r ≤ u v → v ∈ M.verts) ∧
      (M.vertsᶜ.ncard : ℝ) ≤ (m + 2 * a * m + t) / (d - a + 1) := by
  classical
  let Z : Finset V := univ.filter (fun v => r ≤ u v)
  have hsize : r * (Z.card : ℝ) ≤ t :=
    BipartitePackingStep.saturated_set_bound u r t hu hload
  have hsmall : (2 : ℝ) * Z.card < d - a := by nlinarith
  obtain ⟨M, hM, hcover, hdef⟩ := exists_maximum_matching_with_deficiency
    G Z m d a t u hd ha hu horder hlower hupper hload hsmall
  refine ⟨M, hM, ?_, hdef⟩
  intro v hv
  exact hcover (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)

/-- A matching in an even-order graph misses an even number of vertices. -/
theorem matching_uncovered_even (G : SimpleGraph V) (M : G.Subgraph)
    (hM : M.IsMatching) (horder : Even (Fintype.card V)) : Even M.vertsᶜ.ncard := by
  have h := TutteBerge.matching_uncovered_add_twice_edges G M hM
  simp only [Nat.card_eq_fintype_card] at h
  rw [Nat.even_iff] at horder ⊢
  omega

end Overfull.OrdinaryPackingDeficiency
