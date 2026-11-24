import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

/-!
# Degree and reserve accounting for a family of matchings

The used edges, the remaining graph, and the reserve loads in this file are
defined from actual graph edges. In particular, the residual degree identity
does not assume the degree estimates needed by adaptive packing.
-/

namespace Overfull.BipartitePackingAccounting

open Finset Classical SimpleGraph
open scoped BigOperators

variable {V I : Type*} [Fintype V]

/-- The union of the edge sets indexed by a finite set. -/
def edgeUnion (G : I → SimpleGraph V) (T : Finset I) : SimpleGraph V where
  Adj v w := ∃ i ∈ T, (G i).Adj v w
  symm := by rintro v w ⟨i, hi, hvw⟩; exact ⟨i, hi, hvw.symm⟩
  loopless := by rintro v ⟨i, _, hvv⟩; exact (G i).loopless v hvv

omit [Fintype V] in
@[simp] theorem edgeUnion_adj (G : I → SimpleGraph V) (T : Finset I) (v w : V) :
    (edgeUnion G T).Adj v w ↔ ∃ i ∈ T, (G i).Adj v w := Iff.rfl

omit [Fintype V] in
theorem edgeUnion_le (G : I → SimpleGraph V) (T : Finset I) (H : SimpleGraph V)
    (h : ∀ i ∈ T, G i ≤ H) : edgeUnion G T ≤ H := by
  rintro v w ⟨i, hi, hadj⟩
  exact h i hi hadj

theorem edgeUnion_degree_eq_sum (G : I → SimpleGraph V) (T : Finset I)
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (G i) (G j)) (v : V) :
    (edgeUnion G T).degree v = ∑ i ∈ T, (G i).degree v := by
  have hneighbors : (edgeUnion G T).neighborFinset v =
      T.biUnion (fun i => (G i).neighborFinset v) := by
    ext w
    simp
  rw [SimpleGraph.degree, hneighbors, Finset.card_biUnion]
  · rfl
  · intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro w hwi hwj
    have hiadj : (G i).Adj v w := by simpa using hwi
    have hjadj : (G j).Adj v w := by simpa using hwj
    have : (⊥ : SimpleGraph V).Adj v w :=
      (hdisj i hi j hj hij).le_bot ⟨hiadj, hjadj⟩
    exact this

omit [Fintype V] in
@[simp] theorem edgeUnion_empty (G : I → SimpleGraph V) :
    edgeUnion G ∅ = ⊥ := by
  ext v w
  simp

omit [Fintype V] in
@[simp] theorem edgeUnion_insert (G : I → SimpleGraph V) (T : Finset I) (i : I) :
    edgeUnion G (insert i T) = G i ⊔ edgeUnion G T := by
  ext v w
  simp only [edgeUnion_adj, Finset.mem_insert, SimpleGraph.sup_adj]
  aesop

theorem degree_sup_add_degree_inf (G H : SimpleGraph V) (v : V) :
    (G ⊔ H).degree v + (G ⊓ H).degree v = G.degree v + H.degree v := by
  have hu : (G ⊔ H).neighborFinset v = G.neighborFinset v ∪ H.neighborFinset v := by
    ext w
    simp
  have hi : (G ⊓ H).neighborFinset v = G.neighborFinset v ∩ H.neighborFinset v := by
    ext w
    simp
  simpa only [SimpleGraph.degree, hu, hi] using
    Finset.card_union_add_card_inter (G.neighborFinset v) (H.neighborFinset v)

theorem degree_sdiff_add_degree_inf (G H : SimpleGraph V) (v : V) :
    (G \ H).degree v + (G ⊓ H).degree v = G.degree v := by
  have hd : (G \ H).neighborFinset v = G.neighborFinset v \ H.neighborFinset v := by
    ext w
    simp
  have hi : (G ⊓ H).neighborFinset v = G.neighborFinset v ∩ H.neighborFinset v := by
    ext w
    simp
  simpa only [SimpleGraph.degree, hd, hi] using
    Finset.card_sdiff_add_card_inter (G.neighborFinset v) (H.neighborFinset v)

theorem degree_sdiff_add_of_le (G H : SimpleGraph V) (hHG : H ≤ G) (v : V) :
    (G \ H).degree v + H.degree v = G.degree v := by
  have hi : (G ⊓ H).degree v = H.degree v := by
    apply congrArg Finset.card
    ext w
    simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.inf_adj]
    exact and_iff_right_of_imp (fun hw => hHG hw)
  have h := degree_sdiff_add_degree_inf G H v
  omega

theorem matching_degree (G : SimpleGraph V) (M : G.Subgraph) (hM : M.IsMatching)
    (v : V) : M.spanningCoe.degree v = if v ∈ M.verts then 1 else 0 := by
  by_cases hv : v ∈ M.verts
  · rw [if_pos hv, Subgraph.degree_spanningCoe]
    exact Subgraph.isMatching_iff_forall_degree.mp hM v hv
  · rw [if_neg hv]
    apply (M.spanningCoe.degree_eq_zero_iff_notMem_support v).mpr
    rintro ⟨w, hw⟩
    exact hv (M.edge_vert hw)

theorem matching_degree_le_one (G : SimpleGraph V) (M : G.Subgraph)
    (hM : M.IsMatching) (v : V) : M.spanningCoe.degree v ≤ 1 := by
  rw [matching_degree G M hM v]
  split_ifs <;> omega

variable (G : SimpleGraph V) (R : SimpleGraph V) (M : I → G.Subgraph) (T : Finset I)

/-- The number of previous matchings that leave a vertex uncovered. -/
noncomputable def missingCount (v : V) : ℕ :=
  (T.filter (fun i => v ∉ (M i).verts)).card

/-- The number of distinct used reserve edges at a vertex. -/
noncomputable def reserveLoad (v : V) : ℕ :=
  (R ⊓ edgeUnion (fun i => (M i).spanningCoe) T).degree v

/-- Delete the reserve and all edges used by the indexed matchings. -/
def residualGraph : SimpleGraph V :=
  G \ (R ⊔ edgeUnion (fun i => (M i).spanningCoe) T)

theorem matchingUnion_degree_add_missing
    (hM : ∀ i ∈ T, (M i).IsMatching)
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      Disjoint (M i).spanningCoe (M j).spanningCoe) (v : V) :
    (edgeUnion (fun i => (M i).spanningCoe) T).degree v +
      missingCount G M T v = T.card := by
  rw [edgeUnion_degree_eq_sum _ _ hdisj]
  have hsum : (∑ i ∈ T, (M i).spanningCoe.degree v) =
      (T.filter (fun i => v ∈ (M i).verts)).card := by
    calc
      _ = ∑ i ∈ T, if v ∈ (M i).verts then 1 else 0 :=
        Finset.sum_congr rfl (fun i hi => matching_degree G (M i) (hM i hi) v)
      _ = _ := by simp
  rw [hsum]
  exact Finset.filter_card_add_filter_neg_card_eq_card (s := T)
    (fun i => v ∈ (M i).verts)

/-- Exact integer accounting before deleting the next forbidden set. -/
theorem residual_degree_identity (hRG : R ≤ G)
    (hM : ∀ i ∈ T, (M i).IsMatching)
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      Disjoint (M i).spanningCoe (M j).spanningCoe) (v : V) :
    (residualGraph G R M T).degree v + R.degree v + T.card =
      G.degree v + missingCount G M T v + reserveLoad G R M T v := by
  let N := G.neighborFinset v
  let Q := R.neighborFinset v
  let U := (edgeUnion (fun i => (M i).spanningCoe) T).neighborFinset v
  have hsub : Q ∪ U ⊆ N := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · have hRw : R.Adj v w := by simpa [Q] using hw
      simpa [N] using hRG hRw
    · have hw' : (edgeUnion (fun i => (M i).spanningCoe) T).Adj v w := by
        simpa [U] using hw
      obtain ⟨i, _, hadj⟩ := hw'
      simpa [N] using (M i).adj_sub hadj
  have hres : (residualGraph G R M T).neighborFinset v = N \ (Q ∪ U) := by
    ext w
    simp [N, Q, U, residualGraph]
  have hload : reserveLoad G R M T v = (Q ∩ U).card := by
    unfold reserveLoad
    apply congrArg Finset.card
    ext w
    simp [Q, U]
  have hremaining : (residualGraph G R M T).degree v + (Q ∪ U).card = N.card := by
    rw [SimpleGraph.degree, hres]
    exact Finset.card_sdiff_add_card_eq_card hsub
  have hunion := Finset.card_union_add_card_inter Q U
  have hmatching : U.card + missingCount G M T v = T.card :=
    matchingUnion_degree_add_missing G M T hM hdisj v
  change (residualGraph G R M T).degree v + Q.card + T.card =
    N.card + missingCount G M T v + reserveLoad G R M T v
  omega

/-- The same identity in the real form used by the packing proof. -/
theorem residual_degree_eq (hRG : R ≤ G)
    (hM : ∀ i ∈ T, (M i).IsMatching)
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      Disjoint (M i).spanningCoe (M j).spanningCoe) (v : V) :
    ((residualGraph G R M T).degree v : ℝ) =
      G.degree v - R.degree v - T.card + missingCount G M T v + reserveLoad G R M T v := by
  have h := residual_degree_identity G R M T hRG hM hdisj v
  have h' : ((residualGraph G R M T).degree v : ℝ) + R.degree v + T.card =
      G.degree v + missingCount G M T v + reserveLoad G R M T v := by exact_mod_cast h
  linarith

omit [Fintype V] in
/-- For matchings perfect outside prescribed sets, the missing count is
exactly the incidence count of those sets. -/
theorem missingCount_eq_forbidden (S : I → Finset V)
    (hverts : ∀ i ∈ T, (M i).verts = (↑(S i) : Set V)ᶜ) (v : V) :
    missingCount G M T v = (T.filter (fun i => v ∈ S i)).card := by
  unfold missingCount
  congr 1
  apply Finset.filter_congr
  intro i hi
  simp [hverts i hi]

/-- Vertex deletion removes at most the size of the deleted set from a degree. -/
theorem induced_compl_degree_bounds (H : SimpleGraph V) (S : Finset V)
    (v : ↥((↑S : Set V)ᶜ)) :
    (H.induce (↑S : Set V)ᶜ).degree v ≤ H.degree v ∧
      H.degree v ≤ (H.induce (↑S : Set V)ᶜ).degree v + S.card := by
  have heq : ((H.induce (↑S : Set V)ᶜ).neighborFinset v).map
      (Function.Embedding.subtype (fun w => w ∈ (↑S : Set V)ᶜ)) =
      H.neighborFinset v \ S := by
    ext w
    simp only [Finset.mem_map, Finset.mem_sdiff, SimpleGraph.mem_neighborFinset,
      SimpleGraph.comap_adj, Function.Embedding.subtype_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, x.property⟩
    · rintro ⟨hw, hwS⟩
      exact ⟨⟨w, hwS⟩, hw, rfl⟩
  have hcard : (H.induce (↑S : Set V)ᶜ).degree v = (H.neighborFinset v \ S).card := by
    rw [← heq, Finset.card_map]
    rfl
  rw [hcard]
  constructor
  · exact Finset.card_le_card Finset.sdiff_subset
  · have h := Finset.card_sdiff_add_card_inter (H.neighborFinset v) S
    have hi : (H.neighborFinset v ∩ S).card ≤ S.card :=
      Finset.card_le_card Finset.inter_subset_right
    change (H.neighborFinset v).card ≤ (H.neighborFinset v \ S).card + S.card
    omega

/-- The working degree bounds follow from actual edge deletion, the
reserve degrees, and the total forbidden-set incidences. -/
theorem working_degree_bounds (hRG : R ≤ G)
    (hM : ∀ i ∈ T, (M i).IsMatching)
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      Disjoint (M i).spanningCoe (M j).spanningCoe)
    (S : Finset V) (Δ p ε m : ℝ)
    (hG : ∀ v, Δ - ε * m ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ Δ + ε * m)
    (hR : ∀ v, |(R.degree v : ℝ) - p * Δ| ≤ 2 * ε * m)
    (hmissing : ∀ v, (missingCount G M T v : ℝ) ≤ ε * m)
    (hS : (S.card : ℝ) ≤ ε * m) (v : ↥((↑S : Set V)ᶜ)) :
    (1 - p) * Δ - T.card - 4 * ε * m ≤
        ((residualGraph G R M T).induce (↑S : Set V)ᶜ).degree v ∧
      (((residualGraph G R M T).induce (↑S : Set V)ᶜ).degree v : ℝ) ≤
        (1 - p) * Δ - T.card + 4 * ε * m + reserveLoad G R M T v := by
  have heq := residual_degree_eq G R M T hRG hM hdisj (v : V)
  obtain ⟨hgl, hgu⟩ := hG v
  obtain ⟨hrl, hru⟩ := abs_le.mp (hR v)
  have hcount := hmissing v
  have hf : (0 : ℝ) ≤ missingCount G M T v := Nat.cast_nonneg _
  have hu : (0 : ℝ) ≤ reserveLoad G R M T v := Nat.cast_nonneg _
  obtain ⟨hdelu, hdell⟩ := induced_compl_degree_bounds (residualGraph G R M T) S v
  have hdelu' : (((residualGraph G R M T).induce (↑S : Set V)ᶜ).degree v : ℝ) ≤
      (residualGraph G R M T).degree v := by exact_mod_cast hdelu
  have hdell' : ((residualGraph G R M T).degree v : ℝ) ≤
      ((residualGraph G R M T).induce (↑S : Set V)ᶜ).degree v + S.card := by exact_mod_cast hdell
  constructor <;> nlinarith

/-- Reserve load is also the sum of the degrees supplied by the individual
matchings, because no edge occurs in two of them. -/
theorem reserveLoad_eq_sum
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      Disjoint (M i).spanningCoe (M j).spanningCoe) (v : V) :
    reserveLoad G R M T v = ∑ i ∈ T, (R ⊓ (M i).spanningCoe).degree v := by
  have heq : R ⊓ edgeUnion (fun i => (M i).spanningCoe) T =
      edgeUnion (fun i => R ⊓ (M i).spanningCoe) T := by
    ext x y
    simp only [SimpleGraph.inf_adj, edgeUnion_adj]
    aesop
  have hdegree : (R ⊓ edgeUnion (fun i => (M i).spanningCoe) T).degree v =
      (edgeUnion (fun i => R ⊓ (M i).spanningCoe) T).degree v := by
    apply congrArg Finset.card
    ext w
    simp only [SimpleGraph.mem_neighborFinset]
    rw [heq]
  unfold reserveLoad
  apply hdegree.trans
  have hd : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      Disjoint (R ⊓ (M i).spanningCoe) (R ⊓ (M j).spanningCoe) := by
    intro i hi j hj hij
    exact (hdisj i hi j hj hij).mono inf_le_right inf_le_right
  refine (edgeUnion_degree_eq_sum (fun i => R ⊓ (M i).spanningCoe) T hd v).trans ?_
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg Finset.card
  ext w
  simp only [SimpleGraph.mem_neighborFinset]

theorem reserve_matching_degree (N : G.Subgraph) (hN : N.IsMatching) (v : V) :
    (R ⊓ N.spanningCoe).degree v =
      if ∃ w, R.Adj v w ∧ N.Adj v w then 1 else 0 := by
  have hle : (R ⊓ N.spanningCoe).degree v ≤ 1 :=
    ((R ⊓ N.spanningCoe).degree_le_of_le
      (show R ⊓ N.spanningCoe ≤ N.spanningCoe from inf_le_right)).trans
      (matching_degree_le_one G N hN v)
  by_cases hv : ∃ w, R.Adj v w ∧ N.Adj v w
  · rw [if_pos hv]
    have hpos : 0 < (R ⊓ N.spanningCoe).degree v :=
      (SimpleGraph.degree_pos_iff_exists_adj _ _).mpr hv
    omega
  · rw [if_neg hv]
    apply (SimpleGraph.degree_eq_zero_iff_notMem_support _ _).mpr
    exact hv

/-- This agrees with counting the matching indices for which the vertex
is an end of a used reserve edge, as in the manuscript. -/
theorem reserveLoad_eq_count
    (hM : ∀ i ∈ T, (M i).IsMatching)
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      Disjoint (M i).spanningCoe (M j).spanningCoe) (v : V) :
    reserveLoad G R M T v =
      (T.filter (fun i => ∃ w, R.Adj v w ∧ (M i).Adj v w)).card := by
  rw [reserveLoad_eq_sum G R M T hdisj]
  calc
    _ = ∑ i ∈ T, if ∃ w, R.Adj v w ∧ (M i).Adj v w then 1 else 0 :=
      Finset.sum_congr rfl (fun i hi => reserve_matching_degree G R (M i) (hM i hi) v)
    _ = _ := by simp

@[simp] theorem reserveLoad_empty (v : V) :
    reserveLoad G R M ∅ v = 0 := by
  unfold reserveLoad
  apply (SimpleGraph.degree_eq_zero_iff_notMem_support _ _).mpr
  rintro ⟨w, hw⟩
  simpa using hw.2

theorem reserveLoad_insert (i : I) (hi : i ∉ T)
    (hdisj : ∀ j ∈ insert i T, ∀ k ∈ insert i T, j ≠ k →
      Disjoint (M j).spanningCoe (M k).spanningCoe) (v : V) :
    reserveLoad G R M (insert i T) v =
      reserveLoad G R M T v + (R ⊓ (M i).spanningCoe).degree v := by
  have hold : ∀ j ∈ T, ∀ k ∈ T, j ≠ k →
      Disjoint (M j).spanningCoe (M k).spanningCoe := by
    intro j hj k hk hjk
    exact hdisj j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk
  rw [reserveLoad_eq_sum G R M (insert i T) hdisj,
    reserveLoad_eq_sum G R M T hold, Finset.sum_insert hi]
  omega

theorem reserveLoad_insert_le_add_one (i : I) (hi : i ∉ T)
    (hM : (M i).IsMatching)
    (hdisj : ∀ j ∈ insert i T, ∀ k ∈ insert i T, j ≠ k →
      Disjoint (M j).spanningCoe (M k).spanningCoe) (v : V) :
    reserveLoad G R M (insert i T) v ≤ reserveLoad G R M T v + 1 := by
  rw [reserveLoad_insert G R M T i hi hdisj]
  have hle := (R ⊓ (M i).spanningCoe).degree_le_of_le (v := v)
    (show R ⊓ (M i).spanningCoe ≤ (M i).spanningCoe from inf_le_right)
  exact Nat.add_le_add_left (hle.trans (matching_degree_le_one G (M i) hM v)) _

/-- Avoiding reserve edges at every saturated vertex preserves the capacity. -/
theorem reserveLoad_insert_le_capacity (i : I) (hi : i ∉ T)
    (hM : (M i).IsMatching)
    (hdisj : ∀ j ∈ insert i T, ∀ k ∈ insert i T, j ≠ k →
      Disjoint (M j).spanningCoe (M k).spanningCoe)
    (r : ℕ) (hcapacity : ∀ v, reserveLoad G R M T v ≤ r)
    (havoid : ∀ v, reserveLoad G R M T v = r →
      ∀ w, ¬(R.Adj v w ∧ (M i).Adj v w)) (v : V) :
    reserveLoad G R M (insert i T) v ≤ r := by
  by_cases hv : reserveLoad G R M T v = r
  · have hzero : (R ⊓ (M i).spanningCoe).degree v = 0 := by
      apply (SimpleGraph.degree_eq_zero_iff_notMem_support _ _).mpr
      rintro ⟨w, hw⟩
      exact havoid v hv w hw
    rw [reserveLoad_insert G R M T i hi hdisj, hzero, Nat.add_zero, hv]
  · have h := reserveLoad_insert_le_add_one G R M T i hi hM hdisj v
    have hcap := hcapacity v
    omega

/-- The total increase in reserve load is exactly twice the number of
reserve edges in the new matching. -/
theorem total_reserveLoad_insert (i : I) (hi : i ∉ T)
    (hdisj : ∀ j ∈ insert i T, ∀ k ∈ insert i T, j ≠ k →
      Disjoint (M j).spanningCoe (M k).spanningCoe) :
    (∑ v, reserveLoad G R M (insert i T) v) =
      (∑ v, reserveLoad G R M T v) + 2 * (R ⊓ (M i).spanningCoe).edgeFinset.card := by
  simp_rw [reserveLoad_insert G R M T i hi hdisj]
  rw [Finset.sum_add_distrib]
  apply congrArg ((∑ v, reserveLoad G R M T v) + ·)
  have h := (R ⊓ (M i).spanningCoe).sum_degrees_eq_twice_card_edges
  refine h.trans ?_
  apply congrArg (2 * ·)
  apply congrArg Finset.card
  ext e
  simp only [SimpleGraph.mem_edgeFinset]

/-- Each used reserve edge is deleted once, with no loss beyond the load. -/
theorem unused_reserve_degree (v : V) :
    (R \ edgeUnion (fun i => (M i).spanningCoe) T).degree v +
      reserveLoad G R M T v = R.degree v := by
  exact degree_sdiff_add_degree_inf _ _ v

theorem unused_reserve_degree_lower (lam μ m : ℝ)
    (hR : ∀ v, lam * m ≤ (R.degree v : ℝ))
    (hload : ∀ v, (reserveLoad G R M T v : ℝ) ≤ μ * m) (v : V) :
    (lam - μ) * m ≤ (R \ edgeUnion (fun i => (M i).spanningCoe) T).degree v := by
  have h := unused_reserve_degree G R M T v
  have h' : ((R \ edgeUnion (fun i => (M i).spanningCoe) T).degree v : ℝ) +
      reserveLoad G R M T v = R.degree v := by exact_mod_cast h
  have hdegree := hR v
  have hused := hload v
  nlinarith

end Overfull.BipartitePackingAccounting
