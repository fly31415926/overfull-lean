import Overfull.HallDefect
import Overfull.BipartitePackingHistory

/-!
# Actual dense bipartite matching candidates

Local sides are finite subsets of one ambient simple graph. All degree
hypotheses count actual neighbors on the opposite local side. No assumption
is made about edges outside the two sides.
-/

noncomputable section

namespace Overfull.DenseLinkPacking

open Finset Classical SimpleGraph BipartitePackingAccounting

/-- The half-degree form of finite Hall, returning an actual adjacency
bijection between two balanced finite populations. -/
theorem dense_bipartite_bijection {A B : Type*} [Fintype A] [Fintype B]
    (R : A → B → Prop) (hbalance : Fintype.card A = Fintype.card B)
    (hleft : ∀ a, (Fintype.card A : ℝ) / 2 ≤ (univ.filter (R a)).card)
    (hright : ∀ b, (Fintype.card A : ℝ) / 2 ≤
      (univ.filter (fun a => R a b)).card) :
    ∃ f : A ≃ B, ∀ a, R a (f a) := by
  let N : A → Finset B := fun a => univ.filter (R a)
  have hHall : ∀ S : Finset A, S.card ≤ (S.biUnion N).card := by
    intro S
    by_cases hS : S.Nonempty
    · by_cases hsmall : (S.card : ℝ) ≤ (Fintype.card A : ℝ) / 2
      · obtain ⟨a, ha⟩ := hS
        have hsub : N a ⊆ S.biUnion N := by
          intro b hb
          exact Finset.mem_biUnion.mpr ⟨a, ha, hb⟩
        have hcard : S.card ≤ (N a).card := by
          exact_mod_cast hsmall.trans (hleft a)
        exact hcard.trans (Finset.card_le_card hsub)
      · have hall : S.biUnion N = univ := by
          apply Finset.eq_univ_iff_forall.mpr
          intro b
          by_contra hb
          have hsub : univ.filter (fun a => R a b) ⊆ univ \ S := by
            intro a ha
            refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ?_⟩
            intro haS
            exact hb (Finset.mem_biUnion.mpr ⟨a, haS,
              Finset.mem_filter.mpr ⟨Finset.mem_univ b, (Finset.mem_filter.mp ha).2⟩⟩)
          have hcount := Finset.card_le_card hsub
          have hpart : (univ \ S).card + S.card = Fintype.card A := by
            simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
          have hsum : (univ.filter (fun a => R a b)).card + S.card ≤
              Fintype.card A := by omega
          have hsumR : ((univ.filter (fun a => R a b)).card : ℝ) + S.card ≤
              Fintype.card A := by exact_mod_cast hsum
          have hdeg := hright b
          linarith
        rw [hall, Finset.card_univ, ← hbalance]
        exact Finset.card_le_univ S
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.card_empty,
        Finset.biUnion_empty, le_refl]
  obtain ⟨f, hf, hfN⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' N).mp hHall
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hbalance⟩
  exact ⟨Equiv.ofBijective f hbij, fun a => (Finset.mem_filter.mp (hfN a)).2⟩

variable {V : Type*} [Fintype V]

/-- A subset viewed inside a finite population has the expected ambient
cardinality. -/
theorem subtype_neighbor_card (G : SimpleGraph V) (B : Finset V) (v : V) :
    ((univ : Finset B).filter (fun b => G.Adj v b.val)).card =
      (G.neighborFinset v ∩ B).card := by
  have heq : ((univ : Finset B).filter (fun b => G.Adj v b.val)).image Subtype.val =
      G.neighborFinset v ∩ B := by
    ext w
    constructor
    · intro hw
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_inter.mpr
        ⟨by simpa using (Finset.mem_filter.mp hb).2, b.property⟩
    · intro hw
      obtain ⟨hG, hB⟩ := Finset.mem_inter.mp hw
      exact Finset.mem_image.mpr ⟨⟨w, hB⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hG⟩,
        rfl⟩
  rw [← heq, Finset.card_image_of_injective _ Subtype.val_injective]

/-- Actual crossing half-degrees give an ambient matching covering exactly
the two prescribed local sides, including the case of two empty sides. -/
theorem exists_matching_on_sides (G : SimpleGraph V) (A B : Finset V)
    (hAB : Disjoint A B) (hbalance : A.card = B.card)
    (hleft : ∀ v ∈ A, (A.card : ℝ) / 2 ≤ (G.neighborFinset v ∩ B).card)
    (hright : ∀ v ∈ B, (A.card : ℝ) / 2 ≤ (G.neighborFinset v ∩ A).card) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.verts = (↑(A ∪ B) : Set V) := by
  obtain ⟨f, hf⟩ := dense_bipartite_bijection
    (fun (a : A) (b : B) => G.Adj a.val b.val)
    (by simpa only [Fintype.card_coe] using hbalance)
    (fun a => by
      simpa only [Fintype.card_coe, subtype_neighbor_card] using hleft a.val a.property)
    (fun b => by
      have hcard : ((univ : Finset A).filter (fun a => G.Adj a.val b.val)).card =
          (G.neighborFinset b.val ∩ A).card := by
        simp_rw [G.adj_comm]
        exact subtype_neighbor_card G A b.val
      simpa only [Fintype.card_coe, hcard] using hright b.val b.property)
  obtain ⟨M, hverts, hM⟩ := Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv
    (G := G) (s := (↑A : Set V)) (t := (↑B : Set V))
    (by simpa only [Finset.disjoint_coe] using hAB) f hf
  exact ⟨M, hM, by simpa only [Finset.coe_union] using hverts⟩

/-- Deleting arbitrary edges removes at most their total degree from an
actual opposite-side neighbor count. -/
theorem cross_degree_after_deletion (G H : SimpleGraph V) (B : Finset V) (v : V) :
    (G.neighborFinset v ∩ B).card ≤
      ((G \ H).neighborFinset v ∩ B).card + H.degree v := by
  have heq : (G.neighborFinset v ∩ B) \ H.neighborFinset v =
      (G \ H).neighborFinset v ∩ B := by
    ext w
    simp only [Finset.mem_sdiff, Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      SimpleGraph.sdiff_adj]
    tauto
  have hpart := Finset.card_sdiff_add_card_inter
    (G.neighborFinset v ∩ B) (H.neighborFinset v)
  rw [heq] at hpart
  have hcap : ((G.neighborFinset v ∩ B) ∩ H.neighborFinset v).card ≤ H.degree v :=
    Finset.card_le_card Finset.inter_subset_right
  omega

/-- Inclusion of the ambient graph preserves the actual vertices and edges
of a matching; the map on vertices is the identity. -/
def liftOfLE {G H : SimpleGraph V} (hHG : H ≤ G) (M : H.Subgraph) : G.Subgraph :=
  M.map (SimpleGraph.Hom.ofLE hHG)

omit [Fintype V] in
@[simp] theorem liftOfLE_verts {G H : SimpleGraph V} (hHG : H ≤ G) (M : H.Subgraph) :
    (liftOfLE hHG M).verts = M.verts := by
  simp [liftOfLE, Subgraph.map_verts]

omit [Fintype V] in
@[simp] theorem liftOfLE_adj {G H : SimpleGraph V} (hHG : H ≤ G) (M : H.Subgraph)
    (v w : V) : (liftOfLE hHG M).Adj v w ↔ M.Adj v w := by
  simp [liftOfLE, Subgraph.map_adj, Relation.Map]

omit [Fintype V] in
theorem liftOfLE_isMatching {G H : SimpleGraph V} (hHG : H ≤ G) (M : H.Subgraph)
    (hM : M.IsMatching) : (liftOfLE hHG M).IsMatching :=
  hM.map _ Function.injective_id

/-- A bounded-degree forbidden graph can be deleted before constructing the
actual matching. The output remains a subgraph of the original ambient graph. -/
theorem exists_matching_on_sides_avoiding (G H : SimpleGraph V) (A B : Finset V)
    (hAB : Disjoint A B) (hbalance : A.card = B.card) (r : ℕ)
    (hleft : ∀ v ∈ A,
      (A.card : ℝ) / 2 + r ≤ (G.neighborFinset v ∩ B).card)
    (hright : ∀ v ∈ B,
      (A.card : ℝ) / 2 + r ≤ (G.neighborFinset v ∩ A).card)
    (hH : ∀ v, H.degree v ≤ r) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.verts = (↑(A ∪ B) : Set V) ∧
      Disjoint M.spanningCoe H := by
  obtain ⟨R, hR⟩ : ∃ R : SimpleGraph V, R = G \ H := ⟨_, rfl⟩
  have hneighbors (v : V) : (G \ H).neighborFinset v = R.neighborFinset v := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset]
    rw [hR]
  have hl : ∀ v ∈ A,
      (A.card : ℝ) / 2 ≤ (R.neighborFinset v ∩ B).card := by
    intro v hv
    have hdeg := cross_degree_after_deletion G H B v
    rw [hneighbors v] at hdeg
    have hdegR : ((G.neighborFinset v ∩ B).card : ℝ) ≤
        (R.neighborFinset v ∩ B).card + r := by
      exact_mod_cast hdeg.trans (Nat.add_le_add_left (hH v) _)
    have h := hleft v hv
    linarith
  have hr : ∀ v ∈ B,
      (A.card : ℝ) / 2 ≤ (R.neighborFinset v ∩ A).card := by
    intro v hv
    have hdeg := cross_degree_after_deletion G H A v
    rw [hneighbors v] at hdeg
    have hdegR : ((G.neighborFinset v ∩ A).card : ℝ) ≤
        (R.neighborFinset v ∩ A).card + r := by
      exact_mod_cast hdeg.trans (Nat.add_le_add_left (hH v) _)
    have h := hright v hv
    linarith
  obtain ⟨N, hN, hNverts⟩ := exists_matching_on_sides R A B hAB hbalance hl hr
  have hRG : R ≤ G := by rw [hR]; exact sdiff_le
  let N' : G.Subgraph := liftOfLE hRG N
  refine ⟨N', liftOfLE_isMatching _ N hN, ?_, ?_⟩
  · simpa only [N', liftOfLE_verts] using hNverts
  · apply disjoint_iff_inf_le.mpr
    intro v w h
    have hNadj : N.Adj v w := (liftOfLE_adj _ N v w).mp h.1
    have hres : (G \ H).Adj v w := by
      rw [← hR]
      exact N.adj_sub hNadj
    exact hres.2 h.2

/-- Dense local sides contain as many actual edge-disjoint perfect-matching
candidates as the displayed degree surplus requests. -/
theorem exists_matching_candidates (G : SimpleGraph V) (A B : Finset V)
    (hAB : Disjoint A B) (hbalance : A.card = B.card) (t : ℕ)
    (hleft : ∀ v ∈ A,
      (A.card : ℝ) / 2 + t ≤ (G.neighborFinset v ∩ B).card)
    (hright : ∀ v ∈ B,
      (A.card : ℝ) / 2 + t ≤ (G.neighborFinset v ∩ A).card) :
    ∃ M : Fin t → G.Subgraph,
      (∀ i, (M i).IsMatching) ∧
      (∀ i, (M i).verts = (↑(A ∪ B) : Set V)) ∧
      Pairwise (fun i j => Disjoint (M i).spanningCoe (M j).spanningCoe) := by
  classical
  induction t with
  | zero =>
    exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ t ih =>
    have hleft' : ∀ v ∈ A,
        (A.card : ℝ) / 2 + t ≤ (G.neighborFinset v ∩ B).card := by
      intro v hv
      have h := hleft v hv
      simp only [Nat.cast_add, Nat.cast_one] at h
      linarith
    have hright' : ∀ v ∈ B,
        (A.card : ℝ) / 2 + t ≤ (G.neighborFinset v ∩ A).card := by
      intro v hv
      have h := hright v hv
      simp only [Nat.cast_add, Nat.cast_one] at h
      linarith
    obtain ⟨M, hM, hverts, hdisj⟩ := ih hleft' hright'
    let U : SimpleGraph V := edgeUnion (fun i => (M i).spanningCoe) univ
    have hU (v : V) : U.degree v ≤ t := by
      rw [show U = edgeUnion (fun i => (M i).spanningCoe) univ from rfl,
        edgeUnion_degree_eq_sum _ _ (fun i _ j _ hij => hdisj hij)]
      calc
        _ ≤ ∑ _i : Fin t, 1 := Finset.sum_le_sum (fun i _ =>
          matching_degree_le_one G (M i) (hM i) v)
        _ = t := by simp
    obtain ⟨N, hN, hNverts, hNdisj⟩ :=
      exists_matching_on_sides_avoiding G U A B hAB hbalance t hleft' hright' hU
    refine ⟨Fin.snoc M N, BipartitePackingHistory.matching_snoc G M N hM hN, ?_, ?_⟩
    · intro i
      induction i using Fin.lastCases with
      | last => simpa using hNverts
      | cast i => simpa using hverts i
    · exact BipartitePackingHistory.pairwise_disjoint_snoc G M N hdisj hNdisj

variable {κ : Type*} [Fintype κ]

/-- The actual candidate indices that use an edge from `v` into `Y`. -/
def harmfulCandidates (G : SimpleGraph V) (M : κ → G.Subgraph)
    (v : V) (Y : Finset V) : Finset κ :=
  univ.filter (fun i => ∃ w ∈ Y, (M i).Adj v w)

omit [Fintype V] in
/-- Edge-disjoint candidates meeting a fixed vertex use distinct neighbors.
This bound also applies to empty fallback candidates and needs only that
their vertices lie in the stated finite set. -/
theorem harmfulCandidates_card_le (G : SimpleGraph V) (M : κ → G.Subgraph)
    (W : Finset V) (hverts : ∀ i, (M i).verts ⊆ (↑W : Set V))
    (hdisj : Pairwise (fun i j => Disjoint (M i).spanningCoe (M j).spanningCoe))
    (v : V) (Y : Finset V) :
    (harmfulCandidates G M v Y).card ≤ (Y ∩ W).card := by
  have hex : ∀ i : harmfulCandidates G M v Y,
      ∃ w, w ∈ Y ∩ W ∧ (M i.val).Adj v w := by
    intro i
    obtain ⟨w, hw, hadj⟩ := (Finset.mem_filter.mp i.property).2
    exact ⟨w, Finset.mem_inter.mpr ⟨hw, hverts i.val ((M i.val).edge_vert hadj.symm)⟩,
      hadj⟩
  choose f hf hAdj using hex
  let e : harmfulCandidates G M v Y → ↥(Y ∩ W) := fun i => ⟨f i, hf i⟩
  have hinj : Function.Injective e := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    have heq : f i = f j := congrArg Subtype.val hij
    have hbot : (⊥ : SimpleGraph V).Adj v (f i) :=
      (hdisj hne).le_bot ⟨hAdj i, heq.symm ▸ hAdj j⟩
    exact hbot
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective e hinj

omit [Fintype V] in
theorem harmfulCandidates_card_le_sides (G : SimpleGraph V) (M : κ → G.Subgraph)
    (A B : Finset V) (hverts : ∀ i, (M i).verts = (↑(A ∪ B) : Set V))
    (hdisj : Pairwise (fun i j => Disjoint (M i).spanningCoe (M j).spanningCoe))
    (v : V) (Y : Finset V) :
    (harmfulCandidates G M v Y).card ≤ (Y ∩ (A ∪ B)).card := by
  exact harmfulCandidates_card_le G M (A ∪ B)
    (fun i => by rw [hverts i]) hdisj v Y

end Overfull.DenseLinkPacking
