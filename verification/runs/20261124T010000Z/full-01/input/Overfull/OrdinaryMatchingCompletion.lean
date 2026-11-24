import Overfull.BipartiteMatchingCompletion
import Overfull.BipartitePackingDeficiency
import Overfull.RobustRealization.Relabeling
import Overfull.OrdinaryPackingWorking

/-!
# Ordinary matching completion through a supplied paired cut

The cut and its robust expansion are explicit inputs.  The augmenting
paths and completed matching are constructed from those inputs.
-/

namespace Overfull.OrdinaryMatchingCompletion

open Finset Classical SimpleGraph
open scoped BigOperators

variable {V W A B : Type*}

/-- Express the matching in new vertex labels, allowing its edges in the
complete graph so that the available path graph remains a separate input. -/
def pullMatching (G : SimpleGraph V) (M : G.Subgraph) (e : W ≃ V) :
    (⊤ : SimpleGraph W).Subgraph where
  verts := e ⁻¹' M.verts
  Adj v w := M.Adj (e v) (e w)
  adj_sub := by
    intro v w h
    change v ≠ w
    exact fun heq => (G.ne_of_adj (M.adj_sub h)) (congrArg e heq)
  edge_vert := M.edge_vert
  symm := fun _ _ h => M.symm h

theorem pullMatching_isMatching (G : SimpleGraph V) (M : G.Subgraph)
    (hM : M.IsMatching) (e : W ≃ V) : (pullMatching G M e).IsMatching := by
  intro v hv
  obtain ⟨w, hvw, huniq⟩ := hM hv
  refine ⟨e.symm w, ?_, ?_⟩
  · change M.Adj (e v) (e (e.symm w))
    simpa using hvw
  · intro z hz
    apply e.injective
    change M.Adj (e v) (e z) at hz
    simpa using huniq (e z) hz

/-- Return a matching from the cut labels to the original host. -/
def pushMatching (G : SimpleGraph V) (e : W ≃ V)
    (M : (G.comap e).Subgraph) : G.Subgraph where
  verts := e.symm ⁻¹' M.verts
  Adj v w := M.Adj (e.symm v) (e.symm w)
  adj_sub := by
    intro v w h
    have hh := M.adj_sub h
    simpa only [SimpleGraph.comap_adj, e.apply_symm_apply] using hh
  edge_vert := M.edge_vert
  symm := fun _ _ h => M.symm h

theorem pushMatching_isMatching (G : SimpleGraph V) (e : W ≃ V)
    (M : (G.comap e).Subgraph) (hM : M.IsMatching) :
    (pushMatching G e M).IsMatching := by
  intro v hv
  obtain ⟨w, hvw, huniq⟩ := hM hv
  refine ⟨e w, ?_, ?_⟩
  · change M.Adj (e.symm v) (e.symm (e w))
    simpa using hvw
  · intro z hz
    apply e.symm.injective
    change M.Adj (e.symm v) (e.symm z) at hz
    simpa using huniq (e.symm z) hz

theorem pushMatching_reserve_graph (G R : SimpleGraph V) (e : W ≃ V)
    (M : (G.comap e).Subgraph) :
    ((pushMatching G e M).spanningCoe ⊓ R).comap e =
      M.spanningCoe ⊓ R.comap e := by
  ext v w
  simp only [SimpleGraph.comap_adj, SimpleGraph.inf_adj, Subgraph.spanningCoe_adj,
    pushMatching, e.symm_apply_apply]

variable [Fintype V] [Fintype W]

omit [Fintype V] [Fintype W] in
theorem pullMatching_uncovered_card (G : SimpleGraph V) (M : G.Subgraph)
    (e : W ≃ V) : (pullMatching G M e).vertsᶜ.ncard = M.vertsᶜ.ncard := by
  classical
  let f : ↥((pullMatching G M e).vertsᶜ) ≃ ↥(M.vertsᶜ) :=
    { toFun v := ⟨e v.val, v.property⟩
      invFun v := ⟨e.symm v.val, by simpa only [pullMatching, Set.mem_compl_iff,
        Set.mem_preimage, e.apply_symm_apply] using v.property⟩
      left_inv v := by apply Subtype.ext; exact e.symm_apply_apply v.val
      right_inv v := by apply Subtype.ext; exact e.apply_symm_apply v.val }
  simpa only [Nat.card_coe_set_eq] using Nat.card_congr f

theorem pushMatching_reserve_degree (G R : SimpleGraph V) (e : W ≃ V)
    (M : (G.comap e).Subgraph) (v : W) :
    ((pushMatching G e M).spanningCoe ⊓ R).degree (e v) =
      (M.spanningCoe ⊓ R.comap e).degree v := by
  classical
  have h := RobustRealization.comap_equiv_degree
    ((pushMatching G e M).spanningCoe ⊓ R) e v
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h ⊢
  rw [pushMatching_reserve_graph] at h
  exact h.symm

theorem pushMatching_reserve_sum (G R : SimpleGraph V) (e : W ≃ V)
    (M : (G.comap e).Subgraph) :
    (∑ v : V, ((pushMatching G e M).spanningCoe ⊓ R).degree v) =
      ∑ v : W, (M.spanningCoe ⊓ R.comap e).degree v := by
  classical
  calc
    _ = ∑ v : W, ((pushMatching G e M).spanningCoe ⊓ R).degree (e v) :=
      (Equiv.sum_comp e _).symm
    _ = _ := Finset.sum_congr rfl (fun v _ => pushMatching_reserve_degree G R e M v)

variable [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
theorem crossingMatching_bipartite
    (M : (⊤ : SimpleGraph (A ⊕ B)).Subgraph) (hM : IsCrossingMatching M) :
    M.spanningCoe.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) where
  disjoint := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    cases hb
  mem_of_adj := by
    rintro (a | b) (a' | b') h
    · exact (hM.2.1 a a' h).elim
    · exact Or.inl ⟨⟨a, rfl⟩, ⟨b', rfl⟩⟩
    · exact Or.inr ⟨⟨b, rfl⟩, ⟨a', rfl⟩⟩
    · exact (hM.2.2 b b' h).elim

theorem crossingMatching_uncovered_balance
    (M : (⊤ : SimpleGraph (A ⊕ B)).Subgraph) (hM : IsCrossingMatching M)
    (hbalance : Fintype.card A = Fintype.card B) :
    (BipartiteMatchingCompletion.uncoveredLeftOutside M ∅).card =
      (BipartiteMatchingCompletion.uncoveredRightOutside M ∅).card := by
  classical
  let N : M.spanningCoe.Subgraph :=
    { verts := M.verts
      Adj := M.Adj
      adj_sub := fun h => h
      edge_vert := M.edge_vert
      symm := M.symm }
  have h := BipartitePackingDeficiency.matching_uncovered_sides_eq M.spanningCoe
    (crossingMatching_bipartite M hM) hbalance N hM.1
  simpa only [uncoveredLeft,
    BipartiteMatchingCompletion.uncoveredLeftOutside,
    BipartiteMatchingCompletion.uncoveredRightOutside,
    Finset.notMem_empty, not_false_eq_true, true_and, N] using h

theorem crossingMatching_uncovered_total
    (M : (⊤ : SimpleGraph (A ⊕ B)).Subgraph) :
    (BipartiteMatchingCompletion.uncoveredLeftOutside M ∅).card +
      (BipartiteMatchingCompletion.uncoveredRightOutside M ∅).card =
        M.vertsᶜ.ncard := by
  classical
  have heq : (BipartiteMatchingCompletion.uncoveredLeftOutside M ∅).disjSum
      (BipartiteMatchingCompletion.uncoveredRightOutside M ∅) = M.vertsᶜ.toFinset := by
    ext v
    cases v <;> simp [BipartiteMatchingCompletion.uncoveredLeftOutside,
      BipartiteMatchingCompletion.uncoveredRightOutside]
  have h := congrArg Finset.card heq
  simpa only [Finset.card_disjSum, ← Set.ncard_eq_toFinset_card'] using h

/-- A supplied balanced paired cut completes an ordinary matching. The
proof constructs every augmenting path and preserves the original matching
edges at the protected vertices. The reserve contribution is measured in
the original reserve, even if only a smaller path graph is available. -/
theorem exists_completion_of_balanced_cut
    (G R : SimpleGraph V) (M : G.Subgraph) (hM : M.IsMatching)
    (e : A ⊕ B ≃ V) (hbalance : Fintype.card A = Fintype.card B)
    (hleftM : ∀ a a' : A, ¬M.Adj (e (.inl a)) (e (.inl a')))
    (hrightM : ∀ b b' : B, ¬M.Adj (e (.inr b)) (e (.inr b')))
    (hMR : Disjoint M.spanningCoe R)
    (Q : SimpleGraph (A ⊕ B)) [DecidableRel Q.Adj]
    (hQR : Q ≤ R.comap e) (hQG : Q ≤ G.comap e)
    (Z : Finset V) (hZ : ∀ v ∈ Z, v ∈ M.verts)
    (θ τ δ : ℝ) (hθ : 0 < θ) (hτ : 0 < τ) (hδ : 2 * τ ≤ δ)
    (hleft : ∀ a, δ * Fintype.card A ≤ ((rightNeighbors Q a).card : ℝ))
    (hright : ∀ b, δ * Fintype.card A ≤ ((leftNeighbors Q b).card : ℝ))
    (hexpand : IsBipartiteRobustExpander Q θ τ)
    (ℓ : ℕ) (hℓ : Nat.ceil (2 / θ) + 2 ≤ ℓ)
    (hbudget : (2 : ℝ) * Z.card + ℓ * M.vertsᶜ.ncard ≤
      min θ δ * Fintype.card A / 2 - 1) :
    ∃ N : G.Subgraph,
      N.IsMatching ∧ N.verts = Set.univ ∧
      (∀ v w, N.Adj v w → M.Adj v w ∨ Q.Adj (e.symm v) (e.symm w)) ∧
      (∀ v ∈ Z, (N.spanningCoe ⊓ R).degree v = 0) ∧
      (∀ v, (N.spanningCoe ⊓ R).degree v ≤ 1) ∧
      (∑ v, (N.spanningCoe ⊓ R).degree v) ≤ ℓ * M.vertsᶜ.ncard := by
  classical
  let L := pullMatching G M e
  have hL : IsCrossingMatching L :=
    ⟨pullMatching_isMatching G M hM e, hleftM, hrightM⟩
  have hLR : ∀ v w, L.Adj v w → ¬(R.comap e).Adj v w := by
    intro v w hvw hRvw
    exact hMR.le_bot ⟨hvw, hRvw⟩
  let Z' := Z.map e.symm.toEmbedding
  have hZ'card : Z'.card = Z.card := Finset.card_map _
  have hZ'mem (v : A ⊕ B) : v ∈ Z' ↔ e v ∈ Z := by
    simp [Z', Finset.mem_map_equiv]
  have hZ' : ∀ v ∈ Z', v ∈ L.verts := by
    intro v hv
    exact hZ (e v) ((hZ'mem v).mp hv)
  have hbal := crossingMatching_uncovered_balance L hL hbalance
  have htotal := crossingMatching_uncovered_total L
  have hpair : 2 * (BipartiteMatchingCompletion.uncoveredLeftOutside L ∅).card =
      M.vertsᶜ.ncard := by
    rw [← hbal, pullMatching_uncovered_card] at htotal
    omega
  have hpairR : (2 : ℝ) * (BipartiteMatchingCompletion.uncoveredLeftOutside L ∅).card =
      M.vertsᶜ.ncard := by exact_mod_cast hpair
  have hbudget' : ((∅ : Finset (A ⊕ B)).card : ℝ) + 2 * Z'.card +
      2 * ℓ * (BipartiteMatchingCompletion.uncoveredLeftOutside L ∅).card ≤
        min θ δ * Fintype.card A / 2 - 1 := by
    have heq : (2 : ℝ) * ℓ *
        (BipartiteMatchingCompletion.uncoveredLeftOutside L ∅).card =
          ℓ * M.vertsᶜ.ncard := by rw [← hpairR]; ring
    simpa only [Finset.card_empty, Nat.cast_zero, zero_add, hZ'card, heq] using hbudget
  obtain ⟨N, hN, hNverts, _, hedges, hzero, hdegree, hsum⟩ :=
    BipartiteMatchingCompletion.exists_completion_in_graph Q (R.comap e) (G.comap e)
      hQR hQG L hL (fun _ _ h => M.adj_sub h) hLR ∅ Z'
      (by intro v hv; exact (Finset.notMem_empty v hv).elim)
      hZ' hbal θ τ δ hθ hτ hδ hleft hright hexpand ℓ hℓ hbudget'
  refine ⟨pushMatching G e N, pushMatching_isMatching G e N hN, ?_, ?_, ?_, ?_, ?_⟩
  · change e.symm ⁻¹' N.verts = Set.univ
    rw [hNverts]
    simp
  · intro v w hvw
    have h := hedges (e.symm v) (e.symm w) hvw
    simpa only [L, pullMatching, e.apply_symm_apply] using h
  · intro v hv
    have hz : e.symm v ∈ (∅ : Finset (A ⊕ B)) ∪ Z' := by
      apply Finset.mem_union_right
      exact (hZ'mem (e.symm v)).mpr (by simpa using hv)
    have hd := pushMatching_reserve_degree G R e N (e.symm v)
    rw [e.apply_symm_apply] at hd
    exact hd.trans (hzero (e.symm v) hz)
  · intro v
    have hd := pushMatching_reserve_degree G R e N (e.symm v)
    rw [e.apply_symm_apply] at hd
    exact hd.le.trans (hdegree (e.symm v))
  · rw [pushMatching_reserve_sum]
    calc
      _ ≤ 2 * ℓ * (BipartiteMatchingCompletion.uncoveredLeftOutside L ∅).card := hsum
      _ = ℓ * M.vertsᶜ.ncard := by rw [← hpair]; ring

open OrdinaryPackingWorking

/-- Restrict the preliminary matching to the vertices outside `S`. -/
def restrictMatching (G : SimpleGraph V) (M : G.Subgraph) (S : Finset V) :
    (G.induce (↑S : Set V)ᶜ).Subgraph where
  verts := Subtype.val ⁻¹' M.verts
  Adj v w := M.Adj v.val w.val
  adj_sub := M.adj_sub
  edge_vert := M.edge_vert
  symm := fun _ _ h => M.symm h

omit [Fintype V] in
theorem restrictMatching_isMatching (G : SimpleGraph V) (M : G.Subgraph)
    (hM : M.IsMatching) (S : Finset V) (hMS : M.verts ⊆ (↑S : Set V)ᶜ) :
    (restrictMatching G M S).IsMatching := by
  intro v hv
  obtain ⟨w, hvw, huniq⟩ := hM hv
  refine ⟨⟨w, hMS (M.edge_vert (M.symm hvw))⟩, hvw, ?_⟩
  intro z hz
  exact Subtype.ext (huniq z.val hz)

theorem restrictMatching_uncovered_card (G : SimpleGraph V) (M : G.Subgraph)
    (S : Finset V) :
    (restrictMatching G M S).vertsᶜ.ncard = (uncoveredOutside G M S).card := by
  classical
  have himage : ((restrictMatching G M S).vertsᶜ.toFinset).image Subtype.val =
      uncoveredOutside G M S := by
    ext v
    simp only [Finset.mem_image, Set.mem_toFinset, Set.mem_compl_iff,
      restrictMatching, Set.mem_preimage, uncoveredOutside, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.property, hw⟩
    · rintro ⟨hvS, hvM⟩
      exact ⟨⟨v, hvS⟩, hvM, rfl⟩
  rw [← himage, Finset.card_image_of_injective _ Subtype.val_injective,
    ← Set.ncard_eq_toFinset_card']

omit [Fintype V] in
theorem liftMatching_adj (G : SimpleGraph V) (S : Finset V)
    (M : (G.induce (↑S : Set V)ᶜ).Subgraph) (v w : Remaining S) :
    (liftMatching G S M).Adj v.val w.val ↔ M.Adj v w := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    have ha' : a = v := Subtype.ext ha
    have hb' : b = w := Subtype.ext hb
    simpa only [ha', hb'] using hab
  · intro h
    exact ⟨v, w, h, rfl, rfl⟩

theorem liftMatching_reserve_degree (G R : SimpleGraph V) (S : Finset V)
    (M : (G.induce (↑S : Set V)ᶜ).Subgraph) (v : Remaining S) :
    ((liftMatching G S M).spanningCoe ⊓ R).degree v.val =
      (M.spanningCoe ⊓ R.induce (↑S : Set V)ᶜ).degree v := by
  classical
  have himage : ((M.spanningCoe ⊓ R.induce (↑S : Set V)ᶜ).neighborFinset v).image
      Subtype.val = ((liftMatching G S M).spanningCoe ⊓ R).neighborFinset v.val := by
    ext w
    simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset, SimpleGraph.inf_adj,
      SimpleGraph.comap_adj, Subgraph.spanningCoe_adj]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(liftMatching_adj G S M v z).mpr hz.1, hz.2⟩
    · rintro ⟨hwM, hwR⟩
      have hwS : w ∉ S := liftMatching_verts_subset G S M
        ((liftMatching G S M).edge_vert ((liftMatching G S M).symm hwM))
      exact ⟨⟨w, hwS⟩, ⟨(liftMatching_adj G S M v ⟨w, hwS⟩).mp hwM, hwR⟩, rfl⟩
  simp only [← SimpleGraph.card_neighborFinset_eq_degree]
  rw [← himage, Finset.card_image_of_injective _ Subtype.val_injective]

theorem liftMatching_reserve_degree_zero (G R : SimpleGraph V) (S : Finset V)
    (M : (G.induce (↑S : Set V)ᶜ).Subgraph) (v : V) (hv : v ∈ S) :
    ((liftMatching G S M).spanningCoe ⊓ R).degree v = 0 := by
  classical
  apply (((liftMatching G S M).spanningCoe ⊓ R).degree_eq_zero_iff_notMem_support v).mpr
  rintro ⟨w, hw⟩
  exact liftMatching_verts_subset G S M ((liftMatching G S M).edge_vert hw.1) hv

theorem liftMatching_reserve_sum (G R : SimpleGraph V) (S : Finset V)
    (M : (G.induce (↑S : Set V)ᶜ).Subgraph) :
    (∑ v : V, ((liftMatching G S M).spanningCoe ⊓ R).degree v) =
      ∑ v : Remaining S, (M.spanningCoe ⊓ R.induce (↑S : Set V)ᶜ).degree v := by
  classical
  let f := fun v => ((liftMatching G S M).spanningCoe ⊓ R).degree v
  have hsum : (∑ v ∈ Sᶜ, f v) = ∑ v : V, f v := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    exact liftMatching_reserve_degree_zero G R S M v (by simpa using hv)
  calc
    _ = ∑ v ∈ Sᶜ, f v := hsum.symm
    _ = ∑ v : Remaining S, f v.val :=
      Finset.sum_subtype Sᶜ (fun _ => Finset.mem_compl) f
    _ = _ := Finset.sum_congr rfl (fun v _ => liftMatching_reserve_degree G R S M v)

variable [DecidableEq V]

set_option maxHeartbeats 800000 in
/-- Complete the actual working matching outside the forbidden set. The
available graph `P` may already have all previously used edges removed.
Protected vertices remain in the paired cut and receive no reserve edge. -/
theorem exists_completion_outside_set
    (G R P : SimpleGraph V) (hPR : P ≤ R) (hPG : P ≤ G)
    (M : G.Subgraph) (hM : M.IsMatching) (S : Finset V)
    (hMS : M.verts ⊆ (↑S : Set V)ᶜ) (hMR : Disjoint M.spanningCoe R)
    (e : A ⊕ B ≃ Remaining S) (hbalance : Fintype.card A = Fintype.card B)
    (hleftM : ∀ a a' : A, ¬M.Adj (e (.inl a)).val (e (.inl a')).val)
    (hrightM : ∀ b b' : B, ¬M.Adj (e (.inr b)).val (e (.inr b')).val)
    (Q : SimpleGraph (A ⊕ B)) [DecidableRel Q.Adj]
    (hQP : Q ≤ (P.induce (↑S : Set V)ᶜ).comap e)
    (Z : Finset V) (hZ : ∀ v ∈ Z, v ∈ M.verts)
    (θ τ δ : ℝ) (hθ : 0 < θ) (hτ : 0 < τ) (hδ : 2 * τ ≤ δ)
    (hleft : ∀ a, δ * Fintype.card A ≤ ((rightNeighbors Q a).card : ℝ))
    (hright : ∀ b, δ * Fintype.card A ≤ ((leftNeighbors Q b).card : ℝ))
    (hexpand : IsBipartiteRobustExpander Q θ τ)
    (ℓ : ℕ) (hℓ : Nat.ceil (2 / θ) + 2 ≤ ℓ)
    (hbudget : (2 : ℝ) * Z.card + ℓ * (uncoveredOutside G M S).card ≤
      min θ δ * Fintype.card A / 2 - 1) :
    ∃ N : G.Subgraph,
      N.IsMatching ∧ N.verts = (↑S : Set V)ᶜ ∧
      (∀ v w, N.Adj v w → M.Adj v w ∨ P.Adj v w) ∧
      (∀ v ∈ S ∪ Z, (N.spanningCoe ⊓ R).degree v = 0) ∧
      (∀ v, (N.spanningCoe ⊓ R).degree v ≤ 1) ∧
      (∑ v, (N.spanningCoe ⊓ R).degree v) ≤
        ℓ * (uncoveredOutside G M S).card := by
  classical
  let M' := restrictMatching G M S
  let Z' : Finset (Remaining S) := univ.filter (fun v => v.val ∈ Z)
  have hZ'card : Z'.card = Z.card := by
    have himage : Z'.image Subtype.val = Z := by
      ext v
      simp only [Finset.mem_image, Z', Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hv
        exact ⟨⟨v, hMS (hZ v hv)⟩, hv, rfl⟩
    rw [← himage, Finset.card_image_of_injective _ Subtype.val_injective]
  have hZ' : ∀ v ∈ Z', v ∈ M'.verts := by
    intro v hv
    exact hZ v.val (Finset.mem_filter.mp hv).2
  have hMR' : Disjoint M'.spanningCoe (R.induce (↑S : Set V)ᶜ) := by
    apply disjoint_iff_inf_le.mpr
    intro v w h
    exact hMR.le_bot ⟨h.1, h.2⟩
  have hQR : Q ≤ (R.induce (↑S : Set V)ᶜ).comap e :=
    fun _ _ h => hPR (hQP h)
  have hQG : Q ≤ (G.induce (↑S : Set V)ᶜ).comap e :=
    fun _ _ h => hPG (hQP h)
  have hbudget' : (2 : ℝ) * Z'.card + ℓ * M'.vertsᶜ.ncard ≤
      min θ δ * Fintype.card A / 2 - 1 := by
    rw [hZ'card, restrictMatching_uncovered_card]
    exact hbudget
  obtain ⟨N, hN, hNverts, hedges, hzero, hdegree, hsum⟩ :=
    exists_completion_of_balanced_cut (G.induce (↑S : Set V)ᶜ)
      (R.induce (↑S : Set V)ᶜ) M' (restrictMatching_isMatching G M hM S hMS)
      e hbalance hleftM hrightM hMR' Q hQR hQG Z' hZ'
      θ τ δ hθ hτ hδ hleft hright hexpand ℓ hℓ hbudget'
  refine ⟨liftMatching G S N, liftMatching_isMatching G S N hN, ?_, ?_, ?_, ?_, ?_⟩
  · apply Set.Subset.antisymm (liftMatching_verts_subset G S N)
    intro v hv
    refine ⟨⟨v, hv⟩, ?_, rfl⟩
    rw [hNverts]
    trivial
  · rintro v w ⟨a, b, hab, rfl, rfl⟩
    rcases hedges a b hab with h | h
    · exact Or.inl h
    · apply Or.inr
      have hh := hQP h
      simpa only [SimpleGraph.comap_adj, e.apply_symm_apply] using hh
  · intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact liftMatching_reserve_degree_zero G R S N v hv
    · let w : Remaining S := ⟨v, hMS (hZ v hv)⟩
      have hw : w ∈ Z' := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
      have hd := liftMatching_reserve_degree G R S N w
      have hz := hzero w hw
      simp only [← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] at hd hz ⊢
      exact hd.trans hz
  · intro v
    by_cases hv : v ∈ S
    · rw [liftMatching_reserve_degree_zero G R S N v hv]
      omega
    · have hd := liftMatching_reserve_degree G R S N ⟨v, hv⟩
      have hdeg := hdegree ⟨v, hv⟩
      simp only [← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] at hd hdeg ⊢
      exact hd.le.trans hdeg
  · have hs := liftMatching_reserve_sum G R S N
    simp only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] at hs hsum ⊢
    rw [hs]
    simp only [M', restrictMatching_uncovered_card] at hsum
    convert hsum using 1
    congr 1
    ext v
    simp

end Overfull.OrdinaryMatchingCompletion
