import Overfull.ColorCoverage
import Overfull.TwoColorEndpoints
import Overfull.TutteBerge.Matching

/-!
# Extending the covered set of a matching

Two actual matchings are encoded by two colors, with shared edges represented
by parallel copies. Component interchanges preserve properness and give a
maximum matching covering every vertex of the original matching.
-/

namespace Overfull.MatchingExtension

open Finset Classical SimpleGraph
open scoped BigOperators

variable {V : Type*} (G : SimpleGraph V)

/-- Two edges of a matching that share a vertex are the same edge. -/
theorem matching_edge_eq {M : G.Subgraph} (hM : M.IsMatching)
    (e f : M.edgeSet) {v : V} (he : v ∈ e.val) (hf : v ∈ f.val) : e = f := by
  apply Subtype.ext
  rcases e with ⟨e, heM⟩
  rcases f with ⟨f, hfM⟩
  induction e using Sym2.ind with
  | h a b =>
    induction f using Sym2.ind with
    | h x y =>
      simp only [Sym2.mem_iff] at he hf
      rcases he with rfl | rfl
      · rcases hf with rfl | rfl
        · have h : b = y := hM.eq_of_adj_left heM hfM
          exact Sym2.eq_iff.mpr (Or.inl ⟨rfl, h⟩)
        · have h : b = x := hM.eq_of_adj_left heM hfM.symm
          exact Sym2.eq_iff.mpr (Or.inr ⟨rfl, h⟩)
      · rcases hf with rfl | rfl
        · have h : a = y := hM.eq_of_adj_left heM.symm hfM
          exact Sym2.eq_iff.mpr (Or.inr ⟨h, rfl⟩)
        · have h : a = x := hM.eq_of_adj_right heM hfM
          exact Sym2.eq_iff.mpr (Or.inl ⟨h, rfl⟩)

/-- The two matchings retain separate copies even where their edges coincide. -/
def pairGraph (M N : G.Subgraph) : Multigraph V (M.edgeSet ⊕ N.edgeSet) where
  edge e := match e with
    | .inl e => e.val
    | .inr e => e.val
  loopless e := by
    cases e with
    | inl e => exact G.not_isDiag_of_mem_edgeSet (M.edgeSet_subset e.property)
    | inr e => exact G.not_isDiag_of_mem_edgeSet (N.edgeSet_subset e.property)

def pairColoring (M N : G.Subgraph) (hM : M.IsMatching) (hN : N.IsMatching) :
    (pairGraph G M N).EdgeColoring 2 where
  color e := match e with
    | .inl _ => 0
    | .inr _ => 1
  proper := by
    intro e f v hef hev hfv
    cases e with
    | inl e =>
      cases f with
      | inl f => exact congrArg Sum.inl (matching_edge_eq G hM e f hev hfv)
      | inr f => norm_num at hef
    | inr e =>
      cases f with
      | inl f => norm_num at hef
      | inr f => exact congrArg Sum.inr (matching_edge_eq G hN e f hev hfv)

theorem pairColoring_covers_zero (M N : G.Subgraph) (hM : M.IsMatching) (hN : N.IsMatching)
    (v : V) : (pairColoring G M N hM hN).Covers 0 v ↔ v ∈ M.verts := by
  constructor
  · rintro ⟨e, he, hev⟩
    cases e with
    | inl e => exact Subgraph.mem_verts_of_mem_edge e.property hev
    | inr e => norm_num [pairColoring] at he
  · intro hv
    obtain ⟨w, hvw, _⟩ := hM hv
    exact ⟨.inl ⟨s(v,w), hvw⟩, rfl, by simp [pairGraph]⟩

theorem pairColoring_covers_one (M N : G.Subgraph) (hM : M.IsMatching) (hN : N.IsMatching)
    (v : V) : (pairColoring G M N hM hN).Covers 1 v ↔ v ∈ N.verts := by
  constructor
  · rintro ⟨e, he, hev⟩
    cases e with
    | inl e => norm_num [pairColoring] at he
    | inr e => exact Subgraph.mem_verts_of_mem_edge e.property hev
  · intro hv
    obtain ⟨w, hvw, _⟩ := hN hv
    exact ⟨.inr ⟨s(v,w), hvw⟩, rfl, by simp [pairGraph]⟩

private theorem edge_pair_of_incident {E : Type*} (H : Multigraph V E) (e : E)
    (v : V) (hv : v ∈ H.edge e) : ∃ w, H.edge e = s(v,w) := by
  rcases (H.incident_iff e v).mp hv with hv | hv
  · exact ⟨H.secondEnd e, by rw [← H.edge_eq e, hv]⟩
  · exact ⟨H.firstEnd e, by rw [← H.edge_eq e, hv, Sym2.eq_swap]⟩

/-- A color class of actual copies whose underlying edges lie in `G`
defines an actual matching subgraph of `G`. -/
def colorMatching {E : Type*} (H : Multigraph V E) {q : ℕ} (c : H.EdgeColoring q)
    (hedges : ∀ e, H.edge e ∈ G.edgeSet) (i : Fin q) : G.Subgraph where
  verts v := c.Covers i v
  Adj v w := ∃ e, c.color e = i ∧ H.edge e = s(v,w)
  adj_sub := by
    rintro v w ⟨e, he, heq⟩
    have h := hedges e
    rwa [heq, SimpleGraph.mem_edgeSet] at h
  edge_vert := by
    rintro v w ⟨e, he, heq⟩
    exact ⟨e, he, by rw [heq]; simp⟩
  symm := by
    rintro v w ⟨e, he, heq⟩
    exact ⟨e, he, heq.trans Sym2.eq_swap⟩

theorem colorMatching_isMatching {E : Type*} (H : Multigraph V E) {q : ℕ}
    (c : H.EdgeColoring q) (hedges : ∀ e, H.edge e ∈ G.edgeSet) (i : Fin q) :
    (colorMatching G H c hedges i).IsMatching := by
  intro v hv
  obtain ⟨e, he, hev⟩ := hv
  obtain ⟨w, hew⟩ := edge_pair_of_incident H e v hev
  refine ⟨w, ⟨e, he, hew⟩, ?_⟩
  rintro w' ⟨f, hf, hfw⟩
  have hef : e = f := c.proper (he.trans hf.symm) hev (by rw [hfw]; simp)
  subst f
  have hpair := Sym2.eq_iff.mp (hfw.symm.trans hew)
  rcases hpair with h | h
  · exact h.2
  · exact h.2.trans h.1

theorem pairGraph_edges (M N : G.Subgraph) (e : M.edgeSet ⊕ N.edgeSet) :
    (pairGraph G M N).edge e ∈ G.edgeSet := by
  cases e with
  | inl e => exact M.edgeSet_subset e.property
  | inr e => exact N.edgeSet_subset e.property

variable [Fintype V]

private theorem component_transfer_nonneg {E : Type*} [Fintype E]
    (H : Multigraph V E) {q : ℕ} (c : H.EdgeColoring q) (i j : Fin q) (hij : i ≠ j)
    (C : (c.twoColorGraph i j).ConnectedComponent) (x : V)
    (hx : x ∈ c.componentVertices i j C) (hxi : c.Covers i x) (hxj : ¬ c.Covers j x) :
    0 ≤ c.transfer i j univ (c.componentVertices i j C) := by
  let P := c.componentEndpoints i j C
  have hxP : x ∈ P := Finset.mem_filter.mpr ⟨hx, Or.inl ⟨hxi, hxj⟩⟩
  have hcard : (P.erase x).card ≤ 1 := by
    have h : P.card ≤ 2 := c.componentEndpoints_card_le_two i j hij C
    have h' := Finset.card_erase_add_one hxP
    omega
  have heq : c.transfer i j univ (c.componentVertices i j C) =
      ∑ v ∈ P, (c.coverIndicator i v - c.coverIndicator j v) := by
    rw [c.transfer_eq_sum]
    simp only [Finset.mem_univ, if_true]
    rw [show P = (c.componentVertices i j C).filter (fun v =>
      (c.Covers i v ∧ ¬ c.Covers j v) ∨ (c.Covers j v ∧ ¬ c.Covers i v)) from rfl,
      Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hi : c.Covers i v <;> by_cases hj : c.Covers j v <;>
      simp [Multigraph.EdgeColoring.coverIndicator, hi, hj]
  have hroot : c.coverIndicator i x - c.coverIndicator j x = 1 := by
    simp [Multigraph.EdgeColoring.coverIndicator, hxi, hxj]
  have hlow : -((P.erase x).card : ℤ) ≤
      ∑ v ∈ P.erase x, (c.coverIndicator i v - c.coverIndicator j v) := by
    calc
      _ = ∑ _v ∈ P.erase x, (-1 : ℤ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro v _
        by_cases hi : c.Covers i v <;> by_cases hj : c.Covers j v <;>
          simp [Multigraph.EdgeColoring.coverIndicator, hi, hj]
  have hsum := Finset.sum_erase_add P (fun v => c.coverIndicator i v - c.coverIndicator j v) hxP
  have hcardZ : ((P.erase x).card : ℤ) ≤ 1 := by exact_mod_cast hcard
  simp only [hroot] at hsum
  rw [heq]
  omega

/-- A maximum matching can retain every vertex covered by a prescribed
matching. The conclusion is an actual matching and an actual maximum-edge
comparison, without an assumed augmenting-path theorem. -/
theorem exists_maximum_covering (M₀ : G.Subgraph) (hM₀ : M₀.IsMatching) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M₀.verts ⊆ M.verts ∧
      ∀ N : G.Subgraph, N.IsMatching →
        N.spanningCoe.edgeFinset.card ≤ M.spanningCoe.edgeFinset.card := by
  let S : Finset G.Subgraph := univ.filter Subgraph.IsMatching
  have hS : S.Nonempty := ⟨M₀, Finset.mem_filter.mpr ⟨Finset.mem_univ M₀, hM₀⟩⟩
  obtain ⟨K, hKS, hmax⟩ := Finset.exists_max_image S
    (fun M => M.verts.toFinset.card) hS
  let T : Finset G.Subgraph := S.filter (fun M => M.verts.toFinset.card = K.verts.toFinset.card)
  have hT : T.Nonempty := ⟨K, Finset.mem_filter.mpr ⟨hKS, rfl⟩⟩
  obtain ⟨M, hMT, hcovermax⟩ := Finset.exists_max_image T
    (fun M => (M₀.verts.toFinset ∩ M.verts.toFinset).card) hT
  have hMS : M ∈ S := (Finset.mem_filter.mp hMT).1
  have hM : M.IsMatching := (Finset.mem_filter.mp hMS).2
  have hMK : M.verts.toFinset.card = K.verts.toFinset.card := (Finset.mem_filter.mp hMT).2
  have hmaxV (N : G.Subgraph) (hN : N.IsMatching) :
      N.verts.toFinset.card ≤ M.verts.toFinset.card := by
    rw [hMK]
    exact hmax N (Finset.mem_filter.mpr ⟨Finset.mem_univ N, hN⟩)
  have hcover : M₀.verts ⊆ M.verts := by
    intro x hx₀
    by_contra hxM
    let H := pairGraph G M₀ M
    let c := pairColoring G M₀ M hM₀ hM
    have hx0 : c.Covers 0 x := (pairColoring_covers_zero G M₀ M hM₀ hM x).mpr hx₀
    have hx1 : ¬ c.Covers 1 x := fun h =>
      hxM ((pairColoring_covers_one G M₀ M hM₀ hM x).mp h)
    let C := (c.twoColorGraph 0 1).connectedComponentMk x
    let X := c.componentVertices 0 1 C
    have hxX : x ∈ X := by
      rw [c.mem_componentVertices, SimpleGraph.ConnectedComponent.mem_supp_iff]
    let c' := c.swapOn 0 1 X (c.component_closed 0 1 C)
    let N := colorMatching G H c' (pairGraph_edges G M₀ M) 1
    have hN : N.IsMatching := colorMatching_isMatching G H c' (pairGraph_edges G M₀ M) 1
    have hMverts : c.coveredVertices 1 = M.verts.toFinset := by
      ext v
      simp only [Multigraph.EdgeColoring.mem_coveredVertices, Set.mem_toFinset]
      exact pairColoring_covers_one G M₀ M hM₀ hM v
    have hNverts : c'.coveredVertices 1 = N.verts.toFinset := by
      ext v
      simp only [Multigraph.EdgeColoring.mem_coveredVertices, Set.mem_toFinset]
      rfl
    have htransfer := component_transfer_nonneg H c 0 1 (by decide) C x hxX hx0 hx1
    change 0 ≤ c.transfer 0 1 univ X at htransfer
    have hcount := c.swapOn_coveredCount_right 0 1 X (c.component_closed 0 1 C) univ
    change c'.coveredCount univ 1 = c.coveredCount univ 1 + c.transfer 0 1 univ X at hcount
    rw [c'.coveredCount_univ, c.coveredCount_univ, hMverts, hNverts] at hcount
    have hcountN : M.verts.toFinset.card ≤ N.verts.toFinset.card := by
      have hz : (M.verts.toFinset.card : ℤ) ≤ N.verts.toFinset.card := by omega
      exact_mod_cast hz
    have hNcard : N.verts.toFinset.card = M.verts.toFinset.card :=
      le_antisymm (hmaxV N hN) hcountN
    have hNT : N ∈ T := Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ N, hN⟩, hNcard.trans hMK⟩
    have hretain : M₀.verts.toFinset ∩ M.verts.toFinset ⊆
        M₀.verts.toFinset ∩ N.verts.toFinset := by
      intro v hv
      obtain ⟨hv₀, hvM⟩ := Finset.mem_inter.mp hv
      apply Finset.mem_inter.mpr
      refine ⟨hv₀, ?_⟩
      rw [Set.mem_toFinset]
      change c'.Covers 1 v
      apply (c.swapOn_covers 0 1 1 X (c.component_closed 0 1 C) v).mpr
      by_cases hvX : v ∈ X
      · rw [if_pos hvX, Equiv.swap_apply_right]
        exact (pairColoring_covers_zero G M₀ M hM₀ hM v).mpr (Set.mem_toFinset.mp hv₀)
      · rw [if_neg hvX]
        exact (pairColoring_covers_one G M₀ M hM₀ hM v).mpr (Set.mem_toFinset.mp hvM)
    have hxN : x ∈ M₀.verts.toFinset ∩ N.verts.toFinset := by
      apply Finset.mem_inter.mpr
      refine ⟨Set.mem_toFinset.mpr hx₀, ?_⟩
      rw [Set.mem_toFinset]
      change c'.Covers 1 x
      apply (c.swapOn_covers 0 1 1 X (c.component_closed 0 1 C) x).mpr
      rw [if_pos hxX, Equiv.swap_apply_right]
      exact hx0
    have hxnot : x ∉ M₀.verts.toFinset ∩ M.verts.toFinset := by
      intro h
      exact hxM (Set.mem_toFinset.mp (Finset.mem_inter.mp h).2)
    have hstrict : (M₀.verts.toFinset ∩ M.verts.toFinset).card <
        (M₀.verts.toFinset ∩ N.verts.toFinset).card := by
      apply Finset.card_lt_card
      exact Finset.ssubset_iff_subset_ne.mpr ⟨hretain, fun h => hxnot (h ▸ hxN)⟩
    have hnot := hcovermax N hNT
    omega
  refine ⟨M, hM, hcover, ?_⟩
  intro N hN
  have hcard := hmaxV N hN
  have hMsize := TutteBerge.matching_vertices_card G M hM
  have hNsize := TutteBerge.matching_vertices_card G N hN
  simp only [Set.toFinset_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at hcard
  omega

private theorem matching_cover_subset [DecidableRel G.Adj]
    (Z : Finset V) (hdegree : ∀ v ∈ Z, 2 * Z.card < G.degree v)
    (S : Finset V) (hSZ : S ⊆ Z) :
    ∃ M : G.Subgraph, M.IsMatching ∧ (↑S : Set V) ⊆ M.verts ∧
      M.verts.toFinset.card ≤ 2 * S.card := by
  revert hSZ
  induction S using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨⊥, ?_, ?_, ?_⟩
    · intro v hv
      simp at hv
    · simp
    · simp
  | @insert v S hvS ih =>
    intro hSZ
    have hS : S ⊆ Z := fun u hu => hSZ (Finset.mem_insert_of_mem hu)
    have hvZ : v ∈ Z := hSZ (Finset.mem_insert_self v S)
    obtain ⟨M, hM, hcover, hcard⟩ := ih hS
    by_cases hvM : v ∈ M.verts
    · refine ⟨M, hM, ?_, ?_⟩
      · intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact hvM
        · exact hcover hu
      · rw [Finset.card_insert_of_notMem hvS]
        omega
    · have hsize : M.verts.toFinset.card < (G.neighborFinset v).card := by
        rw [G.card_neighborFinset_eq_degree]
        exact hcard.trans_lt ((Nat.mul_le_mul_left 2 (Finset.card_le_card hS)).trans_lt
          (hdegree v hvZ))
      obtain ⟨w, hw, hwM⟩ := Finset.exists_mem_notMem_of_card_lt_card hsize
      have hvw : G.Adj v w := (G.mem_neighborFinset v w).mp hw
      have hwM' : w ∉ M.verts := by simpa only [Set.mem_toFinset] using hwM
      have hedge : (G.subgraphOfAdj hvw).IsMatching := Subgraph.IsMatching.subgraphOfAdj hvw
      have hdisjoint : Disjoint M.support (G.subgraphOfAdj hvw).support := by
        rw [hM.support_eq_verts, hedge.support_eq_verts, G.subgraphOfAdj_verts]
        apply Set.disjoint_left.mpr
        intro u hu hu'
        rcases Set.mem_insert_iff.mp hu' with rfl | hu'
        · exact hvM hu
        · have huw : u = w := Set.mem_singleton_iff.mp hu'
          exact hwM' (huw ▸ hu)
      let N := M ⊔ G.subgraphOfAdj hvw
      have hN : N.IsMatching := hM.sup hedge hdisjoint
      have hverts : N.verts.toFinset = M.verts.toFinset ∪ {v, w} := by
        ext u
        simp [N, Subgraph.verts_sup]
      refine ⟨N, hN, ?_, ?_⟩
      · intro u hu
        change u ∈ M.verts ∪ (G.subgraphOfAdj hvw).verts
        rcases Finset.mem_insert.mp hu with rfl | hu
        · right
          rw [G.subgraphOfAdj_verts]
          simp
        · exact Or.inl (hcover hu)
      · rw [hverts, Finset.card_insert_of_notMem hvS]
        have hu := Finset.card_union_le M.verts.toFinset ({v, w} : Finset V)
        have hp : ({v, w} : Finset V).card = 2 := Finset.card_pair hvw.ne
        omega

/-- A small prescribed set can be covered greedily whenever every one of
its vertices has more than twice its size many neighbors. -/
theorem exists_matching_covering_small_set [DecidableRel G.Adj]
    (Z : Finset V) (hdegree : ∀ v ∈ Z, 2 * Z.card < G.degree v) :
    ∃ M : G.Subgraph, M.IsMatching ∧ (↑Z : Set V) ⊆ M.verts := by
  obtain ⟨M, hM, hcover, _⟩ := matching_cover_subset G Z hdegree Z (Finset.Subset.refl Z)
  exact ⟨M, hM, hcover⟩

/-- The maximum matching needed in Step 2 of adaptive packing: all
prescribed saturated vertices remain covered. -/
theorem exists_maximum_covering_small_set [DecidableRel G.Adj]
    (Z : Finset V) (hdegree : ∀ v ∈ Z, 2 * Z.card < G.degree v) :
    ∃ M : G.Subgraph, M.IsMatching ∧ (↑Z : Set V) ⊆ M.verts ∧
      ∀ N : G.Subgraph, N.IsMatching →
        N.spanningCoe.edgeFinset.card ≤ M.spanningCoe.edgeFinset.card := by
  obtain ⟨M₀, hM₀, hcover⟩ := exists_matching_covering_small_set G Z hdegree
  obtain ⟨M, hM, hcontains, hmax⟩ := exists_maximum_covering G M₀ hM₀
  exact ⟨M, hM, hcover.trans hcontains, hmax⟩

end Overfull.MatchingExtension
