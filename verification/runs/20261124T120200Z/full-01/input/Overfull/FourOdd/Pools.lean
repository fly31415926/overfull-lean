import Overfull.CompatibleCircuits.FourLabel
import Overfull.CompatibleCircuits.Lifting
import Overfull.SparseColoring

/-!
# The six actual joining-edge pools

Pools are fibers of the actual unordered label pair, with original copies
retained. Their disjointness, exact covers, projected degree counts, and
parity transfers are finite identities. Restricting the original graph to
one pool gives an actual bipartite multigraph.
-/

noncomputable section

namespace Overfull.FourOdd

open Finset Classical Compression
open scoped BigOperators

variable {E : Type*} [Fintype E] (Q : Multigraph (Fin 4) E)

def pairPool (p : LabelPair) : Finset E :=
  univ.filter (fun e => Q.edgeLabelPair e = p)

@[simp] theorem mem_pairPool (p : LabelPair) (e : E) :
    e ∈ pairPool Q p ↔ Q.edgeLabelPair e = p := by
  simp [pairPool]

theorem pairPool_disjoint {p q : LabelPair} (hpq : p ≠ q) :
    Disjoint (pairPool Q p) (pairPool Q q) := by
  apply disjoint_left.mpr
  intro e hp hq
  exact hpq (((mem_pairPool Q p e).mp hp).symm.trans ((mem_pairPool Q q e).mp hq))

theorem biUnion_pairPool (P : Finset LabelPair) :
    P.biUnion (pairPool Q) = univ.filter (fun e => Q.edgeLabelPair e ∈ P) := by
  ext e
  simp only [mem_biUnion, mem_pairPool, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨p, hp, he⟩
    rwa [he]
  · intro he
    exact ⟨Q.edgeLabelPair e, he, rfl⟩

theorem pairPool_cover : (univ : Finset LabelPair).biUnion (pairPool Q) = univ := by
  rw [biUnion_pairPool]
  simp

theorem biUnion_pairPool_disjoint {P R : Finset LabelPair} (hPR : Disjoint P R) :
    Disjoint (P.biUnion (pairPool Q)) (R.biUnion (pairPool Q)) := by
  rw [biUnion_pairPool, biUnion_pairPool]
  apply disjoint_left.mpr
  intro e heP heR
  exact disjoint_left.mp hPR (mem_filter.mp heP).2 (mem_filter.mp heR).2

theorem inter_pairPool_eq_filter (C : Finset E) (p : LabelPair) :
    C ∩ pairPool Q p = C.filter (fun e => Q.edgeLabelPair e = p) := by
  ext e
  simp

theorem image_subset_pairPool {C : Finset E} {p : LabelPair}
    (hC : C ⊆ pairPool Q p) : C.image Q.edgeLabelPair ⊆ {p} := by
  intro q hq
  obtain ⟨e, he, rfl⟩ := mem_image.mp hq
  exact mem_singleton.mpr ((mem_pairPool Q p e).mp (hC he))

theorem image_eq_singleton_of_subset_pairPool {C : Finset E} {p : LabelPair}
    (hC : C ⊆ pairPool Q p) (hne : C.Nonempty) : C.image Q.edgeLabelPair = {p} := by
  apply subset_antisymm (image_subset_pairPool Q hC)
  intro q hq
  have hqp : q = p := mem_singleton.mp hq
  subst q
  obtain ⟨e, he⟩ := hne
  exact mem_image.mpr ⟨e, he, (mem_pairPool Q p e).mp (hC he)⟩

theorem degreeOn_eq_sum_pairPool (C : Finset E) (i : Fin 4) :
    Q.degreeOn C i =
      ∑ p ∈ univ.filter (fun p : LabelPair => i ∈ p.val), (C ∩ pairPool Q p).card := by
  have hf := (sum_card_fiberwise_eq_card_filter C
    (univ.filter (fun p : LabelPair => i ∈ p.val)) Q.edgeLabelPair).symm
  simp only [← inter_pairPool_eq_filter Q] at hf
  simp only [mem_filter, mem_univ, true_and, Multigraph.mem_edgeLabelPair] at hf
  unfold Multigraph.degreeOn
  convert hf using 1
  congr 1
  ext e
  simp

theorem degree_eq_sum_pairPool (i : Fin 4) :
    Q.degree i =
      ∑ p ∈ univ.filter (fun p : LabelPair => i ∈ p.val), (pairPool Q p).card := by
  simpa [Multigraph.degreeOn, Multigraph.degree, Multigraph.incidenceEdges] using
    degreeOn_eq_sum_pairPool Q univ i

theorem degreeOn_pairPool (p : LabelPair) (i : Fin 4) :
    Q.degreeOn (pairPool Q p) i = if i ∈ p.val then (pairPool Q p).card else 0 := by
  have hfilter : (pairPool Q p).filter (fun e => i ∈ Q.edge e) =
      if i ∈ p.val then pairPool Q p else ∅ := by
    ext e
    have he : e ∈ pairPool Q p → (i ∈ Q.edge e ↔ i ∈ p.val) := by
      intro he
      rw [← Q.mem_edgeLabelPair e i, (mem_pairPool Q p e).mp he]
    by_cases hi : i ∈ p.val <;> simp only [hi, if_true, if_false, mem_filter, notMem_empty]
    · exact ⟨And.left, fun h => ⟨h, (he h).mpr hi⟩⟩
    · constructor
      · intro h
        exact hi ((he h.1).mp h.2)
      · intro h
        exact False.elim h
  unfold Multigraph.degreeOn
  calc
    _ = ((pairPool Q p).filter (fun e => i ∈ Q.edge e)).card := by
      congr 1
      ext e
      simp
    _ = _ := by rw [hfilter]; split_ifs <;> simp

/-- Selections contained in different pools retain exact pool membership. -/
theorem inter_biUnion_selected_pairPool (S : LabelPair → Finset E)
    (hS : ∀ p, S p ⊆ pairPool Q p) (p : LabelPair) :
    ((univ : Finset LabelPair).biUnion S) ∩ pairPool Q p = S p := by
  ext e
  constructor
  · intro he
    obtain ⟨heU, hep⟩ := mem_inter.mp he
    obtain ⟨q, _, heq⟩ := mem_biUnion.mp heU
    have hqp : q = p :=
      ((mem_pairPool Q q e).mp (hS q heq)).symm.trans ((mem_pairPool Q p e).mp hep)
    simpa only [hqp] using heq
  · intro he
    exact mem_inter.mpr ⟨mem_biUnion.mpr ⟨p, mem_univ _, he⟩, hS p he⟩

theorem selected_pairPool_disjoint (S : LabelPair → Finset E)
    (hS : ∀ p, S p ⊆ pairPool Q p) {p q : LabelPair} (hpq : p ≠ q) :
    Disjoint (S p) (S q) :=
  (pairPool_disjoint Q hpq).mono (hS p) (hS q)

theorem card_biUnion_selected_pairPool (S : LabelPair → Finset E)
    (hS : ∀ p, S p ⊆ pairPool Q p) :
    ((univ : Finset LabelPair).biUnion S).card = ∑ p : LabelPair, (S p).card := by
  apply card_biUnion
  intro p _ q _ hpq
  exact selected_pairPool_disjoint Q S hS hpq

theorem degreeOn_selected_pairPool (S : LabelPair → Finset E)
    (hS : ∀ p, S p ⊆ pairPool Q p) (i : Fin 4) :
    Q.degreeOn ((univ : Finset LabelPair).biUnion S) i =
      ∑ p ∈ univ.filter (fun p : LabelPair => i ∈ p.val), (S p).card := by
  rw [degreeOn_eq_sum_pairPool]
  apply sum_congr rfl
  intro p _
  rw [inter_biUnion_selected_pairPool Q S hS]

theorem selected_pairPool_degree_parity (S : LabelPair → Finset E)
    (hS : ∀ p, S p ⊆ pairPool Q p)
    (hpar : ∀ p, (S p).card % 2 = (pairPool Q p).card % 2) (i : Fin 4) :
    Q.degreeOn ((univ : Finset LabelPair).biUnion S) i % 2 = Q.degree i % 2 := by
  rw [degreeOn_selected_pairPool Q S hS, degree_eq_sum_pairPool]
  rw [sum_nat_mod _ 2 (fun p => (S p).card),
    sum_nat_mod _ 2 (fun p => (pairPool Q p).card)]
  congr 1
  exact sum_congr rfl (fun p _ => hpar p)

theorem pairPool_sdiff_selected_cover (S : LabelPair → Finset E)
    (hS : ∀ p, S p ⊆ pairPool Q p) :
    (univ : Finset LabelPair).biUnion (fun p => pairPool Q p \ S p) =
      univ \ (univ : Finset LabelPair).biUnion S := by
  ext e
  constructor
  · intro he
    obtain ⟨p, _, he⟩ := mem_biUnion.mp he
    obtain ⟨heP, heS⟩ := mem_sdiff.mp he
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    intro heU
    obtain ⟨q, _, heq⟩ := mem_biUnion.mp heU
    have hqp : q = p :=
      ((mem_pairPool Q q e).mp (hS q heq)).symm.trans ((mem_pairPool Q p e).mp heP)
    exact heS (hqp ▸ heq)
  · intro he
    refine mem_biUnion.mpr ⟨Q.edgeLabelPair e, mem_univ _, mem_sdiff.mpr ⟨?_, ?_⟩⟩
    · exact (mem_pairPool Q _ e).mpr rfl
    · intro heS
      exact (mem_sdiff.mp he).2 (mem_biUnion.mpr ⟨Q.edgeLabelPair e, mem_univ _, heS⟩)

variable {V : Type*} (G : Multigraph V E)

theorem restrictEdges_degree_eq_degreeOn (S : Finset E) (v : V) :
    (G.restrictEdges S).degree v = G.degreeOn S v := by
  rw [G.restrictEdges_degree]
  unfold Multigraph.degreeOn
  congr 1
  ext e
  simp

theorem degreeOn_le_degree (S : Finset E) (v : V) :
    G.degreeOn S v ≤ G.degree v := by
  apply card_le_card
  intro e he
  exact (G.mem_incidenceEdges v e).mpr (mem_filter.mp he).2

theorem restrictEdges_degree_le_original (S : Finset E) (v : V) :
    (G.restrictEdges S).degree v ≤ G.degree v := by
  rw [restrictEdges_degree_eq_degreeOn]
  exact degreeOn_le_degree G S v

omit [Fintype E] in
theorem labelQuotient_edgeLabelPair_val (label : V → Fin 4)
    (hjoin : ∀ e, label (G.firstEnd e) ≠ label (G.secondEnd e)) (e : E) :
    ((G.labelQuotient label hjoin).edgeLabelPair e).val =
      {label (G.firstEnd e), label (G.secondEnd e)} := by
  simp [Multigraph.edgeLabelPair, Multigraph.labelQuotient, Sym2.toFinset_mk_eq]

/-- Every actual pair pool is bipartite in the original vertex graph. -/
theorem pairPool_bipartite (label : V → Fin 4)
    (hjoin : ∀ e, label (G.firstEnd e) ≠ label (G.secondEnd e)) (p : LabelPair) :
    (G.restrictEdges (pairPool (G.labelQuotient label hjoin) p)).IsBipartite := by
  obtain ⟨i, j, hij, hp⟩ := card_eq_two.mp p.property
  refine ⟨fun v => decide (label v = i), ?_⟩
  intro e
  change decide (label (G.firstEnd e.val) = i) ≠ decide (label (G.secondEnd e.val) = i)
  have he := (mem_pairPool (G.labelQuotient label hjoin) p e.val).mp e.property
  have hends : ({label (G.firstEnd e.val), label (G.secondEnd e.val)} : Finset (Fin 4)) = {i, j} := by
    rw [← labelQuotient_edgeLabelPair_val G label hjoin, he, hp]
  have hf : label (G.firstEnd e.val) = i ∨ label (G.firstEnd e.val) = j := by
    have hm : label (G.firstEnd e.val) ∈ ({i, j} : Finset (Fin 4)) := by
      rw [← hends]
      simp
    simpa only [mem_insert, mem_singleton] using hm
  have hs : label (G.secondEnd e.val) = i ∨ label (G.secondEnd e.val) = j := by
    have hm : label (G.secondEnd e.val) ∈ ({i, j} : Finset (Fin 4)) := by
      rw [← hends]
      simp
    simpa only [mem_insert, mem_singleton] using hm
  have hn := hjoin e.val
  rcases hf with hf | hf <;> rcases hs with hs | hs <;> simp_all [eq_comm]

end Overfull.FourOdd
