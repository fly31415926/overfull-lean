import Overfull.TwoApexFactorization.Completion

/-!
# The actual shores of an indexed bipartite core

The finite shores consist of original ambient vertices.  Degree sums for
a selected copy set follow from regularity and the genuinely bipartite
unselected graph, after the two equally saturated apices are removed.
-/

noncomputable section

namespace Overfull.TwoApexFactorization

open Finset Classical SmallCuts

variable {V E A B : Type*} [Fintype V] [Fintype E] [Fintype A] [Fintype B]
variable {G : Multigraph V E} {U : Finset V}

def leftEmbedding (e : A ⊕ B ≃ U) : A ↪ V where
  toFun a := (e (.inl a)).val
  inj' _ _ h := Sum.inl.inj (e.injective (Subtype.ext h))

def rightEmbedding (e : A ⊕ B ≃ U) : B ↪ V where
  toFun b := (e (.inr b)).val
  inj' _ _ h := Sum.inr.inj (e.injective (Subtype.ext h))

def leftShore (e : A ⊕ B ≃ U) : Finset V := univ.map (leftEmbedding e)
def rightShore (e : A ⊕ B ≃ U) : Finset V := univ.map (rightEmbedding e)

omit [Fintype V] [Fintype B] in
@[simp] theorem leftShore_card (e : A ⊕ B ≃ U) :
    (leftShore e).card = Fintype.card A := by simp [leftShore]

omit [Fintype V] [Fintype A] in
@[simp] theorem rightShore_card (e : A ⊕ B ≃ U) :
    (rightShore e).card = Fintype.card B := by simp [rightShore]

omit [Fintype V] [Fintype B] in
@[simp] theorem mem_leftShore (e : A ⊕ B ≃ U) (v : V) :
    v ∈ leftShore e ↔ ∃ a, (e (.inl a)).val = v := by
  simp [leftShore, leftEmbedding]

omit [Fintype V] [Fintype A] in
@[simp] theorem mem_rightShore (e : A ⊕ B ≃ U) (v : V) :
    v ∈ rightShore e ↔ ∃ b, (e (.inr b)).val = v := by
  simp [rightShore, rightEmbedding]

omit [Fintype V] [Fintype B] in
theorem leftShore_subset (e : A ⊕ B ≃ U) : leftShore e ⊆ U := by
  intro v hv
  obtain ⟨a, rfl⟩ := (mem_leftShore e v).mp hv
  exact (e (.inl a)).property

omit [Fintype V] [Fintype A] in
theorem rightShore_subset (e : A ⊕ B ≃ U) : rightShore e ⊆ U := by
  intro v hv
  obtain ⟨a, rfl⟩ := (mem_rightShore e v).mp hv
  exact (e (.inr a)).property

omit [Fintype V] in
theorem shores_disjoint (e : A ⊕ B ≃ U) : Disjoint (leftShore e) (rightShore e) := by
  apply Finset.disjoint_left.mpr
  intro v hvA hvB
  obtain ⟨a, ha⟩ := (mem_leftShore e v).mp hvA
  obtain ⟨b, hb⟩ := (mem_rightShore e v).mp hvB
  have h := e.injective (Subtype.ext (ha.trans hb.symm))
  exact Sum.noConfusion h

omit [Fintype V] in
theorem shores_union (e : A ⊕ B ≃ U) : leftShore e ∪ rightShore e = U := by
  apply Finset.Subset.antisymm
  · exact Finset.union_subset (leftShore_subset e) (rightShore_subset e)
  · intro v hv
    have h := e.apply_symm_apply (⟨v, hv⟩ : U)
    cases he : e.symm (⟨v, hv⟩ : U) with
    | inl a =>
      apply mem_union_left
      exact (mem_leftShore e v).mpr ⟨a, congrArg Subtype.val (he ▸ h)⟩
    | inr b =>
      apply mem_union_right
      exact (mem_rightShore e v).mpr ⟨b, congrArg Subtype.val (he ▸ h)⟩

omit [Fintype E] [Fintype B] in
theorem left_covered_card {F : Finset E} {q : ℕ}
    (c : (G.restrictEdges F).EdgeColoring q) (e : A ⊕ B ≃ U) (i : Fin q) :
    (univ.filter (fun a : A => c.Covers i (e (.inl a)).val)).card =
      (leftShore e ∩ c.coveredVertices i).card := by
  have heq : (univ.filter (fun a : A => c.Covers i (e (.inl a)).val)).map
      (leftEmbedding e) = leftShore e ∩ c.coveredVertices i := by
    ext v
    simp only [mem_map, mem_filter, mem_univ, true_and, leftEmbedding,
      Function.Embedding.coeFn_mk, mem_inter, mem_leftShore, c.mem_coveredVertices]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, rfl⟩, ha⟩
    · rintro ⟨⟨a, rfl⟩, ha⟩
      exact ⟨a, ha, rfl⟩
  rw [← heq, Finset.card_map]

omit [Fintype E] [Fintype A] in
theorem right_covered_card {F : Finset E} {q : ℕ}
    (c : (G.restrictEdges F).EdgeColoring q) (e : A ⊕ B ≃ U) (i : Fin q) :
    (univ.filter (fun b : B => c.Covers i (e (.inr b)).val)).card =
      (rightShore e ∩ c.coveredVertices i).card := by
  have heq : (univ.filter (fun b : B => c.Covers i (e (.inr b)).val)).map
      (rightEmbedding e) = rightShore e ∩ c.coveredVertices i := by
    ext v
    simp only [mem_map, mem_filter, mem_univ, true_and, rightEmbedding,
      Function.Embedding.coeFn_mk, mem_inter, mem_rightShore, c.mem_coveredVertices]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, rfl⟩, hb⟩
    · rintro ⟨⟨b, rfl⟩, hb⟩
      exact ⟨b, hb, rfl⟩
  rw [← heq, Finset.card_map]

omit [Fintype V] in
/-- A core copy crosses the ambient shore obtained from its actual
bipartite indexing, even after adding an exterior apex to that shore. -/
theorem core_copies_cross (C : Core G U) (e : A ⊕ B ≃ U) (x : V) (hx : x ∉ U)
    (hbip : (C.graph.comap e).IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr)) :
    ∀ f ∈ OneCore.coreEdges C, f ∈ G.cutEdges (insert x (leftShore e)) := by
  intro f hf
  obtain ⟨g, rfl⟩ := (OneCore.mem_coreEdges C f).mp hf
  rcases g with ⟨⟨u, v⟩, huv⟩
  have hindex : (C.graph.comap e).Adj (e.symm u) (e.symm v) := by
    simpa only [SimpleGraph.comap_adj, e.apply_symm_apply] using huv
  have hsides := hbip.mem_of_adj hindex
  rcases hsides with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ | ⟨⟨b, hb⟩, ⟨a, ha⟩⟩
  · have hua : e (.inl a) = u := by rw [ha, e.apply_symm_apply]
    have hvb : e (.inr b) = v := by rw [hb, e.apply_symm_apply]
    apply (G.mem_cutEdges_iff _ _).mpr
    refine ⟨u.val, v.val, C.map_edge _, mem_insert_of_mem ?_, ?_⟩
    · exact (mem_leftShore e u.val).mpr ⟨a, congrArg Subtype.val hua⟩
    · intro hv
      rcases mem_insert.mp hv with h | h
      · exact hx (h ▸ v.property)
      · exact Finset.disjoint_left.mp (shores_disjoint e) h
          ((mem_rightShore e v.val).mpr ⟨b, congrArg Subtype.val hvb⟩)
  · have hua : e (.inr b) = u := by rw [hb, e.apply_symm_apply]
    have hvb : e (.inl a) = v := by rw [ha, e.apply_symm_apply]
    apply (G.mem_cutEdges_iff _ _).mpr
    refine ⟨v.val, u.val, (C.map_edge _).trans Sym2.eq_swap, mem_insert_of_mem ?_, ?_⟩
    · exact (mem_leftShore e v.val).mpr ⟨a, congrArg Subtype.val hvb⟩
    · intro hu
      rcases mem_insert.mp hu with h | h
      · exact hx (h ▸ u.property)
      · exact Finset.disjoint_left.mp (shores_disjoint e) h
          ((mem_rightShore e u.val).mpr ⟨b, congrArg Subtype.val hua⟩)

/-- Summing degrees on the two parts of an actual bipartition counts
every edge copy once on each side. -/
theorem degree_sums_of_crossing (H : Multigraph V E) (L : Finset V)
    (hcross : ∀ f : E, f ∈ H.cutEdges L) :
    (∑ v ∈ L, H.degree v) = ∑ v ∈ Lᶜ, H.degree v := by
  have hleft : H.internalEdges L = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    have hs := (H.mem_cutEdges L f).mp (hcross f)
    obtain ⟨hu, hv⟩ := (H.mem_internalEdges L f).mp hf
    exact hs (propext ⟨fun _ => hv, fun _ => hu⟩)
  have hright : H.internalEdges Lᶜ = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    have hs := (H.mem_cutEdges L f).mp (hcross f)
    obtain ⟨hu, hv⟩ := (H.mem_internalEdges Lᶜ f).mp hf
    simp only [mem_compl] at hu hv
    exact hs (propext ⟨fun h => (hu h).elim, fun h => (hv h).elim⟩)
  rw [H.degree_sum_on L, H.degree_sum_on Lᶜ, hleft, hright, H.cutSize_compl]

/-- In a regular host the selected degree sums on the balanced augmented
parts agree whenever every unselected copy crosses those parts. -/
theorem selected_degree_sums (H : Multigraph V E) (L : Finset V) (F : Finset E)
    (k : ℕ) (hregular : ∀ v, H.degree v = k) (hcard : L.card = Lᶜ.card)
    (hcross : ∀ f : E, f ∉ F → f ∈ H.cutEdges L) :
    (∑ v ∈ L, (H.restrictEdges F).degree v) =
      ∑ v ∈ Lᶜ, (H.restrictEdges F).degree v := by
  have hrem := degree_sums_of_crossing (H.restrictEdges Fᶜ) L
    (by
      intro f
      simpa only [Multigraph.mem_cutEdges] using hcross f.val (mem_compl.mp f.property))
  have hsum (S : Finset V) :
      (∑ v ∈ S, (H.restrictEdges Fᶜ).degree v) +
        (∑ v ∈ S, (H.restrictEdges F).degree v) = S.card * k := by
    rw [← Finset.sum_add_distrib]
    simp only [OneCore.complement_degree_add, hregular, sum_const, smul_eq_mul]
  have hA := hsum L
  have hB := hsum Lᶜ
  rw [← hcard, ← hrem] at hB
  omega

omit [Fintype V] in
/-- The two actual shore incidence pools partition the incidences into
the core, with every parallel copy counted separately. -/
theorem side_edges_sum (H : Multigraph V E) (e : A ⊕ B ≃ U) (v : V) :
    (H.edgesTo v (leftShore e)).card + (H.edgesTo v (rightShore e)).card =
      (H.edgesTo v U).card := by
  have hdisj : Disjoint (H.edgesTo v (leftShore e)) (H.edgesTo v (rightShore e)) := by
    apply Finset.disjoint_left.mpr
    intro f hfA hfB
    exact Finset.disjoint_left.mp (shores_disjoint e)
      ((H.mem_edgesTo v _ f).mp hfA).2 ((H.mem_edgesTo v _ f).mp hfB).2
  rw [← Finset.card_union_of_disjoint hdisj]
  congr 1
  ext f
  simp only [mem_union, H.mem_edgesTo, ← shores_union e]
  tauto

end Overfull.TwoApexFactorization
