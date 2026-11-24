import Overfull.TwoApexFactorization.Packing
import Overfull.TwoApexFactorization.Shores
import Overfull.BalancedColoring

/-!
# Balanced selected colors with an arbitrary exterior partition

Equal exterior shores may contain any number of vertices.  When every
exterior vertex has the selected degree, and every unselected copy crosses
the augmented shores, the selected core degree sums agree.  The existing
balanced-coloring theorem then supplies the exact footprints needed by the
robust bipartite packing theorem.

This file was reconstructed from the recovered interfaces after the original
checkpoint files became unavailable.  Its proofs are checked anew.
-/

noncomputable section

namespace Overfull.BoundedExterior

open Finset Classical SmallCuts TwoApexFactorization

variable {V E : Type*} [Fintype V] [Fintype E]

theorem augmented_shores_compl (U A B ZA ZB : Finset V)
    (hAB : Disjoint A B) (hU : A ∪ B = U)
    (hZ : Disjoint ZA ZB) (hcover : ZA ∪ ZB = Uᶜ) :
    (A ∪ ZA)ᶜ = B ∪ ZB := by
  ext v
  have hu : (v ∈ A ∨ v ∈ B) ↔ v ∈ U := by rw [← hU]; simp
  have hz : (v ∈ ZA ∨ v ∈ ZB) ↔ v ∉ U := by rw [← mem_union, hcover]; simp
  have hab : ¬ (v ∈ A ∧ v ∈ B) := fun h => disjoint_left.mp hAB h.1 h.2
  have hzz : ¬ (v ∈ ZA ∧ v ∈ ZB) := fun h => disjoint_left.mp hZ h.1 h.2
  simp only [mem_compl, mem_union]
  tauto

theorem exterior_partition_even (U ZA ZB : Finset V)
    (hZ : Disjoint ZA ZB) (hcover : ZA ∪ ZB = Uᶜ)
    (hbalance : ZA.card = ZB.card) : Even Uᶜ.card := by
  rw [← hcover, card_union_of_disjoint hZ, ← hbalance]
  exact ⟨ZA.card, rfl⟩

theorem selected_core_degree_sums (G : Multigraph V E)
    (U A B ZA ZB : Finset V) (F : Finset E) (k q : ℕ)
    (hAB : Disjoint A B) (hU : A ∪ B = U) (hcard : A.card = B.card)
    (hZ : Disjoint ZA ZB) (hcover : ZA ∪ ZB = Uᶜ)
    (hbalance : ZA.card = ZB.card)
    (hregular : ∀ v, G.degree v = k)
    (houtside : ∀ v, v ∉ U → (G.restrictEdges F).degree v = q)
    (hcross : ∀ f : E, f ∉ F → f ∈ G.cutEdges (A ∪ ZA)) :
    (∑ v ∈ A, (G.restrictEdges F).degree v) =
      ∑ v ∈ B, (G.restrictEdges F).degree v := by
  have hZA (v : V) (hv : v ∈ ZA) : v ∉ U := by
    exact mem_compl.mp (hcover ▸ mem_union_left ZB hv)
  have hZB (v : V) (hv : v ∈ ZB) : v ∉ U := by
    exact mem_compl.mp (hcover ▸ mem_union_right ZA hv)
  have hAZA : Disjoint A ZA := by
    apply disjoint_left.mpr
    intro v hvA hvZ
    exact hZA v hvZ (hU ▸ mem_union_left B hvA)
  have hBZB : Disjoint B ZB := by
    apply disjoint_left.mpr
    intro v hvB hvZ
    exact hZB v hvZ (hU ▸ mem_union_right A hvB)
  have hcomp := augmented_shores_compl U A B ZA ZB hAB hU hZ hcover
  have hsize : (A ∪ ZA).card = (A ∪ ZA)ᶜ.card := by
    rw [hcomp, card_union_of_disjoint hAZA, card_union_of_disjoint hBZB,
      hcard, hbalance]
  have hs := selected_degree_sums G (A ∪ ZA) F k hregular hsize hcross
  have hsZA : (∑ v ∈ ZA, (G.restrictEdges F).degree v) = ZA.card * q := by
    calc
      _ = ∑ _v ∈ ZA, q := sum_congr rfl (fun v hv => houtside v (hZA v hv))
      _ = _ := by simp
  have hsZB : (∑ v ∈ ZB, (G.restrictEdges F).degree v) = ZB.card * q := by
    calc
      _ = ∑ _v ∈ ZB, q := sum_congr rfl (fun v hv => houtside v (hZB v hv))
      _ = _ := by simp
  rw [hcomp, sum_union hAZA, sum_union hBZB, hsZA, hsZB, hbalance] at hs
  omega

theorem exists_balanced_selected_coloring (G : Multigraph V E)
    (U A B ZA ZB : Finset V) (F : Finset E) (k q : ℕ) (a : ℝ)
    (hq : 0 < q)
    (hAB : Disjoint A B) (hU : A ∪ B = U) (hcard : A.card = B.card)
    (hZ : Disjoint ZA ZB) (hcover : ZA ∪ ZB = Uᶜ)
    (hbalance : ZA.card = ZB.card)
    (hregular : ∀ v, G.degree v = k)
    (houtside : ∀ v, v ∉ U → (G.restrictEdges F).degree v = q)
    (hlow : ∀ v ∈ U, ((G.restrictEdges F).degree v : ℝ) ≤ a)
    (hcross : ∀ f : E, f ∉ F → f ∈ G.cutEdges (A ∪ ZA))
    (hcolor : Nonempty ((G.restrictEdges F).EdgeColoring q)) :
    ∃ c : (G.restrictEdges F).EdgeColoring q,
      (∀ i, (A ∩ c.coveredVertices i).card = (B ∩ c.coveredVertices i).card) ∧
      (∀ i, ((U ∩ c.coveredVertices i).card : ℝ) ≤ 2 * A.card * a / q + 4) := by
  have hdegrees := selected_core_degree_sums G U A B ZA ZB F k q
    hAB hU hcard hZ hcover hbalance hregular houtside hcross
  obtain ⟨c, _hcover, hbal, _hspread, _hload, _hbound, hbounda⟩ :=
    (G.restrictEdges F).balanced_edgeColoring q hq A B Uᶜ hAB
      (hU ▸ disjoint_compl_right) (by rw [hU, union_compl]) hcard
      (exterior_partition_even U ZA ZB hZ hcover hbalance)
      (fun v hv => houtside v (mem_compl.mp hv)) hdegrees hcolor
  refine ⟨c, hbal, ?_⟩
  intro i
  simpa only [hU] using hbounda a (fun v hv => hlow v (hU ▸ hv)) i

variable {A B : Type*} [Fintype A] [Fintype B]
variable {G : Multigraph V E} {U : Finset V}

/-- Adding exterior vertices to a core shore preserves crossing for each
actual embedded bipartite core edge copy. -/
theorem core_copies_cross_augmented (C : Core G U) (e : A ⊕ B ≃ U)
    (ZA : Finset V) (hZA : ZA ⊆ Uᶜ)
    (hbip : (C.graph.comap e).IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr)) :
    ∀ f ∈ OneCore.coreEdges C, f ∈ G.cutEdges (leftShore e ∪ ZA) := by
  intro f hf
  obtain ⟨g, rfl⟩ := (OneCore.mem_coreEdges C f).mp hf
  rcases g with ⟨⟨u, v⟩, huv⟩
  have hindex : (C.graph.comap e).Adj (e.symm u) (e.symm v) := by
    simpa only [SimpleGraph.comap_adj, e.apply_symm_apply] using huv
  rcases hbip.mem_of_adj hindex with
    ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ | ⟨⟨b, hb⟩, ⟨a, ha⟩⟩
  · have hua : e (.inl a) = u := by rw [ha, e.apply_symm_apply]
    have hvb : e (.inr b) = v := by rw [hb, e.apply_symm_apply]
    apply (G.mem_cutEdges_iff _ _).mpr
    refine ⟨u.val, v.val, C.map_edge _, mem_union_left ZA ?_, ?_⟩
    · exact (mem_leftShore e u.val).mpr ⟨a, congrArg Subtype.val hua⟩
    · intro hv
      rcases mem_union.mp hv with hv | hv
      · exact disjoint_left.mp (shores_disjoint e) hv
          ((mem_rightShore e v.val).mpr ⟨b, congrArg Subtype.val hvb⟩)
      · exact mem_compl.mp (hZA hv) v.property
  · have hua : e (.inr b) = u := by rw [hb, e.apply_symm_apply]
    have hvb : e (.inl a) = v := by rw [ha, e.apply_symm_apply]
    apply (G.mem_cutEdges_iff _ _).mpr
    refine ⟨v.val, u.val, (C.map_edge _).trans Sym2.eq_swap, mem_union_left ZA ?_, ?_⟩
    · exact (mem_leftShore e v.val).mpr ⟨a, congrArg Subtype.val hvb⟩
    · intro hu
      rcases mem_union.mp hu with hu | hu
      · exact disjoint_left.mp (shores_disjoint e) hu
          ((mem_rightShore e u.val).mpr ⟨b, congrArg Subtype.val hua⟩)
      · exact mem_compl.mp (hZA hu) u.property

end Overfull.BoundedExterior
