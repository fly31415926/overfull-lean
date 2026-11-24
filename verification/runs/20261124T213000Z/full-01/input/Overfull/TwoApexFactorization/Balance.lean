import Overfull.TwoApexFactorization.Selection
import Overfull.TwoApexFactorization.Shores

/-!
# Constructing the selected balanced coloring

The selected graph has two saturated apices and small degree on its core.
The proved multigraph fan criterion constructs its coloring.  Equal side
degree sums follow from the bipartite unselected host, so the actual colors
can then be balanced and equitized for robust matching packing.
-/

noncomputable section

namespace Overfull.TwoApexFactorization

open Finset Classical SmallCuts BipartiteFactorization

variable {V E : Type*} [Fintype V] [Fintype E]
variable (G : Multigraph V E) (U A B : Finset V)

theorem internal_two_apices_bipartite (x y : V) (hxy : x ≠ y)
    (houtside : Uᶜ = {x, y}) :
    (G.restrictEdges (G.internalEdges Uᶜ)).IsBipartite := by
  refine ⟨fun v => decide (v = x), ?_⟩
  intro e
  have he := (G.mem_internalEdges Uᶜ e.val).mp e.property
  simp only [houtside] at he
  simp only [mem_insert, mem_singleton] at he
  change decide (G.firstEnd e.val = x) ≠ decide (G.secondEnd e.val = x)
  rcases he.1 with hfirst | hfirst <;> rcases he.2 with hsecond | hsecond
  · exact (G.endpoints_distinct e.val (hfirst.trans hsecond.symm)).elim
  · simp [hfirst, hsecond, hxy.symm]
  · simp [hfirst, hsecond, hxy.symm]
  · exact (G.endpoints_distinct e.val (hfirst.trans hsecond.symm)).elim

theorem selection_core_degree_sums (C : Core G U) (x y : V) (k q : ℕ)
    (S : Selection G U A B C x y q)
    (hxy : x ≠ y) (houtside : Uᶜ = {x, y})
    (hAB : Disjoint A B) (hunion : A ∪ B = U) (hcard : A.card = B.card)
    (hregular : ∀ v, G.degree v = k)
    (hcore : ∀ f ∈ OneCore.coreEdges C, f ∈ G.cutEdges (insert x A)) :
    (∑ v ∈ A, (G.restrictEdges S.edges).degree v) =
      ∑ v ∈ B, (G.restrictEdges S.edges).degree v := by
  have hx : x ∉ U := by
    apply mem_compl.mp
    rw [houtside]
    simp
  have hy : y ∉ U := by
    apply mem_compl.mp
    rw [houtside]
    simp
  have hxA : x ∉ A := fun h => hx (hunion ▸ mem_union_left B h)
  have hyB : y ∉ B := fun h => hy (hunion ▸ mem_union_right A h)
  have hcomp := augmented_shore_compl U A B x y hxy houtside hAB hunion
  have hsize : (insert x A).card = (insert x A)ᶜ.card := by
    rw [hcomp]
    simp only [card_insert_of_notMem hxA, card_insert_of_notMem hyB, hcard]
  have hs := selected_degree_sums G (insert x A) S.edges k hregular hsize
    (fun f hf => S.remaining_cross hcore hf)
  rw [hcomp, sum_insert hxA, sum_insert hyB,
    S.apex_degree_left, S.apex_degree_right] at hs
  omega

/-- The coloring is constructed from the fan criterion.  Its only initial
colored residue is the bipartite graph of copies between the two apices. -/
theorem exists_balanced_selection_coloring (C : Core G U) (x y : V) (k q : ℕ)
    (S : Selection G U A B C x y q) (a : ℝ)
    (hxy : x ≠ y) (houtside : Uᶜ = {x, y})
    (hAB : Disjoint A B) (hunion : A ∪ B = U) (hcard : A.card = B.card)
    (hregular : ∀ v, G.degree v = k)
    (hcoreCross : ∀ f ∈ OneCore.coreEdges C, f ∈ G.cutEdges (insert x A))
    (ha : 0 ≤ a) (hqa : 2 * a < q)
    (hactive : 2 * a < (min q (G.edgesTo x U).card : ℕ))
    (hdegree : ∀ v : U, ((G.restrictEdges (OneCore.coreEdges C)ᶜ).degree v.val : ℝ) ≤ a) :
    ∃ c : (G.restrictEdges S.edges).EdgeColoring q,
      (∀ i, (A ∩ c.coveredVertices i).card = (B ∩ c.coveredVertices i).card) ∧
      (∀ i, ((U ∩ c.coveredVertices i).card : ℝ) ≤ 2 * A.card * a / q + 4) := by
  let H := G.restrictEdges S.edges
  have hlow (v : V) (hv : v ∈ U) : (H.degree v : ℝ) ≤ a := by
    have h := S.degree_le_complement v
    exact (Nat.cast_le.mpr h).trans (hdegree ⟨v, hv⟩)
  have hsat (v : V) (hv : v ∉ U) : H.degree v = q := by
    have hv' : v = x ∨ v = y := by
      have hh : v ∈ Uᶜ := mem_compl.mpr hv
      simpa only [houtside, mem_insert, mem_singleton] using hh
    rcases hv' with rfl | rfl
    · exact S.apex_degree_left
    · exact S.apex_degree_right
  have hmax (v : V) : H.degree v ≤ q := by
    by_cases hv : v ∈ U
    · have h := hlow v hv
      have h' : (H.degree v : ℝ) ≤ q := by linarith
      exact_mod_cast h'
    · exact (hsat v hv).le
  have hinactive : inactiveExterior H U Uᶜ = H.internalEdges Uᶜ := by
    simp only [inactiveExterior_eq, sdiff_self, Finset.bot_eq_empty, Finset.biUnion_empty, union_empty]
  have hinactiveBip : (H.restrictEdges (inactiveExterior H U Uᶜ)).IsBipartite := by
    rw [hinactive]
    exact internal_two_apices_bipartite H U x y hxy houtside
  have hinactiveColor : Nonempty ((H.restrictEdges (inactiveExterior H U Uᶜ)).EdgeColoring q) :=
    (H.restrictEdges (inactiveExterior H U Uᶜ)).exists_edgeColoring_of_bipartite
      hinactiveBip q (fun v => (H.restrictEdges_degree_le _ v).trans (hmax v))
  have hactive' (v : V) (hv : v ∈ Uᶜ) : 2 * a < ((H.edgesTo v U).card : ℝ) := by
    have hv' : v = x ∨ v = y := by
      simpa only [houtside, mem_insert, mem_singleton] using hv
    rcases hv' with rfl | rfl
    · simpa only [H, S.apex_core_left] using hactive
    · simpa only [H, S.apex_core_right] using hactive
  have hcolor : Nonempty (H.EdgeColoring q) :=
    coloring_from_inactive_exterior H U Uᶜ q a ha hlow (fun v hv => (hsat v hv).le)
      hqa hactive' hinactiveColor
  have hq : 0 < q := by
    have h : (0 : ℝ) < q := by linarith
    exact_mod_cast h
  have hZeven : Even Uᶜ.card := by rw [houtside, card_pair hxy]; decide
  have hdegrees := selection_core_degree_sums G U A B C x y k q S hxy houtside
    hAB hunion hcard hregular hcoreCross
  obtain ⟨c, _hcover, hbalance, _hspread, _hload, _hbound, hbounda⟩ :=
    H.balanced_edgeColoring q hq A B Uᶜ hAB
      (hunion ▸ disjoint_compl_right) (by rw [hunion, union_compl])
      hcard hZeven (fun v hv => hsat v (mem_compl.mp hv)) hdegrees hcolor
  refine ⟨c, hbalance, ?_⟩
  intro i
  simpa only [hunion] using hbounda a (fun v hv => hlow v (hunion ▸ hv)) i

end Overfull.TwoApexFactorization
