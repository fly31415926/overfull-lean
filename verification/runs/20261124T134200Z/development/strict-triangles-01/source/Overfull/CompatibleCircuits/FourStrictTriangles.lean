import Overfull.CompatibleCircuits.FourStrictSupport
import Overfull.CompatibleCircuits.FourStrictCoarsening

/-!
# Triangle obstructions in the strict four-label branch

The triangle-bundle selector is lifted to actual compatible circuits.
Monochromatic corners are bounded by original local and nonlocal cuts.
These facts rule out complete four-vertex support when both compatible
pairs and triangles are absent.
-/

namespace Overfull.Multigraph

open Finset Classical Overfull.CompatibleCircuits

variable {V E K : Type*} (G : Multigraph V E)

theorem cutOn_mem_of_endpoints {C : Finset E} {e : E} (heC : e ∈ C)
    {u v : V} (hedge : G.edge e = s(u, v)) (X : Finset V)
    (hcross : (u ∈ X) ≠ (v ∈ X)) : e ∈ G.cutOn C X := by
  apply (G.mem_cutOn C X e).mpr
  refine ⟨heC, ?_⟩
  rcases Sym2.eq_iff.mp ((G.edge_eq e).trans hedge) with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · simpa only [ha, hb] using hcross
  · simpa only [ha, hb] using hcross.symm

/-- Three actual copies with three distinct endpoint pairs are a circuit,
even when the ambient vertex type contains additional vertices. -/
theorem isCircuit_triangle_of_distinct_vertices {u v w : V}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) {e f g : E}
    (he : G.edge e = s(u, v)) (hf : G.edge f = s(u, w))
    (hg : G.edge g = s(v, w)) : G.IsCircuit {e, f, g} := by
  have hef : e ≠ f := by
    intro h
    have hp := (he.symm.trans (congrArg G.edge h)).trans hf
    rcases Sym2.eq_iff.mp hp with ⟨_, h⟩ | ⟨h, _⟩
    · exact hvw h
    · exact huw h
  have heg : e ≠ g := by
    intro h
    have hp := (he.symm.trans (congrArg G.edge h)).trans hg
    rcases Sym2.eq_iff.mp hp with ⟨h, _⟩ | ⟨h, _⟩
    · exact huv h
    · exact huw h
  have hfg : f ≠ g := by
    intro h
    have hp := (hf.symm.trans (congrArg G.edge h)).trans hg
    rcases Sym2.eq_iff.mp hp with ⟨h, _⟩ | ⟨h, _⟩
    · exact huv h
    · exact huw h
  have hs : G.edgeSupport {e, f, g} = {u, v, w} := by
    ext a
    simp only [mem_edgeSupport, mem_insert, mem_singleton]
    simp [he, hf, hg]
    tauto
  refine ⟨by simp, ?_, ?_⟩
  · intro a ha
    rw [hs] at ha
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;>
      simp [degreeOn, filter_insert, filter_singleton, he, hf, hg,
        huv, huw, hvw, Ne.symm huv, Ne.symm huw, Ne.symm hvw, hef, heg, hfg]
  · intro X hX hnonempty hproper
    have hsome : u ∈ X ∨ v ∈ X ∨ w ∈ X := by
      obtain ⟨a, ha⟩ := hnonempty
      have hmem := hX ha
      rw [hs] at hmem
      simp only [mem_insert, mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl <;> tauto
    have hnotall : ¬ (u ∈ X ∧ v ∈ X ∧ w ∈ X) := by
      intro h
      apply hproper
      apply Subset.antisymm hX
      rw [hs]
      intro a ha
      simp only [mem_insert, mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> tauto
    by_cases hu : u ∈ X
    · by_cases hv : v ∈ X
      · have hw : w ∉ X := by tauto
        exact ⟨f, G.cutOn_mem_of_endpoints (by simp) hf X (by simp [hu, hw])⟩
      · exact ⟨e, G.cutOn_mem_of_endpoints (by simp) he X (by simp [hu, hv])⟩
    · by_cases hv : v ∈ X
      · exact ⟨e, G.cutOn_mem_of_endpoints (by simp) he X (by simp [hu, hv])⟩
      · have hw : w ∈ X := by tauto
        exact ⟨f, G.cutOn_mem_of_endpoints (by simp) hf X (by simp [hu, hw])⟩

theorem compatible_triangle_of_endpoint_classes
    (classOf : V → E → K) {u v w : V}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) {e f g : E}
    (he : G.edge e = s(u, v)) (hf : G.edge f = s(u, w))
    (hg : G.edge g = s(v, w))
    (hu : classOf u e ≠ classOf u f) (hv : classOf v e ≠ classOf v g)
    (hw : classOf w f ≠ classOf w g) : G.Compatible classOf {e, f, g} := by
  intro a x hx hax y hy hay hclass
  simp only [mem_insert, mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  all_goals try rfl
  all_goals simp only [he, hf, hg, Sym2.mem_iff] at hax hay
  all_goals rcases hax with rfl | rfl <;> simp_all

/-- The absence of an actual compatible triangle forces a common class
on one whole triangle corner. -/
theorem triangle_common_corner_of_no_short_circuit
    (classOf : V → E → K) (C : Finset E)
    (hnone : ¬ ∃ D : Finset E, D ⊆ C ∧ G.IsCircuit D ∧
      G.Compatible classOf D ∧ D.card ≤ 3)
    {u v w : V} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hUV : (G.edgeBundleOn C u v).Nonempty)
    (hUW : (G.edgeBundleOn C u w).Nonempty)
    (hVW : (G.edgeBundleOn C v w).Nonempty) :
    CommonClassOn (G.edgeBundleOn C u v) (G.edgeBundleOn C u w) (classOf u) ∨
      CommonClassOn (G.edgeBundleOn C u v) (G.edgeBundleOn C v w) (classOf v) ∨
      CommonClassOn (G.edgeBundleOn C u w) (G.edgeBundleOn C v w) (classOf w) := by
  have hpair : ¬ ∃ D : Finset E, D ⊆ C ∧ G.IsCircuit D ∧
      G.Compatible classOf D ∧ D.card = 2 := by
    rintro ⟨D, hDC, hcir, hcomp, hcard⟩
    exact hnone ⟨D, hDC, hcir, hcomp, by omega⟩
  apply monochromatic_corner_of_no_compatible_triple _ _ _ _ _ _ hUV hUW hVW
    (G.bundle_monochromatic_of_no_compatible_pair classOf C hpair u v hUV)
    (G.bundle_monochromatic_of_no_compatible_pair classOf C hpair u w hUW)
    (G.bundle_monochromatic_of_no_compatible_pair classOf C hpair v w hVW)
  rintro ⟨e, he, f, hf, g, hg, hu, hv, hw⟩
  obtain ⟨heC, heends⟩ := (G.mem_edgeBundleOn C u v e).mp he
  obtain ⟨hfC, hfends⟩ := (G.mem_edgeBundleOn C u w f).mp hf
  obtain ⟨hgC, hgends⟩ := (G.mem_edgeBundleOn C v w g).mp hg
  apply hnone
  refine ⟨{e, f, g}, ?_,
    G.isCircuit_triangle_of_distinct_vertices huv huw hvw heends hfends hgends,
    G.compatible_triangle_of_endpoint_classes classOf huv huw hvw heends hfends hgends
      hu hv hw, ?_⟩
  · intro a ha
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> assumption
  · exact (card_insert_le e _).trans (Nat.succ_le_succ
      ((card_insert_le f _).trans (by simp)))

/-- A monochromatic corner fits inside one original local class. -/
theorem common_corner_local_bound
    (classOf : V → E → K) {C : Finset E}
    (hadmissible : G.AdmissibleOn classOf C) {v u w : V}
    (hvw : v ≠ w) (huw : u ≠ w)
    (hcommon : CommonClassOn (G.edgeBundleOn C v u)
      (G.edgeBundleOn C v w) (classOf v)) :
    2 * ((G.edgeBundleOn C v u).card + (G.edgeBundleOn C v w).card) ≤
      G.degreeOn C v := by
  obtain ⟨k, hk⟩ := hcommon
  have hpairs : s(v, u) ≠ s(v, w) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨_, h⟩ | ⟨h, _⟩
    · exact huw h
    · exact hvw h
  have hdis : Disjoint (G.edgeBundleOn C v u) (G.edgeBundleOn C v w) :=
    G.edgeBundleOn_disjoint hpairs
  have hsub : G.edgeBundleOn C v u ∪ G.edgeBundleOn C v w ⊆
      C.filter (fun e => v ∈ G.edge e ∧ classOf v e = k) := by
    intro e he
    have hends : e ∈ C ∧ v ∈ G.edge e := by
      rcases mem_union.mp he with he | he
      · obtain ⟨heC, hends⟩ := (G.mem_edgeBundleOn C v u e).mp he
        exact ⟨heC, by simp [hends]⟩
      · obtain ⟨heC, hends⟩ := (G.mem_edgeBundleOn C v w e).mp he
        exact ⟨heC, by simp [hends]⟩
    exact mem_filter.mpr ⟨hends.1, hends.2, hk e he⟩
  have hcard := card_le_card hsub
  rw [card_union_of_disjoint hdis] at hcard
  exact (Nat.mul_le_mul_left 2 hcard).trans (hadmissible.local_class_bound G v k)

/-- Across a shore containing both neighbors, a monochromatic corner
satisfies the original strict nonlocal cut bound. -/
theorem common_corner_strict_cut_bound
    (classOf : V → E → K) {C : Finset E}
    (hstrict : G.StrictNonlocalOn classOf C) {v u w : V}
    (hvw : v ≠ w) (huw : u ≠ w) (X : Finset V)
    (hvX : v ∉ X) (huX : u ∈ X) (hwX : w ∈ X)
    (hX : NonlocalShore v X)
    (hcommon : CommonClassOn (G.edgeBundleOn C v u)
      (G.edgeBundleOn C v w) (classOf v)) :
    2 * ((G.edgeBundleOn C v u).card + (G.edgeBundleOn C v w).card) <
      (G.cutOn C X).card := by
  obtain ⟨k, hk⟩ := hcommon
  have hpairs : s(v, u) ≠ s(v, w) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨_, h⟩ | ⟨h, _⟩
    · exact huw h
    · exact hvw h
  have hdis : Disjoint (G.edgeBundleOn C v u) (G.edgeBundleOn C v w) :=
    G.edgeBundleOn_disjoint hpairs
  have hsub : G.edgeBundleOn C v u ∪ G.edgeBundleOn C v w ⊆
      G.classCutOn classOf C v k X := by
    intro e he
    have hends : e ∈ G.cutOn C X ∧ v ∈ G.edge e := by
      rcases mem_union.mp he with he | he
      · obtain ⟨heC, hends⟩ := (G.mem_edgeBundleOn C v u e).mp he
        exact ⟨G.cutOn_mem_of_endpoints heC hends X (by simp [hvX, huX]),
          by simp [hends]⟩
      · obtain ⟨heC, hends⟩ := (G.mem_edgeBundleOn C v w e).mp he
        exact ⟨G.cutOn_mem_of_endpoints heC hends X (by simp [hvX, hwX]),
          by simp [hends]⟩
    exact mem_filter.mpr ⟨hends.1, hends.2, hk e he⟩
  have hcard := card_le_card hsub
  rw [card_union_of_disjoint hdis] at hcard
  exact (Nat.mul_le_mul_left 2 hcard).trans_lt (hstrict v k X hX)

end Overfull.Multigraph
