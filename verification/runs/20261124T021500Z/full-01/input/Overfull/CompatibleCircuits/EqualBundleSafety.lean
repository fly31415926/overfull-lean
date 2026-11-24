import Overfull.CompatibleCircuits.EqualBundleSelection
import Overfull.CompatibleCircuits.LocalCoarsening
import Overfull.CompatibleCircuits.ThreeLabelBundles

/-!
# Safe triangles in the equal-bundle case

On three labels with three equal positive parallel bundles, a tight
nonlocal incidence class fills its whole bundle. Local tight classes can
be met simultaneously using the checked local coarsening. These facts
supply the triangle branch of the safe-circuit selector.
-/

namespace Overfull.CompatibleCircuits

open Finset Classical

variable {E K : Type*}

/-- The equal-bundle triangle selector is symmetric in its three labels:
a monochromatic bundle at any one of its incident endpoints suffices. -/
theorem exists_compatible_triple_of_equal_bundles_of_monochromatic
    (AB AC BC : Finset E) (a b c : E → K)
    (hABAC : Disjoint AB AC) (hABBC : Disjoint AB BC) (hACBC : Disjoint AC BC)
    (hAC : AC.card = AB.card) (hBC : BC.card = AB.card) (hpos : 0 < AB.card)
    (hA : ∀ k, 2 * ((AB ∪ AC).filter (fun e => a e = k)).card ≤ (AB ∪ AC).card)
    (hB : ∀ k, 2 * ((AB ∪ BC).filter (fun e => b e = k)).card ≤ (AB ∪ BC).card)
    (hC : ∀ k, 2 * ((AC ∪ BC).filter (fun e => c e = k)).card ≤ (AC ∪ BC).card)
    (hmono : (∃ k, ∀ e ∈ AB, a e = k) ∨ (∃ k, ∀ e ∈ AC, a e = k) ∨
      (∃ k, ∀ e ∈ AB, b e = k) ∨ (∃ k, ∀ e ∈ BC, b e = k) ∨
      (∃ k, ∀ e ∈ AC, c e = k) ∨ (∃ k, ∀ e ∈ BC, c e = k)) :
    ∃ e ∈ AB, ∃ h ∈ AC, ∃ g ∈ BC,
      a e ≠ a h ∧ b e ≠ b g ∧ c h ≠ c g := by
  rcases hmono with hmono | hmono | hmono | hmono | hmono | hmono
  · exact exists_compatible_triple_of_equal_bundles AB AC BC a b c
      hABAC hABBC hACBC hAC hBC hpos hA hB hC hmono
  · obtain ⟨h, hh, e, he, g, hg, h0, h2, h1⟩ :=
      exists_compatible_triple_of_equal_bundles AC AB BC a c b
        hABAC.symm hACBC hABBC hAC.symm (hBC.trans hAC.symm)
        (by omega) (by simpa only [union_comm] using hA) hC hB hmono
    exact ⟨e, he, h, hh, g, hg, h0.symm, h1, h2⟩
  · obtain ⟨e, he, g, hg, h, hh, h1, h0, h2⟩ :=
      exists_compatible_triple_of_equal_bundles AB BC AC b a c
        hABBC hABAC hACBC.symm hBC hAC hpos hB hA
        (by simpa only [union_comm] using hC) hmono
    exact ⟨e, he, h, hh, g, hg, h0, h1, h2.symm⟩
  · obtain ⟨g, hg, e, he, h, hh, h1, h2, h0⟩ :=
      exists_compatible_triple_of_equal_bundles BC AB AC b c a
        hABBC.symm hACBC.symm hABAC hBC.symm (hAC.trans hBC.symm)
        (by omega) (by simpa only [union_comm] using hB)
        (by simpa only [union_comm] using hC) hA hmono
    exact ⟨e, he, h, hh, g, hg, h0, h1.symm, h2.symm⟩
  · obtain ⟨h, hh, g, hg, e, he, h2, h0, h1⟩ :=
      exists_compatible_triple_of_equal_bundles AC BC AB c a b
        hACBC hABAC.symm hABBC.symm (hBC.trans hAC.symm) hAC.symm
        (by omega) hC (by simpa only [union_comm] using hA)
        (by simpa only [union_comm] using hB) hmono
    exact ⟨e, he, h, hh, g, hg, h0.symm, h1.symm, h2⟩
  · obtain ⟨g, hg, h, hh, e, he, h2, h1, h0⟩ :=
      exists_compatible_triple_of_equal_bundles BC AC AB c b a
        hACBC.symm hABBC.symm hABAC.symm (hAC.trans hBC.symm) hBC.symm
        (by omega) (by simpa only [union_comm] using hC)
        (by simpa only [union_comm] using hB)
        (by simpa only [union_comm] using hA) hmono
    exact ⟨e, he, h, hh, g, hg, h0.symm, h1.symm, h2.symm⟩

end Overfull.CompatibleCircuits

namespace Overfull.Multigraph

open Finset Classical CompatibleCircuits

variable {E K : Type*} (Q : Multigraph (Fin 3) E)

/-- Equal canonical bundle sizes give the same size at every ordered
pair of distinct labels. -/
theorem threeLabel_equal_bundle_card {C : Finset E}
    (hAC : (Q.edgeBundleOn C 0 2).card = (Q.edgeBundleOn C 0 1).card)
    (hBC : (Q.edgeBundleOn C 1 2).card = (Q.edgeBundleOn C 0 1).card)
    (v w : Fin 3) (hne : v ≠ w) :
    (Q.edgeBundleOn C v w).card = (Q.edgeBundleOn C 0 1).card := by
  fin_cases v <;> fin_cases w
  · exact False.elim (hne rfl)
  · rfl
  · exact hAC
  · change (Q.edgeBundleOn C 1 0).card = (Q.edgeBundleOn C 0 1).card
    rw [Q.edgeBundleOn_swap C 1 0]
  · exact False.elim (hne rfl)
  · exact hBC
  · change (Q.edgeBundleOn C 2 0).card = (Q.edgeBundleOn C 0 1).card
    rw [Q.edgeBundleOn_swap C 2 0]
    exact hAC
  · change (Q.edgeBundleOn C 2 1).card = (Q.edgeBundleOn C 0 1).card
    rw [Q.edgeBundleOn_swap C 2 1]
    exact hBC
  · exact False.elim (hne rfl)

/-- All three degrees are twice the common equal-bundle size. -/
theorem threeLabel_degree_of_equal_bundles {C : Finset E}
    (hAC : (Q.edgeBundleOn C 0 2).card = (Q.edgeBundleOn C 0 1).card)
    (hBC : (Q.edgeBundleOn C 1 2).card = (Q.edgeBundleOn C 0 1).card)
    (v : Fin 3) : Q.degreeOn C v = 2 * (Q.edgeBundleOn C 0 1).card := by
  fin_cases v
  · change Q.degreeOn C 0 = 2 * (Q.edgeBundleOn C 0 1).card
    rw [Q.threeLabel_degree_zero, hAC]
    omega
  · change Q.degreeOn C 1 = 2 * (Q.edgeBundleOn C 0 1).card
    rw [Q.threeLabel_degree_one, hBC]
    omega
  · change Q.degreeOn C 2 = 2 * (Q.edgeBundleOn C 0 1).card
    rw [Q.threeLabel_degree_two, hAC, hBC]
    omega

/-- With three equal bundles, every tight nonlocal incidence class
contains the whole corresponding bundle of actual copies. -/
theorem threeLabel_nonlocal_tight_eq_bundle_of_equal_bundles
    (classOf : Fin 3 → E → K) {C : Finset E}
    (hAC : (Q.edgeBundleOn C 0 2).card = (Q.edgeBundleOn C 0 1).card)
    (hBC : (Q.edgeBundleOn C 1 2).card = (Q.edgeBundleOn C 0 1).card)
    {v w : Fin 3} (hne : v ≠ w) (k : K)
    (htight : 2 * (Q.classCutOn classOf C v k {w}).card = Q.degreeOn C w) :
    Q.classCutOn classOf C v k {w} = Q.edgeBundleOn C v w := by
  have hsize := Q.threeLabel_equal_bundle_card hAC hBC v w hne
  have hdegree := Q.threeLabel_degree_of_equal_bundles hAC hBC w
  rw [Q.classCutOn_singleton_other classOf C hne k] at htight ⊢
  exact Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)

/-- If a tight nonlocal class fills a bundle, any selected copy from
that bundle witnesses the class after restriction. -/
theorem classCutOn_nonempty_of_full_bundle {classOf : Fin 3 → E → K}
    {C D : Finset E} (hDC : D ⊆ C) {v w : Fin 3} (hne : v ≠ w) (k : K)
    (hfull : Q.classCutOn classOf C v k {w} = Q.edgeBundleOn C v w)
    (hpart : (Q.edgeBundleOn D v w).Nonempty) :
    (Q.classCutOn classOf D v k {w}).Nonempty := by
  obtain ⟨e, he⟩ := hpart
  have hde := (Q.mem_edgeBundleOn D v w e).mp he
  have hce : e ∈ Q.edgeBundleOn C v w :=
    (Q.mem_edgeBundleOn C v w e).mpr ⟨hDC hde.1, hde.2⟩
  have hclass : classOf v e = k := by
    rw [← hfull, Q.classCutOn_singleton_other classOf C hne k] at hce
    exact (mem_filter.mp hce).2
  rw [Q.classCutOn_singleton_other classOf D hne k]
  exact ⟨e, mem_filter.mpr ⟨he, hclass⟩⟩

/-- In the equal positive-bundle case, any original tight nonlocal class
forces a compatible triangle whose deletion preserves every half-cut
inequality. The hypothesis allows any of the six ordered nonlocal pairs. -/
theorem exists_safe_triangle_of_equal_bundles_of_nonlocal_tight
    (classOf : Fin 3 → E → K) (C : Finset E)
    (hadmissible : Q.AdmissibleOn classOf C)
    (hAC : (Q.edgeBundleOn C 0 2).card = (Q.edgeBundleOn C 0 1).card)
    (hBC : (Q.edgeBundleOn C 1 2).card = (Q.edgeBundleOn C 0 1).card)
    (hpos : 0 < (Q.edgeBundleOn C 0 1).card)
    (htight : ∃ v w k, v ≠ w ∧
      Q.degreeOn C w = 2 * (Q.classCutOn classOf C v k {w}).card) :
    ∃ D : Finset E, D ⊆ C ∧ Q.IsCircuit D ∧ Q.Compatible classOf D ∧
      Q.AdmissibleOn classOf (C \ D) ∧ D.card = 3 := by
  classical
  let AB := Q.edgeBundleOn C 0 1
  let AC := Q.edgeBundleOn C 0 2
  let BC := Q.edgeBundleOn C 1 2
  have hABAC : Disjoint AB AC := Q.edgeBundleOn_disjoint (by decide)
  have hABBC : Disjoint AB BC := Q.edgeBundleOn_disjoint (by decide)
  have hACBC : Disjoint AC BC := Q.edgeBundleOn_disjoint (by decide)
  let I : Fin 3 → Finset E := fun v => C.filter (fun e => v ∈ Q.edge e)
  have hclassI (v : Fin 3) (k : K) :
      (I v).filter (fun e => classOf v e = k) = Q.classCutOn classOf C v k {v} := by
    ext e
    simp [I, Q.classCutOn_singleton_self, and_assoc]
  have hIcard (v : Fin 3) : (I v).card = Q.degreeOn C v := by
    unfold degreeOn
    congr 1
    ext e
    simp [I]
  have hlocal (v : Fin 3) (k : K) :
      2 * ((I v).filter (fun e => classOf v e = k)).card ≤ (I v).card := by
    rw [hclassI, hIcard]
    have hv := hadmissible v k {v}
    simpa only [Q.cutOn_singleton_card] using hv
  let L : (v : Fin 3) → LocalCoarsening (I v) (classOf v) :=
    fun v => Classical.choice (exists_localCoarsening (I v) (classOf v) (hlocal v))
  let gamma : Fin 3 → E → K ⊕ Bool := fun v => (L v).coarse
  have hA (q : K ⊕ Bool) :
      2 * ((AB ∪ AC).filter (fun e => gamma 0 e = q)).card ≤ (AB ∪ AC).card := by
    have h := (L 0).half_bound q
    simpa only [I, Q.threeLabel_incident_zero, AB, AC, gamma] using h
  have hB (q : K ⊕ Bool) :
      2 * ((AB ∪ BC).filter (fun e => gamma 1 e = q)).card ≤ (AB ∪ BC).card := by
    have h := (L 1).half_bound q
    simpa only [I, Q.threeLabel_incident_one, AB, BC, gamma] using h
  have hC (q : K ⊕ Bool) :
      2 * ((AC ∪ BC).filter (fun e => gamma 2 e = q)).card ≤ (AC ∪ BC).card := by
    have h := (L 2).half_bound q
    simpa only [I, Q.threeLabel_incident_two, AC, BC, gamma] using h
  have hmono : ∃ v w, v ≠ w ∧ ∃ q, ∀ e ∈ Q.edgeBundleOn C v w, gamma v e = q := by
    obtain ⟨v, w, k, hne, hk⟩ := htight
    have hfull := Q.threeLabel_nonlocal_tight_eq_bundle_of_equal_bundles
      classOf hAC hBC hne k hk.symm
    have hbundlepos : 0 < (Q.edgeBundleOn C v w).card := by
      rw [Q.threeLabel_equal_bundle_card hAC hBC v w hne]
      exact hpos
    obtain ⟨a, ha⟩ := card_pos.mp hbundlepos
    have hclass (e : E) (he : e ∈ Q.edgeBundleOn C v w) : classOf v e = k := by
      rw [← hfull, Q.classCutOn_singleton_other classOf C hne k] at he
      exact (mem_filter.mp he).2
    refine ⟨v, w, hne, gamma v a, ?_⟩
    intro e he
    by_contra hdiff
    exact (L v).refines e a hdiff ((hclass e he).trans (hclass a ha).symm)
  have hmono' : (∃ q, ∀ e ∈ AB, gamma 0 e = q) ∨
      (∃ q, ∀ e ∈ AC, gamma 0 e = q) ∨
      (∃ q, ∀ e ∈ AB, gamma 1 e = q) ∨
      (∃ q, ∀ e ∈ BC, gamma 1 e = q) ∨
      (∃ q, ∀ e ∈ AC, gamma 2 e = q) ∨
      (∃ q, ∀ e ∈ BC, gamma 2 e = q) := by
    obtain ⟨v, w, hne, q, hq⟩ := hmono
    fin_cases v <;> fin_cases w
    · exact False.elim (hne rfl)
    · exact Or.inl ⟨q, hq⟩
    · exact Or.inr (Or.inl ⟨q, hq⟩)
    · change ∀ e ∈ Q.edgeBundleOn C 1 0, gamma 1 e = q at hq
      rw [Q.edgeBundleOn_swap C 1 0] at hq
      exact Or.inr (Or.inr (Or.inl ⟨q, hq⟩))
    · exact False.elim (hne rfl)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨q, hq⟩)))
    · change ∀ e ∈ Q.edgeBundleOn C 2 0, gamma 2 e = q at hq
      rw [Q.edgeBundleOn_swap C 2 0] at hq
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, hq⟩))))
    · change ∀ e ∈ Q.edgeBundleOn C 2 1, gamma 2 e = q at hq
      rw [Q.edgeBundleOn_swap C 2 1] at hq
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨q, hq⟩))))
    · exact False.elim (hne rfl)
  obtain ⟨e, he, h, hh, g, hg, h0, h1, h2⟩ :=
    exists_compatible_triple_of_equal_bundles_of_monochromatic AB AC BC
      (gamma 0) (gamma 1) (gamma 2) hABAC hABBC hACBC hAC hBC hpos
      (fun q => by
        convert hA q using 1
        congr 2
        ext d
        simp)
      (fun q => by
        convert hB q using 1
        congr 2
        ext d
        simp)
      (fun q => by
        convert hC q using 1
        congr 2
        ext d
        simp) hmono'
  have hedata := (Q.mem_edgeBundleOn C 0 1 e).mp he
  have hhdata := (Q.mem_edgeBundleOn C 0 2 h).mp hh
  have hgdata := (Q.mem_edgeBundleOn C 1 2 g).mp hg
  let D : Finset E := {e, h, g}
  have hDC : D ⊆ C := by
    intro d hd
    simp only [D, mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact hedata.1
    · exact hhdata.1
    · exact hgdata.1
  have hDcircuit : Q.IsCircuit D := Q.isCircuit_triangle hedata.2 hhdata.2 hgdata.2
  have hDcomp : Q.Compatible classOf D := Q.compatible_triangle classOf
    hedata.2 hhdata.2 hgdata.2 ((L 0).refines e h h0)
    ((L 1).refines e g h1) ((L 2).refines h g h2)
  have hDlocal (v : Fin 3) (d f : E) (hd : d ∈ D) (hf : f ∈ D)
      (hvd : v ∈ Q.edge d) (hvf : v ∈ Q.edge f) (hdiff : gamma v d ≠ gamma v f)
      (k : K) (hk : Q.degreeOn C v = 2 * (Q.classCutOn classOf C v k {v}).card) :
      (Q.classCutOn classOf D v k {v}).Nonempty := by
    have hdk : d ∈ I v := mem_filter.mpr ⟨hDC hd, hvd⟩
    have hfk : f ∈ I v := mem_filter.mpr ⟨hDC hf, hvf⟩
    have ht : 2 * ((I v).filter (fun e => classOf v e = k)).card = (I v).card := by
      rw [hclassI, hIcard]
      exact hk.symm
    rcases (L v).meets_tight k ht d hdk f hfk hdiff with hdk | hfk
    · refine ⟨d, ?_⟩
      rw [Q.classCutOn_singleton_self]
      simp only [mem_filter]
      exact ⟨hd, hvd, hdk⟩
    · refine ⟨f, ?_⟩
      rw [Q.classCutOn_singleton_self]
      simp only [mem_filter]
      exact ⟨hf, hvf, hfk⟩
  have hDlocal_all (v : Fin 3) (k : K)
      (hk : Q.degreeOn C v = 2 * (Q.classCutOn classOf C v k {v}).card) :
      (Q.classCutOn classOf D v k {v}).Nonempty := by
    fin_cases v
    · exact hDlocal 0 e h (by simp [D]) (by simp [D])
        (by simp [hedata.2]) (by simp [hhdata.2]) h0 k hk
    · exact hDlocal 1 e g (by simp [D]) (by simp [D])
        (by simp [hedata.2]) (by simp [hgdata.2]) h1 k hk
    · exact hDlocal 2 h g (by simp [D]) (by simp [D])
        (by simp [hhdata.2]) (by simp [hgdata.2]) h2 k hk
  have hDbundle (v w : Fin 3) (hne : v ≠ w) : (Q.edgeBundleOn D v w).Nonempty := by
    fin_cases v <;> fin_cases w
    · exact False.elim (hne rfl)
    · exact ⟨e, (Q.mem_edgeBundleOn D 0 1 e).mpr ⟨by simp [D], hedata.2⟩⟩
    · exact ⟨h, (Q.mem_edgeBundleOn D 0 2 h).mpr ⟨by simp [D], hhdata.2⟩⟩
    · change (Q.edgeBundleOn D 1 0).Nonempty
      rw [Q.edgeBundleOn_swap D 1 0]
      exact ⟨e, (Q.mem_edgeBundleOn D 0 1 e).mpr ⟨by simp [D], hedata.2⟩⟩
    · exact False.elim (hne rfl)
    · exact ⟨g, (Q.mem_edgeBundleOn D 1 2 g).mpr ⟨by simp [D], hgdata.2⟩⟩
    · change (Q.edgeBundleOn D 2 0).Nonempty
      rw [Q.edgeBundleOn_swap D 2 0]
      exact ⟨h, (Q.mem_edgeBundleOn D 0 2 h).mpr ⟨by simp [D], hhdata.2⟩⟩
    · change (Q.edgeBundleOn D 2 1).Nonempty
      rw [Q.edgeBundleOn_swap D 2 1]
      exact ⟨g, (Q.mem_edgeBundleOn D 1 2 g).mpr ⟨by simp [D], hgdata.2⟩⟩
    · exact False.elim (hne rfl)
  have heven (v : Fin 3) : Even (Q.degreeOn C v) := by
    rw [Q.threeLabel_degree_of_equal_bundles hAC hBC v]
    exact even_two_mul _
  have hsafe : Q.AdmissibleOn classOf (C \ D) := by
    apply (Q.admissibleOn_sdiff_iff_meets_tight_singletons (by simp)
      classOf hDC hDcircuit hadmissible heven).mpr
    intro v k w hk _
    by_cases hEq : v = w
    · subst w
      exact hDlocal_all v k hk
    · exact Q.classCutOn_nonempty_of_full_bundle hDC hEq k
        (Q.threeLabel_nonlocal_tight_eq_bundle_of_equal_bundles
          classOf hAC hBC hEq k hk.symm) (hDbundle v w hEq)
  have heh : e ≠ h := fun hEq => h0 (congrArg (gamma 0) hEq)
  have heg : e ≠ g := fun hEq => h1 (congrArg (gamma 1) hEq)
  have hhg : h ≠ g := fun hEq => h2 (congrArg (gamma 2) hEq)
  exact ⟨D, hDC, hDcircuit, hDcomp, hsafe, by simp [D, heh, heg, hhg]⟩

end Overfull.Multigraph
