import Overfull.CompatibleCircuits.LocalCoarsening
import Overfull.CompatibleCircuits.ThreeLabelBundles
import Overfull.CompatibleCircuits.FourLabel

/-!
# Safe parallel-pair selection in equal bundles

When neither of the two equal incident bundles is an original incidence
class, the local coarsening is nonconstant on each bundle. Applying the
two-coordinate selector at both ends produces a compatible parallel pair
meeting every local tight class. If no nonlocal singleton constraint is
tight, this pair is an actual safely removable circuit in the original
three-label multigraph. This proves that branch of the selector; the
nonlocal-tight and unequal-bundle branches are separate obligations.
-/

namespace Overfull.CompatibleCircuits

open Finset Classical

variable {E K L : Type*}

/-- In two equal disjoint bundles, a coarsening can be constant on one
bundle only if one of the two bundles is an entire original class. -/
theorem LocalCoarsening.nonconstant_on_equal_bundle
    (B D : Finset E) (classOf : E → K) (hBD : Disjoint B D)
    (hcard : D.card = B.card) (hpos : 0 < B.card)
    (L : LocalCoarsening (B ∪ D) classOf)
    (hB : ∀ k, (B.filter (fun e => classOf e = k)).card < B.card)
    (hD : ∀ k, (D.filter (fun e => classOf e = k)).card < D.card) :
    ∃ e ∈ B, ∃ h ∈ B, L.coarse e ≠ L.coarse h := by
  obtain ⟨b, hb⟩ := card_pos.mp hpos
  by_contra! hconstant
  rcases L.identity_or_tight with hidentity | ⟨k, hk, hbinary⟩
  · have hmono (e : E) (he : e ∈ B) : classOf e = classOf b := by
      apply Sum.inl.inj (β := Bool)
      rw [← hidentity e, ← hidentity b]
      exact hconstant e he b hb
    have hfilter : B.filter (fun e => classOf e = classOf b) = B :=
      filter_eq_self.mpr hmono
    have hlt := hB (classOf b)
    rw [hfilter] at hlt
    omega
  · have hdecide (e : E) (he : e ∈ B) :
        decide (classOf e = k) = decide (classOf b = k) := by
      apply Sum.inr.inj (α := K)
      rw [← hbinary e, ← hbinary b]
      exact hconstant e he b hb
    by_cases hbk : classOf b = k
    · have hmono (e : E) (he : e ∈ B) : classOf e = k := by
        have h := hdecide e he
        simpa [hbk] using h
      have hfilter : B.filter (fun e => classOf e = k) = B :=
        filter_eq_self.mpr hmono
      have hlt := hB k
      rw [hfilter] at hlt
      omega
    · have hmono (e : E) (he : e ∈ B) : classOf e ≠ k := by
        have h := hdecide e he
        simpa [hbk] using h
      have hfilter : (B ∪ D).filter (fun e => classOf e = k) =
          D.filter (fun e => classOf e = k) := by
        ext e
        simp only [mem_filter, mem_union]
        constructor
        · rintro ⟨he | he, hclass⟩
          · exact False.elim (hmono e he hclass)
          · exact ⟨he, hclass⟩
        · rintro ⟨he, hclass⟩
          exact ⟨Or.inr he, hclass⟩
      rw [hfilter, card_union_of_disjoint hBD, ← hcard] at hk
      have hlt := hD k
      omega

/-- Two endpoint coarsenings on a common equal bundle yield a pair
meeting all local tight classes at both ends if neither incident bundle
is an entire original class. -/
theorem exists_pair_meeting_tight_classes_of_equal_bundles
    (AB AC BC : Finset E) (a : E → K) (b : E → L)
    (hABAC : Disjoint AB AC) (hABBC : Disjoint AB BC)
    (hAC : AC.card = AB.card) (hBC : BC.card = AB.card) (hpos : 0 < AB.card)
    (hA : ∀ k, 2 * ((AB ∪ AC).filter (fun e => a e = k)).card ≤ (AB ∪ AC).card)
    (hB : ∀ k, 2 * ((AB ∪ BC).filter (fun e => b e = k)).card ≤ (AB ∪ BC).card)
    (hAAB : ∀ k, (AB.filter (fun e => a e = k)).card < AB.card)
    (hAAC : ∀ k, (AC.filter (fun e => a e = k)).card < AC.card)
    (hBAB : ∀ k, (AB.filter (fun e => b e = k)).card < AB.card)
    (hBBC : ∀ k, (BC.filter (fun e => b e = k)).card < BC.card) :
    ∃ e ∈ AB, ∃ h ∈ AB, e ≠ h ∧ a e ≠ a h ∧ b e ≠ b h ∧
      (∀ k, 2 * ((AB ∪ AC).filter (fun d => a d = k)).card = (AB ∪ AC).card →
        a e = k ∨ a h = k) ∧
      (∀ k, 2 * ((AB ∪ BC).filter (fun d => b d = k)).card = (AB ∪ BC).card →
        b e = k ∨ b h = k) := by
  obtain ⟨La⟩ := exists_localCoarsening (AB ∪ AC) a hA
  obtain ⟨Lb⟩ := exists_localCoarsening (AB ∪ BC) b hB
  obtain ⟨e, he, h, hh, hne, hae, hbe⟩ :=
    exists_pair_distinct_both_coordinates AB La.coarse Lb.coarse
      (La.nonconstant_on_equal_bundle AB AC a hABAC hAC hpos hAAB hAAC)
      (Lb.nonconstant_on_equal_bundle AB BC b hABBC hBC hpos hBAB hBBC)
  refine ⟨e, he, h, hh, hne, La.refines e h hae, Lb.refines e h hbe, ?_, ?_⟩
  · intro k hk
    exact La.meets_tight k hk e (mem_union_left AC he) h (mem_union_left AC hh) hae
  · intro k hk
    exact Lb.meets_tight k hk e (mem_union_left BC he) h (mem_union_left BC hh) hbe

end Overfull.CompatibleCircuits

namespace Overfull.Multigraph

open Finset Classical

variable {E K : Type*} (Q : Multigraph (Fin 3) E)

/-- Distinct classes at the two endpoints make a parallel pair compatible. -/
theorem compatible_parallel_pair (classOf : Fin 3 → E → K) {e h : E}
    (he : Q.edge e = s(0, 1)) (hh : Q.edge h = s(0, 1))
    (h0 : classOf 0 e ≠ classOf 0 h) (h1 : classOf 1 e ≠ classOf 1 h) :
    Q.Compatible classOf {e, h} := by
  intro v d hd hvd f hf hvf hclass
  simp only [mem_insert, mem_singleton] at hd hf
  rcases hd with rfl | rfl <;> rcases hf with rfl | rfl
  all_goals try rfl
  all_goals fin_cases v <;> simp_all

/-- Without a nonlocal tight singleton constraint, meeting all local
tight classes at the two ends is sufficient for safe pair deletion. -/
theorem admissibleOn_sdiff_parallel_pair_of_no_nonlocal_tight
    (classOf : Fin 3 → E → K) {C : Finset E} {e h : E}
    (heC : e ∈ C) (hhC : h ∈ C) (hne : e ≠ h)
    (he : Q.edge e = s(0, 1)) (hh : Q.edge h = s(0, 1))
    (hadmissible : Q.AdmissibleOn classOf C)
    (heven : ∀ v, Even (Q.degreeOn C v))
    (hno : ∀ v k w, v ≠ w →
      Q.degreeOn C w ≠ 2 * (Q.classCutOn classOf C v k {w}).card)
    (hmeet0 : ∀ k, Q.degreeOn C 0 = 2 * (Q.classCutOn classOf C 0 k {0}).card →
      classOf 0 e = k ∨ classOf 0 h = k)
    (hmeet1 : ∀ k, Q.degreeOn C 1 = 2 * (Q.classCutOn classOf C 1 k {1}).card →
      classOf 1 e = k ∨ classOf 1 h = k) :
    Q.AdmissibleOn classOf (C \ {e, h}) := by
  have hsub : ({e, h} : Finset E) ⊆ C := by
    intro d hd
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl <;> assumption
  apply (Q.admissibleOn_sdiff_iff_meets_tight_singletons (by simp) classOf hsub
    (Q.isCircuit_parallel_pair hne (he.trans hh.symm)) hadmissible heven).mpr
  intro v k w htight hcross
  by_cases hvw : v = w
  · subst v
    fin_cases w
    · rcases hmeet0 k htight with heclass | hhclass
      · refine ⟨e, ?_⟩
        simp [Q.classCutOn_singleton_self, he, heclass]
      · refine ⟨h, ?_⟩
        simp [Q.classCutOn_singleton_self, hh, hhclass]
    · rcases hmeet1 k htight with heclass | hhclass
      · refine ⟨e, ?_⟩
        simp [Q.classCutOn_singleton_self, he, heclass]
      · refine ⟨h, ?_⟩
        simp [Q.classCutOn_singleton_self, hh, hhclass]
    · simp [Q.cutOn_singleton, filter_insert, filter_singleton, he, hh] at hcross
  · exact False.elim (hno v k w hvw htight)

/-- The equal-bundle case without a nonlocal tight class has an actual
compatible parallel pair whose deletion preserves all cut inequalities. -/
theorem exists_safe_parallel_pair_of_equal_bundles_no_nonlocal_tight
    (classOf : Fin 3 → E → K) (C : Finset E)
    (hadmissible : Q.AdmissibleOn classOf C)
    (heven : ∀ v, Even (Q.degreeOn C v))
    (hAC : (Q.edgeBundleOn C 0 2).card = (Q.edgeBundleOn C 0 1).card)
    (hBC : (Q.edgeBundleOn C 1 2).card = (Q.edgeBundleOn C 0 1).card)
    (hpos : 0 < (Q.edgeBundleOn C 0 1).card)
    (hno : ∀ v k w, v ≠ w →
      Q.degreeOn C w ≠ 2 * (Q.classCutOn classOf C v k {w}).card) :
    ∃ D : Finset E, D ⊆ C ∧ Q.IsCircuit D ∧ Q.Compatible classOf D ∧
      D.card = 2 ∧ Q.AdmissibleOn classOf (C \ D) := by
  let AB := Q.edgeBundleOn C 0 1
  let AC := Q.edgeBundleOn C 0 2
  let BC := Q.edgeBundleOn C 1 2
  have hABAC : Disjoint AB AC := Q.edgeBundleOn_disjoint (by decide)
  have hABBC : Disjoint AB BC := Q.edgeBundleOn_disjoint (by decide)
  have hd0 : Q.degreeOn C 0 = (AB ∪ AC).card := by
    rw [card_union_of_disjoint hABAC]
    exact Q.threeLabel_degree_zero C
  have hd1 : Q.degreeOn C 1 = (AB ∪ BC).card := by
    rw [card_union_of_disjoint hABBC]
    exact Q.threeLabel_degree_one C
  have hclass0 (k : K) : Q.classCutOn classOf C 0 k {0} =
      (AB ∪ AC).filter (fun e => classOf 0 e = k) := by
    calc
      _ = (C.filter (fun e => (0 : Fin 3) ∈ Q.edge e)).filter
          (fun e => classOf 0 e = k) := by
        ext e
        simp [classCutOn, Q.cutOn_singleton, and_assoc]
      _ = _ := by rw [Q.threeLabel_incident_zero]
  have hclass1 (k : K) : Q.classCutOn classOf C 1 k {1} =
      (AB ∪ BC).filter (fun e => classOf 1 e = k) := by
    calc
      _ = (C.filter (fun e => (1 : Fin 3) ∈ Q.edge e)).filter
          (fun e => classOf 1 e = k) := by
        ext e
        simp [classCutOn, Q.cutOn_singleton, and_assoc]
      _ = _ := by rw [Q.threeLabel_incident_one]
  have hA (k : K) : 2 * ((AB ∪ AC).filter (fun e => classOf 0 e = k)).card ≤
      (AB ∪ AC).card := by
    simpa only [hclass0, Q.cutOn_singleton_card, hd0] using hadmissible 0 k {0}
  have hB (k : K) : 2 * ((AB ∪ BC).filter (fun e => classOf 1 e = k)).card ≤
      (AB ∪ BC).card := by
    simpa only [hclass1, Q.cutOn_singleton_card, hd1] using hadmissible 1 k {1}
  have hAAB (k : K) : (AB.filter (fun e => classOf 0 e = k)).card < AB.card := by
    have hn := hno 0 k 1 (by decide)
    rw [Q.classCutOn_singleton_other classOf C (by decide), Q.threeLabel_degree_one,
      hBC] at hn
    have hb := card_filter_le AB (fun e => classOf 0 e = k)
    change AB.card + AB.card ≠ 2 * (AB.filter (fun e => classOf 0 e = k)).card at hn
    omega
  have hAAC (k : K) : (AC.filter (fun e => classOf 0 e = k)).card < AC.card := by
    have hn := hno 0 k 2 (by decide)
    rw [Q.classCutOn_singleton_other classOf C (by decide), Q.threeLabel_degree_two,
      hAC, hBC] at hn
    have hb := card_filter_le AC (fun e => classOf 0 e = k)
    have hc : AC.card = AB.card := hAC
    change AB.card + AB.card ≠ 2 * (AC.filter (fun e => classOf 0 e = k)).card at hn
    omega
  have hBAB (k : K) : (AB.filter (fun e => classOf 1 e = k)).card < AB.card := by
    have hn := hno 1 k 0 (by decide)
    rw [Q.classCutOn_singleton_other classOf C (by decide),
      Q.edgeBundleOn_swap C 1 0, Q.threeLabel_degree_zero, hAC] at hn
    have hb := card_filter_le AB (fun e => classOf 1 e = k)
    change AB.card + AB.card ≠ 2 * (AB.filter (fun e => classOf 1 e = k)).card at hn
    omega
  have hBBC (k : K) : (BC.filter (fun e => classOf 1 e = k)).card < BC.card := by
    have hn := hno 1 k 2 (by decide)
    rw [Q.classCutOn_singleton_other classOf C (by decide), Q.threeLabel_degree_two,
      hAC, hBC] at hn
    have hb := card_filter_le BC (fun e => classOf 1 e = k)
    have hc : BC.card = AB.card := hBC
    change AB.card + AB.card ≠ 2 * (BC.filter (fun e => classOf 1 e = k)).card at hn
    omega
  obtain ⟨e, heB, h, hhB, hne, h0, h1, ht0, ht1⟩ :=
    CompatibleCircuits.exists_pair_meeting_tight_classes_of_equal_bundles AB AC BC
      (classOf 0) (classOf 1) hABAC hABBC hAC hBC hpos hA hB hAAB hAAC hBAB hBBC
  obtain ⟨heC, he⟩ := Q.mem_edgeBundleOn C 0 1 e |>.mp heB
  obtain ⟨hhC, hh⟩ := Q.mem_edgeBundleOn C 0 1 h |>.mp hhB
  have hsub : ({e, h} : Finset E) ⊆ C := by
    intro d hd
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl <;> assumption
  refine ⟨{e, h}, hsub, Q.isCircuit_parallel_pair hne (he.trans hh.symm),
    Q.compatible_parallel_pair classOf he hh h0 h1, by simp [hne], ?_⟩
  apply Q.admissibleOn_sdiff_parallel_pair_of_no_nonlocal_tight classOf heC hhC hne
    he hh hadmissible heven hno
  · intro k hk
    apply ht0 k
    rw [← hclass0, ← hd0]
    exact hk.symm
  · intro k hk
    apply ht1 k
    rw [← hclass1, ← hd1]
    exact hk.symm

end Overfull.Multigraph
