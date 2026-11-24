import Overfull.CompatibleCircuits.LocalCoarsening
import Overfull.CompatibleCircuits.ThreeLabelBundles
import Overfull.CompatibleCircuits.FourLabel

/-!
# Selecting the safe parallel pair for unequal bundles

The finite sets below retain actual edge-copy identities. The class bounds
are precisely the local and nonlocal singleton-cut bounds for the two
ends of a prospective parallel pair. Under `|AB| > |BC|` and
`|AC| ≥ |BC|`, a pair in `AB` can be chosen compatible at both ends and
meeting every tight class on the two cuts that it crosses. The third
vertex's potential tight constraints are excluded by separate cardinal
inequalities. No circuit-selector hypothesis is assumed.
-/

namespace Overfull.CompatibleCircuits

open Finset Classical

variable {E K L : Type*}

theorem fiber_card_union_of_disjoint (S T : Finset E) (f : E → K)
    (hST : Disjoint S T) (k : K) :
    ((S ∪ T).filter (fun e => f e = k)).card =
      (S.filter (fun e => f e = k)).card + (T.filter (fun e => f e = k)).card := by
  rw [filter_union, card_union_of_disjoint
    (hST.mono (filter_subset _ _) (filter_subset _ _))]

/-- Two disjoint class fibers whose sizes cover the ambient set really
cover every actual copy of that set. -/
theorem mem_one_of_two_classes_of_card_sum
    (S : Finset E) (f : E → K) {k l : K} (hkl : k ≠ l)
    (hsize : S.card ≤ (S.filter (fun e => f e = k)).card +
      (S.filter (fun e => f e = l)).card)
    {e : E} (he : e ∈ S) : f e = k ∨ f e = l := by
  have hd : Disjoint (S.filter (fun a => f a = k))
      (S.filter (fun a => f a = l)) := by
    apply disjoint_left.mpr
    intro a ha hb
    exact hkl ((mem_filter.mp ha).2.symm.trans (mem_filter.mp hb).2)
  have hsub : S.filter (fun a => f a = k) ∪ S.filter (fun a => f a = l) ⊆ S :=
    union_subset (filter_subset _ _) (filter_subset _ _)
  have hcover : S.filter (fun a => f a = k) ∪ S.filter (fun a => f a = l) = S := by
    apply eq_of_subset_of_card_le hsub
    rwa [card_union_of_disjoint hd]
  have hh : e ∈ S.filter (fun a => f a = k) ∪ S.filter (fun a => f a = l) := by
    rw [hcover]
    exact he
  rcases mem_union.mp hh with h | h
  · exact Or.inl (mem_filter.mp h).2
  · exact Or.inr (mem_filter.mp h).2

/-- The coarsening of the first endpoint is nonconstant even when `AB`
has exactly half its degree: the two nonlocal bounds exclude both a
monochromatic bundle and a tight class disjoint from that bundle. -/
theorem LocalCoarsening.nonconstant_on_dominant_bundle
    (AB AC : Finset E) (f : E → K) (z : ℕ)
    (hdisj : Disjoint AB AC) (hxz : z < AB.card)
    (hAB : ∀ k, 2 * (AB.filter (fun e => f e = k)).card ≤ AB.card + z)
    (hAC : ∀ k, 2 * (AC.filter (fun e => f e = k)).card ≤ AC.card + z)
    (Q : LocalCoarsening (AB ∪ AC) f) :
    ∃ e ∈ AB, ∃ h ∈ AB, Q.coarse e ≠ Q.coarse h := by
  have hpos : 0 < AB.card := by omega
  obtain ⟨a, ha⟩ := card_pos.mp hpos
  by_contra! hconstant
  have hwhole (k : K) (hk : ∀ e ∈ AB, f e = k) : False := by
    have hsub : AB ⊆ AB.filter (fun e => f e = k) :=
      fun e he => mem_filter.mpr ⟨he, hk e he⟩
    have hcard := card_le_card hsub
    have hbound := hAB k
    omega
  rcases Q.identity_or_tight with hid | ⟨k, hk, hbin⟩
  · apply hwhole (f a)
    intro e he
    have hh := hconstant e he a ha
    simpa only [hid, Sum.inl.injEq] using hh
  · by_cases hak : f a = k
    · apply hwhole k
      intro e he
      have hh := hconstant e he a ha
      simpa [hbin, hak] using hh
    · have hempty : AB.filter (fun e => f e = k) = ∅ := by
        apply filter_eq_empty_iff.mpr
        intro e he hek
        have hh := hconstant e he a ha
        simp [hbin, hak, hek] at hh
      have hsum := fiber_card_union_of_disjoint AB AC f hdisj k
      have htotal := card_union_of_disjoint hdisj
      have hbound := hAC k
      rw [hempty, card_empty] at hsum
      omega

/-- A nonlocal tight class on the larger bundle can be used as a binary
coordinate. Crossing it also meets every other local or relevant
nonlocal tight class at that endpoint. -/
theorem pair_meets_endpoint_tight_classes_of_crossing_nonlocal
    (AB AC : Finset E) (f : E → K) (z : ℕ)
    (hdisj : Disjoint AB AC)
    (hAC : ∀ k, 2 * (AC.filter (fun e => f e = k)).card ≤ AC.card + z)
    {k : K} (hk : 2 * (AB.filter (fun e => f e = k)).card = AB.card + z)
    {e h : E} (he : e ∈ AB) (hh : h ∈ AB)
    (hdiff : decide (f e = k) ≠ decide (f h = k)) :
    f e ≠ f h ∧
      ∀ l, (2 * ((AB ∪ AC).filter (fun a => f a = l)).card = (AB ∪ AC).card ∨
        2 * (AB.filter (fun a => f a = l)).card = AB.card + z) →
        f e = l ∨ f h = l := by
  refine ⟨?_, ?_⟩
  · intro heq
    apply hdiff
    rw [heq]
  · intro l hl
    by_cases hlk : l = k
    · subst l
      by_contra! hn
      exact hdiff (by simp [hn.1, hn.2])
    · have hcover : AB.card ≤ (AB.filter (fun a => f a = k)).card +
          (AB.filter (fun a => f a = l)).card := by
        rcases hl with hlocal | hnonlocal
        · have hsum := fiber_card_union_of_disjoint AB AC f hdisj l
          have htotal := card_union_of_disjoint hdisj
          have hbound := hAC l
          omega
        · omega
      rcases mem_one_of_two_classes_of_card_sum AB f (Ne.symm hlk) hcover he with
        hek | hel
      · rcases mem_one_of_two_classes_of_card_sum AB f (Ne.symm hlk) hcover hh with
          hhk | hhl
        · exact False.elim (hdiff (by simp [hek, hhk]))
        · exact Or.inr hhl
      · exact Or.inl hel

/-- In the unequal-bundle case, a nonlocal tight class at the second
endpoint is already locally tight. -/
theorem local_tight_of_second_endpoint_nonlocal_tight
    (AB AC BC : Finset E) (g : E → L) (hdisj : Disjoint AB BC)
    (hyz : BC.card ≤ AC.card)
    (hlocal : ∀ l, 2 * ((AB ∪ BC).filter (fun e => g e = l)).card ≤ (AB ∪ BC).card)
    {l : L} (htight : 2 * (AB.filter (fun e => g e = l)).card = AB.card + AC.card) :
    2 * ((AB ∪ BC).filter (fun e => g e = l)).card = (AB ∪ BC).card := by
  have hsub : AB.filter (fun e => g e = l) ⊆
      (AB ∪ BC).filter (fun e => g e = l) :=
    filter_subset_filter _ subset_union_left
  have hcard := card_le_card hsub
  have hbound := hlocal l
  have htotal := card_union_of_disjoint hdisj
  omega

/-- The full finite-copy pair selector for the unequal-bundle case.
It derives compatibility and all required endpoint tight-class witnesses
from the original class bounds; no selector or pair witness is assumed. -/
theorem exists_pair_meeting_tight_classes_of_unequal_bundles
    (AB AC BC : Finset E) (f : E → K) (g : E → L)
    (hABAC : Disjoint AB AC) (hABBC : Disjoint AB BC)
    (hxz : BC.card < AB.card) (hyz : BC.card ≤ AC.card)
    (hf : ∀ k, 2 * ((AB ∪ AC).filter (fun e => f e = k)).card ≤ (AB ∪ AC).card)
    (hg : ∀ l, 2 * ((AB ∪ BC).filter (fun e => g e = l)).card ≤ (AB ∪ BC).card)
    (hfAB : ∀ k, 2 * (AB.filter (fun e => f e = k)).card ≤ AB.card + BC.card)
    (hfAC : ∀ k, 2 * (AC.filter (fun e => f e = k)).card ≤ AC.card + BC.card) :
    ∃ e ∈ AB, ∃ h ∈ AB, e ≠ h ∧ f e ≠ f h ∧ g e ≠ g h ∧
      (∀ k, (2 * ((AB ∪ AC).filter (fun a => f a = k)).card = (AB ∪ AC).card ∨
        2 * (AB.filter (fun a => f a = k)).card = AB.card + BC.card) →
        f e = k ∨ f h = k) ∧
      (∀ l, (2 * ((AB ∪ BC).filter (fun a => g a = l)).card = (AB ∪ BC).card ∨
        2 * (AB.filter (fun a => g a = l)).card = AB.card + AC.card) →
        g e = l ∨ g h = l) := by
  obtain ⟨Qg⟩ := exists_localCoarsening (AB ∪ BC) g hg
  have hlarge : (AB ∪ BC).card < 2 * AB.card := by
    rw [card_union_of_disjoint hABBC]
    omega
  have hgnon := Qg.nonconstant_on_large_subset (S := AB) subset_union_left hlarge
  have hmeetg {e h : E} (he : e ∈ AB) (hh : h ∈ AB)
      (hd : Qg.coarse e ≠ Qg.coarse h) (l : L)
      (hl : 2 * ((AB ∪ BC).filter (fun a => g a = l)).card = (AB ∪ BC).card ∨
        2 * (AB.filter (fun a => g a = l)).card = AB.card + AC.card) :
      g e = l ∨ g h = l := by
    apply Qg.meets_tight l _ e (mem_union_left _ he) h (mem_union_left _ hh) hd
    rcases hl with hl | hl
    · exact hl
    · exact local_tight_of_second_endpoint_nonlocal_tight AB AC BC g hABBC hyz hg hl
  by_cases htight : ∃ k, 2 * (AB.filter (fun e => f e = k)).card = AB.card + BC.card
  · obtain ⟨k, hk⟩ := htight
    have hpos : 0 < (AB.filter (fun e => f e = k)).card := by omega
    have hlt : (AB.filter (fun e => f e = k)).card < AB.card := by omega
    have hsum := AB.filter_card_add_filter_neg_card_eq_card (fun e => f e = k)
    have hnegpos : 0 < (AB.filter (fun e => ¬ f e = k)).card := by omega
    obtain ⟨a, ha⟩ := card_pos.mp hpos
    obtain ⟨b, hb⟩ := card_pos.mp hnegpos
    have hbin : ∃ a ∈ AB, ∃ b ∈ AB,
        decide (f a = k) ≠ decide (f b = k) :=
      ⟨a, (mem_filter.mp ha).1, b, (mem_filter.mp hb).1,
        by simp [(mem_filter.mp ha).2, (mem_filter.mp hb).2]⟩
    obtain ⟨e, he, h, hh, hne, hfd, hgd⟩ :=
      exists_pair_distinct_both_coordinates AB (fun a => decide (f a = k)) Qg.coarse hbin hgnon
    have hmeetf := pair_meets_endpoint_tight_classes_of_crossing_nonlocal
      AB AC f BC.card hABAC hfAC hk he hh hfd
    exact ⟨e, he, h, hh, hne, hmeetf.1, Qg.refines e h hgd,
      hmeetf.2, fun l hl => hmeetg he hh hgd l hl⟩
  · obtain ⟨Qf⟩ := exists_localCoarsening (AB ∪ AC) f hf
    have hfnon := Qf.nonconstant_on_dominant_bundle AB AC f BC.card hABAC hxz hfAB hfAC
    obtain ⟨e, he, h, hh, hne, hfd, hgd⟩ :=
      exists_pair_distinct_both_coordinates AB Qf.coarse Qg.coarse hfnon hgnon
    refine ⟨e, he, h, hh, hne, Qf.refines e h hfd, Qg.refines e h hgd, ?_,
      fun l hl => hmeetg he hh hgd l hl⟩
    intro k hk
    rcases hk with hk | hk
    · exact Qf.meets_tight k hk e (mem_union_left _ he) h (mem_union_left _ hh) hfd
    · exact False.elim (htight ⟨k, hk⟩)

end Overfull.CompatibleCircuits

namespace Overfull.Multigraph

open Finset Classical CompatibleCircuits

variable {E K : Type*} (Q : Multigraph (Fin 3) E)

/-- An actual safely removable parallel pair in the unequal-bundle case.
The original admissibility and parity hypotheses imply all selection
bounds; no tight-class witness or compatible pair is assumed. -/
theorem exists_safe_parallel_pair_of_unequal_threeLabel_bundles
    (classOf : Fin 3 → E → K) (C : Finset E)
    (hadmissible : Q.AdmissibleOn classOf C)
    (heven : ∀ v, Even (Q.degreeOn C v))
    (hxz : (Q.edgeBundleOn C 1 2).card < (Q.edgeBundleOn C 0 1).card)
    (hyz : (Q.edgeBundleOn C 1 2).card ≤ (Q.edgeBundleOn C 0 2).card) :
    ∃ D ⊆ C, Q.IsCircuit D ∧ Q.Compatible classOf D ∧
      Q.AdmissibleOn classOf (C \ D) ∧ D.card = 2 := by
  classical
  let AB := Q.edgeBundleOn C 0 1
  let AC := Q.edgeBundleOn C 0 2
  let BC := Q.edgeBundleOn C 1 2
  have hdABAC : Disjoint AB AC := Q.edgeBundleOn_disjoint (by decide)
  have hdABBC : Disjoint AB BC := Q.edgeBundleOn_disjoint (by decide)
  have hlocal0 (k : K) : Q.classCutOn classOf C 0 k {0} =
      (AB ∪ AC).filter (fun e => classOf 0 e = k) := by
    rw [Q.classCutOn_singleton_self]
    change _ = (Q.edgeBundleOn C 0 1 ∪ Q.edgeBundleOn C 0 2).filter _
    rw [← Q.threeLabel_incident_zero C]
    ext e
    simp [and_assoc]
  have hlocal1 (k : K) : Q.classCutOn classOf C 1 k {1} =
      (AB ∪ BC).filter (fun e => classOf 1 e = k) := by
    rw [Q.classCutOn_singleton_self]
    change _ = (Q.edgeBundleOn C 0 1 ∪ Q.edgeBundleOn C 1 2).filter _
    rw [← Q.threeLabel_incident_one C]
    ext e
    simp [and_assoc]
  have hdegree0 : Q.degreeOn C 0 = (AB ∪ AC).card := by
    rw [card_union_of_disjoint hdABAC]
    exact Q.threeLabel_degree_zero C
  have hdegree1 : Q.degreeOn C 1 = (AB ∪ BC).card := by
    rw [card_union_of_disjoint hdABBC]
    exact Q.threeLabel_degree_one C
  have hsingle := (Q.admissibleOn_iff_singleton_cuts (by simp) classOf C).mp hadmissible
  have hbound0 (k : K) : 2 * ((AB ∪ AC).filter (fun e => classOf 0 e = k)).card ≤
      (AB ∪ AC).card := by
    simpa only [hlocal0, hdegree0] using hsingle 0 k 0
  have hbound1 (k : K) : 2 * ((AB ∪ BC).filter (fun e => classOf 1 e = k)).card ≤
      (AB ∪ BC).card := by
    simpa only [hlocal1, hdegree1] using hsingle 1 k 1
  have hboundAB (k : K) : 2 * (AB.filter (fun e => classOf 0 e = k)).card ≤
      AB.card + BC.card := by
    simpa only [Q.classCutOn_singleton_other classOf C (by decide : (0 : Fin 3) ≠ 1),
      Q.threeLabel_degree_one] using hsingle 0 k 1
  have hboundAC (k : K) : 2 * (AC.filter (fun e => classOf 0 e = k)).card ≤
      AC.card + BC.card := by
    simpa only [Q.classCutOn_singleton_other classOf C (by decide : (0 : Fin 3) ≠ 2),
      Q.threeLabel_degree_two] using hsingle 0 k 2
  obtain ⟨e, he, h, hh, hne, hf, hg, hmeet0, hmeet1⟩ :=
    exists_pair_meeting_tight_classes_of_unequal_bundles AB AC BC
      (classOf 0) (classOf 1) hdABAC hdABBC hxz hyz hbound0 hbound1 hboundAB hboundAC
  have hedgee : Q.edge e = s(0, 1) := (Q.mem_edgeBundleOn C 0 1 e |>.mp he).2
  have hedgeh : Q.edge h = s(0, 1) := (Q.mem_edgeBundleOn C 0 1 h |>.mp hh).2
  let D : Finset E := {e, h}
  have hDC : D ⊆ C := by
    intro d hd
    rcases mem_insert.mp hd with hde | hd
    · subst d
      exact (Q.mem_edgeBundleOn C 0 1 e |>.mp he).1
    · have hdh := mem_singleton.mp hd
      subst d
      exact (Q.mem_edgeBundleOn C 0 1 h |>.mp hh).1
  have hcircuit : Q.IsCircuit D :=
    Q.isCircuit_parallel_pair hne (hedgee.trans hedgeh.symm)
  have hcomp : Q.Compatible classOf D := by
    intro v d hd hvd d' hd' hvd' hclass
    simp only [D, mem_insert, mem_singleton] at hd hd'
    rcases hd with rfl | rfl <;> rcases hd' with rfl | rfl
    all_goals try rfl
    all_goals fin_cases v <;> simp_all
  refine ⟨D, hDC, hcircuit, hcomp, ?_, by simp [D, hne]⟩
  apply (Q.admissibleOn_sdiff_iff_meets_tight_singletons (by simp)
    classOf hDC hcircuit hadmissible heven).mpr
  have hwitness (v w : Fin 3) (k : K) (hv : v = 0 ∨ v = 1) (hw : w = 0 ∨ w = 1)
      (hclass : classOf v e = k ∨ classOf v h = k) :
      (Q.classCutOn classOf D v k {w}).Nonempty := by
    rcases hclass with heclass | hhclass
    · refine ⟨e, ?_⟩
      simp only [classCutOn, Q.cutOn_singleton, mem_filter]
      refine ⟨⟨by simp [D], ?_⟩, ?_, heclass⟩
      · rcases hw with rfl | rfl <;> simp [hedgee]
      · rcases hv with rfl | rfl <;> simp [hedgee]
    · refine ⟨h, ?_⟩
      simp only [classCutOn, Q.cutOn_singleton, mem_filter]
      refine ⟨⟨by simp [D], ?_⟩, ?_, hhclass⟩
      · rcases hw with rfl | rfl <;> simp [hedgeh]
      · rcases hv with rfl | rfl <;> simp [hedgeh]
  have hcases (v : Fin 3) : v = 0 ∨ v = 1 ∨ v = 2 := by
    fin_cases v <;> simp
  intro v k w htight hcross
  rcases hcases w with rfl | rfl | rfl
  · rcases hcases v with rfl | rfl | rfl
    · apply hwitness 0 0 k (Or.inl rfl) (Or.inl rfl)
      apply hmeet0 k (Or.inl ?_)
      simpa only [hlocal0, hdegree0] using htight.symm
    · apply hwitness 1 0 k (Or.inr rfl) (Or.inl rfl)
      apply hmeet1 k (Or.inr ?_)
      simpa only [Q.classCutOn_singleton_other classOf C (by decide : (1 : Fin 3) ≠ 0),
        Q.edgeBundleOn_swap C 1 0, Q.threeLabel_degree_zero] using htight.symm
    · have hsub : Q.classCutOn classOf C 2 k {0} ⊆ Q.classCutOn classOf C 2 k {2} := by
        intro d hd
        simp only [classCutOn, mem_filter, Q.mem_cutOn] at hd
        simpa only [Q.classCutOn_singleton_self, mem_filter] using And.intro hd.1.1 hd.2
      have hcard := card_le_card hsub
      have hb := hsingle 2 k 2
      have hdeg0 := Q.threeLabel_degree_zero C
      have hdeg2 := Q.threeLabel_degree_two C
      omega
  · rcases hcases v with rfl | rfl | rfl
    · apply hwitness 0 1 k (Or.inl rfl) (Or.inr rfl)
      apply hmeet0 k (Or.inr ?_)
      simpa only [Q.classCutOn_singleton_other classOf C (by decide : (0 : Fin 3) ≠ 1),
        Q.threeLabel_degree_one] using htight.symm
    · apply hwitness 1 1 k (Or.inr rfl) (Or.inr rfl)
      apply hmeet1 k (Or.inl ?_)
      simpa only [hlocal1, hdegree1] using htight.symm
    · have hcard : (Q.classCutOn classOf C 2 k {1}).card ≤ BC.card := by
        rw [Q.classCutOn_singleton_other classOf C (by decide : (2 : Fin 3) ≠ 1),
          Q.edgeBundleOn_swap C 2 1]
        exact card_le_card (filter_subset _ _)
      have hdeg1 := Q.threeLabel_degree_one C
      change BC.card < AB.card at hxz
      change Q.degreeOn C 1 = AB.card + BC.card at hdeg1
      omega
  · have hcut : Q.cutOn D {(2 : Fin 3)} = ∅ := by
      rw [Q.cutOn_singleton]
      simp [D, hedgee, hedgeh]
    rw [hcut] at hcross
    exact False.elim (not_nonempty_empty hcross)

end Overfull.Multigraph
