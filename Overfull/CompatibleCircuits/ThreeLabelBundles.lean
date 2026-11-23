import Overfull.CompatibleCircuits.ThreeVertexDeletion

/-!
# Actual bundles and singleton-cut inequalities on three labels

Every edge copy is retained in exactly one unordered endpoint bundle.
For at most three vertices, all class-cut inequalities reduce to the
singleton cuts.  At a distinct vertex, the singleton class-cut is exactly
the appropriate parallel bundle filtered by its original incidence class.
These are identities, not an assumption that a safe selector exists.
-/

namespace Overfull.Multigraph

open Finset Classical

variable {V E K : Type*} (G : Multigraph V E)

/-- Actual selected copies with the specified unordered pair of ends. -/
noncomputable def edgeBundleOn (C : Finset E) (u v : V) : Finset E :=
  C.filter (fun e => G.edge e = s(u, v))

@[simp] theorem mem_edgeBundleOn (C : Finset E) (u v : V) (e : E) :
    e ∈ G.edgeBundleOn C u v ↔ e ∈ C ∧ G.edge e = s(u, v) := by
  simp [edgeBundleOn]

theorem edgeBundleOn_subset (C : Finset E) (u v : V) :
    G.edgeBundleOn C u v ⊆ C := filter_subset _ _

theorem edgeBundleOn_swap (C : Finset E) (u v : V) :
    G.edgeBundleOn C u v = G.edgeBundleOn C v u := by
  simp only [edgeBundleOn, Sym2.eq_swap (a := u) (b := v)]

theorem edgeBundleOn_disjoint {C : Finset E} {u v u' v' : V}
    (hne : s(u, v) ≠ s(u', v')) :
    Disjoint (G.edgeBundleOn C u v) (G.edgeBundleOn C u' v') := by
  apply disjoint_left.mpr
  intro e he he'
  exact hne ((G.mem_edgeBundleOn C u v e |>.mp he).2.symm.trans
    (G.mem_edgeBundleOn C u' v' e |>.mp he').2)

/-- A singleton cut consists of all incidences at that vertex. -/
theorem cutOn_singleton (C : Finset E) (v : V) :
    G.cutOn C {v} = C.filter (fun e => v ∈ G.edge e) := by
  ext e
  have hnot : ¬ (G.firstEnd e = v ∧ G.secondEnd e = v) :=
    fun h => G.endpoints_distinct e (h.1.trans h.2.symm)
  simp only [mem_cutOn, mem_singleton, mem_filter, G.incident_iff]
  tauto

theorem cutOn_singleton_card (C : Finset E) (v : V) :
    (G.cutOn C {v}).card = G.degreeOn C v := by
  rw [G.cutOn_singleton]
  rfl

theorem classCutOn_singleton_self (classOf : V → E → K)
    (C : Finset E) (v : V) (k : K) :
    G.classCutOn classOf C v k {v} =
      C.filter (fun e => v ∈ G.edge e ∧ classOf v e = k) := by
  ext e
  simp [classCutOn, G.cutOn_singleton, and_assoc]

/-- Distinct incident vertices determine the unordered ends of a copy. -/
theorem incident_pair_iff_edge_eq {u v : V} (hne : u ≠ v) (e : E) :
    (u ∈ G.edge e ∧ v ∈ G.edge e) ↔ G.edge e = s(u, v) := by
  rw [← G.edge_eq e]
  simp only [Sym2.mem_iff, Sym2.eq_iff]
  constructor
  · rintro ⟨hu | hu, hv | hv⟩
    · exact False.elim (hne (hu.trans hv.symm))
    · exact Or.inl ⟨hu.symm, hv.symm⟩
    · exact Or.inr ⟨hv.symm, hu.symm⟩
    · exact False.elim (hne (hu.trans hv.symm))
  · rintro (⟨hu, hv⟩ | ⟨hv, hu⟩) <;> simp_all

/-- Nonlocal singleton-cut classes are actual endpoint-bundle fibers. -/
theorem classCutOn_singleton_other (classOf : V → E → K)
    (C : Finset E) {v w : V} (hne : v ≠ w) (k : K) :
    G.classCutOn classOf C v k {w} =
      (G.edgeBundleOn C v w).filter (fun e => classOf v e = k) := by
  ext e
  simp only [classCutOn, G.cutOn_singleton, mem_filter, mem_edgeBundleOn]
  have hpair := G.incident_pair_iff_edge_eq hne e
  tauto

theorem cutOn_compl [Fintype V] (C : Finset E) (X : Finset V) :
    G.cutOn C Xᶜ = G.cutOn C X := by
  ext e
  simp only [mem_cutOn, mem_compl, ne_eq, eq_iff_iff]
  tauto

theorem classCutOn_compl [Fintype V] (classOf : V → E → K)
    (C : Finset E) (v : V) (k : K) (X : Finset V) :
    G.classCutOn classOf C v k Xᶜ = G.classCutOn classOf C v k X := by
  simp only [classCutOn, G.cutOn_compl]

/-- The local incidence-class half bound follows from its own singleton cut. -/
theorem AdmissibleOn.local_class_bound {classOf : V → E → K} {C : Finset E}
    (hadmissible : G.AdmissibleOn classOf C) (v : V) (k : K) :
    2 * (C.filter (fun e => v ∈ G.edge e ∧ classOf v e = k)).card ≤
      G.degreeOn C v := by
  simpa only [G.classCutOn_singleton_self, G.cutOn_singleton_card] using
    hadmissible v k {v}

/-- The nonlocal bound on a bundle uses the degree of its other endpoint. -/
theorem AdmissibleOn.bundle_class_bound {classOf : V → E → K} {C : Finset E}
    (hadmissible : G.AdmissibleOn classOf C) {v w : V} (hne : v ≠ w) (k : K) :
    2 * ((G.edgeBundleOn C v w).filter (fun e => classOf v e = k)).card ≤
      G.degreeOn C w := by
  simpa only [G.classCutOn_singleton_other classOf C hne, G.cutOn_singleton_card] using
    hadmissible v k {w}

/-- A shore on at most three labels is trivial, a singleton, or a
singleton complement. -/
theorem shore_cases_of_card_le_three [Fintype V]
    (hV : Fintype.card V ≤ 3) (X : Finset V) :
    X = ∅ ∨ X = univ ∨ ∃ w, X = {w} ∨ X = ({w} : Finset V)ᶜ := by
  by_cases hzero : X = ∅
  · exact Or.inl hzero
  by_cases hfull : X = univ
  · exact Or.inr (Or.inl hfull)
  apply Or.inr ∘ Or.inr
  have hpos : 0 < X.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hzero)
  have hlt : X.card < Fintype.card V := card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ X, hfull⟩)
  by_cases hone : X.card = 1
  · obtain ⟨w, hw⟩ := card_eq_one.mp hone
    exact ⟨w, Or.inl hw⟩
  · have hcomp : Xᶜ.card = 1 := by rw [card_compl]; omega
    obtain ⟨w, hw⟩ := card_eq_one.mp hcomp
    exact ⟨w, Or.inr (by rw [← hw, compl_compl])⟩

/-- On at most three vertices, no additional nonsingleton cut checks are
needed.  This includes empty graphs and vertex types with fewer labels. -/
theorem admissibleOn_iff_singleton_cuts [Fintype V]
    (hV : Fintype.card V ≤ 3) (classOf : V → E → K) (C : Finset E) :
    G.AdmissibleOn classOf C ↔
      ∀ v k w, 2 * (G.classCutOn classOf C v k {w}).card ≤ G.degreeOn C w := by
  constructor
  · intro h v k w
    simpa only [G.cutOn_singleton_card] using h v k {w}
  · intro h v k X
    by_cases hzero : X = ∅
    · subst X
      simp [classCutOn, cutOn]
    by_cases hfull : X = univ
    · subst X
      simp [classCutOn, cutOn]
    have hpos : 0 < X.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hzero)
    have hlt : X.card < Fintype.card V := card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ X, hfull⟩)
    by_cases hone : X.card = 1
    · obtain ⟨w, rfl⟩ := card_eq_one.mp hone
      simpa only [G.cutOn_singleton_card] using h v k w
    · have hcomp : Xᶜ.card = 1 := by
        rw [card_compl]
        omega
      obtain ⟨w, hw⟩ := card_eq_one.mp hcomp
      have hX : X = ({w} : Finset V)ᶜ := by rw [← hw, compl_compl]
      rw [hX, G.classCutOn_compl, G.cutOn_compl, G.cutOn_singleton_card]
      exact h v k w

/-- Exact safe deletion needs witnesses only on tight singleton cuts
when there are at most three labels. -/
theorem admissibleOn_sdiff_iff_meets_tight_singletons [Fintype V]
    (hV : Fintype.card V ≤ 3) (classOf : V → E → K)
    {C D : Finset E} (hDC : D ⊆ C) (hD : G.IsCircuit D)
    (hadmissible : G.AdmissibleOn classOf C)
    (heven : ∀ v, Even (G.degreeOn C v)) :
    G.AdmissibleOn classOf (C \ D) ↔
      ∀ v k w, G.degreeOn C w = 2 * (G.classCutOn classOf C v k {w}).card →
        (G.cutOn D {w}).Nonempty → (G.classCutOn classOf D v k {w}).Nonempty := by
  rw [G.admissibleOn_sdiff_iff_meets_tight_classes_of_card_le_three
    hV classOf hDC hD hadmissible heven]
  constructor
  · intro h v k w htight hcross
    exact h v k {w} (by simpa only [G.cutOn_singleton_card] using htight) hcross
  · intro h v k X htight hcross
    rcases shore_cases_of_card_le_three hV X with rfl | rfl | ⟨w, rfl | rfl⟩
    · simp [cutOn] at hcross
    · simp [cutOn] at hcross
    · exact h v k w (by simpa only [G.cutOn_singleton_card] using htight) hcross
    · simpa only [G.classCutOn_compl] using
        h v k w (by simpa only [G.classCutOn_compl, G.cutOn_compl,
          G.cutOn_singleton_card] using htight)
          (by simpa only [G.cutOn_compl] using hcross)

variable (Q : Multigraph (Fin 3) E)

/-- A loopless edge on three labels lies in one of the three bundles. -/
theorem threeLabel_edge_cases (e : E) :
    Q.edge e = s((0 : Fin 3), 1) ∨ Q.edge e = s((0 : Fin 3), 2) ∨
      Q.edge e = s((1 : Fin 3), 2) := by
  have hne := Q.endpoints_distinct e
  rw [← Q.edge_eq e]
  generalize ha : Q.firstEnd e = a at *
  generalize hb : Q.secondEnd e = b at *
  fin_cases a <;> fin_cases b <;> simp_all

/-- Exact union of the actual parallel-copy bundles. -/
theorem threeLabel_bundles_cover (C : Finset E) :
    Q.edgeBundleOn C 0 1 ∪ Q.edgeBundleOn C 0 2 ∪ Q.edgeBundleOn C 1 2 = C := by
  ext e
  simp only [mem_union, mem_edgeBundleOn]
  have hcases := Q.threeLabel_edge_cases e
  tauto

theorem threeLabel_incident_zero (C : Finset E) :
    C.filter (fun e => (0 : Fin 3) ∈ Q.edge e) =
      Q.edgeBundleOn C 0 1 ∪ Q.edgeBundleOn C 0 2 := by
  ext e
  rcases Q.threeLabel_edge_cases e with he | he | he <;>
    simp [mem_edgeBundleOn, he]

theorem threeLabel_incident_one (C : Finset E) :
    C.filter (fun e => (1 : Fin 3) ∈ Q.edge e) =
      Q.edgeBundleOn C 0 1 ∪ Q.edgeBundleOn C 1 2 := by
  ext e
  rcases Q.threeLabel_edge_cases e with he | he | he <;>
    simp [mem_edgeBundleOn, he]

theorem threeLabel_incident_two (C : Finset E) :
    C.filter (fun e => (2 : Fin 3) ∈ Q.edge e) =
      Q.edgeBundleOn C 0 2 ∪ Q.edgeBundleOn C 1 2 := by
  ext e
  rcases Q.threeLabel_edge_cases e with he | he | he <;>
    simp [mem_edgeBundleOn, he]

theorem threeLabel_degree_zero (C : Finset E) :
    Q.degreeOn C 0 = (Q.edgeBundleOn C 0 1).card + (Q.edgeBundleOn C 0 2).card := by
  have hinc := congrArg Finset.card (Q.threeLabel_incident_zero C)
  have hd : Disjoint (Q.edgeBundleOn C 0 1) (Q.edgeBundleOn C 0 2) :=
    Q.edgeBundleOn_disjoint (by decide)
  rw [card_union_of_disjoint hd] at hinc
  convert hinc using 1
  unfold degreeOn
  congr 1
  ext e
  simp

theorem threeLabel_degree_one (C : Finset E) :
    Q.degreeOn C 1 = (Q.edgeBundleOn C 0 1).card + (Q.edgeBundleOn C 1 2).card := by
  have hinc := congrArg Finset.card (Q.threeLabel_incident_one C)
  have hd : Disjoint (Q.edgeBundleOn C 0 1) (Q.edgeBundleOn C 1 2) :=
    Q.edgeBundleOn_disjoint (by decide)
  rw [card_union_of_disjoint hd] at hinc
  convert hinc using 1
  unfold degreeOn
  congr 1
  ext e
  simp

theorem threeLabel_degree_two (C : Finset E) :
    Q.degreeOn C 2 = (Q.edgeBundleOn C 0 2).card + (Q.edgeBundleOn C 1 2).card := by
  have hinc := congrArg Finset.card (Q.threeLabel_incident_two C)
  have hd : Disjoint (Q.edgeBundleOn C 0 2) (Q.edgeBundleOn C 1 2) :=
    Q.edgeBundleOn_disjoint (by decide)
  rw [card_union_of_disjoint hd] at hinc
  convert hinc using 1
  unfold degreeOn
  congr 1
  ext e
  simp

/-- Even degrees give the common parity used in the selector case split. -/
theorem threeLabel_bundle_parity {C : Finset E}
    (heven : ∀ v, Even (Q.degreeOn C v)) :
    (Q.edgeBundleOn C 0 1).card % 2 = (Q.edgeBundleOn C 0 2).card % 2 ∧
      (Q.edgeBundleOn C 0 1).card % 2 = (Q.edgeBundleOn C 1 2).card % 2 := by
  have h0 := Nat.even_iff.mp (heven 0)
  have h1 := Nat.even_iff.mp (heven 1)
  rw [Q.threeLabel_degree_zero] at h0
  rw [Q.threeLabel_degree_one] at h1
  omega

end Overfull.Multigraph
