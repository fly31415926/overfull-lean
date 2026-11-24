import Overfull.CompatibleCircuits.FourTriangleSelection
import Overfull.CompatibleCircuits.ThreeLabelBundles
import Overfull.CompatibleCircuits.FourLabel

/-!
# Support restrictions under strict nonlocal singleton bounds

All bundles consist of the original selected edge copies.  The absence of a
compatible parallel pair forces a monochromatic endpoint on each nonempty
bundle.  Admissibility then forbids a vertex with just one neighbor.  If the
nonlocal singleton inequalities are strict, a vertex with exactly two
neighbors has equally large bundles, each monochromatic at that vertex,
with different classes on the two bundles.  No bound on multiplicity or
degree, and no circuit partition, is assumed.
-/

namespace Overfull.Multigraph

open Finset Classical Overfull.CompatibleCircuits

variable {V E K : Type*} (G : Multigraph V E)

/-- Endpoint compatibility suffices for a parallel pair on any vertex type. -/
theorem compatible_parallel_pair_of_endpoint_classes
    (classOf : V → E → K) {u v : V} {e f : E}
    (he : G.edge e = s(u, v)) (hf : G.edge f = s(u, v))
    (hu : classOf u e ≠ classOf u f) (hv : classOf v e ≠ classOf v f) :
    G.Compatible classOf {e, f} := by
  intro w a ha hwa b hb hwb hclass
  simp only [mem_insert, mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rfl
  · have hw : w = u ∨ w = v := by simpa [he] using hwa
    rcases hw with rfl | rfl
    · exact False.elim (hu hclass)
    · exact False.elim (hv hclass)
  · have hw : w = u ∨ w = v := by simpa [hf] using hwa
    rcases hw with rfl | rfl
    · exact False.elim (hu hclass.symm)
    · exact False.elim (hv hclass.symm)
  · rfl

/-- Failure of an actual compatible two-circuit makes a whole bundle
monochromatic at one of its endpoints. -/
theorem bundle_monochromatic_of_no_compatible_pair
    (classOf : V → E → K) (C : Finset E)
    (hnone : ¬ ∃ D : Finset E, D ⊆ C ∧ G.IsCircuit D ∧
      G.Compatible classOf D ∧ D.card = 2)
    (u v : V) (hB : (G.edgeBundleOn C u v).Nonempty) :
    MonochromaticOn (G.edgeBundleOn C u v) (classOf u) ∨
      MonochromaticOn (G.edgeBundleOn C u v) (classOf v) := by
  apply monochromatic_coordinate_of_no_pair _ _ _ hB
  rintro ⟨e, he, f, hf, hu, hv⟩
  obtain ⟨heC, heends⟩ := (G.mem_edgeBundleOn C u v e).mp he
  obtain ⟨hfC, hfends⟩ := (G.mem_edgeBundleOn C u v f).mp hf
  have hef : e ≠ f := fun h => hu (congrArg (classOf u) h)
  apply hnone
  refine ⟨{e, f}, ?_, G.isCircuit_parallel_pair hef (heends.trans hfends.symm),
    G.compatible_parallel_pair_of_endpoint_classes classOf heends hfends hu hv, ?_⟩
  · intro a ha
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl <;> assumption
  · simp [hef]

/-- A monochromatic original bundle satisfies the local half-degree bound. -/
theorem monochromatic_bundle_local_bound
    (classOf : V → E → K) {C : Finset E}
    (hadmissible : G.AdmissibleOn classOf C) (u v : V)
    (hmono : MonochromaticOn (G.edgeBundleOn C u v) (classOf u)) :
    2 * (G.edgeBundleOn C u v).card ≤ G.degreeOn C u := by
  obtain ⟨k, hk⟩ := hmono
  have hsub : G.edgeBundleOn C u v ⊆
      C.filter (fun e => u ∈ G.edge e ∧ classOf u e = k) := by
    intro e he
    obtain ⟨heC, hends⟩ := (G.mem_edgeBundleOn C u v e).mp he
    exact mem_filter.mpr ⟨heC, by simp [hends], hk e he⟩
  exact (Nat.mul_le_mul_left 2 (card_le_card hsub)).trans
    (hadmissible.local_class_bound G u k)

/-- No positive vertex can have just one actual endpoint bundle when
there is no compatible parallel pair. -/
theorem no_single_bundle_incidence_of_no_compatible_pair
    (classOf : V → E → K) (C : Finset E)
    (hadmissible : G.AdmissibleOn classOf C)
    (hnone : ¬ ∃ D : Finset E, D ⊆ C ∧ G.IsCircuit D ∧
      G.Compatible classOf D ∧ D.card = 2)
    {v u : V} (hvu : v ≠ u) (hB : (G.edgeBundleOn C v u).Nonempty)
    (hinc : C.filter (fun e => v ∈ G.edge e) = G.edgeBundleOn C v u) : False := by
  have hd : G.degreeOn C v = (G.edgeBundleOn C v u).card :=
    congrArg Finset.card hinc
  have hpos := card_pos.mpr hB
  rcases G.bundle_monochromatic_of_no_compatible_pair classOf C hnone v u hB with
      hlocal | ⟨k, hk⟩
  · have hbound := G.monochromatic_bundle_local_bound classOf hadmissible v u hlocal
    omega
  · have hbound := hadmissible.bundle_class_bound G hvu.symm k
    rw [G.edgeBundleOn_swap C u v] at hbound
    have hfilter : (G.edgeBundleOn C v u).filter (fun e => classOf u e = k) =
        G.edgeBundleOn C v u := filter_eq_self.mpr hk
    rw [hfilter] at hbound
    omega

/-- A bundle occupying at least half the incidences at a vertex cannot be
monochromatic at its other endpoint under a strict nonlocal singleton bound. -/
theorem dominant_bundle_not_monochromatic_at_other
    (classOf : V → E → K) (C : Finset E) {v u : V} (hvu : v ≠ u)
    (hstrict : ∀ k, 2 * (G.classCutOn classOf C u k {v}).card < G.degreeOn C v)
    (hlarge : G.degreeOn C v ≤ 2 * (G.edgeBundleOn C v u).card) :
    ¬ MonochromaticOn (G.edgeBundleOn C v u) (classOf u) := by
  rintro ⟨k, hk⟩
  have hbound := hstrict k
  rw [G.classCutOn_singleton_other classOf C hvu.symm,
    G.edgeBundleOn_swap C u v, filter_eq_self.mpr hk] at hbound
  omega

/-- With two neighbors, the larger bundle must be locally monochromatic
and hence cannot be strictly larger than the other bundle. -/
theorem two_bundle_dominant_is_tight
    (classOf : V → E → K) (C : Finset E)
    (hadmissible : G.AdmissibleOn classOf C)
    (hnone : ¬ ∃ D : Finset E, D ⊆ C ∧ G.IsCircuit D ∧
      G.Compatible classOf D ∧ D.card = 2)
    {v u w : V} (hvu : v ≠ u) (hB : (G.edgeBundleOn C v u).Nonempty)
    (hstrict : ∀ k, 2 * (G.classCutOn classOf C u k {v}).card < G.degreeOn C v)
    (hdegree : G.degreeOn C v =
      (G.edgeBundleOn C v u).card + (G.edgeBundleOn C v w).card)
    (hlarge : (G.edgeBundleOn C v w).card ≤ (G.edgeBundleOn C v u).card) :
    (G.edgeBundleOn C v u).card = (G.edgeBundleOn C v w).card ∧
      MonochromaticOn (G.edgeBundleOn C v u) (classOf v) := by
  have hnot := G.dominant_bundle_not_monochromatic_at_other classOf C hvu hstrict
    (by omega)
  have hmono : MonochromaticOn (G.edgeBundleOn C v u) (classOf v) :=
    (G.bundle_monochromatic_of_no_compatible_pair classOf C hnone v u hB).resolve_right hnot
  have hbound := G.monochromatic_bundle_local_bound classOf hadmissible v u hmono
  exact ⟨by omega, hmono⟩

/-- Exact structure at a vertex with two distinct neighbors.  The bundles
have equal size and constant, different original incidence classes at the
vertex; consequently every choice of one copy from each is compatible there. -/
theorem two_neighbor_bundle_structure
    (classOf : V → E → K) (C : Finset E)
    (hadmissible : G.AdmissibleOn classOf C)
    (hnone : ¬ ∃ D : Finset E, D ⊆ C ∧ G.IsCircuit D ∧
      G.Compatible classOf D ∧ D.card = 2)
    {v u w : V} (hvu : v ≠ u) (hvw : v ≠ w) (huw : u ≠ w)
    (hB : (G.edgeBundleOn C v u).Nonempty)
    (hD : (G.edgeBundleOn C v w).Nonempty)
    (hinc : C.filter (fun e => v ∈ G.edge e) =
      G.edgeBundleOn C v u ∪ G.edgeBundleOn C v w)
    (hstrictu : ∀ k, 2 * (G.classCutOn classOf C u k {v}).card < G.degreeOn C v)
    (hstrictw : ∀ k, 2 * (G.classCutOn classOf C w k {v}).card < G.degreeOn C v) :
    (G.edgeBundleOn C v u).card = (G.edgeBundleOn C v w).card ∧
      ∃ k l : K, k ≠ l ∧
        (∀ e ∈ G.edgeBundleOn C v u, classOf v e = k) ∧
        (∀ e ∈ G.edgeBundleOn C v w, classOf v e = l) := by
  have hpairs : s(v, u) ≠ s(v, w) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨_, h⟩ | ⟨h, _⟩
    · exact huw h
    · exact hvw h
  have hdis : Disjoint (G.edgeBundleOn C v u) (G.edgeBundleOn C v w) :=
    G.edgeBundleOn_disjoint hpairs
  have hdegree : G.degreeOn C v =
      (G.edgeBundleOn C v u).card + (G.edgeBundleOn C v w).card := by
    change (C.filter (fun e => v ∈ G.edge e)).card = _
    rw [hinc, card_union_of_disjoint hdis]
  have hequal : (G.edgeBundleOn C v u).card = (G.edgeBundleOn C v w).card := by
    rcases le_total (G.edgeBundleOn C v w).card (G.edgeBundleOn C v u).card with h | h
    · exact (G.two_bundle_dominant_is_tight classOf C hadmissible hnone hvu hB
        hstrictu hdegree h).1
    · exact (G.two_bundle_dominant_is_tight classOf C hadmissible hnone (w := u) hvw hD
        hstrictw (by omega) h).1.symm
  obtain ⟨k, hk⟩ := (G.two_bundle_dominant_is_tight classOf C hadmissible hnone hvu hB
    hstrictu hdegree (by omega)).2
  obtain ⟨l, hl⟩ := (G.two_bundle_dominant_is_tight classOf C hadmissible hnone (w := u) hvw hD
    hstrictw (by omega) (by omega)).2
  refine ⟨hequal, k, l, ?_, hk, hl⟩
  intro hkl
  have hall : C.filter (fun e => v ∈ G.edge e ∧ classOf v e = k) =
      C.filter (fun e => v ∈ G.edge e) := by
    ext e
    simp only [mem_filter]
    constructor
    · tauto
    · rintro ⟨he, hv⟩
      have hemem : e ∈ G.edgeBundleOn C v u ∪ G.edgeBundleOn C v w := by
        rw [← hinc]
        exact mem_filter.mpr ⟨he, hv⟩
      refine ⟨he, hv, ?_⟩
      rcases mem_union.mp hemem with h | h
      · exact hk e h
      · exact (hl e h).trans hkl.symm
  have hbound := hadmissible.local_class_bound G v k
  rw [hall] at hbound
  have hpos := card_pos.mpr hB
  change 2 * G.degreeOn C v ≤ G.degreeOn C v at hbound
  omega

end Overfull.Multigraph
