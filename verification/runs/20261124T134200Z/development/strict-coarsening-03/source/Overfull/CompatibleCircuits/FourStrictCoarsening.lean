import Overfull.CompatibleCircuits.FourGlobalCoarsening
import Overfull.CompatibleCircuits.FourCutCriterion
import Overfull.CompatibleCircuits.SafeSelectionInduction

/-!
# Strict nonlocal cuts and safe short-circuit deletion

A shore is nonlocal for a class at `v` if both shores contain a vertex
different from `v`. Strictness on all such shores is preserved by tight
local coarsening. Under that hypothesis, every coarse-compatible pair or
triangle is safely removable from the original incidence-class graph.
All cut, degree and partition statements retain the actual edge copies.

This is the strict branch of the four-label reduction. The existence of a
short compatible circuit, or a terminal partition when none exists, is a
separate obligation. No existence conclusion is hidden in this interface.
-/

namespace Overfull.Multigraph

open Finset Classical
open Overfull.CompatibleCircuits

variable {V E K : Type*} (G : Multigraph V E)

/-- Both shores contain a vertex other than the tested class vertex. -/
def NonlocalShore (v : V) (X : Finset V) : Prop :=
  (∃ x ∈ X, x ≠ v) ∧ ∃ y, y ∉ X ∧ y ≠ v

/-- Every genuinely nonlocal class-cut inequality is strict. Empty cuts
are included: this predicate is the branch with no tight nonlocal cut. -/
def StrictNonlocalOn (classOf : V → E → K) (C : Finset E) : Prop :=
  ∀ v k X, NonlocalShore v X →
    2 * (G.classCutOn classOf C v k X).card < (G.cutOn C X).card

theorem nonlocalShore_toggle_iff (v : V) (X : Finset V) :
    NonlocalShore v (MatchingProbability.toggle X v) ↔ NonlocalShore v X := by
  have hmem (x : V) (hx : x ≠ v) :
      x ∈ MatchingProbability.toggle X v ↔ x ∈ X := by
    by_cases hv : v ∈ X <;> simp [MatchingProbability.toggle, hv, hx]
  constructor
  · rintro ⟨⟨x, hx, hxv⟩, y, hy, hyv⟩
    exact ⟨⟨x, (hmem x hxv).mp hx, hxv⟩,
      y, fun h => hy ((hmem y hyv).mpr h), hyv⟩
  · rintro ⟨⟨x, hx, hxv⟩, y, hy, hyv⟩
    exact ⟨⟨x, (hmem x hxv).mpr hx, hxv⟩,
      y, fun h => hy ((hmem y hyv).mp h), hyv⟩

/-- The slack of the complementary tight local class is exactly the slack
of the original tight class on the toggled shore; in particular it is strict. -/
theorem complement_class_cut_strict_of_local_tight
    (classOf : V → E → K) {C : Finset E}
    (hstrict : G.StrictNonlocalOn classOf C) (v : V) (k : K)
    (htight : 2 * (C.filter (fun e => v ∈ G.edge e ∧ classOf v e = k)).card =
      G.degreeOn C v) (X : Finset V) (hX : NonlocalShore v X) :
    2 * ((G.cutOn C X).filter
      (fun e => v ∈ G.edge e ∧ classOf v e ≠ k)).card < (G.cutOn C X).card := by
  have htoggle := G.cutOn_toggle_card C X v
  have hclass := G.classCutOn_card_add_toggle_card classOf C v k X
  have hother := hstrict v k (MatchingProbability.toggle X v)
    ((nonlocalShore_toggle_iff v X).mpr hX)
  have hpart : (G.classCutOn classOf C v k X).card +
      ((G.cutOn C X).filter (fun e => v ∈ G.edge e ∧ classOf v e ≠ k)).card =
      G.degreeOn (G.cutOn C X) v := by
    simpa only [classCutOn, degreeOn, filter_filter, ne_eq] using
      ((G.cutOn C X).filter (fun e => v ∈ G.edge e)).filter_card_add_filter_neg_card_eq_card
        (fun e => classOf v e = k)
  omega

/-- Simultaneous tight local coarsenings preserve strictness on every
nonlocal shore, without an even-degree or vertex-count hypothesis. -/
theorem strictNonlocalOn_localCoarsening [Nonempty K] (classOf : V → E → K)
    (C : Finset E) (hstrict : G.StrictNonlocalOn classOf C)
    (L : ∀ v, LocalCoarsening (C.filter (fun e => v ∈ G.edge e)) (classOf v)) :
    G.StrictNonlocalOn (fun v e => (L v).coarse e) C := by
  intro v q X hX
  rcases (L v).identity_or_tight with hid | ⟨k, htight, hmap⟩
  · rcases q with q | q
    · simpa only [classCutOn, hid, Sum.inl.injEq] using hstrict v q X hX
    · have hpos : 0 < (G.cutOn C X).card := by
        have h := hstrict v (Classical.choice inferInstance) X hX
        omega
      simpa [classCutOn, hid] using hpos
  · have htight' :
        2 * (C.filter (fun e => v ∈ G.edge e ∧ classOf v e = k)).card =
          G.degreeOn C v := by
      simpa only [filter_filter, degreeOn] using htight
    rcases q with q | q
    · have hpos := hstrict v k X hX
      have : 0 < (G.cutOn C X).card := by omega
      simpa [classCutOn, hmap] using this
    · cases q
      · simpa [classCutOn, hmap] using
          G.complement_class_cut_strict_of_local_tight classOf hstrict v k htight' X hX
      · simpa [classCutOn, hmap] using hstrict v k X hX

/-- The same coarsenings simultaneously preserve admissibility and all
strict nonlocal bounds while meeting the original tight local classes. -/
theorem exists_strict_globally_admissible_localCoarsening [Nonempty K]
    (classOf : V → E → K) (C : Finset E)
    (hadmissible : G.AdmissibleOn classOf C)
    (hstrict : G.StrictNonlocalOn classOf C) :
    ∃ L : ∀ v, LocalCoarsening (C.filter (fun e => v ∈ G.edge e)) (classOf v),
      G.AdmissibleOn (fun v e => (L v).coarse e) C ∧
      G.StrictNonlocalOn (fun v e => (L v).coarse e) C := by
  obtain ⟨L, hL⟩ := G.exists_globally_admissible_localCoarsening classOf C hadmissible
  exact ⟨L, hL, G.strictNonlocalOn_localCoarsening classOf C hstrict L⟩

theorem nonlocalShore_compl_iff [Fintype V] (v : V) (X : Finset V) :
    NonlocalShore v Xᶜ ↔ NonlocalShore v X := by
  simp only [NonlocalShore, mem_compl, not_not]
  constructor
  · rintro ⟨⟨x, hx, hxv⟩, y, hy, hyv⟩
    exact ⟨⟨y, hy, hyv⟩, x, hx, hxv⟩

/-- With at least three available labels, a singleton at another label
is nonlocal. This translates the global strict predicate to bundle bounds. -/
theorem nonlocalShore_singleton [Fintype V] (hV : 3 ≤ Fintype.card V)
    {v w : V} (hvw : v ≠ w) : NonlocalShore v {w} := by
  refine ⟨⟨w, by simp, hvw.symm⟩, ?_⟩
  have hcard : ({v, w} : Finset V).card < Fintype.card V := by
    rw [card_pair hvw]
    omega
  obtain ⟨y, hy⟩ := exists_notMem_of_card_lt_card hcard
  refine ⟨y, ?_, ?_⟩
  · intro h
    exact hy (mem_insert_of_mem (mem_singleton.mpr (mem_singleton.mp h)))
  · intro h
    exact hy (h ▸ mem_insert_self _ _)

theorem StrictNonlocalOn.singleton_bound [Fintype V]
    {classOf : V → E → K} {C : Finset E}
    (hstrict : G.StrictNonlocalOn classOf C) (hV : 3 ≤ Fintype.card V)
    {v w : V} (hvw : v ≠ w) (k : K) :
    2 * (G.classCutOn classOf C v k {w}).card < G.degreeOn C w := by
  simpa only [G.cutOn_singleton_card] using
    hstrict v k {w} (nonlocalShore_singleton hV hvw)

/-- Strict nonlocal bounds are exactly the absence of a tight nonlocal
class-cut inequality once all weak half-cut bounds hold. -/
theorem strictNonlocalOn_iff_no_tight_nonlocal
    (classOf : V → E → K) {C : Finset E}
    (hadmissible : G.AdmissibleOn classOf C) :
    G.StrictNonlocalOn classOf C ↔
      ¬ ∃ v k X, NonlocalShore v X ∧
        2 * (G.classCutOn classOf C v k X).card = (G.cutOn C X).card := by
  constructor
  · intro hs ⟨v, k, X, hX, ht⟩
    have h := hs v k X hX
    omega
  · intro hn v k X hX
    have hle := hadmissible v k X
    have hne : 2 * (G.classCutOn classOf C v k X).card ≠ (G.cutOn C X).card :=
      fun h => hn ⟨v, k, X, hX, h⟩
    omega
  · rintro ⟨⟨x, hx, hxv⟩, y, hy, hyv⟩
    exact ⟨⟨y, hy, hyv⟩, x, hx, hxv⟩

/-- A nonempty cut that is not nonlocal for `v` isolates exactly `v`. -/
theorem singleton_or_compl_of_not_nonlocal [Fintype V]
    {C : Finset E} {v : V} {X : Finset V}
    (hnonlocal : ¬ NonlocalShore v X) (hcut : (G.cutOn C X).Nonempty) :
    X = {v} ∨ Xᶜ = {v} := by
  have hside : X ⊆ {v} ∨ Xᶜ ⊆ {v} := by
    by_cases h : ∃ x ∈ X, x ≠ v
    · right
      intro y hy
      apply mem_singleton.mpr
      by_contra hyv
      exact hnonlocal ⟨h, y, mem_compl.mp hy, hyv⟩
    · left
      intro x hx
      apply mem_singleton.mpr
      by_contra hxv
      exact h ⟨x, hx, hxv⟩
  rcases hside with hside | hside
  · rcases subset_singleton_iff.mp hside with hempty | heq
    · have : G.cutOn C X = ∅ := by simp [hempty, cutOn]
      exact False.elim (hcut.ne_empty this)
    · exact Or.inl heq
  · rcases subset_singleton_iff.mp hside with hempty | heq
    · have : G.cutOn C X = ∅ := by
        rw [← G.cutOn_compl C X, hempty]
        simp [cutOn]
      exact False.elim (hcut.ne_empty this)
    · exact Or.inr heq

/-- At every vertex it meets, a coarse-compatible circuit uses an original
incidence from each tight local class. -/
theorem IsCircuit.meets_local_tight_of_localCoarsening
    (classOf : V → E → K) {C D : Finset E} (hDC : D ⊆ C)
    (hD : G.IsCircuit D)
    (L : ∀ v, LocalCoarsening (C.filter (fun e => v ∈ G.edge e)) (classOf v))
    (hcomp : G.Compatible (fun v e => (L v).coarse e) D)
    (v : V) (k : K)
    (htight : 2 * (C.filter (fun e => v ∈ G.edge e ∧ classOf v e = k)).card =
      G.degreeOn C v) (hv : v ∈ G.edgeSupport D) :
    ∃ e ∈ D, v ∈ G.edge e ∧ classOf v e = k := by
  obtain ⟨e, f, hef, hpair⟩ := card_eq_two.mp (hD.2.1 v hv)
  have he : e ∈ D ∧ v ∈ G.edge e := by
    apply mem_filter.mp
    rw [hpair]
    simp
  have hf : f ∈ D ∧ v ∈ G.edge f := by
    apply mem_filter.mp
    rw [hpair]
    simp
  have hdiff : (L v).coarse e ≠ (L v).coarse f :=
    fun h => hef (hcomp v e he.1 he.2 f hf.1 hf.2 h)
  have htight' :
      2 * ((C.filter (fun a => v ∈ G.edge a)).filter (fun a => classOf v a = k)).card =
        (C.filter (fun a => v ∈ G.edge a)).card := by
    simpa only [filter_filter, degreeOn] using htight
  rcases (L v).meets_tight k htight' e (mem_filter.mpr ⟨hDC he.1, he.2⟩)
      f (mem_filter.mpr ⟨hDC hf.1, hf.2⟩) hdiff with hk | hk
  · exact ⟨e, he.1, he.2, hk⟩
  · exact ⟨f, hf.1, hf.2, hk⟩

/-- With all nonlocal bounds strict, deleting any coarse-compatible pair
or triangle preserves the original global half-cut inequalities. -/
theorem admissibleOn_sdiff_of_strict_nonlocal_small_coarse_circuit [Fintype V]
    (classOf : V → E → K) {C D : Finset E} (hDC : D ⊆ C)
    (hD : G.IsCircuit D) (hsmall : D.card ≤ 3)
    (hadmissible : G.AdmissibleOn classOf C)
    (heven : ∀ v, Even (G.degreeOn C v))
    (hstrict : G.StrictNonlocalOn classOf C)
    (L : ∀ v, LocalCoarsening (C.filter (fun e => v ∈ G.edge e)) (classOf v))
    (hcomp : G.Compatible (fun v e => (L v).coarse e) D) :
    G.AdmissibleOn classOf (C \ D) := by
  apply (G.admissibleOn_sdiff_iff_tight_classes_of_small_circuit
    classOf hDC hD hsmall hadmissible heven).mpr
  intro v k X htight hcross
  have hCcross : (G.cutOn C X).Nonempty :=
    hcross.mono (filter_subset_filter _ hDC)
  have hlocal : ¬ NonlocalShore v X := by
    intro hX
    have h := hstrict v k X hX
    omega
  have hsingle : ∀ Y : Finset V, Y = {v} →
      (G.cutOn C Y).card = 2 * (G.classCutOn classOf C v k Y).card →
      (G.cutOn D Y).Nonempty → (G.classCutOn classOf D v k Y).Nonempty := by
    intro Y hY ht hc
    subst Y
    have hv : v ∈ G.edgeSupport D := by
      obtain ⟨e, he⟩ := hc
      rw [G.cutOn_singleton] at he
      obtain ⟨he, hve⟩ := mem_filter.mp he
      exact (G.mem_edgeSupport D v).mpr ⟨e, he, hve⟩
    have ht' :
        2 * (C.filter (fun e => v ∈ G.edge e ∧ classOf v e = k)).card =
          G.degreeOn C v := by
      simpa only [G.cutOn_singleton_card, G.classCutOn_singleton_self] using ht.symm
    obtain ⟨e, he, hve, hek⟩ := hD.meets_local_tight_of_localCoarsening
      G classOf hDC L hcomp v k ht' hv
    rw [G.classCutOn_singleton_self]
    exact ⟨e, mem_filter.mpr ⟨he, hve, hek⟩⟩
  rcases G.singleton_or_compl_of_not_nonlocal hlocal hCcross with hX | hX
  · exact hsingle X hX htight hcross
  · have ht : (G.cutOn C Xᶜ).card = 2 * (G.classCutOn classOf C v k Xᶜ).card := by
      simpa only [G.cutOn_compl, G.classCutOn_compl] using htight
    have hc : (G.cutOn D Xᶜ).Nonempty := by
      simpa only [G.cutOn_compl] using hcross
    simpa only [G.classCutOn_compl] using hsingle Xᶜ hX ht hc

end Overfull.Multigraph
