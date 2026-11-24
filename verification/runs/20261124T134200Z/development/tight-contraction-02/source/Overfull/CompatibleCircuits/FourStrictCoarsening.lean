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

end Overfull.Multigraph
