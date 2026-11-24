import Overfull.MultigraphMatchingProbability
import Overfull.CompatibleCircuits.Basic

/-!
# Actual cut bounds for a regular multigraph with no overfull set

The cuts retain every original edge copy. Odd shores have at least the
regular degree many crossing copies; even shores have even cuts, and no
original vertex accounts for more than half of such a cut. In particular,
an odd label fiber forces a positive joining-edge degree bound.
-/

namespace Overfull.FourOdd

open Finset Classical

variable {V E : Type*} (G : Multigraph V E)

theorem cutOn_eq_probability_cut (F : Finset E) (X : Finset V) :
    G.cutOn F X = MultigraphMatchingProbability.cutEdges (G := G) F X := rfl

theorem degreeOn_eq_probability_incident (F : Finset E) (v : V) :
    G.degreeOn F v = MultigraphMatchingProbability.incidentCount (G := G) F v := by
  simp only [Multigraph.degreeOn, MultigraphMatchingProbability.incidentCount,
    G.incident_iff]

variable [Fintype V] [Fintype E]

/-- Cut parity follows from the actual regular-degree handshake identity. -/
theorem regular_cut_parity {h : ℕ} (hregular : ∀ v, G.degree v = h)
    (X : Finset V) :
    (G.cutOn univ X).card % 2 = (h * X.card) % 2 := by
  have hs := MultigraphMatchingProbability.regular_cut_handshake (G := G) hregular X
  change h * X.card = (G.cutOn univ X).card + 2 * (G.internalEdges X).card at hs
  omega

/-- An odd shore has at least `h` crossing copies. -/
theorem regular_odd_cut_lower {h : ℕ} (hregular : ∀ v, G.degree v = h)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull h X)
    (X : Finset V) (hX : X.card % 2 = 1) :
    h ≤ (G.cutOn univ X).card := by
  obtain ⟨s, hs, _⟩ :=
    MultigraphMatchingProbability.regular_odd_cut (G := G) hregular hno X hX
  change (G.cutOn univ X).card = h + s at hs
  omega

theorem regular_odd_cut_parity {h : ℕ} (hregular : ∀ v, G.degree v = h)
    (X : Finset V) (hX : X.card % 2 = 1) :
    (G.cutOn univ X).card % 2 = h % 2 := by
  rw [regular_cut_parity G hregular X, Nat.mul_mod, hX]
  simp

/-- The excess of an odd cut over `h` consists of an actual even number
of edge copies. -/
theorem regular_odd_cut_eq_add_twice {h : ℕ}
    (hregular : ∀ v, G.degree v = h)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull h X)
    (X : Finset V) (hX : X.card % 2 = 1) :
    ∃ s : ℕ, (G.cutOn univ X).card = h + 2 * s := by
  obtain ⟨s, hs, hpar⟩ :=
    MultigraphMatchingProbability.regular_odd_cut (G := G) hregular hno X hX
  change (G.cutOn univ X).card = h + s at hs
  exact ⟨s / 2, by omega⟩

theorem regular_even_cut_parity {h : ℕ} (hregular : ∀ v, G.degree v = h)
    (X : Finset V) (hX : X.card % 2 = 0) :
    (G.cutOn univ X).card % 2 = 0 := by
  rw [regular_cut_parity G hregular X, Nat.mul_mod, hX]
  simp

/-- Toggling any original vertex produces an odd shore. Its cut lower
bound gives the half-cut bound for that vertex's actual incident copies. -/
theorem regular_even_cut_twice_degree_le {h : ℕ}
    (hregular : ∀ v, G.degree v = h)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull h X)
    (X : Finset V) (hX : X.card % 2 = 0) (v : V) :
    2 * G.degreeOn (G.cutOn univ X) v ≤ (G.cutOn univ X).card := by
  have hodd := MatchingProbability.toggle_odd hX v
  have hlower := regular_odd_cut_lower G hregular hno
    (MatchingProbability.toggle X v) hodd
  have ht := MultigraphMatchingProbability.cut_toggle (G := G) univ X v
  rw [MultigraphMatchingProbability.incidentCount_univ (G := G), hregular v] at ht
  change (G.cutOn univ (MatchingProbability.toggle X v)).card +
    2 * MultigraphMatchingProbability.incidentCount (G := G) (G.cutOn univ X) v =
      (G.cutOn univ X).card + h at ht
  rw [← degreeOn_eq_probability_incident G] at ht
  omega

theorem regular_even_cut_degree_le_half {h : ℕ}
    (hregular : ∀ v, G.degree v = h)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull h X)
    (X : Finset V) (hX : X.card % 2 = 0) (v : V) :
    G.degreeOn (G.cutOn univ X) v ≤ (G.cutOn univ X).card / 2 := by
  have ht := regular_even_cut_twice_degree_le G hregular hno X hX v
  omega

/-- One odd label fiber forces a genuine joining copy. Labels need not be
injective, and parallel original copies remain distinct. -/
theorem joining_nonempty_of_odd_fiber {I : Type*} [DecidableEq I]
    (label : V → I) (i : I)
    {h : ℕ} (hh : 0 < h) (hregular : ∀ v, G.degree v = h)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull h X)
    (hodd : (univ.filter (fun v => label v = i)).card % 2 = 1) :
    (univ.filter (fun e => label (G.firstEnd e) ≠ label (G.secondEnd e))).Nonempty := by
  let X := univ.filter (fun v => label v = i)
  have hlower := regular_odd_cut_lower G hregular hno X hodd
  obtain ⟨e, he⟩ := Finset.card_pos.mp (lt_of_lt_of_le hh hlower)
  have hcross := (G.mem_cutOn univ X e).mp he |>.2
  refine ⟨e, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
  intro hsame
  apply hcross
  simp [X, hsame]

/-- Any common upper bound on the actual joining degrees must be positive
when one label fiber is odd and the regular degree is positive. -/
theorem joining_degree_bound_pos_of_odd_fiber {I : Type*} [DecidableEq I]
    (label : V → I) (i : I) {h D : ℕ}
    (hh : 0 < h) (hregular : ∀ v, G.degree v = h)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull h X)
    (hodd : (univ.filter (fun v => label v = i)).card % 2 = 1)
    (hD : ∀ v, G.degreeOn
      (univ.filter (fun e => label (G.firstEnd e) ≠ label (G.secondEnd e))) v ≤ D) :
    0 < D := by
  obtain ⟨e, he⟩ := joining_nonempty_of_odd_fiber G label i hh hregular hno hodd
  have hpos : 0 < G.degreeOn
      (univ.filter (fun f => label (G.firstEnd f) ≠ label (G.secondEnd f)))
      (G.firstEnd e) := by
    apply Finset.card_pos.mpr
    exact ⟨e, mem_filter.mpr ⟨he, (G.incident_iff e _).mpr (Or.inl rfl)⟩⟩
  exact lt_of_lt_of_le hpos (hD _)

/-- In particular, the joining-boundary degree bound of four odd parts
cannot be zero. -/
theorem four_odd_joining_degree_bound_pos (label : V → Fin 4) {h D : ℕ}
    (hh : 0 < h) (hregular : ∀ v, G.degree v = h)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull h X)
    (hodd : ∀ i : Fin 4, (univ.filter (fun v => label v = i)).card % 2 = 1)
    (hD : ∀ v, G.degreeOn
      (univ.filter (fun e => label (G.firstEnd e) ≠ label (G.secondEnd e))) v ≤ D) :
    0 < D := by
  apply joining_degree_bound_pos_of_odd_fiber G label (0 : Fin 4) hh hregular hno
  · simpa using hodd (0 : Fin 4)
  · simpa using hD

end Overfull.FourOdd
