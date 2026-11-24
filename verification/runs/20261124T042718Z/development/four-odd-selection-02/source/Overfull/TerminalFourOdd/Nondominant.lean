import Overfull.TerminalFourOdd.BoundaryColoring

/-!
# Four-odd factorization with a singleton reserve in every part

The actual primary matchings prescribe one common label on every joining
copy. Each robust shore independently extends that boundary coloring, and
the extensions agree on every original overlap copy. No local or global
coloring is assumed.
-/

noncomputable section

namespace Overfull.TerminalFourOdd

open Finset Classical FourOdd BoundaryExtension NativeTerminal SmallCuts Multigraph

set_option maxHeartbeats 1000000 in
theorem exists_uniform_nondominant_coloring (α γ ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hγ : 0 < γ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ α/8) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (V E : Type*) [Fintype V] [Fintype E] (G : Multigraph V E)
        (label : V → Fin 4) (C : ∀ i, Core G (labelShore label {i})) (k : ℕ) (a : ℝ),
        (∀ i, m₀ ≤ (labelShore label {i}).card) →
        (∀ i, (labelShore label {i}).card % 2 = 1) →
        (∀ v, G.degree v = k) →
        (∀ i, α*(labelShore label {i}).card ≤ (k : ℝ)) →
        (∀ i, IsRobustExpander (C i).graph ν τ) → 0 ≤ a →
        (∀ i, a ≤ ε*(labelShore label {i}).card) →
        (∀ i v, (k : ℝ)-a ≤ ((C i).graph.degree v : ℝ)) →
        (M : Fin k → Finset E) → (∀ j, G.IsMatching (M j)) →
        Pairwise (fun i j => Disjoint (M i) (M j)) →
        univ.biUnion M = joiningCopies G label →
        (∀ j i, (G.cutOn (M j) (labelShore label {i})).card = 1 ∨
          (G.cutOn (M j) (labelShore label {i})).card = 3) →
        (∀ i, γ*(labelShore label {i}).card ≤
          ((univ.filter (fun j => (G.cutOn (M j) (labelShore label {i})).card = 1)).card : ℝ)) →
        Nonempty (G.EdgeColoring k) := by
  obtain ⟨ε, hε, m₀, hfactor⟩ := boundary_extension α γ ν τ hα hα1 hγ hν hντ hτ
  refine ⟨ε, hε, m₀, ?_⟩
  intro V E _ _ G label C k a hm hodd hregular hdensity hrob ha herror hdegree
    M hM hdisj hcover hclasses hsingle
  let U := fun i : Fin 4 => labelShore label {i}
  let c := primaryBoundaryColoring G label k M hcover
  have hlocal : ∀ i, ∃ full : (retainedGraph G (U i)).EdgeColoring k,
      ∀ e : G.cutEdges (U i), full.color (boundaryLift G (U i) e) = (c i hM).color e := by
    intro i
    apply hfactor V E G (U i) (C i) k a (c i hM) (hm i) (hodd i)
      (fun v => hregular v.val) (hdensity i) (hrob i) ha (herror i) (hdegree i)
    · intro j
      rw [primaryBoundaryColoring_class_card G label k M hcover i hM hdisj j]
      exact hclasses j i
    · rw [primaryBoundaryColoring_singletonColors G label k M hcover i hM hdisj]
      exact hsingle i
  choose full hfull using hlocal
  have hUcover : ∀ v, ∃ i, v ∈ U i := by
    intro v
    exact ⟨label v, by simp [U]⟩
  have hUdisj : Pairwise (fun i j => Disjoint (U i) (U j)) := by
    intro i j hij
    apply disjoint_left.mpr
    intro v hi hj
    have hi' : label v = i := by simpa only [U, mem_labelShore, mem_singleton] using hi
    have hj' : label v = j := by simpa only [U, mem_labelShore, mem_singleton] using hj
    exact hij (hi'.symm.trans hj')
  obtain ⟨d, _⟩ := exists_glued_retained_coloring G U hUcover
    (fun i => PaletteColoring.ofEdgeColoring (full i)) (by
      intro i j e hi hj
      by_cases hij : i = j
      · subst j
        rfl
      obtain ⟨hei, hej⟩ := boundary_of_two_retained G (U i) (U j) (hUdisj hij) e hi hj
      exact (hfull i ⟨e,hei⟩).trans
        ((primaryBoundaryColoring_agrees G label k M hcover i j hM e hei hej).trans
          (hfull j ⟨e,hej⟩).symm))
  exact ⟨d.toEdgeColoring⟩

end Overfull.TerminalFourOdd
