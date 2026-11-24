import Overfull.OneCore.Complement

/-!
# Coloring the terminal exceptional complement

The first-fan theorem removes the core incidences of every ordinary
exceptional vertex from a hypothetical minimal obstruction. The resulting
obstruction has at most one vertex of large degree, so the proved one-high
coloring theorem gives a contradiction. This argument permits an arbitrary
apex and does not require bounds on its parallel bundles or triangles.

The distinguished core is represented by its actual original edge copies.
The final wrappers retain those copies after moving vertices out of the
core, using the already proved bounded-core-move theorem.
-/

namespace Overfull.TerminalComplement

open Finset Classical SmallCuts OneCore

variable {V E : Type*} [Fintype V] [Fintype E]

/-- An actual core complement is colorable when every exterior vertex
except a possible apex has few incidences outside the core. The apex is
arbitrary and may belong to the core. No coloring is supplied as an input. -/
theorem colorable_one_apex (G : Multigraph V E) (U : Finset V) (H : Finset E)
    (z : V) (k : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hregular : ∀ v, G.degree v = k)
    (hcore : ∀ v ∈ U, ((G.restrictEdges Hᶜ).degree v : ℝ) ≤ a)
    (houtside : ∀ v ∉ U, v ≠ z → ((G.edgesTo v Uᶜ).card : ℝ) ≤ b)
    (hfan : 2 * a + b < k) (hgreedy : 2 * max a b < k) :
    Nonempty ((G.restrictEdges Hᶜ).EdgeColoring k) := by
  by_contra hnot
  obtain ⟨F, hsub, hminimal⟩ := G.exists_kMinimal_subset k
    (fun v => (hregular v).le) Hᶜ hnot
  obtain ⟨_hinside, hfirst⟩ := G.first_fan k a ha U H F hregular hsub hminimal
    hcore (by linarith)
  apply hminimal.2.1
  apply (G.restrictEdges F).edgeColoring_one_high k (max a b) z hminimal.1
  · intro v hvz
    by_cases hvU : v ∈ U
    · exact (show ((G.restrictEdges F).degree v : ℝ) ≤
          ((G.restrictEdges Hᶜ).degree v : ℝ) by
            exact_mod_cast G.restrictEdges_degree_mono hsub v).trans
        ((hcore v hvU).trans (le_max_left _ _))
    · have hout := houtside v hvU hvz
      have hsum : ((G.edgesTo v Uᶜ).card : ℝ) + (G.edgesTo v U).card = k := by
        exact_mod_cast (G.edgesTo_compl_card_add v U).trans (hregular v)
      have hmany : 2 * a < ((G.edgesTo v U).card : ℝ) := by linarith
      have hnone := (hfirst v hmany).1
      have hdegree := (G.restrictEdges F).edgesTo_compl_card_add v U
      rw [hnone, Finset.card_empty, Nat.add_zero] at hdegree
      have hbound : (G.restrictEdges F).degree v ≤ (G.edgesTo v Uᶜ).card := by
        rw [← hdegree]
        exact G.restrictEdges_edgesTo_card_le F v Uᶜ
      exact (show ((G.restrictEdges F).degree v : ℝ) ≤
        ((G.edgesTo v Uᶜ).card : ℝ) by exact_mod_cast hbound).trans
          (hout.trans (le_max_right _ _))
  · exact hgreedy

/-- The terminal complement theorem for an actual embedded simple core,
using its minimum degree and the ordinary exceptional incidence bound. -/
theorem core_colorable_one_apex (G : Multigraph V E) (U : Finset V)
    (C : Core G U) (z : V) (k : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ))
    (houtside : ∀ v ∉ U, v ≠ z → ((G.edgesTo v Uᶜ).card : ℝ) ≤ b)
    (hfan : 2 * a + b < k) (hgreedy : 2 * max a b < k) :
    Nonempty ((G.restrictEdges (coreEdges C)ᶜ).EdgeColoring k) := by
  apply colorable_one_apex G U (coreEdges C) z k a b ha hb hregular
    (fun v hv => complement_degree_le_error C k a hregular hdegree ⟨v, hv⟩)
    houtside hfan hgreedy

/-- If every exceptional vertex has the ordinary incidence bound, any
vertex in a nonempty core may play the harmless distinguished role. -/
theorem core_colorable (G : Multigraph V E) (U : Finset V) (C : Core G U)
    (k : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hU : U.Nonempty)
    (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ))
    (houtside : ∀ v ∉ U, ((G.edgesTo v Uᶜ).card : ℝ) ≤ b)
    (hfan : 2 * a + b < k) (hgreedy : 2 * max a b < k) :
    Nonempty ((G.restrictEdges (coreEdges C)ᶜ).EdgeColoring k) := by
  obtain ⟨z, _hz⟩ := hU
  exact core_colorable_one_apex G U C z k a b ha hb hregular hdegree
    (fun v hv _ => houtside v hv) hfan hgreedy

/-- Moving any bounded set out of the terminal core preserves the
constructed complement coloring, on the exact surviving original copies. -/
theorem moved_core_colorable_one_apex (G : Multigraph V E) (U : Finset V)
    (C : Core G U) (z : V) (W : Finset V) (k : ℕ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ))
    (houtside : ∀ v ∉ U, v ≠ z → ((G.edgesTo v Uᶜ).card : ℝ) ≤ b)
    (hfan : 2 * a + b < k) (hgreedy : 2 * max a b < k)
    (hmove : 3 * (a + W.card) < k) :
    Nonempty ((G.restrictEdges (coreEdges (restrictCore C W))ᶜ).EdgeColoring k) ∧
      ∀ v ∈ U \ W,
        ((G.restrictEdges (coreEdges (restrictCore C W))ᶜ).degree v : ℝ) ≤ a + W.card := by
  have hc := core_colorable_one_apex G U C z k a b ha hb hregular hdegree
    houtside hfan hgreedy
  rw [restrictCore_edges]
  exact G.bounded_core_move k a ha U W (coreEdges C) hregular
    (coreEdges_subset_internal C) (coreEdges_simple C)
    (fun v hv => complement_degree_le_error C k a hregular hdegree ⟨v, hv⟩) hc hmove

end Overfull.TerminalComplement
