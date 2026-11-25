import Overfull.NativeTerminal.PairColoring
import Overfull.NativeTerminal.ShoreFactorization
import Overfull.NativeTerminal.ColoringGlue

/-!
# Coloring two separately closed exceptional pairs

The two components reuse the same palette.  Every edge in the union is an
original retained copy, and closedness prevents a color conflict between
the two components.  No bound on their combined order by two is assumed.
-/

noncomputable section

namespace Overfull.NativeTerminal

open Finset Classical Multigraph BoundaryExtension SmallCuts

variable {V E : Type*} [Fintype E]

/-- Every incidence of a retained copy lies in its closed shore. -/
theorem incident_mem_of_retained_closed (G : Multigraph V E) (A : Finset V)
    (hcut : G.cutEdges A = ∅) (e : RetainedEdge G A) {v : V}
    (hv : v ∈ G.edge e.val) : v ∈ A := by
  obtain ⟨w, hw⟩ := e.property
  have hi := internal_of_incident_of_cut_empty G A hcut w.property hw
  have hends := (G.mem_internalEdges A e.val).mp hi
  rcases (G.incident_iff e.val v).mp hv with h | h
  · exact h ▸ hends.1
  · exact h ▸ hends.2

/-- Colorings of two disjoint closed shores give a coloring of all original
copies retained by their union, using exactly the same palette. -/
theorem retained_closed_union_colorable (G : Multigraph V E) (A B : Finset V)
    (k : ℕ) (hAB : Disjoint A B)
    (hA : G.cutEdges A = ∅) (hB : G.cutEdges B = ∅)
    (cA : (retainedGraph G A).EdgeColoring k)
    (cB : (retainedGraph G B).EdgeColoring k) :
    Nonempty ((retainedGraph G (A ∪ B)).EdgeColoring k) := by
  have inB (e : RetainedEdge G (A ∪ B))
      (ha : ¬ ∃ v : A, v.val ∈ G.edge e.val) :
      ∃ v : B, v.val ∈ G.edge e.val := by
    obtain ⟨v, hv⟩ := e.property
    rcases mem_union.mp v.property with hvA | hvB
    · exact (ha ⟨⟨v.val, hvA⟩, hv⟩).elim
    · exact ⟨⟨v.val, hvB⟩, hv⟩
  let color (e : RetainedEdge G (A ∪ B)) : Fin k :=
    if ha : ∃ v : A, v.val ∈ G.edge e.val then cA.color ⟨e.val, ha⟩
    else cB.color ⟨e.val, inB e ha⟩
  refine ⟨⟨color, ?_⟩⟩
  intro e f v hc hev hfv
  change v ∈ G.edge e.val at hev
  change v ∈ G.edge f.val at hfv
  dsimp only [color] at hc
  split_ifs at hc with heA hfA hfA
  · exact Subtype.ext
      (congrArg (fun q : RetainedEdge G A => q.val) (cA.proper hc hev hfv))
  · have hvA := incident_mem_of_retained_closed G A hA ⟨e.val, heA⟩ hev
    have hvB := incident_mem_of_retained_closed G B hB ⟨f.val, inB f hfA⟩ hfv
    exact (disjoint_left.mp hAB hvA hvB).elim
  · have hvB := incident_mem_of_retained_closed G B hB ⟨e.val, inB e heA⟩ hev
    have hvA := incident_mem_of_retained_closed G A hA ⟨f.val, hfA⟩ hfv
    exact (disjoint_left.mp hAB hvA hvB).elim
  · exact Subtype.ext
      (congrArg (fun q : RetainedEdge G B => q.val) (cB.proper hc hev hfv))

/-- The union of two separately closed exceptional pairs is colorable by
the maximum-degree palette.  Both parallel-copy pools are retained. -/
theorem retained_two_pairs_colorable (G : Multigraph V E) (B₀ B₁ : Finset V)
    (k : ℕ) (hdisjoint : Disjoint B₀ B₁)
    (hcut₀ : G.cutEdges B₀ = ∅) (hcut₁ : G.cutEdges B₁ = ∅)
    (hcard₀ : B₀.card ≤ 2) (hcard₁ : B₁.card ≤ 2)
    (hdegree : ∀ v ∈ B₀ ∪ B₁, G.degree v ≤ k) :
    Nonempty ((retainedGraph G (B₀ ∪ B₁)).EdgeColoring k) := by
  obtain ⟨c₀⟩ := retained_pair_colorable G B₀ k hcut₀ hcard₀
    (fun v hv => hdegree v (mem_union_left _ hv))
  obtain ⟨c₁⟩ := retained_pair_colorable G B₁ k hcut₁ hcard₁
    (fun v hv => hdegree v (mem_union_right _ hv))
  exact retained_closed_union_colorable G B₀ B₁ k hdisjoint hcut₀ hcut₁ c₀ c₁

/-- A union of two closed shores is closed, with no assumption on its size. -/
theorem cutEdges_union_eq_empty (G : Multigraph V E) (A B : Finset V)
    (hA : G.cutEdges A = ∅) (hB : G.cutEdges B = ∅) :
    G.cutEdges (A ∪ B) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  have ha : (G.firstEnd e ∈ A) = (G.secondEnd e ∈ A) := by
    by_contra hn
    have hh := (G.mem_cutEdges A e).mpr hn
    rw [hA] at hh
    exact notMem_empty e hh
  have hb : (G.firstEnd e ∈ B) = (G.secondEnd e ∈ B) := by
    by_contra hn
    have hh := (G.mem_cutEdges B e).mpr hn
    rw [hB] at hh
    exact notMem_empty e hh
  apply (G.mem_cutEdges (A ∪ B) e).mp he
  simp only [mem_union, ha, hb]

/-- Uniform terminal factorization with two robust assigned shores and two
separate closed exceptional pairs.  Each pair may be empty, a singleton, or
a parallel-copy component on two vertices.  The large shores retain the
same even/odd alternatives and the same bounded-star hypotheses as before. -/
theorem exists_uniform_two_shore_two_pair_factorization (α ν τ : ℝ) (s : ℕ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ min α 1 / 16) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (V E : Type*) [Fintype E] (G : Multigraph V E)
        (U₀ U₁ A₀ A₁ B₀ B₁ : Finset V) (C₀ : Core G U₀) (C₁ : Core G U₁)
        (k : ℕ) (a : ℝ),
        Disjoint A₀ A₁ → Disjoint B₀ B₁ →
        Disjoint A₀ (B₀ ∪ B₁) → Disjoint A₁ (B₀ ∪ B₁) →
        (∀ v, v ∈ A₀ ∨ v ∈ A₁ ∨ v ∈ B₀ ∪ B₁) →
        U₀ ⊆ A₀ → U₁ ⊆ A₁ → m₀ ≤ U₀.card → m₀ ≤ U₁.card →
        (A₀ \ U₀).card ≤ s → (A₁ \ U₁).card ≤ s →
        B₀.card ≤ 2 → B₁.card ≤ 2 →
        G.cutEdges B₀ = ∅ → G.cutEdges B₁ = ∅ → (∀ v, G.degree v = k) →
        α * U₀.card ≤ (k : ℝ) → α * U₁.card ≤ (k : ℝ) →
        IsRobustExpander C₀.graph ν τ → IsRobustExpander C₁.graph ν τ →
        a ≤ ε * U₀.card → a ≤ ε * U₁.card →
        (∀ v, (k : ℝ) - a ≤ (C₀.graph.degree v : ℝ)) →
        (∀ v, (k : ℝ) - a ≤ (C₁.graph.degree v : ℝ)) →
        (∀ z ∈ A₀ \ U₀, ∀ e, z ∈ G.edge e → G.otherEnd z e ∈ U₀) →
        (∀ z ∈ A₁ \ U₁, ∀ e, z ∈ G.edge e → G.otherEnd z e ∈ U₁) →
        G.cutEdges A₀ = G.cutEdges A₁ →
        ((Even A₀.card ∧ Even A₁.card ∧ G.cutEdges A₀ = ∅) ∨
          (Odd A₀.card ∧ Odd A₁.card ∧ G.cutSize A₀ = k)) →
        Nonempty (G.EdgeColoring k) := by
  obtain ⟨ε,hε,m₀,hshore⟩ :=
    exists_uniform_shore_coloring_of_star_incidence α ν τ s hα hν hντ hτ
  refine ⟨ε,hε,m₀,?_⟩
  intro V E _ G U₀ U₁ A₀ A₁ B₀ B₁ C₀ C₁ k a h01 hBB h0B h1B hcover
    hUA₀ hUA₁ hm₀ hm₁ hs₀ hs₁ hBcard₀ hBcard₁ hBcut₀ hBcut₁ hregular
    hk₀ hk₁ hrob₀ hrob₁ ha₀ ha₁ hdegree₀ hdegree₁ hstar₀ hstar₁ hcut hparity
  obtain ⟨hEven₀,hOdd₀⟩ := hshore V E G A₀ U₀ C₀ k a hUA₀ hm₀ hs₀
    (fun v _ => hregular v) hk₀ hrob₀ ha₀ hdegree₀ hstar₀
  obtain ⟨hEven₁,hOdd₁⟩ := hshore V E G A₁ U₁ C₁ k a hUA₁ hm₁ hs₁
    (fun v _ => hregular v) hk₁ hrob₁ ha₁ hdegree₁ hstar₁
  obtain ⟨cB⟩ := retained_two_pairs_colorable G B₀ B₁ k hBB hBcut₀ hBcut₁
    hBcard₀ hBcard₁ (fun v _ => (hregular v).le)
  have hBcut := cutEdges_union_eq_empty G B₀ B₁ hBcut₀ hBcut₁
  rcases hparity with ⟨he₀,he₁,hzero⟩ | ⟨ho₀,ho₁,hsize⟩
  · obtain ⟨c₀⟩ := hEven₀ hzero he₀
    obtain ⟨c₁⟩ := hEven₁ (hcut.symm.trans hzero) he₁
    exact exists_glued_closed_shores_coloring G A₀ A₁ (B₀ ∪ B₁) k
      h01 h0B h1B hcover hzero hBcut c₀ c₁ cB
  · have hsize₁ : G.cutSize A₁ = k := by
      simpa only [Multigraph.cutSize, ← hcut] using hsize
    obtain ⟨c₀⟩ := hOdd₀ hsize ho₀
    obtain ⟨c₁⟩ := hOdd₁ hsize₁ ho₁
    exact exists_glued_contracted_shores_coloring G A₀ A₁ (B₀ ∪ B₁) k
      h01 h0B h1B hcover hBcut hcut hsize c₀ c₁ cB

end Overfull.NativeTerminal
