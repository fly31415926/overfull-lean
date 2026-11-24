import Overfull.NativeTerminal.ShoreHost

/-!
# Gluing shore colorings on the original edge copies

Local colorings are compared on individual retained copies.  Agreement on
those overlaps gives a proper coloring on the original vertex and edge types.
For disjoint shores, overlap copies are exactly their shared boundary copies.
-/

noncomputable section

namespace Overfull.NativeTerminal

open Finset Classical Multigraph BoundaryExtension

variable {V E I C : Type*}

/-- A covering family of retained-graph colorings glues when every common
original copy has the same label in both local colorings. -/
theorem exists_glued_retained_coloring (G : Multigraph V E)
    (A : I → Finset V) (hcover : ∀ v, ∃ i, v ∈ A i)
    (c : ∀ i, PaletteColoring (retainedGraph G (A i)) C)
    (hagrees : ∀ i j (e : E)
      (hi : ∃ u : A i, u.val ∈ G.edge e)
      (hj : ∃ u : A j, u.val ∈ G.edge e),
      (c i).color ⟨e,hi⟩ = (c j).color ⟨e,hj⟩) :
    ∃ d : PaletteColoring G C,
      ∀ i (e : RetainedEdge G (A i)), d.color e.val = (c i).color e := by
  let pick (e : E) : I := Classical.choose (hcover (G.firstEnd e))
  have hpick (e : E) : ∃ u : A (pick e), u.val ∈ G.edge e :=
    ⟨⟨G.firstEnd e, Classical.choose_spec (hcover (G.firstEnd e))⟩,
      (G.incident_iff e _).mpr (Or.inl rfl)⟩
  let color (e : E) : C := (c (pick e)).color ⟨e,hpick e⟩
  have hcolor (i : I) (e : RetainedEdge G (A i)) :
      color e.val = (c i).color e := hagrees (pick e.val) i e.val (hpick e.val) e.property
  have hproper : ∀ {e f : E} {v : V}, color e = color f →
      v ∈ G.edge e → v ∈ G.edge f → e = f := by
    intro e f v hc hev hfv
    obtain ⟨i,hvi⟩ := hcover v
    let ei : RetainedEdge G (A i) := ⟨e,⟨⟨v,hvi⟩,hev⟩⟩
    let fi : RetainedEdge G (A i) := ⟨f,⟨⟨v,hvi⟩,hfv⟩⟩
    have hlocal : (c i).color ei = (c i).color fi :=
      (hcolor i ei).symm.trans (hc.trans (hcolor i fi))
    exact congrArg Subtype.val ((c i).proper hlocal hev hfv)
  exact ⟨⟨color,hproper⟩,hcolor⟩

variable [Fintype E]

/-- A copy retained by two disjoint shores crosses both shore cuts. -/
theorem boundary_of_two_retained (G : Multigraph V E) (A B : Finset V)
    (hAB : Disjoint A B) (e : E)
    (hA : ∃ u : A, u.val ∈ G.edge e)
    (hB : ∃ u : B, u.val ∈ G.edge e) :
    e ∈ G.cutEdges A ∧ e ∈ G.cutEdges B := by
  have ha := retained_endpoints G A ⟨e,hA⟩
  have hb := retained_endpoints G B ⟨e,hB⟩
  have hf : ¬ (G.firstEnd e ∈ A ∧ G.firstEnd e ∈ B) :=
    fun h => disjoint_left.mp hAB h.1 h.2
  have hs : ¬ (G.secondEnd e ∈ A ∧ G.secondEnd e ∈ B) :=
    fun h => disjoint_left.mp hAB h.1 h.2
  simp only [Multigraph.mem_cutEdges, ne_eq, eq_iff_iff]
  tauto

/-- A component shore has no retained copy in common with a disjoint shore. -/
theorem no_overlap_of_closed_shore (G : Multigraph V E) (A B : Finset V)
    (hAB : Disjoint A B) (hB : G.cutEdges B = ∅) (e : E)
    (ha : ∃ u : A, u.val ∈ G.edge e)
    (hb : ∃ u : B, u.val ∈ G.edge e) : False := by
  have hh := (boundary_of_two_retained G A B hAB e ha hb).2
  rw [hB] at hh
  exact notMem_empty e hh

/-- Three disjoint vertex shores, one of them closed, can be glued using
agreement only on the two nonclosed shores' actual crossing copies. -/
theorem exists_glued_three_shore_coloring (G : Multigraph V E)
    (A₀ A₁ B : Finset V)
    (h01 : Disjoint A₀ A₁) (h0B : Disjoint A₀ B) (h1B : Disjoint A₁ B)
    (hcover : ∀ v, v ∈ A₀ ∨ v ∈ A₁ ∨ v ∈ B)
    (hB : G.cutEdges B = ∅)
    (c₀ : PaletteColoring (retainedGraph G A₀) C)
    (c₁ : PaletteColoring (retainedGraph G A₁) C)
    (cB : PaletteColoring (retainedGraph G B) C)
    (hagrees : ∀ (e : E) (h₀ : e ∈ G.cutEdges A₀) (h₁ : e ∈ G.cutEdges A₁),
      c₀.color (boundaryLift G A₀ ⟨e,h₀⟩) =
        c₁.color (boundaryLift G A₁ ⟨e,h₁⟩)) :
    Nonempty (PaletteColoring G C) := by
  let A : Fin 3 → Finset V := ![A₀,A₁,B]
  have hA : ∀ v, ∃ i, v ∈ A i := by
    intro v
    rcases hcover v with h | h | h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
  let c : ∀ i, PaletteColoring (retainedGraph G (A i)) C := by
    refine Fin.cases c₀ ?_
    refine Fin.cases c₁ ?_
    refine Fin.cases cB ?_
    exact Fin.elim0
  have hcompat : ∀ i j (e : E)
      (hi : ∃ u : A i, u.val ∈ G.edge e)
      (hj : ∃ u : A j, u.val ∈ G.edge e),
      (c i).color ⟨e,hi⟩ = (c j).color ⟨e,hj⟩ := by
    intro i j e hi hj
    fin_cases i <;> fin_cases j
    · rfl
    · obtain ⟨he₀,he₁⟩ := boundary_of_two_retained G A₀ A₁ h01 e hi hj
      exact hagrees e he₀ he₁
    · exact (no_overlap_of_closed_shore G A₀ B h0B hB e hi hj).elim
    · obtain ⟨he₀,he₁⟩ := boundary_of_two_retained G A₀ A₁ h01 e hj hi
      exact (hagrees e he₀ he₁).symm
    · rfl
    · exact (no_overlap_of_closed_shore G A₁ B h1B hB e hi hj).elim
    · exact (no_overlap_of_closed_shore G A₀ B h0B hB e hj hi).elim
    · exact (no_overlap_of_closed_shore G A₁ B h1B hB e hj hi).elim
    · rfl
  obtain ⟨d,_⟩ := exists_glued_retained_coloring G A hA c hcompat
  exact ⟨d⟩

/-- When both large shores are components, their retained colorings glue
without any palette constraints on different components. -/
theorem exists_glued_closed_shores_coloring (G : Multigraph V E)
    (A₀ A₁ B : Finset V) (k : ℕ)
    (h01 : Disjoint A₀ A₁) (h0B : Disjoint A₀ B) (h1B : Disjoint A₁ B)
    (hcover : ∀ v, v ∈ A₀ ∨ v ∈ A₁ ∨ v ∈ B)
    (h₀ : G.cutEdges A₀ = ∅) (hB : G.cutEdges B = ∅)
    (c₀ : (retainedGraph G A₀).EdgeColoring k)
    (c₁ : (retainedGraph G A₁).EdgeColoring k)
    (cB : (retainedGraph G B).EdgeColoring k) :
    Nonempty (G.EdgeColoring k) := by
  obtain ⟨c⟩ := exists_glued_three_shore_coloring G A₀ A₁ B h01 h0B h1B hcover hB
    (PaletteColoring.ofEdgeColoring c₀) (PaletteColoring.ofEdgeColoring c₁)
    (PaletteColoring.ofEdgeColoring cB) (by
      intro e he _
      rw [h₀] at he
      exact (notMem_empty e he).elim)
  exact ⟨c.toEdgeColoring⟩

/-- Both odd shores use the same labels on the same original crossing
copies.  The singleton label restoration theorem constructs the agreement. -/
theorem exists_glued_contracted_shores_coloring (G : Multigraph V E)
    (A₀ A₁ B : Finset V) (k : ℕ)
    (h01 : Disjoint A₀ A₁) (h0B : Disjoint A₀ B) (h1B : Disjoint A₁ B)
    (hcover : ∀ v, v ∈ A₀ ∨ v ∈ A₁ ∨ v ∈ B)
    (hB : G.cutEdges B = ∅)
    (hcut : G.cutEdges A₀ = G.cutEdges A₁)
    (hsize : G.cutSize A₀ = k)
    (c₀ : (contract G A₀).EdgeColoring k)
    (c₁ : (contract G A₁).EdgeColoring k)
    (cB : (retainedGraph G B).EdgeColoring k) :
    Nonempty (G.EdgeColoring k) := by
  have hcard : Fintype.card (G.cutEdges A₀) = Fintype.card (Fin k) := by
    simpa only [Fintype.card_coe, Fintype.card_fin, Multigraph.cutSize] using hsize
  let label : G.cutEdges A₀ ≃ Fin k := Fintype.equivOfCardEq hcard
  let transfer : G.cutEdges A₁ ≃ G.cutEdges A₀ := Equiv.setCongr (by rw [hcut])
  let label₁ : G.cutEdges A₁ → Fin k := label ∘ transfer
  have hsize₁ : G.cutSize A₁ = k := by
    simpa only [Multigraph.cutSize, ← hcut] using hsize
  obtain ⟨d₀,hd₀,_⟩ := exists_singleton_boundary_extension G A₀ k c₀ hsize
    label label.injective
  obtain ⟨d₁,hd₁,_⟩ := exists_singleton_boundary_extension G A₁ k c₁ hsize₁
    label₁ (label.injective.comp transfer.injective)
  obtain ⟨d⟩ := exists_glued_three_shore_coloring G A₀ A₁ B h01 h0B h1B hcover hB
    d₀ d₁ (PaletteColoring.ofEdgeColoring cB) (by
      intro e he₀ he₁
      rw [hd₀,hd₁]
      rfl)
  exact ⟨d.toEdgeColoring⟩

end Overfull.NativeTerminal
