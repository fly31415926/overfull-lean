import Overfull.Dense.FiniteAbsorberAssembly
import Overfull.Dense.FiniteAbsorberRemainders

/-!
# The finite absorber lemma

For every bounded vertex set, all of its locally balanced remainders have
simultaneous absorbers in the actual dense tripartite host. The order threshold
is uniform in the host, and the total size is at most `4*h^2*2^(h^2)`.

The epsilon condition is written as `16*h*epsilon ≤ gamma`; this is the
manuscript's condition for positive `h` and also covers the empty-set case.
-/

namespace Overfull.Dense.FiniteAbsorber

open Finset Classical
open TripartiteGraph

variable {A B W : Type*} [Fintype A] [Fintype B] [Fintype W]

@[simp] theorem edgeGraph_of_edgeFinset (G : TripartiteGraph A B W) :
    edgeGraph G.edgeFinset = G := by
  cases G
  simp [edgeGraph,TripartiteGraph.edgeFinset,IsEdge,abPos,awPos,bwPos]

/-- Lemma 5.5: a bounded finite absorber for every locally balanced remainder
on the prescribed vertices. Edge coordinates specify an actual simple
subgraph through `edgeGraph`, and all triangle coordinates are actual host
triangles. -/
theorem finite_absorber (h : ℕ) (η γ : ℝ) (hη : 0 < η) (hγ : 0 < γ) :
    ∃ N : ℕ, ∀ (A B W : Type*) [Fintype A] [Fintype B] [Fintype W]
      (G : TripartiteGraph A B W) (ε : ℝ),
      N ≤ Fintype.card A → Density G η γ ε →
      0 < ε → ε ≤ η/32 → 16*(h : ℝ)*ε ≤ γ →
      ∀ U Z : Finset (HostVertex (A := A) (B := B) (W := W)),
      U ⊆ Z → U.card ≤ h → (Z.card : ℝ) ≤ min η γ*Fintype.card A/16 →
      ∃ E : Finset (EdgePosition (A := A) (B := B) (W := W)),
        E ⊆ G.edgeFinset ∧ Disjoint E (internalEdges G Z) ∧
        (∀ v ∈ supportVertices E \ U, v ∉ Z) ∧
        E.card+(supportVertices E \ U).card ≤ 4*h^2*2^(h^2) ∧
        (∃ T : Finset G.Triangle, G.IsTriangleDecomposition T E) ∧
        ∀ L : TripartiteGraph A B W, L.edgeFinset ⊆ internalEdges G U →
          L.IsLocallyBalanced → ∃ T : Finset G.Triangle,
            G.IsTriangleDecomposition T (E ∪ L.edgeFinset) := by
  let b := 4*(h^2*2^(h^2))
  have hmin : 0 < min η γ := lt_min hη hγ
  obtain ⟨N,hN⟩ := exists_nat_gt (16*(b : ℝ)/min η γ+1)
  have hNpos : 0 < N := by
    have hz : (0 : ℝ) ≤ 16*(b : ℝ)/min η γ := by positivity
    have hp : (0 : ℝ) < N := by linarith
    exact_mod_cast hp
  refine ⟨N,?_⟩
  intro A B W _ _ _ G ε horder hG hεpos hε hεh U Z hUZ hU hZ
  have hm : 0 < Fintype.card A := hNpos.trans_le horder
  have hlarge : (b : ℝ) ≤ min η γ*Fintype.card A/16 := by
    have hr : 16*(b : ℝ)/min η γ < N := by linarith
    have hp := (div_lt_iff₀ hmin).mp hr
    have hcast : (N : ℝ) ≤ Fintype.card A := by exact_mod_cast horder
    have hmul := mul_le_mul_of_nonneg_right hcast hmin.le
    nlinarith
  obtain ⟨R⟩ := remainderCycles_exists G U
  have hbudget := R.budget_of_card_le G hU
  have hauxTotal : (∑ i, (2*(R.length i : ℝ)+1)) ≤ (b : ℝ) := by
    have hn : (∑ i, (2*R.length i+1)) ≤ b := by
      calc
        _ ≤ ∑ i, 3*R.length i := Finset.sum_le_sum (fun i _ => by
          have := R.positive i
          omega)
        _ ≤ h^2*2^(h^2) := hbudget
        _ ≤ b := by dsimp [b]; omega
    exact_mod_cast hn
  have hcenter (i : Fin R.count) : 2*(R.length i : ℝ)*ε ≤ γ/16 := by
    have hn : 2*R.length i ≤ h := by have := R.small i; omega
    have hr : 2*(R.length i : ℝ) ≤ h := by exact_mod_cast hn
    have hp := mul_le_mul_of_nonneg_right hr hεpos.le
    nlinarith
  obtain ⟨P,hP⟩ := exists_disjoint_placements G η γ ε hη hγ hε hm hG
    R.count R.length R.cycle hcenter Z (by linarith)
  have hgadgets (i : Fin R.count) : ∃ Q : Gadget G (R.cycle i) U Z,
      Q.aux = (P i).auxVertices G :=
    gadget_of_placement G (R.cycle i) (R.positive i) U Z hUZ
      (R.xInside i) (R.yInside i) (R.wInside i) (P i)
  choose Q hQaux using hgadgets
  have haux : Pairwise (fun i j => Disjoint (Q i).aux (Q j).aux) := by
    intro i j hij
    rw [hQaux i,hQaux j]
    exact hP hij
  have hEdges : Pairwise (fun i j => Disjoint (Q i).edges (Q j).edges) :=
    fun i j hij => (Q i).disjoint_of_aux G (Q j) hUZ (haux hij)
  let E := univ.biUnion (fun i => (Q i).edges)
  refine ⟨E,?_,?_,?_,?_,?_,?_⟩
  · intro e he
    obtain ⟨i,_,hei⟩ := Finset.mem_biUnion.mp he
    exact (Q i).subgraph hei
  · apply Finset.disjoint_left.mpr
    intro e he heZ
    obtain ⟨i,_,hei⟩ := Finset.mem_biUnion.mp he
    obtain ⟨v,hve,hvaux⟩ := (Q i).meets e hei
    exact (Q i).outside v hvaux (((mem_internalEdges G Z e).mp heZ).2 v hve)
  · intro v hv
    obtain ⟨hv,hvU⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨e,he,hve⟩ := (mem_supportVertices E v).mp hv
    obtain ⟨i,_,hei⟩ := Finset.mem_biUnion.mp he
    exact (Q i).outside v (((Q i).support e hei v hve).resolve_left hvU)
  · calc
      _ ≤ 4*(∑ i, 3*R.length i) := gadget_union_size G Q R.positive
      _ ≤ 4*(h^2*2^(h^2)) := Nat.mul_le_mul_left 4 hbudget
      _ = 4*h^2*2^(h^2) := (Nat.mul_assoc _ _ _).symm
  · exact G.decomposition_biUnion (fun i => (Q i).edges) hEdges (fun i => (Q i).default)
  · intro L hL hbalanced
    let S := univ.filter (fun i => R.tag i = L.edgeFinset)
    have hinside (i : Fin R.count) := (R.cycle i).edges_inside G U
      (R.xInside i) (R.yInside i) (R.wInside i)
    have hS : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
        Disjoint ((R.cycle i).graph G).edgeFinset ((R.cycle j).graph G).edgeFinset := by
      intro i hi j hj hij
      exact R.sameTagDisjoint i j hij
        ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
    obtain ⟨T,hT⟩ := assemble_gadgets G Q hUZ haux hinside S hS
    have hcover : S.biUnion (fun i => ((R.cycle i).graph G).edgeFinset) = L.edgeFinset :=
      R.cover L.edgeFinset hL (by simpa only [edgeGraph_of_edgeFinset] using hbalanced)
    refine ⟨T,?_⟩
    simpa only [hcover] using hT

theorem edgeGraph_toSimpleGraph_le (G : TripartiteGraph A B W)
    (E : Finset (EdgePosition (A := A) (B := B) (W := W)))
    (hE : E ⊆ G.edgeFinset) : (edgeGraph E).toSimpleGraph ≤ G.toSimpleGraph := by
  rintro (a | b | w) (a' | b' | w') h
  all_goals simp only [toSimpleGraph,edgeGraph] at h ⊢
  · exact (G.mem_edgeFinset (abPos a b')).mp (hE h)
  · exact (G.mem_edgeFinset (awPos a w')).mp (hE h)
  · exact (G.mem_edgeFinset (abPos a' b)).mp (hE h)
  · exact (G.mem_edgeFinset (bwPos b w')).mp (hE h)
  · exact (G.mem_edgeFinset (awPos a' w)).mp (hE h)
  · exact (G.mem_edgeFinset (bwPos b' w)).mp (hE h)

/-- The finite absorber theorem with its actual simple subgraph returned
explicitly. The decompositions consist of actual host triangles and cover
exactly the indicated subgraph edges. -/
theorem finite_absorber_graph (h : ℕ) (η γ : ℝ) (hη : 0 < η) (hγ : 0 < γ) :
    ∃ N : ℕ, ∀ (A B W : Type*) [Fintype A] [Fintype B] [Fintype W]
      (G : TripartiteGraph A B W) (ε : ℝ),
      N ≤ Fintype.card A → Density G η γ ε →
      0 < ε → ε ≤ η/32 → 16*(h : ℝ)*ε ≤ γ →
      ∀ U Z : Finset (HostVertex (A := A) (B := B) (W := W)),
      U ⊆ Z → U.card ≤ h → (Z.card : ℝ) ≤ min η γ*Fintype.card A/16 →
      ∃ H : TripartiteGraph A B W,
        H.toSimpleGraph ≤ G.toSimpleGraph ∧
        Disjoint H.edgeFinset (internalEdges G Z) ∧
        (∀ v ∈ supportVertices H.edgeFinset \ U, v ∉ Z) ∧
        H.edgeFinset.card+(supportVertices H.edgeFinset \ U).card ≤ 4*h^2*2^(h^2) ∧
        (∃ T : Finset G.Triangle, G.IsTriangleDecomposition T H.edgeFinset) ∧
        ∀ L : TripartiteGraph A B W, L.edgeFinset ⊆ internalEdges G U →
          L.IsLocallyBalanced → ∃ T : Finset G.Triangle,
            G.IsTriangleDecomposition T (H.edgeFinset ∪ L.edgeFinset) := by
  obtain ⟨N,hN⟩ := finite_absorber h η γ hη hγ
  refine ⟨N,?_⟩
  intro A B W _ _ _ G ε horder hG hεpos hε hεh U Z hUZ hU hZ
  obtain ⟨E,hEG,hrest⟩ := hN A B W G ε horder hG hεpos hε hεh U Z hUZ hU hZ
  refine ⟨edgeGraph E,edgeGraph_toSimpleGraph_le G E hEG,?_⟩
  simpa only [edgeGraph_edgeFinset] using hrest

end Overfull.Dense.FiniteAbsorber
