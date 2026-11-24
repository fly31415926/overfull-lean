import Overfull.OneCore.Complement
import Overfull.BalancedColoring
import Overfull.ColoringExtension.Exterior

/-!
# Actual exterior data for a balanced bipartite core

The host is a regular loopless multigraph, and the simple bipartite core
is embedded by its actual edge copies. Removing those copies preserves
the full degree of every exterior vertex. The two exterior side-degree
sums agree because each core copy meets each side exactly once.

The proved balanced-coloring theorem therefore constructs a proper
exterior coloring saturating every exceptional vertex. Its actual core
footprints have equal side sizes, bounded total size, and exact incidence
load. These are preparatory inputs to robust-core factorization; no
coloring of the whole host is asserted.
-/

noncomputable section

namespace Overfull.BipartiteFactorization

open Finset Classical SmallCuts
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E]
variable {G : Multigraph V E} {U A B : Finset V}

/-- The exterior graph retains precisely the original non-core copies. -/
abbrev exterior (C : Core G U) := G.restrictEdges (OneCore.coreEdges C)ᶜ

omit [Fintype V] [Fintype E] in
/-- An original core copy has one endpoint on each actual side. -/
theorem core_copy_crosses (C : Core G (A ∪ B))
    (hbip : C.graph.IsBipartiteWith {v | v.val ∈ A} {v | v.val ∈ B})
    {e : E} (he : e ∈ OneCore.coreEdges C) :
    ∃ x ∈ A, ∃ y ∈ B, G.edge e = s(x,y) := by
  obtain ⟨f,rfl⟩ := (OneCore.mem_coreEdges C e).mp he
  let x := (Multigraph.ofSimpleGraph C.graph).firstEnd f
  let y := (Multigraph.ofSimpleGraph C.graph).secondEnd f
  have hf : s(x,y) = f.val := (Multigraph.ofSimpleGraph C.graph).edge_eq f
  have hxy : C.graph.Adj x y := by
    have hh := f.property
    rw [← hf] at hh
    exact hh
  have hedge : G.edge (C.edgeMap f) = s(x.val,y.val) := by
    rw [C.map_edge, ← hf]
    rfl
  rcases hbip.mem_of_adj hxy with ⟨hx,hy⟩ | ⟨hy,hx⟩
  · exact ⟨x.val,hx,y.val,hy,hedge⟩
  · exact ⟨y.val,hx,x.val,hy,hedge.trans Sym2.eq_swap⟩

omit [Fintype V] in
/-- Every copy crossing between two disjoint sides contributes once to
the degree sum on either side, even when several copies are parallel. -/
theorem degree_sum_eq_copies_of_crossing (H : Multigraph V E)
    (A B : Finset V) (hAB : Disjoint A B)
    (hcross : ∀ e, ∃ x ∈ A, ∃ y ∈ B, H.edge e = s(x,y)) :
    (∑ v ∈ A, H.degree v) = Fintype.card E := by
  have hcut : H.cutEdges A = univ := by
    apply Finset.eq_univ_of_forall
    intro e
    obtain ⟨x,hx,y,hy,he⟩ := hcross e
    exact (H.mem_cutEdges_iff A e).mpr
      ⟨x,y,he,hx,fun hyA => Finset.disjoint_left.mp hAB hyA hy⟩
  have hinternal : H.internalEdges A = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨x,_hx,y,hy,hedge⟩ := hcross e
    have hsub := (Finset.mem_filter.mp he).2
    have hyA : y ∈ A := hsub (by rw [hedge]; simp)
    exact Finset.disjoint_left.mp hAB hyA hy
  simpa only [hinternal, Finset.card_empty, mul_zero, zero_add,
    Multigraph.cutSize, hcut, Finset.card_univ] using H.degree_sum_on A

omit [Fintype V] [Fintype E] in
/-- Exact core-copy counting on both sides of the embedded bipartite core. -/
theorem core_side_degree_sums (C : Core G (A ∪ B))
    (hAB : Disjoint A B)
    (hbip : C.graph.IsBipartiteWith {v | v.val ∈ A} {v | v.val ∈ B}) :
    (∑ v ∈ A, (G.restrictEdges (OneCore.coreEdges C)).degree v) =
        (OneCore.coreEdges C).card ∧
      (∑ v ∈ B, (G.restrictEdges (OneCore.coreEdges C)).degree v) =
        (OneCore.coreEdges C).card := by
  have hcross (e : ↥(OneCore.coreEdges C)) :
      ∃ x ∈ A, ∃ y ∈ B,
        (G.restrictEdges (OneCore.coreEdges C)).edge e = s(x,y) :=
    core_copy_crosses C hbip e.property
  constructor
  · simpa only [Fintype.card_coe] using
      degree_sum_eq_copies_of_crossing (G.restrictEdges (OneCore.coreEdges C)) A B hAB hcross
  · have hcross' (e : ↥(OneCore.coreEdges C)) :
        ∃ y ∈ B, ∃ x ∈ A,
          (G.restrictEdges (OneCore.coreEdges C)).edge e = s(y,x) := by
      obtain ⟨x,hx,y,hy,he⟩ := hcross e
      exact ⟨y,hy,x,hx,he.trans Sym2.eq_swap⟩
    simpa only [Fintype.card_coe] using
      degree_sum_eq_copies_of_crossing
        (G.restrictEdges (OneCore.coreEdges C)) B A hAB.symm hcross'

omit [Fintype V] in
/-- No core copy is incident with an exterior vertex, so all of that
vertex's original degree remains in the exterior graph. -/
theorem exterior_degree_outside (C : Core G U) (v : V) (hv : v ∉ U) :
    (exterior C).degree v = G.degree v := by
  have hzero : (G.restrictEdges (OneCore.coreEdges C)).degree v = 0 := by
    rw [Multigraph.restrictEdges_degree]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    have h := Finset.mem_inter.mp he
    exact hv (OneCore.coreEdges_endpoint C h.1
      ((G.mem_incidenceEdges v e).mp h.2))
  have hsum := OneCore.complement_degree_add G (OneCore.coreEdges C) v
  simpa only [hzero, add_zero] using hsum

omit [Fintype V] in
/-- Regularity and the actual core degree lower bound give the exterior
degree bound at every core vertex. -/
theorem exterior_degree_le_error (C : Core G U) (k : ℕ) (a : ℝ)
    (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ)) :
    ∀ v ∈ U, ((exterior C).degree v : ℝ) ≤ a := by
  intro v hv
  exact OneCore.complement_degree_le_error C k a hregular hdegree ⟨v,hv⟩

omit [Fintype V] in
/-- Equal side orders and equal core-copy counts force equal sums of
the actual exterior degrees. -/
theorem exterior_side_degree_sums (C : Core G (A ∪ B)) (k : ℕ)
    (hAB : Disjoint A B) (hcard : A.card = B.card)
    (hbip : C.graph.IsBipartiteWith {v | v.val ∈ A} {v | v.val ∈ B})
    (hregular : ∀ v, G.degree v = k) :
    (∑ v ∈ A, (exterior C).degree v) = ∑ v ∈ B, (exterior C).degree v := by
  have hadd (S : Finset V) :
      (∑ v ∈ S, (exterior C).degree v) +
        (∑ v ∈ S, (G.restrictEdges (OneCore.coreEdges C)).degree v) = S.card * k := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ v ∈ S, G.degree v := Finset.sum_congr rfl (fun v _ =>
        OneCore.complement_degree_add G (OneCore.coreEdges C) v)
      _ = _ := by simp only [hregular, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
  obtain ⟨hleft,hright⟩ := core_side_degree_sums C hAB hbip
  have hA := hadd A
  have hB := hadd B
  rw [hleft] at hA
  rw [hright, ← hcard] at hB
  omega

/-- The exterior order is even because the two core sides have the same
order and the original host has even order. -/
theorem exceptional_even (A B : Finset V)
    (hAB : Disjoint A B) (hcard : A.card = B.card)
    (heven : Even (Fintype.card V)) : Even (A ∪ B)ᶜ.card := by
  have hcore := Finset.card_union_of_disjoint hAB
  have htotal := Finset.card_add_card_compl (A ∪ B)
  rw [Nat.even_iff] at heven ⊢
  omega

/-- Construct all exterior-color data from regularity, an actual embedded
balanced bipartite core, its degree lower bound, and a coloring of its
actual complement. The balance and incidence conclusions are derived.
The coloring may relabel and interchange the supplied exterior classes. -/
theorem exists_balanced_exterior (C : Core G (A ∪ B)) (k : ℕ) (a : ℝ)
    (hk : 0 < k) (hAB : Disjoint A B) (hcard : A.card = B.card)
    (hbip : C.graph.IsBipartiteWith {v | v.val ∈ A} {v | v.val ∈ B})
    (heven : Even (Fintype.card V)) (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ))
    (hcolor : Nonempty ((exterior C).EdgeColoring k)) :
    ∃ c : (exterior C).EdgeColoring k,
      (∀ v ∈ (A ∪ B)ᶜ, (exterior C).degree v = k) ∧
      ((∑ v ∈ A, (exterior C).degree v) = ∑ v ∈ B, (exterior C).degree v) ∧
      (∀ i, (A ∪ B)ᶜ ⊆ c.coveredVertices i) ∧
      (∀ i, (A ∩ c.coveredVertices i).card = (B ∩ c.coveredVertices i).card) ∧
      (∀ i j, |((A ∩ c.coveredVertices i).card : ℤ) -
        (A ∩ c.coveredVertices j).card| ≤ 2) ∧
      (∀ i, ((c.exteriorFootprint (A ∪ B) i).card : ℝ) ≤ 2 * A.card * a / k + 4) ∧
      (∀ i, Even (c.exteriorFootprint (A ∪ B) i).card) ∧
      (∀ v ∈ A ∪ B,
        (univ.filter (fun i => v ∈ c.exteriorFootprint (A ∪ B) i)).card =
          (exterior C).degree v) ∧
      (∀ v ∈ A ∪ B,
        ((univ.filter (fun i => v ∈ c.exteriorFootprint (A ∪ B) i)).card : ℝ) ≤ a) := by
  have hZ (v : V) (hv : v ∈ (A ∪ B)ᶜ) : (exterior C).degree v = k := by
    rw [exterior_degree_outside C v (Finset.mem_compl.mp hv), hregular]
  have hsum := exterior_side_degree_sums C k hAB hcard hbip hregular
  have hZeven := exceptional_even A B hAB hcard heven
  have herror := exterior_degree_le_error C k a hregular hdegree
  obtain ⟨c,hsaturated,hbalanced,hspread,_hload,_hbound,hbound⟩ :=
    (exterior C).balanced_edgeColoring k hk A B (A ∪ B)ᶜ hAB
      disjoint_compl_right (Finset.union_compl _) hcard hZeven hZ hsum hcolor
  refine ⟨c,hZ,hsum,hsaturated,hbalanced,hspread,?_,?_,?_,?_⟩
  · exact hbound a herror
  · exact c.exteriorFootprint_even (A ∪ B) hZ hZeven
  · intro v hv
    exact c.exteriorFootprint_incidence (A ∪ B) v hv
  · intro v hv
    rw [c.exteriorFootprint_incidence (A ∪ B) v hv]
    exact herror v hv

end Overfull.BipartiteFactorization
