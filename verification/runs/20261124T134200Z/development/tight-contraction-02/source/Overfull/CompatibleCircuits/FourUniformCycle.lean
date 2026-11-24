import Overfull.CompatibleCircuits.FourAdmissibleTransfer
import Overfull.CompatibleCircuits.FourTriangleSelection

/-!
# Uniform bundles around a simple circuit

Equal-size bundles can be matched by finite bijections to partition every
actual copy into a simple circuit. Different template edges meeting at a
vertex must have different incidence classes. Parallel copies are never
identified, and there is no bound on their number.

The four-cycle specialization is intended for the final support case in
the four-label compatible-circuit argument.
-/

namespace Overfull.Multigraph

open Finset Classical

variable {V E I K : Type*} [Fintype I]

/-- A uniformly repeated simple circuit has an exact compatible partition.
The index bijections are constructed from the actual bundle cardinalities. -/
theorem exists_compatibleCircuitPartition_of_uniform_simple_template
    (T : Multigraph V I) (G : Multigraph V E)
    (htemplate : T.IsCircuit univ) (hinjective : Function.Injective T.edge)
    (classOf : V → E → K) (C : Finset E) (m : ℕ)
    (hcover : ∀ e ∈ C, ∃ i, G.edge e = T.edge i)
    (hcard : ∀ i, (C.filter (fun e => G.edge e = T.edge i)).card = m)
    (hclasses : ∀ v i j, i ≠ j → v ∈ T.edge i → v ∈ T.edge j →
      ∀ e ∈ C, G.edge e = T.edge i →
      ∀ f ∈ C, G.edge f = T.edge j → classOf v e ≠ classOf v f) :
    Nonempty (G.CompatibleCircuitPartition classOf C) := by
  let B (i : I) := C.filter (fun e => G.edge e = T.edge i)
  let φ (i : I) : Fin m ≃ B i := (Finset.equivFinOfCardEq (hcard i)).symm
  let choose (i : I) (j : Fin m) : E := (φ i j).val
  have hchoose (i : I) (j : Fin m) :
      choose i j ∈ C ∧ G.edge (choose i j) = T.edge i :=
    mem_filter.mp (φ i j).property
  have hglobal {i i' : I} {j j' : Fin m} (h : choose i j = choose i' j') :
      i = i' ∧ j = j' := by
    have hi : i = i' := hinjective
      ((hchoose i j).2.symm.trans ((congrArg G.edge h).trans (hchoose i' j').2))
    subst i'
    exact ⟨rfl, (φ i).injective (Subtype.ext h)⟩
  let ψ (j : Fin m) : I ↪ E := ⟨fun i => choose i j, by
    intro i i' h
    exact (hglobal h).1⟩
  let part (j : Fin m) : Finset E := univ.map (ψ j)
  have hedge (j : Fin m) (i : I) : G.edge (ψ j i) = T.edge i := (hchoose i j).2
  have hcircuit (j : Fin m) : G.IsCircuit (part j) :=
    htemplate.map_copies T G (ψ j) (hedge j)
  have hcompatible (j : Fin m) : G.Compatible classOf (part j) := by
    intro v e he hve f hf hvf heq
    obtain ⟨i, _, rfl⟩ := mem_map.mp he
    obtain ⟨i', _, rfl⟩ := mem_map.mp hf
    by_cases hi : i = i'
    · exact congrArg (ψ j) hi
    · exact False.elim (hclasses v i i' hi
        (by simpa only [hedge] using hve) (by simpa only [hedge] using hvf)
        _ (hchoose i j).1 (hedge j i)
        _ (hchoose i' j).1 (hedge j i') heq)
  refine ⟨{
    parts := univ.image part
    circuit := ?_
    compatible := ?_
    disjoint := ?_
    cover := ?_ }⟩
  · intro D hD
    obtain ⟨j, _, rfl⟩ := mem_image.mp hD
    exact hcircuit j
  · intro D hD
    obtain ⟨j, _, rfl⟩ := mem_image.mp hD
    exact hcompatible j
  · intro D hD D' hD' hne
    obtain ⟨j, _, rfl⟩ := mem_image.mp hD
    obtain ⟨j', _, rfl⟩ := mem_image.mp hD'
    apply disjoint_left.mpr
    intro e he he'
    obtain ⟨i, _, hei⟩ := mem_map.mp he
    obtain ⟨i', _, hei'⟩ := mem_map.mp he'
    have hj : j = j' := (hglobal (hei.trans hei'.symm)).2
    exact hne (congrArg part hj)
  · ext e
    simp only [mem_biUnion, mem_image, mem_univ, true_and, id_eq]
    constructor
    · rintro ⟨D, ⟨j, rfl⟩, he⟩
      obtain ⟨i, _, rfl⟩ := mem_map.mp he
      exact (hchoose i j).1
    · intro he
      obtain ⟨i, hi⟩ := hcover e he
      let b : B i := ⟨e, mem_filter.mpr ⟨he, hi⟩⟩
      let j : Fin m := (φ i).symm b
      have hj : ψ j i = e := congrArg Subtype.val ((φ i).apply_symm_apply b)
      exact ⟨part j, ⟨j, rfl⟩, mem_map.mpr ⟨i, mem_univ i, hj⟩⟩

end Overfull.Multigraph

namespace Overfull.CompatibleCircuits.UniformCycle

open Finset Classical

/-- The four actual endpoint types of a labeled square. -/
def pairs : Fin 4 → Sym2 (Fin 4) :=
  ![s(0,1), s(1,2), s(2,3), s(3,0)]

theorem pairs_injective : Function.Injective pairs := by decide

theorem pairs_loopless : ∀ i, ¬ (pairs i).IsDiag := by decide

def graph : Multigraph (Fin 4) (Fin 4) where
  edge := pairs
  loopless := pairs_loopless

theorem graph_degree (v : Fin 4) : graph.degreeOn univ v = 2 := by
  have h : ∀ v : Fin 4, (univ.filter (fun i => v ∈ pairs i)).card = 2 := by decide
  have hdec : (fun a b : Fin 4 => propDecidable (a = b)) =
      (inferInstance : DecidableEq (Fin 4)) := Subsingleton.elim _ _
  simpa only [Multigraph.degreeOn, graph, hdec] using h v

theorem graph_isCircuit : graph.IsCircuit univ := by
  apply graph.isCircuit_of_even_injective_labels (by simp)
  · intro i _ j _ h
    exact pairs_injective ((graph.edgeLabelPair_eq_iff i j).mp h)
  · intro v
    rw [graph_degree]
    decide

end Overfull.CompatibleCircuits.UniformCycle

namespace Overfull.Multigraph

open Finset Classical CompatibleCircuits UniformCycle

variable {E K : Type*} (Q : Multigraph (Fin 4) E)

/-- Complete actual-copy decomposition for an arbitrary common square-bundle
multiplicity. The assumption compares all actual choices at each corner. -/
theorem exists_compatibleCircuitPartition_of_uniform_four_cycle
    (classOf : Fin 4 → E → K) (C : Finset E) (m : ℕ)
    (hcover : ∀ e ∈ C, ∃ i, Q.edge e = pairs i)
    (hcard : ∀ i, (C.filter (fun e => Q.edge e = pairs i)).card = m)
    (hclasses : ∀ v i j, i ≠ j → v ∈ pairs i → v ∈ pairs j →
      ∀ e ∈ C, Q.edge e = pairs i →
      ∀ f ∈ C, Q.edge f = pairs j → classOf v e ≠ classOf v f) :
    Nonempty (Q.CompatibleCircuitPartition classOf C) := by
  apply exists_compatibleCircuitPartition_of_uniform_simple_template graph Q
    graph_isCircuit pairs_injective classOf C m hcover
  · intro i
    simpa only [graph] using hcard i
  · exact hclasses

end Overfull.Multigraph
