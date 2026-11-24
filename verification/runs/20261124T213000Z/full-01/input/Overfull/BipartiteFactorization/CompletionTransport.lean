import Overfull.BipartiteFactorization.ComplementCompletion
import Overfull.BipartiteFactorization.ResidualPacking

/-!
# Transporting the actual bipartite packing to original host copies

The equivalence only indexes the already specified core by its two sides.
Footprints, matchings, and the whole unused graph are transported exactly.
In particular, no newly chosen simple edge can stand for a different parallel
copy of the ambient multigraph.
-/

noncomputable section

namespace Overfull.BipartiteFactorization

open Finset Classical SmallCuts SimpleGraph OrdinaryFactorization
open BipartitePackingAccounting

variable {V E A B : Type*} [Fintype V] [Fintype E] [Fintype A] [Fintype B]
variable {G : Multigraph V E} {U : Finset V} {q : ℕ}
variable (C : Core G U)
variable (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring q)
variable (e : A ⊕ B ≃ U)

/-- Original color footprints in the side-indexed core. -/
def sideFootprint (i : Fin q) : Finset (A ⊕ B) :=
  (selectedFootprint C c (Function.Embedding.refl _) i).map e.symm.toEmbedding

omit [Fintype A] [Fintype B] in
@[simp] theorem mem_sideFootprint (i : Fin q) (v : A ⊕ B) :
    v ∈ sideFootprint C c e i ↔ c.Covers i (e v).val := by
  simp only [sideFootprint, Finset.mem_map_equiv, Equiv.symm_symm,
    mem_selectedFootprint, Function.Embedding.refl_apply]

omit [Fintype A] [Fintype B] in
theorem sideFootprint_card (i : Fin q) :
    (sideFootprint C c e i).card = (c.exteriorFootprint U i).card := by
  rw [sideFootprint, Finset.card_map, selectedFootprint_card]
  rfl

omit [Fintype A] [Fintype B] in
theorem sideFootprint_load (v : A ⊕ B) :
    (univ.filter (fun i : Fin q => v ∈ sideFootprint C c e i)).card =
      (G.restrictEdges (OneCore.coreEdges C)ᶜ).degree (e v).val := by
  simp only [mem_sideFootprint]
  exact c.coveredColors_card (e v).val

omit [Fintype V] [Fintype E] [Fintype A] [Fintype B] in
/-- Mapping a matching through the core equivalence preserves each adjacency. -/
theorem mapped_subgraph_adj (N : (C.graph.comap e).Subgraph) (v w : A ⊕ B) :
    (N.map (SimpleGraph.Iso.comap e C.graph).toHom).Adj (e v) (e w) ↔ N.Adj v w := by
  constructor
  · rintro ⟨x, y, hxy, hx, hy⟩
    have hx' : x = v := e.injective hx
    have hy' : y = w := e.injective hy
    simpa only [hx', hy'] using hxy
  · intro hvw
    exact ⟨v, w, hvw, rfl, rfl⟩

/-- Lift the actual side-indexed matching family to the embedded core. -/
def BipartiteCorePacking.toComplementCompletion {θ σ : ℝ}
    (P : BipartiteCorePacking (C.graph.comap e) q (sideFootprint C c e) θ σ) :
    ComplementCompletion C c where
  matching i := (P.matching i).map (SimpleGraph.Iso.comap e C.graph).toHom
  isMatching i := (P.isMatching i).map _ e.injective
  verts i := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [P.verts] at hw
      intro hfoot
      apply hw
      exact (Finset.mem_map_equiv).mpr hfoot
    · intro hv
      refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
      rw [P.verts]
      intro hfoot
      apply hv
      have h := (Finset.mem_map_equiv).mp hfoot
      simpa only [Equiv.symm_symm, Equiv.apply_symm_apply] using h
  disjoint := by
    intro i j hij
    apply disjoint_iff_inf_le.mpr
    intro v w hvw
    have hi : (P.matching i).Adj (e.symm v) (e.symm w) := by
      apply (mapped_subgraph_adj C e (P.matching i) _ _).mp
      simpa only [Equiv.apply_symm_apply] using hvw.1
    have hj : (P.matching j).Adj (e.symm v) (e.symm w) := by
      apply (mapped_subgraph_adj C e (P.matching j) _ _).mp
      simpa only [Equiv.apply_symm_apply] using hvw.2
    exact (disjoint_iff_inf_le.mp (P.disjoint hij)) ⟨hi, hj⟩

/-- The unused graph is exactly the same graph in the two indexings. -/
theorem BipartiteCorePacking.remaining_comap {θ σ : ℝ}
    (P : BipartiteCorePacking (C.graph.comap e) q (sideFootprint C c e) θ σ) :
    (P.toComplementCompletion C c e).remainingGraph.comap e = P.remaining := by
  ext v w
  change (C.graph.Adj (e v) (e w) ∧
    ¬ ∃ i ∈ (univ : Finset (Fin q)),
      ((P.matching i).map (SimpleGraph.Iso.comap e C.graph).toHom).Adj (e v) (e w)) ↔
    (C.graph.Adj (e v) (e w) ∧
      ¬ ∃ i ∈ (univ : Finset (Fin q)), (P.matching i).Adj v w)
  simp only [mapped_subgraph_adj C e]

theorem BipartiteCorePacking.completion_robust {θ σ : ℝ}
    (P : BipartiteCorePacking (C.graph.comap e) q (sideFootprint C c e) θ σ) :
    IsBipartiteRobustExpander
      ((P.toComplementCompletion C c e).remainingGraph.comap e) θ σ := by
  convert P.robust using 1
  exact P.remaining_comap C c e

end Overfull.BipartiteFactorization
