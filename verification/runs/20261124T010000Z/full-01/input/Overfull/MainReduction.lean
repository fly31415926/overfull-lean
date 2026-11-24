import Overfull.Basic
import Overfull.Specifications
import Overfull.Relabeling
import Overfull.Arithmetic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Verified steps in the reduction to a critical counterexample

This file proves the monotonicity and minimal-counterexample steps using actual
finite simple graphs and the project's edge-coloring definition. It does not
assert the robust-partition theorem, the structural coloring theorems, Vizing's
theorem, or the manuscript's main asymptotic theorem.

Minimality first concerns proper edge subgraphs on the same vertex type.
We then delete isolated vertices, preserve all relevant properties, and relabel
the support by `Fin m`. The final theorem is explicitly conditional on Vizing's
bound and exclusion of the large critical case.
-/

namespace Overfull

variable {V : Type*} {G H : SimpleGraph V} {k l : ℕ}

/-- Restrict a proper edge coloring to an actual edge subgraph. -/
def EdgeColoring.restrict (c : EdgeColoring G k) (hHG : H ≤ G) : EdgeColoring H k where
  color e := c.color ⟨e.val, SimpleGraph.edgeSet_mono hHG e.property⟩
  proper := by
    intro e f v he hf hcolor
    have hef : (⟨e.val, SimpleGraph.edgeSet_mono hHG e.property⟩ : G.edgeSet) =
        ⟨f.val, SimpleGraph.edgeSet_mono hHG f.property⟩ := c.proper he hf hcolor
    exact Subtype.ext (congrArg (fun a : G.edgeSet => a.val) hef)

/-- Extra available colors do not invalidate an existing proper coloring. -/
def EdgeColoring.enlarge (c : EdgeColoring G k) (hkl : k ≤ l) : EdgeColoring G l where
  color e := Fin.castLE hkl (c.color e)
  proper := by
    intro e f v he hf hcolor
    apply c.proper he hf
    apply Fin.ext
    exact congrArg (fun a : Fin l => a.val) hcolor

/-- The graph with no edges has a proper coloring for every palette size. -/
def emptyEdgeColoring (V : Type*) (k : ℕ) : EdgeColoring (⊥ : SimpleGraph V) k where
  color e := False.elim (by simpa using e.property)
  proper := by
    intro e f v he hf hcolor
    exact False.elim (by simpa using e.property)

/-- Restore one deleted edge using a single fresh color. This does not use
Vizing's theorem. -/
noncomputable def EdgeColoring.restoreEdge (e₀ : G.edgeSet)
    (c : EdgeColoring (G.deleteEdges {e₀.val}) k) : EdgeColoring G (k + 1) := by
  classical
  let oldEdge (e : G.edgeSet) (h : e.val ≠ e₀.val) :
      (G.deleteEdges {e₀.val}).edgeSet :=
    ⟨e.val, by simpa only [SimpleGraph.edgeSet_deleteEdges, Set.mem_diff,
      Set.mem_singleton_iff] using And.intro e.property h⟩
  refine ⟨fun e => if h : e.val = e₀.val then Fin.last k
    else (c.color (oldEdge e h)).castSucc, ?_⟩
  intro e f v he hf hcolor
  by_cases he₀ : e.val = e₀.val <;> by_cases hf₀ : f.val = e₀.val
  · exact Subtype.ext (he₀.trans hf₀.symm)
  · simp only [dif_pos he₀, dif_neg hf₀] at hcolor
    exact False.elim ((Fin.castSucc_ne_last _ ) hcolor.symm)
  · simp only [dif_neg he₀, dif_pos hf₀] at hcolor
    exact False.elim ((Fin.castSucc_ne_last _ ) hcolor)
  · simp only [dif_neg he₀, dif_neg hf₀, Fin.castSucc_inj] at hcolor
    have hef := c.proper (e := oldEdge e he₀) (f := oldEdge f hf₀) he hf hcolor
    exact Subtype.ext (congrArg (fun a : (G.deleteEdges {e₀.val}).edgeSet => a.val) hef)

/-- Deleting an edge that is present gives a proper spanning subgraph. -/
theorem deleteEdge_lt (e : G.edgeSet) : G.deleteEdges {e.val} < G := by
  apply lt_of_le_of_ne (G.deleteEdges_le {e.val})
  intro heq
  have h := SimpleGraph.edgeSet_mono heq.ge e.property
  simp [SimpleGraph.edgeSet_deleteEdges] at h

section VertexMaps

variable {W : Type*} {K : SimpleGraph W}

/-- Restrict a coloring along an actual embedding of simple graphs. -/
def EdgeColoring.pullbackEmbedding (c : EdgeColoring K k) (f : G ↪g K) :
    EdgeColoring G k where
  color e := c.color (f.mapEdgeSet e)
  proper := by
    intro e d v he hd hcolor
    apply f.mapEdgeSet.injective
    apply c.proper (v := f v) _ _ hcolor
    · change f v ∈ Sym2.map f e.val
      exact Sym2.mem_map.mpr ⟨v, he, rfl⟩
    · change f v ∈ Sym2.map f d.val
      exact Sym2.mem_map.mpr ⟨v, hd, rfl⟩

/-- Adding isolated vertices through an injective vertex map creates no new
edges: the induced map on actual edge subtypes is a bijection. -/
noncomputable def edgeMapEquiv (G : SimpleGraph V) (f : V ↪ W) :
    G.edgeSet ≃ (G.map f).edgeSet :=
  Equiv.ofBijective (SimpleGraph.Embedding.map f G).mapEdgeSet
    ⟨(SimpleGraph.Embedding.map f G).mapEdgeSet.injective, by
      intro e
      have he : e.val ∈ f.sym2Map '' G.edgeSet := by
        simpa only [SimpleGraph.edgeSet_map] using e.property
      obtain ⟨d, hd, hde⟩ := he
      exact ⟨⟨d, hd⟩, Subtype.ext hde⟩⟩

/-- Extend a coloring across an injective vertex map; vertices outside the
image are isolated in the mapped graph. -/
noncomputable def EdgeColoring.pushforward (c : EdgeColoring G k) (f : V ↪ W) :
    EdgeColoring (G.map f) k := by
  let E := edgeMapEquiv G f
  refine ⟨fun e => c.color (E.symm e), ?_⟩
  intro e d w he hd hcolor
  have heq : Sym2.map f (E.symm e).val = e.val :=
    congrArg (fun a : (G.map f).edgeSet => a.val) (E.apply_symm_apply e)
  have hdq : Sym2.map f (E.symm d).val = d.val :=
    congrArg (fun a : (G.map f).edgeSet => a.val) (E.apply_symm_apply d)
  rw [← heq] at he
  rw [← hdq] at hd
  obtain ⟨v, hv, hfv⟩ := Sym2.mem_map.mp he
  obtain ⟨u, hu, hfu⟩ := Sym2.mem_map.mp hd
  have hvu : v = u := f.injective (hfv.trans hfu.symm)
  subst u
  exact E.symm.injective (c.proper hv hu hcolor)

/-- A coloring restricts to every induced subgraph. -/
def EdgeColoring.induce (c : EdgeColoring G k) (s : Set V) :
    EdgeColoring (G.induce s) k :=
  c.pullbackEmbedding (SimpleGraph.Embedding.induce s)

/-- Removing all isolated vertices and then putting them back recovers the
graph, including its actual edge set. -/
theorem support_spanningCoe (G : SimpleGraph V) :
    (G.induce G.support).spanningCoe = G := by
  apply le_antisymm (G.spanningCoe_induce_le G.support)
  intro v w hvw
  exact ⟨⟨v, ⟨w, hvw⟩⟩, ⟨w, ⟨v, hvw.symm⟩⟩, hvw, rfl, rfl⟩

/-- Extend a coloring of the support by restoring isolated vertices. -/
noncomputable def EdgeColoring.extend_support
    (c : EdgeColoring (G.induce G.support) k) : EdgeColoring G k := by
  have d := c.pushforward (Function.Embedding.subtype G.support)
  change EdgeColoring (G.induce G.support).spanningCoe k at d
  simpa only [support_spanningCoe] using d

/-- Deleting isolated vertices preserves edge colorability. -/
theorem support_edgeColorable_iff :
    Nonempty (EdgeColoring (G.induce G.support) k) ↔ Nonempty (EdgeColoring G k) :=
  ⟨fun ⟨c⟩ => ⟨c.extend_support⟩, fun ⟨c⟩ => ⟨c.induce G.support⟩⟩

/-- Every vertex remaining in the support has a neighbor there. -/
theorem support_has_no_isolated_vertices (G : SimpleGraph V) :
    ∀ v : G.support, ∃ w : G.support, (G.induce G.support).Adj v w := by
  intro v
  obtain ⟨w, hvw⟩ := v.property
  exact ⟨⟨w, ⟨v.val, hvw.symm⟩⟩, hvw⟩

end VertexMaps

variable [Fintype V]

/-- Passing to an edge subgraph cannot increase the number of internal edges. -/
theorem internalEdges_card_mono (hHG : H ≤ G) (X : Finset V) :
    (internalEdges H X).card ≤ (internalEdges G X).card := by
  classical
  let f : H.edgeSet → G.edgeSet := fun e =>
    ⟨e.val, SimpleGraph.edgeSet_mono hHG e.property⟩
  apply Finset.card_le_card_of_injOn f
  · intro e he
    change f e ∈ internalEdges G X
    change e ∈ internalEdges H X at he
    simpa only [internalEdges, Finset.mem_filter, Finset.mem_univ, true_and] using he
  · intro e he e' he' heq
    exact Subtype.ext (congrArg (fun a : G.edgeSet => a.val) heq)

/-- An overfull vertex set in an edge subgraph is overfull in the host graph
for the same specified degree parameter. -/
theorem overfull_mono (hHG : H ≤ G) (X : Finset V) :
    IsOverfull H k X → IsOverfull G k X := by
  intro h
  exact lt_of_lt_of_le h (internalEdges_card_mono hHG X)

/-- Absence of overfull sets is inherited by edge subgraphs at the same parameter. -/
theorem no_overfull_of_le (hHG : H ≤ G)
    (hG : ∀ X : Finset V, ¬ IsOverfull G k X) :
    ∀ X : Finset V, ¬ IsOverfull H k X := by
  intro X hX
  exact hG X (overfull_mono hHG X hX)

/-- Internal edge counts do not increase when a graph is embedded in another
graph and the vertex set is sent along the same embedding. -/
theorem embedding_internalEdges_card_le {W : Type*} [Fintype W]
    {K : SimpleGraph W} (f : G ↪g K) (X : Finset V) :
    (internalEdges G X).card ≤ (internalEdges K (X.map f.toEmbedding)).card := by
  classical
  apply Finset.card_le_card_of_injOn f.mapEdgeSet
  · intro e he
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hX := (Finset.mem_filter.mp he).2
    intro w hw
    have hw' : w ∈ Sym2.map f e.val := Sym2.mem_toFinset.mp hw
    obtain ⟨v, hv, rfl⟩ := Sym2.mem_map.mp hw'
    exact Finset.mem_map.mpr ⟨v, hX (Sym2.mem_toFinset.mpr hv), rfl⟩
  · intro e he d hd hed
    exact f.mapEdgeSet.injective hed

/-- Absence of overfull sets is inherited under a graph embedding. -/
theorem no_overfull_of_embedding {W : Type*} [Fintype W]
    {K : SimpleGraph W} (f : G ↪g K)
    (hK : ∀ Y : Finset W, ¬ IsOverfull K k Y) :
    ∀ X : Finset V, ¬ IsOverfull G k X := by
  intro X hX
  apply hK (X.map f.toEmbedding)
  unfold IsOverfull at hX ⊢
  simpa only [Finset.card_map] using
    lt_of_lt_of_le hX (embedding_internalEdges_card_le f X)

open Classical in
/-- Removing isolated vertices preserves the maximum degree, including for
the graph with no edges. -/
theorem maxDegree_induce_support : (G.induce G.support).maxDegree = G.maxDegree := by
  apply Nat.le_antisymm
  · apply (G.induce G.support).maxDegree_le_of_forall_degree_le
    intro v
    rw [G.degree_induce_support v]
    exact G.degree_le_maxDegree v.val
  · apply G.maxDegree_le_of_forall_degree_le
    intro v
    by_cases hv : v ∈ G.support
    · calc
        G.degree v = (G.induce G.support).degree ⟨v, hv⟩ :=
          (G.degree_induce_support ⟨v, hv⟩).symm
        _ ≤ (G.induce G.support).maxDegree :=
          (G.induce G.support).degree_le_maxDegree ⟨v, hv⟩
    · rw [(G.degree_eq_zero_iff_notMem_support v).mpr hv]
      exact Nat.zero_le _

/-- Maximum degree is monotone under passage to an edge subgraph. -/
theorem maxDegree_le_of_le [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hHG : H ≤ G) : H.maxDegree ≤ G.maxDegree := by
  apply H.maxDegree_le_of_forall_degree_le
  intro v
  exact (H.degree_le_of_le hHG).trans (G.degree_le_maxDegree v)

/-- Edge-minimal failure of a specified coloring bound, on a fixed vertex type. -/
def IsEdgeMinimalNoncolorable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ¬ Nonempty (EdgeColoring G k) ∧
    ∀ H : SimpleGraph V, H < G → Nonempty (EdgeColoring H k)

/-- Every finite graph that fails a coloring bound contains an edge-minimal
subgraph failing that same bound. The proof minimizes the actual edge count. -/
theorem exists_edgeMinimal_noncolorable (hG : ¬ Nonempty (EdgeColoring G k)) :
    ∃ H : SimpleGraph V, H ≤ G ∧ IsEdgeMinimalNoncolorable H k := by
  classical
  let P : ℕ → Prop := fun n => ∃ H : SimpleGraph V,
    H ≤ G ∧ ¬ Nonempty (EdgeColoring H k) ∧ H.edgeFinset.card = n
  have hP : ∃ n, P n := ⟨G.edgeFinset.card, G, le_rfl, hG, rfl⟩
  obtain ⟨H, hHG, hH, hcard⟩ := Nat.find_spec hP
  refine ⟨H, hHG, hH, ?_⟩
  intro K hKH
  by_contra hK
  have hmin : Nat.find hP ≤ K.edgeFinset.card :=
    Nat.find_min' hP ⟨K, hKH.le.trans hHG, hK, rfl⟩
  have hlt : K.edgeFinset.card < H.edgeFinset.card :=
    Finset.card_lt_card (SimpleGraph.edgeFinset_strict_mono hKH)
  omega

omit [Fintype V] in
/-- Such a minimal counterexample has an edge. -/
theorem IsEdgeMinimalNoncolorable.ne_bot (hG : IsEdgeMinimalNoncolorable G k) : G ≠ ⊥ := by
  intro h
  subst G
  exact hG.1 ⟨emptyEdgeColoring V k⟩

omit [Fintype V] in
/-- Every edge deletion of an edge-minimal counterexample admits the old palette. -/
theorem IsEdgeMinimalNoncolorable.colorable_deleteEdge
    (hG : IsEdgeMinimalNoncolorable G k) (e : G.edgeSet) :
    Nonempty (EdgeColoring (G.deleteEdges {e.val}) k) :=
  hG.2 _ (deleteEdge_lt e)

omit [Fintype V] in
/-- An edge-minimal counterexample to `k` colors has a `(k+1)`-edge-coloring.
This conclusion follows directly by giving one restored edge a fresh color. -/
theorem IsEdgeMinimalNoncolorable.colorable_succ
    (hG : IsEdgeMinimalNoncolorable G k) : Nonempty (EdgeColoring G (k + 1)) := by
  obtain ⟨e, he⟩ := SimpleGraph.edgeSet_nonempty.mpr hG.ne_bot
  obtain ⟨c⟩ := hG.colorable_deleteEdge ⟨e, he⟩
  exact ⟨c.restoreEdge ⟨e, he⟩⟩

omit [Fintype V] in
/-- Removing isolated vertices preserves the genuine edge-minimality property. -/
theorem IsEdgeMinimalNoncolorable.induce_support
    (hG : IsEdgeMinimalNoncolorable G k) :
    IsEdgeMinimalNoncolorable (G.induce G.support) k := by
  refine ⟨fun h => hG.1 (support_edgeColorable_iff.mp h), ?_⟩
  intro K hKG
  have hsp : K.spanningCoe < G := by
    apply lt_of_le_of_ne
      ((SimpleGraph.map_monotone (Function.Embedding.subtype G.support) hKG.le).trans
        (G.spanningCoe_induce_le G.support))
    intro heq
    have hi := congrArg (fun R : SimpleGraph V => R.induce G.support) heq
    have hsame : K = G.induce G.support :=
      (@SimpleGraph.induce_spanningCoe V G.support K).symm.trans hi
    exact hKG.ne hsame
  obtain ⟨c⟩ := hG.2 _ hsp
  have d := c.induce G.support
  exact ⟨by simpa only [SimpleGraph.induce_spanningCoe] using d⟩

omit [Fintype V] in
/-- Edge-minimal failure of a palette size is invariant under a graph
isomorphism. -/
theorem IsEdgeMinimalNoncolorable.of_iso {W : Type*} {K : SimpleGraph W}
    (hG : IsEdgeMinimalNoncolorable G k) (f : G ≃g K) :
    IsEdgeMinimalNoncolorable K k := by
  refine ⟨fun h => hG.1 ((iso_edgeColorable_iff f k).mpr h), ?_⟩
  intro R hRK
  let L := R.comap f.toEquiv.toEmbedding
  have hLG : L < G := by
    apply lt_of_le_of_ne
    · intro v w hvw
      exact f.map_adj_iff.mp (hRK.le hvw)
    · intro heq
      apply hRK.ne
      ext x y
      obtain ⟨v, rfl⟩ := f.surjective x
      obtain ⟨w, rfl⟩ := f.surjective y
      change L.Adj v w ↔ K.Adj (f v) (f w)
      rw [heq]
      exact f.map_adj_iff.symm
  exact (iso_edgeColorable_iff (SimpleGraph.Iso.comap f.toEquiv R) k).mp (hG.2 L hLG)

omit [Fintype V] in
/-- The property of having no isolated vertices is invariant under graph
isomorphism. -/
theorem no_isolated_vertices_of_iso {W : Type*} {K : SimpleGraph W}
    (f : G ≃g K) (hG : ∀ v : V, ∃ w : V, G.Adj v w) :
    ∀ v : W, ∃ w : W, K.Adj v w := by
  intro v
  obtain ⟨w, hw⟩ := hG (f.symm v)
  refine ⟨f w, ?_⟩
  simpa only [RelIso.apply_symm_apply] using f.map_adj_iff.mpr hw

open Classical in
/-- The extracted graph retains the degree upper bound and absence of overfull
sets at the original degree parameter. No assertion of degree equality is made. -/
theorem exists_edgeMinimal_no_overfull (hG : ¬ Nonempty (EdgeColoring G k))
    (hno : ∀ X : Finset V, ¬ IsOverfull G k X) :
    ∃ H : SimpleGraph V, H ≤ G ∧ IsEdgeMinimalNoncolorable H k ∧
      H.maxDegree ≤ G.maxDegree ∧ (∀ X : Finset V, ¬ IsOverfull H k X) ∧
      Nonempty (EdgeColoring H (k + 1)) := by
  obtain ⟨H, hHG, hH⟩ := exists_edgeMinimal_noncolorable hG
  exact ⟨H, hHG, hH, maxDegree_le_of_le hHG, no_overfull_of_le hHG hno,
    hH.colorable_succ⟩

open Classical in
/-- If Vizing's upper bound is supplied explicitly for the host's subgraphs,
then failure at the host's maximum degree forces that maximum degree to be
preserved in the extracted counterexample. The Vizing bound is an explicit
input to this implication; its proof is supplied in `Overfull.Vizing.Theorem`. -/
theorem exists_edgeMinimal_same_maxDegree_of_vizing
    (hG : ¬ Nonempty (EdgeColoring G G.maxDegree))
    (hno : ∀ X : Finset V, ¬ IsOverfull G G.maxDegree X)
    (hVizing : ∀ H : SimpleGraph V, H ≤ G →
      Nonempty (EdgeColoring H (H.maxDegree + 1))) :
    ∃ H : SimpleGraph V, H ≤ G ∧ IsEdgeMinimalNoncolorable H G.maxDegree ∧
      H.maxDegree = G.maxDegree ∧
      (∀ X : Finset V, ¬ IsOverfull H G.maxDegree X) ∧
      Nonempty (EdgeColoring H (G.maxDegree + 1)) := by
  obtain ⟨H, hHG, hH, hdeg, hnoH, hupper⟩ := exists_edgeMinimal_no_overfull hG hno
  have heq : H.maxDegree = G.maxDegree := by
    by_contra hne
    have hlt : H.maxDegree < G.maxDegree := lt_of_le_of_ne hdeg hne
    obtain ⟨c⟩ := hVizing H hHG
    exact hH.1 ⟨c.enlarge (Nat.succ_le_of_lt hlt)⟩
  exact ⟨H, hHG, hH, heq, hnoH, hupper⟩

open Classical in
/-- Conditional on Vizing's bound for the original graph's spanning subgraphs,
a counterexample has an edge-critical representative on `Fin m`, with all
isolated vertices removed. Both order bounds, maximum-degree equality, and
inheritance of the no-overfull property are proved here. -/
theorem exists_critical_on_fin_of_vizing {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : ¬ Nonempty (EdgeColoring G G.maxDegree))
    (hno : ∀ X : Finset (Fin n), ¬ IsOverfull G G.maxDegree X)
    (hVizing : ∀ H : SimpleGraph (Fin n), H ≤ G →
      Nonempty (EdgeColoring H (H.maxDegree + 1))) :
    ∃ m : ℕ, m ≤ n ∧ ∃ H : SimpleGraph (Fin m),
      IsEdgeMinimalNoncolorable H G.maxDegree ∧ H.maxDegree = G.maxDegree ∧
      G.maxDegree + 1 ≤ m ∧
      (∀ v : Fin m, ∃ w : Fin m, H.Adj v w) ∧
      (∀ X : Finset (Fin m), ¬ IsOverfull H G.maxDegree X) ∧
      Nonempty (EdgeColoring H (G.maxDegree + 1)) := by
  obtain ⟨K, hKG, hK, hdeg, hnoK, hupper⟩ :=
    exists_edgeMinimal_same_maxDegree_of_vizing hG hno hVizing
  let S := K.support
  let R := K.induce S
  let m := Fintype.card S
  let H := R.overFin (n := m) rfl
  let f : R ≃g H := R.overFinIso rfl
  have hR : IsEdgeMinimalNoncolorable R G.maxDegree := hK.induce_support
  haveI : Nonempty S := by
    by_contra hS
    haveI : IsEmpty S := not_nonempty_iff.mp hS
    exact hR.ne_bot (Subsingleton.elim _ _)
  have hm : m ≤ n := by
    simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun v => v ∈ K.support)
  have hRdeg : R.maxDegree = G.maxDegree := maxDegree_induce_support.trans hdeg
  have hHdeg : H.maxDegree = G.maxDegree := (iso_maxDegree_eq f).symm.trans hRdeg
  have horder : G.maxDegree + 1 ≤ m := by
    have hlt := R.maxDegree_lt_card_verts
    rw [hRdeg] at hlt
    exact Nat.succ_le_of_lt hlt
  have hnoR : ∀ X : Finset S, ¬ IsOverfull R G.maxDegree X :=
    no_overfull_of_embedding (SimpleGraph.Embedding.induce S) hnoK
  refine ⟨m, hm, H, hR.of_iso f, hHdeg, horder, ?_, ?_, ?_⟩
  · exact no_isolated_vertices_of_iso f (support_has_no_isolated_vertices K)
  · exact (iso_no_overfull_iff f G.maxDegree).mp hnoR
  · exact (iso_edgeColorable_iff f (G.maxDegree + 1)).mp hR.colorable_succ

open Classical in
/-- The Vizing input needed by the final reduction, stated for actual finite
simple graphs and the project's proper edge-coloring definition. This definition
names a proposition; it does not prove it. -/
noncomputable def FiniteVizingBound : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    Nonempty (EdgeColoring G (G.maxDegree + 1))

open Classical in
/-- The structural input needed after the reduction to a critical graph.
For each positive density margin at most `1/12`, sufficiently large edge-minimal
counterexamples with no isolated vertices and no overfull set must be excluded.
The manuscript's common robust partition and five exclusion arguments must
establish this proposition. It is not proved in this file. -/
noncomputable def LargeCriticalExclusion : Prop :=
  ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 12 → ∃ n₁ : ℕ,
    ∀ m : ℕ, n₁ ≤ m → ∀ G : SimpleGraph (Fin m),
      IsEdgeMinimalNoncolorable G G.maxDegree →
      (∀ v : Fin m, ∃ w : Fin m, G.Adj v w) →
      (1 / 4 + θ) * (m : ℝ) ≤ (G.maxDegree : ℝ) →
      (∀ X : Finset (Fin m), ¬ IsOverfull G G.maxDegree X) → False

/-- The final manuscript reduction, with its two inputs stated
explicitly. This is a conditional implication and is not a verification of
`MainTheorem`: the structural exclusion still has to be proved. -/
theorem mainTheorem_of_vizing_and_criticalExclusion
    (hVizing : FiniteVizingBound) (hExclusion : LargeCriticalExclusion) : MainTheorem := by
  classical
  intro ε hε
  let θ : ℝ := min ε (1 / 12)
  have hθpos : 0 < θ := lt_min hε (by norm_num)
  have hθbound : θ ≤ 1 / 12 := min_le_right _ _
  have hθε : θ ≤ ε := min_le_left _ _
  obtain ⟨n₁, hexclude⟩ := hExclusion θ hθpos hθbound
  refine ⟨4 * n₁, ?_⟩
  intro n hn G hdensity
  constructor
  · rintro ⟨c⟩
    exact c.not_overfull
  · intro hno
    by_contra hG
    obtain ⟨m, hmn, H, hH, hdegree, horder, hnoisolates, hnoH, _⟩ :=
      exists_critical_on_fin_of_vizing hG hno (fun K _ => hVizing n K)
    have hquarter : n ≤ 4 * G.maxDegree := by
      have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hepsn : 0 ≤ ε * (n : ℝ) := mul_nonneg hε.le hnnonneg
      have hreal : (n : ℝ) ≤ 4 * (G.maxDegree : ℝ) := by nlinarith
      exact_mod_cast hreal
    have hlarge : n₁ ≤ m :=
      Arithmetic.critical_subgraph_order_threshold n n₁ m G.maxDegree hn hquarter horder
    have hHdens : (1 / 4 + θ) * (m : ℝ) ≤ (H.maxDegree : ℝ) := by
      rw [hdegree]
      calc
        (1 / 4 + θ) * (m : ℝ) ≤ (1 / 4 + θ) * (n : ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hmn) (by linarith)
        _ ≤ (1 / 4 + ε) * (n : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)
        _ ≤ (G.maxDegree : ℝ) := hdensity
    exact hexclude m hlarge H (by simpa only [hdegree] using hH) hnoisolates hHdens
      (by simpa only [hdegree] using hnoH)

end Overfull
