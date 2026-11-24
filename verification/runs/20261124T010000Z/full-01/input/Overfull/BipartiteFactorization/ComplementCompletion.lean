import Overfull.OrdinaryFactorization.Residual
import Overfull.BoundaryExtension.Residual

/-!
# Completing every color of the remaining exterior

The host at the last packing stage is deliberately not regular: core vertices
have degree `q + 2*r`, while exterior vertices have degree `q`.  Completing its
`q` exterior colors therefore leaves an actual simple `2*r`-regular core and
isolated exterior vertices.  This file proves the original-copy accounting;
existence of the core matchings is supplied separately by robust packing.
-/

noncomputable section

namespace Overfull.BipartiteFactorization

open Finset Classical SmallCuts SimpleGraph
open BoundaryExtension OrdinaryFactorization BipartitePackingAccounting

variable {V E : Type*} [Fintype V] [Fintype E]
variable {G : Multigraph V E} {U : Finset V} {q : ℕ}

/-- Internal completions of all colors of the actual core complement. -/
structure ComplementCompletion (C : Core G U)
    (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring q) where
  matching : Fin q → C.graph.Subgraph
  isMatching : ∀ i, (matching i).IsMatching
  verts : ∀ i, (matching i).verts =
    (selectedFootprint C c (Function.Embedding.refl _) i : Set U)ᶜ
  disjoint : Pairwise (fun i j => Disjoint (matching i).spanningCoe (matching j).spanningCoe)

namespace ComplementCompletion

variable {C : Core G U}
variable {c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring q}
variable (D : ComplementCompletion C c)

/-- Completed colors consist of original exterior and embedded core copies. -/
def classes : Fin q → Finset E :=
  completedClass C c (Function.Embedding.refl _) D.matching

/-- The exact set of original edge copies used by the completed colors. -/
def used : Finset E := univ.biUnion D.classes

@[simp] theorem mem_used (e : E) : e ∈ D.used ↔ ∃ i, e ∈ D.classes i := by
  simp only [used, mem_biUnion, mem_univ, true_and]

theorem classes_isMatching (i : Fin q) : G.IsMatching (D.classes i) :=
  completedClass_isMatching C c (Function.Embedding.refl _) D.matching D.isMatching D.verts i

theorem classes_disjoint : Pairwise (fun i j => Disjoint (D.classes i) (D.classes j)) :=
  completedClass_pairwiseDisjoint C c (Function.Embedding.refl _) D.matching D.disjoint

/-- Only exterior regularity is needed for the completed classes to be perfect. -/
theorem classes_isPerfectMatching
    (houtside : ∀ v, v ∉ U → G.degree v = q) (i : Fin q) :
    G.IsPerfectMatching (D.classes i) := by
  apply G.isPerfectMatching_iff.mpr
  refine ⟨D.classes_isMatching i, ?_⟩
  intro v
  by_cases hv : v ∈ U
  · exact completedClass_covers_core C c (Function.Embedding.refl _) D.matching
      D.isMatching D.verts i ⟨v, hv⟩
  · have hdegree : (G.restrictEdges (OneCore.coreEdges C)ᶜ).degree v = q :=
      (complement_degree_outside C v hv).trans (houtside v hv)
    obtain ⟨e, he, hev⟩ := (selectedClass_covers C c (Function.Embedding.refl _) i v).mpr
      (c.covers_of_degree_eq v hdegree i)
    exact ⟨e, mem_union_left _ he, hev⟩

theorem used_degree (houtside : ∀ v, v ∉ U → G.degree v = q) (v : V) :
    (G.restrictEdges D.used).degree v = q := by
  have hsets : D.used ∩ G.incidenceEdges v =
      univ.biUnion (fun i => (D.classes i).filter (fun e => v ∈ G.edge e)) := by
    ext e
    simp only [mem_inter, mem_used, Multigraph.mem_incidenceEdges,
      mem_biUnion, mem_univ, true_and, mem_filter]
    aesop
  rw [Multigraph.restrictEdges_degree, hsets, Finset.card_biUnion]
  · have hone (i : Fin q) :
        ((D.classes i).filter (fun e => v ∈ G.edge e)).card = 1 :=
      D.classes_isPerfectMatching houtside i v
    simp only [hone, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  · intro i _ j _ hij
    exact (D.classes_disjoint hij).mono (filter_subset _ _) (filter_subset _ _)

/-- Every exterior copy retains its prescribed label. -/
theorem exterior_mem_class (e : ↥((OneCore.coreEdges C)ᶜ)) (i : Fin q) :
    e.val ∈ D.classes i ↔ c.color e = i :=
  completedClass_complement C c (Function.Embedding.refl _) D.matching i e

/-- In particular, no exterior copy survives the complete color packing. -/
theorem exterior_used (e : ↥((OneCore.coreEdges C)ᶜ)) : e.val ∈ D.used := by
  exact (D.mem_used e.val).mpr ⟨c.color e, (D.exterior_mem_class e _).mpr rfl⟩

/-- The unused ambient graph retains precisely the unused original copies. -/
def remainingAmbient : Multigraph V ↥(D.usedᶜ) := G.restrictEdges D.usedᶜ

theorem remaining_degree_add
    (houtside : ∀ v, v ∉ U → G.degree v = q) (v : V) :
    D.remainingAmbient.degree v + q = G.degree v := by
  have h := OneCore.complement_degree_add G D.used v
  rw [D.used_degree houtside] at h
  exact h

theorem remaining_degree_core (r : ℕ)
    (houtside : ∀ v, v ∉ U → G.degree v = q)
    (hcore : ∀ v : U, G.degree v.val = q + 2 * r) (v : U) :
    D.remainingAmbient.degree v.val = 2 * r := by
  have h := D.remaining_degree_add houtside v.val
  rw [hcore] at h
  omega

theorem remaining_degree_outside
    (houtside : ∀ v, v ∉ U → G.degree v = q) (v : V) (hv : v ∉ U) :
    D.remainingAmbient.degree v = 0 := by
  have h := D.remaining_degree_add houtside v
  rw [houtside v hv] at h
  omega

/-- The actual simple graph left in the embedded core. -/
def remainingGraph : SimpleGraph U :=
  C.graph \ edgeUnion (fun i => (D.matching i).spanningCoe) univ

theorem core_copy_used_iff (e : C.graph.edgeSet) :
    C.edgeMap e ∈ D.used ↔ ∃ i, e.val ∈ (D.matching i).edgeSet := by
  rw [mem_used]
  apply exists_congr
  intro i
  constructor
  · intro he
    rcases mem_union.mp he with he | he
    · exact (Finset.disjoint_left.mp
        (selectedClass_disjoint_coreEdges C c (Function.Embedding.refl _) i) he
        ((OneCore.mem_coreEdges C _).mpr ⟨e, rfl⟩)).elim
    · obtain ⟨f, hf, hfe⟩ := (mem_coreMatchingCopies C (D.matching i) _).mp he
      have hfe' : f = e := C.edgeMap.injective hfe
      subst f
      exact (mem_filter.mp hf).2
  · intro he
    exact mem_union_right _ ((mem_coreMatchingCopies C (D.matching i) _).mpr
      ⟨e, mem_filter.mpr ⟨mem_univ _, he⟩, rfl⟩)

theorem core_copy_survives_iff (e : C.graph.edgeSet) :
    C.edgeMap e ∉ D.used ↔ e.val ∈ D.remainingGraph.edgeSet := by
  rw [D.core_copy_used_iff]
  rcases e with ⟨⟨u, v⟩, he⟩
  change (¬ ∃ i, (D.matching i).Adj u v) ↔
    C.graph.Adj u v ∧ ¬ ∃ i ∈ (univ : Finset (Fin q)), (D.matching i).Adj u v
  simp only [mem_univ, true_and]
  exact (and_iff_right he).symm

/-- Embed every remaining simple edge by its surviving original copy. -/
def remainingCore : Core D.remainingAmbient U :=
  subcoreInRestriction C D.remainingGraph sdiff_le D.used
    (fun e => (D.core_copy_survives_iff
      ⟨e.val, SimpleGraph.edgeSet_mono sdiff_le e.property⟩).mpr e.property)

@[simp] theorem remainingCore_graph : D.remainingCore.graph = D.remainingGraph := rfl

/-- There are no hidden parallel, same-side, or exterior copies in the
remainder: all surviving copies belong to its embedded simple core. -/
theorem remainingCore_exhausts : OneCore.coreEdges D.remainingCore = univ := by
  apply Finset.eq_univ_of_forall
  intro e
  have hcore : e.val ∈ OneCore.coreEdges C := by
    by_contra hnot
    exact (mem_compl.mp e.property) (D.exterior_used ⟨e.val, mem_compl.mpr hnot⟩)
  obtain ⟨f, hf⟩ := (OneCore.mem_coreEdges C e.val).mp hcore
  have hsurvive : C.edgeMap f ∉ D.used := by
    rw [hf]
    exact mem_compl.mp e.property
  have hrem := (D.core_copy_survives_iff f).mp hsurvive
  apply (OneCore.mem_coreEdges D.remainingCore e).mpr
  refine ⟨⟨f.val, hrem⟩, ?_⟩
  apply Subtype.ext
  exact hf

theorem remainingCore_degree_eq (v : U) :
    D.remainingCore.graph.degree v = D.remainingAmbient.degree v.val := by
  have h := OneCore.core_degree D.remainingCore v
  rw [Multigraph.restrictEdges_degree] at h
  calc
    _ = _ := h.symm
    _ = D.remainingAmbient.degree v.val := by
      unfold Multigraph.degree
      congr 1
      ext e
      simp only [D.remainingCore_exhausts, mem_inter, mem_univ, true_and]

/-- Exact `2*r`-regularity of the actual residual simple graph. -/
theorem remainingGraph_regular (r : ℕ)
    (houtside : ∀ v, v ∉ U → G.degree v = q)
    (hcore : ∀ v : U, G.degree v.val = q + 2 * r) (v : U) :
    D.remainingGraph.degree v = 2 * r :=
  (D.remainingCore_degree_eq v).trans (D.remaining_degree_core r houtside hcore v)

theorem remainingGraph_bipartite (A B : Set U)
    (hbip : C.graph.IsBipartiteWith A B) : D.remainingGraph.IsBipartiteWith A B := by
  exact ⟨hbip.disjoint, fun _ _ h => hbip.mem_of_adj h.1⟩

end ComplementCompletion

end Overfull.BipartiteFactorization
