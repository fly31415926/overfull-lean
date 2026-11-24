import Overfull.BipartiteFactorization.CompletionTransport
import Overfull.BipartiteFactorization.Coloring

/-!
# Completing a selected part of the core complement

The selected copies may contain only some of the incidences at an exterior
vertex.  Completing their colors removes the same number of incidences at
every vertex.  A genuinely bipartite unselected host can then be colored by
König's theorem.  All constructions retain the original edge copies.
-/

noncomputable section

namespace Overfull.TwoApexFactorization

open Finset Classical SmallCuts SimpleGraph BoundaryExtension
open BipartiteFactorization

variable {V E : Type*} [Fintype V] [Fintype E]
variable {G : Multigraph V E} {U : Finset V} {q : ℕ}

def colorCopies {F : Finset E} (c : (G.restrictEdges F).EdgeColoring q)
    (i : Fin q) : Finset E :=
  (c.colorClass i).map (Function.Embedding.subtype (fun e => e ∈ F))

omit [Fintype V] [Fintype E] in
@[simp] theorem mem_colorCopies {F : Finset E}
    (c : (G.restrictEdges F).EdgeColoring q) (i : Fin q) (e : E) :
    e ∈ colorCopies c i ↔ ∃ h : e ∈ F, c.color ⟨e, h⟩ = i := by
  simp only [colorCopies, mem_map, Multigraph.EdgeColoring.colorClass,
    mem_filter, mem_univ, true_and, Function.Embedding.subtype_apply]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f.property, hf⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨e, h⟩, hc, rfl⟩

omit [Fintype V] [Fintype E] in
theorem colorCopies_subset {F : Finset E}
    (c : (G.restrictEdges F).EdgeColoring q) (i : Fin q) :
    colorCopies c i ⊆ F := by
  intro e he
  exact (mem_colorCopies c i e).mp he |>.choose

omit [Fintype V] [Fintype E] in
theorem colorCopies_isMatching {F : Finset E}
    (c : (G.restrictEdges F).EdgeColoring q) (i : Fin q) :
    G.IsMatching (colorCopies c i) := by
  intro e he f hf v hev hfv
  obtain ⟨heF, hec⟩ := (mem_colorCopies c i e).mp he
  obtain ⟨hfF, hfc⟩ := (mem_colorCopies c i f).mp hf
  exact congrArg Subtype.val (c.proper (hec.trans hfc.symm) hev hfv)

omit [Fintype V] [Fintype E] in
theorem colorCopies_disjoint {F : Finset E}
    (c : (G.restrictEdges F).EdgeColoring q) :
    Pairwise (fun i j => Disjoint (colorCopies c i) (colorCopies c j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro e hei hej
  obtain ⟨he, hi⟩ := (mem_colorCopies c i e).mp hei
  obtain ⟨_, hj⟩ := (mem_colorCopies c j e).mp hej
  exact hij (hi.symm.trans hj)

def footprint {F : Finset E} (c : (G.restrictEdges F).EdgeColoring q)
    (i : Fin q) : Finset U := univ.filter (fun u => c.Covers i u.val)

omit [Fintype V] [Fintype E] in
@[simp] theorem mem_footprint {F : Finset E}
    (c : (G.restrictEdges F).EdgeColoring q) (i : Fin q) (u : U) :
    u ∈ footprint c i ↔ c.Covers i u.val := by
  simp only [footprint, mem_filter, mem_univ, true_and]

omit [Fintype V] [Fintype E] in
theorem footprint_iff_incident {F : Finset E}
    (c : (G.restrictEdges F).EdgeColoring q) (i : Fin q) (u : U) :
    u ∈ footprint c i ↔ ∃ e ∈ colorCopies c i, u.val ∈ G.edge e := by
  rw [mem_footprint]
  constructor
  · rintro ⟨e, he, hv⟩
    exact ⟨e.val, (mem_colorCopies c i e.val).mpr ⟨e.property, he⟩, hv⟩
  · rintro ⟨e, he, hv⟩
    obtain ⟨h, hc⟩ := (mem_colorCopies c i e).mp he
    exact ⟨⟨e, h⟩, hc, hv⟩

/-- Actual core matchings completing every color of the selected copy set. -/
structure Completion (C : Core G U) (F : Finset E)
    (c : (G.restrictEdges F).EdgeColoring q) where
  matching : Fin q → C.graph.Subgraph
  isMatching : ∀ i, (matching i).IsMatching
  verts : ∀ i, (matching i).verts = (footprint (U := U) c i : Set U)ᶜ
  disjoint : Pairwise (fun i j => Disjoint (matching i).spanningCoe (matching j).spanningCoe)

namespace Completion

variable {C : Core G U} {F : Finset E}
variable {c : (G.restrictEdges F).EdgeColoring q}
variable (D : Completion C F c)

def classes (i : Fin q) : Finset E := colorCopies c i ∪ coreMatchingCopies C (D.matching i)

omit [Fintype V] [Fintype E] in
private theorem no_common (i : Fin q)
    {e f : E} (he : e ∈ colorCopies c i)
    (hf : f ∈ coreMatchingCopies C (D.matching i))
    {v : V} (hev : v ∈ G.edge e) (hfv : v ∈ G.edge f) : False := by
  have hvU := OneCore.coreEdges_endpoint C
    (coreMatchingCopies_subset_core C (D.matching i) hf) hfv
  have hfoot : (⟨v, hvU⟩ : U) ∈ footprint c i :=
    (footprint_iff_incident c i ⟨v, hvU⟩).mpr ⟨e, he, hev⟩
  have hverts := coreMatchingCopies_incident_verts C (D.matching i) hf ⟨v, hvU⟩ hfv
  rw [D.verts] at hverts
  exact hverts hfoot

omit [Fintype V] [Fintype E] in
theorem classes_isMatching (i : Fin q) :
    G.IsMatching (D.classes i) := by
  intro e he f hf v hev hfv
  rcases mem_union.mp he with he | he <;> rcases mem_union.mp hf with hf | hf
  · exact colorCopies_isMatching c i e he f hf v hev hfv
  · exact (D.no_common i he hf hev hfv).elim
  · exact (D.no_common i hf he hfv hev).elim
  · exact coreMatchingCopies_isMatching C (D.matching i) (D.isMatching i) e he f hf v hev hfv

omit [Fintype V] in
theorem classes_disjoint (hF : F ⊆ (OneCore.coreEdges C)ᶜ) :
    Pairwise (fun i j => Disjoint (D.classes i) (D.classes j)) := by
  have hcross (i j : Fin q) : Disjoint (colorCopies c i) (coreMatchingCopies C (D.matching j)) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact (mem_compl.mp (hF (colorCopies_subset c i he)))
      (coreMatchingCopies_subset_core C (D.matching j) hf)
  intro i j hij
  exact Finset.disjoint_union_left.mpr
    ⟨Finset.disjoint_union_right.mpr ⟨colorCopies_disjoint c hij, hcross i j⟩,
      Finset.disjoint_union_right.mpr ⟨(hcross j i).symm,
        coreMatchingCopies_disjoint C (D.matching i) (D.matching j) (D.disjoint hij)⟩⟩

omit [Fintype V] [Fintype E] in
theorem classes_isPerfectMatching
    (houtside : ∀ v, v ∉ U → (G.restrictEdges F).degree v = q) (i : Fin q) :
    G.IsPerfectMatching (D.classes i) := by
  apply G.isPerfectMatching_iff.mpr
  refine ⟨D.classes_isMatching i, ?_⟩
  intro v
  by_cases hv : v ∈ U
  · by_cases hc : (⟨v, hv⟩ : U) ∈ footprint c i
    · obtain ⟨e, he, hev⟩ := (footprint_iff_incident c i ⟨v, hv⟩).mp hc
      exact ⟨e, mem_union_left _ he, hev⟩
    · have hver : (⟨v, hv⟩ : U) ∈ (D.matching i).verts := by rw [D.verts]; exact hc
      obtain ⟨e, he, hev⟩ := coreMatchingCopies_covers C (D.matching i)
        (D.isMatching i) ⟨v, hv⟩ hver
      exact ⟨e, mem_union_right _ he, hev⟩
  · obtain ⟨e, he, hev⟩ := c.covers_of_degree_eq v (houtside v hv) i
    exact ⟨e.val, mem_union_left _ ((mem_colorCopies c i e.val).mpr ⟨e.property, he⟩), hev⟩

def used : Finset E := univ.biUnion D.classes

omit [Fintype V] [Fintype E] in
@[simp] theorem mem_used (e : E) : e ∈ D.used ↔ ∃ i, e ∈ D.classes i := by
  simp only [used, mem_biUnion, mem_univ, true_and]

omit [Fintype V] [Fintype E] in
theorem selected_used : F ⊆ D.used := by
  intro e he
  exact (D.mem_used e).mpr ⟨c.color ⟨e, he⟩,
    mem_union_left _ ((mem_colorCopies c _ e).mpr ⟨he, rfl⟩)⟩

omit [Fintype V] in
theorem used_degree (hF : F ⊆ (OneCore.coreEdges C)ᶜ)
    (houtside : ∀ v, v ∉ U → (G.restrictEdges F).degree v = q) (v : V) :
    (G.restrictEdges D.used).degree v = q := by
  have hsets : D.used ∩ G.incidenceEdges v =
      univ.biUnion (fun i => (D.classes i).filter (fun e => v ∈ G.edge e)) := by
    ext e
    simp only [mem_inter, mem_used, Multigraph.mem_incidenceEdges,
      mem_biUnion, mem_univ, true_and, mem_filter]
    aesop
  rw [Multigraph.restrictEdges_degree, hsets, Finset.card_biUnion]
  · have hone (i : Fin q) : ((D.classes i).filter (fun e => v ∈ G.edge e)).card = 1 :=
      D.classes_isPerfectMatching houtside i v
    simp only [hone, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  · intro i _ j _ hij
    exact (D.classes_disjoint hF hij).mono (filter_subset _ _) (filter_subset _ _)

def index (e : D.used) : Fin q := Classical.choose ((D.mem_used e.val).mp e.property)

omit [Fintype V] [Fintype E] in
theorem index_mem (e : D.used) : e.val ∈ D.classes (D.index e) :=
  Classical.choose_spec ((D.mem_used e.val).mp e.property)

/-- Color the completed original copies by their matching index. -/
def usedColoring : (G.restrictEdges D.used).EdgeColoring q where
  color := D.index
  proper := by
    intro e f v hef hev hfv
    apply Subtype.ext
    have hf : f.val ∈ D.classes (D.index e) := hef ▸ D.index_mem f
    exact D.classes_isMatching (D.index e) e.val (D.index_mem e) f.val hf v hev hfv

include D in
/-- Once every nonselected copy crosses a genuine bipartition, the whole
host is colored: the packed colors and König's residual colors are disjoint. -/
theorem edgeColorable (k : ℕ) (hq : q ≤ k)
    (hF : F ⊆ (OneCore.coreEdges C)ᶜ)
    (houtside : ∀ v, v ∉ U → (G.restrictEdges F).degree v = q)
    (hregular : ∀ v, G.degree v = k)
    (hbip : (G.restrictEdges Fᶜ).IsBipartite) : Nonempty (G.EdgeColoring k) := by
  have hrem (v : V) : (G.restrictEdges D.usedᶜ).degree v = k - q := by
    have h := OneCore.complement_degree_add G D.used v
    rw [D.used_degree hF houtside v, hregular v] at h
    omega
  have hremBip : (G.restrictEdges D.usedᶜ).IsBipartite := by
    obtain ⟨side, hside⟩ := hbip
    refine ⟨side, ?_⟩
    intro e
    have he : e.val ∈ Fᶜ := mem_compl.mpr (fun h =>
      (mem_compl.mp e.property) (D.selected_used h))
    exact hside ⟨e.val, he⟩
  obtain ⟨r⟩ := (G.restrictEdges D.usedᶜ).exists_edgeColoring_of_bipartite hremBip
    (k - q) (fun v => (hrem v).le)
  let color : E → Fin k := fun e => if he : e ∈ D.used then
    ⟨(D.usedColoring.color ⟨e, he⟩).val, (D.usedColoring.color ⟨e, he⟩).isLt.trans_le hq⟩
    else ⟨q + (r.color ⟨e, mem_compl.mpr he⟩).val, by
      have h := (r.color ⟨e, mem_compl.mpr he⟩).isLt
      omega⟩
  refine ⟨⟨color, ?_⟩⟩
  intro e f v hef hev hfv
  have hval := congrArg Fin.val hef
  by_cases he : e ∈ D.used
  · by_cases hf : f ∈ D.used
    · have hc : D.usedColoring.color ⟨e, he⟩ = D.usedColoring.color ⟨f, hf⟩ := by
        apply Fin.ext
        simpa only [color, dif_pos he, dif_pos hf] using hval
      exact congrArg Subtype.val (D.usedColoring.proper hc hev hfv)
    · simp only [color, dif_pos he, dif_neg hf] at hval
      have h := (D.usedColoring.color ⟨e, he⟩).isLt
      omega
  · by_cases hf : f ∈ D.used
    · simp only [color, dif_neg he, dif_pos hf] at hval
      have h := (D.usedColoring.color ⟨f, hf⟩).isLt
      omega
    · have hc : r.color ⟨e, mem_compl.mpr he⟩ = r.color ⟨f, mem_compl.mpr hf⟩ := by
        apply Fin.ext
        simpa only [color, dif_neg he, dif_neg hf, Nat.add_left_cancel_iff] using hval
      exact congrArg Subtype.val (r.proper hc hev hfv)

end Completion

variable {A B : Type*} [Fintype A] [Fintype B]

def sideFootprint {F : Finset E} (c : (G.restrictEdges F).EdgeColoring q)
    (e : A ⊕ B ≃ U) (i : Fin q) : Finset (A ⊕ B) :=
  (footprint (U := U) c i).map e.symm.toEmbedding

omit [Fintype V] [Fintype E] [Fintype A] [Fintype B] in
@[simp] theorem mem_sideFootprint {F : Finset E}
    (c : (G.restrictEdges F).EdgeColoring q) (e : A ⊕ B ≃ U)
    (i : Fin q) (v : A ⊕ B) :
    v ∈ sideFootprint c e i ↔ c.Covers i (e v).val := by
  simp only [sideFootprint, Finset.mem_map_equiv, Equiv.symm_symm, mem_footprint]

omit [Fintype E] in
theorem footprint_card {F : Finset E} (c : (G.restrictEdges F).EdgeColoring q)
    (i : Fin q) : (footprint (U := U) c i).card = (U ∩ c.coveredVertices i).card := by
  have hmap : (footprint (U := U) c i).map (Function.Embedding.subtype (fun v => v ∈ U)) =
      U ∩ c.coveredVertices i := by
    ext v
    simp only [mem_map, mem_footprint, Function.Embedding.subtype_apply, mem_inter,
      c.mem_coveredVertices]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.property, hu⟩
    · rintro ⟨hv, hc⟩
      exact ⟨⟨v, hv⟩, hc, rfl⟩
  rw [← hmap, Finset.card_map]

omit [Fintype E] [Fintype A] [Fintype B] in
theorem sideFootprint_card {F : Finset E} (c : (G.restrictEdges F).EdgeColoring q)
    (e : A ⊕ B ≃ U) (i : Fin q) :
    (sideFootprint c e i).card = (U ∩ c.coveredVertices i).card := by
  rw [sideFootprint, Finset.card_map, footprint_card]

omit [Fintype V] [Fintype E] [Fintype A] [Fintype B] in
theorem sideFootprint_load {F : Finset E} (c : (G.restrictEdges F).EdgeColoring q)
    (e : A ⊕ B ≃ U) (v : A ⊕ B) :
    (univ.filter (fun i : Fin q => v ∈ sideFootprint c e i)).card =
      (G.restrictEdges F).degree (e v).val := by
  simp only [mem_sideFootprint]
  exact c.coveredColors_card (e v).val

/-- Map the actual packed core matchings through the shore equivalence. -/
def completionOfPacking (C : Core G U) {F : Finset E}
    (c : (G.restrictEdges F).EdgeColoring q) (e : A ⊕ B ≃ U) {θ σ : ℝ}
    (P : BipartiteCorePacking (C.graph.comap e) q (sideFootprint c e) θ σ) :
    Completion C F c where
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
      apply (BipartiteFactorization.mapped_subgraph_adj C e (P.matching i) _ _).mp
      simpa only [Equiv.apply_symm_apply] using hvw.1
    have hj : (P.matching j).Adj (e.symm v) (e.symm w) := by
      apply (BipartiteFactorization.mapped_subgraph_adj C e (P.matching j) _ _).mp
      simpa only [Equiv.apply_symm_apply] using hvw.2
    exact (disjoint_iff_inf_le.mp (P.disjoint hij)) ⟨hi, hj⟩

end Overfull.TwoApexFactorization
