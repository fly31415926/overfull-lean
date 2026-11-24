import Overfull.Dense.Encoding.Coloring

/-!
# Exact equivalence between extensions and triangle decompositions
-/

namespace Overfull.Dense.Encoding.SimplePart

open Finset Classical
open TripartiteGraph

variable {A B E : Type*} [Fintype A] [Fintype B]
variable {G : Multigraph (A ⊕ B) E} (H : SimplePart G) {k : ℕ}
variable (c₀ : H.remainder.EdgeColoring k)

namespace Decomposition

variable {H c₀}
variable {T : Finset (H.encoded c₀).Triangle}
variable (hT : (H.encoded c₀).IsTriangleDecomposition T (H.encoded c₀).edgeFinset)

noncomputable def triangle (e : H.Edge) : (H.encoded c₀).Triangle :=
  ((TripartiteGraph.IsTriangleDecomposition.full_unique (H.encoded c₀) hT
    (e := abPos e.val.1 e.val.2) e.property).exists).choose

theorem triangle_mem (e : H.Edge) : triangle hT e ∈ T :=
  ((TripartiteGraph.IsTriangleDecomposition.full_unique (H.encoded c₀) hT
    (e := abPos e.val.1 e.val.2) e.property).exists).choose_spec.1

theorem triangle_left (e : H.Edge) : (triangle hT e).val.1 = e.val.1 :=
  ((TripartiteGraph.IsTriangleDecomposition.full_unique (H.encoded c₀) hT
    (e := abPos e.val.1 e.val.2) e.property).exists).choose_spec.2.1

theorem triangle_right (e : H.Edge) : (triangle hT e).val.2.1 = e.val.2 :=
  ((TripartiteGraph.IsTriangleDecomposition.full_unique (H.encoded c₀) hT
    (e := abPos e.val.1 e.val.2) e.property).exists).choose_spec.2.2

theorem triangle_injective : Function.Injective (triangle hT) := by
  intro e f hef
  apply Subtype.ext
  apply Prod.ext
  · rw [← triangle_left hT e, ← triangle_left hT f, hef]
  · rw [← triangle_right hT e, ← triangle_right hT f, hef]

noncomputable def availableColoring : H.AvailableColoring c₀ where
  color e := (triangle hT e).val.2.2
  available_left e := by
    have h := (triangle hT e).property.2.1
    simpa only [encoded, triangle_left] using h
  available_right e := by
    have h := (triangle hT e).property.2.2
    simpa only [encoded, triangle_right] using h
  proper e f hcolor hvertex := by
    apply triangle_injective hT
    rcases hvertex with hleft | hright
    · have hu := TripartiteGraph.IsTriangleDecomposition.full_unique
        (H.encoded c₀) hT
        (e := awPos e.val.1 (triangle hT e).val.2.2)
        (by simpa only [IsEdge, awPos, encoded, triangle_left] using
          (triangle hT e).property.2.1)
      apply hu.unique
      · exact ⟨triangle_mem hT e, triangle_left hT e, rfl⟩
      · exact ⟨triangle_mem hT f, (triangle_left hT f).trans hleft.symm,
          hcolor.symm⟩
    · have hu := TripartiteGraph.IsTriangleDecomposition.full_unique
        (H.encoded c₀) hT
        (e := bwPos e.val.2 (triangle hT e).val.2.2)
        (by simpa only [IsEdge, bwPos, encoded, triangle_right] using
          (triangle hT e).property.2.2)
      apply hu.unique
      · exact ⟨triangle_mem hT e, triangle_right hT e, rfl⟩
      · exact ⟨triangle_mem hT f, (triangle_right hT f).trans hright.symm,
          hcolor.symm⟩

end Decomposition

/-- Every actual triangle decomposition gives a proper coloring of all
host edge copies agreeing with the prescribed coloring. -/
theorem exists_extension_of_triangleDecomposition
    (h : (H.encoded c₀).HasTriangleDecomposition) :
    ∃ c : G.EdgeColoring k, H.Extends c₀ c := by
  obtain ⟨T,hT⟩ := h
  exact ⟨(Decomposition.availableColoring hT).extension,
    (Decomposition.availableColoring hT).extension_extends⟩

namespace Extension

variable {H c₀} (c : G.EdgeColoring k) (hc : H.Extends c₀ c)

include hc in
theorem available_at_map (e : H.Edge) (v : A ⊕ B)
    (hv : v ∈ G.edge (H.edgeMap e)) :
    c₀.Available v (c.color (H.edgeMap e)) := by
  rintro ⟨f,hvf,hcolor⟩
  have hef : f.val = H.edgeMap e := c.proper ((hc f).trans hcolor) hvf hv
  exact f.property (hef.symm ▸ H.edgeMap_mem_edges e)

def triangle (e : H.Edge) : (H.encoded c₀).Triangle :=
  ⟨(e.val.1,e.val.2,c.color (H.edgeMap e)), e.property,
    available_at_map c hc e (.inl e.val.1) ((H.map_mem_left e _).mpr rfl),
    available_at_map c hc e (.inr e.val.2) ((H.map_mem_right e _).mpr rfl)⟩

noncomputable def triangles : Finset (H.encoded c₀).Triangle :=
  univ.image (triangle c hc)

@[simp] theorem mem_triangles (t : (H.encoded c₀).Triangle) :
    t ∈ triangles c hc ↔ ∃ e : H.Edge, triangle c hc e = t := by
  simp only [triangles, Finset.mem_image, Finset.mem_univ, true_and]

theorem triangle_mem (e : H.Edge) : triangle c hc e ∈ triangles c hc :=
  (mem_triangles c hc _).mpr ⟨e,rfl⟩

variable [Fintype E]

theorem isTriangleDecomposition (hregular : ∀ v, G.degree v = k) :
    (H.encoded c₀).IsTriangleDecomposition (triangles c hc)
      (H.encoded c₀).edgeFinset := by
  apply TripartiteGraph.isTriangleDecomposition_of_full_unique
  rintro (⟨a,b⟩ | ⟨a,w⟩ | ⟨b,w⟩) hedge
  · let e : H.Edge := ⟨(a,b),hedge⟩
    refine ⟨triangle c hc e, ⟨triangle_mem c hc e, rfl, rfl⟩, ?_⟩
    intro t ht
    obtain ⟨f,rfl⟩ := (mem_triangles c hc t).mp ht.1
    apply congrArg (triangle c hc)
    apply Subtype.ext
    exact Prod.ext ht.2.1 ht.2.2
  · obtain ⟨e,⟨he,hcolor⟩,_⟩ := c.incident_color_unique (.inl a) (hregular _) w
    have heH : e ∈ H.edges := by
      by_contra hn
      apply hedge
      exact ⟨⟨e,hn⟩,he,(hc ⟨e,hn⟩).symm.trans hcolor⟩
    let x : H.Edge := H.edgeOfMem e heH
    have hxmap : H.edgeMap x = e := H.edgeMap_edgeOfMem e heH
    have hxa : x.val.1 = a := (H.map_mem_left x a).mp (by rw [hxmap]; exact he)
    have hxcolor : c.color (H.edgeMap x) = w := by rw [hxmap]; exact hcolor
    refine ⟨triangle c hc x, ⟨triangle_mem c hc x,hxa,hxcolor⟩, ?_⟩
    intro t ht
    obtain ⟨f,rfl⟩ := (mem_triangles c hc t).mp ht.1
    apply congrArg (triangle c hc)
    apply H.edgeMap.injective
    exact c.proper (ht.2.2.trans hxcolor.symm)
      ((H.map_mem_left f a).mpr ht.2.1) ((H.map_mem_left x a).mpr hxa)
  · obtain ⟨e,⟨he,hcolor⟩,_⟩ := c.incident_color_unique (.inr b) (hregular _) w
    have heH : e ∈ H.edges := by
      by_contra hn
      apply hedge
      exact ⟨⟨e,hn⟩,he,(hc ⟨e,hn⟩).symm.trans hcolor⟩
    let x : H.Edge := H.edgeOfMem e heH
    have hxmap : H.edgeMap x = e := H.edgeMap_edgeOfMem e heH
    have hxb : x.val.2 = b := (H.map_mem_right x b).mp (by rw [hxmap]; exact he)
    have hxcolor : c.color (H.edgeMap x) = w := by rw [hxmap]; exact hcolor
    refine ⟨triangle c hc x, ⟨triangle_mem c hc x,hxb,hxcolor⟩, ?_⟩
    intro t ht
    obtain ⟨f,rfl⟩ := (mem_triangles c hc t).mp ht.1
    apply congrArg (triangle c hc)
    apply H.edgeMap.injective
    exact c.proper (ht.2.2.trans hxcolor.symm)
      ((H.map_mem_right f b).mpr ht.2.1) ((H.map_mem_right x b).mpr hxb)

end Extension

variable [Fintype E]

/-- A full proper coloring of a regular host uses every color at every
vertex and therefore partitions all three types of encoded edges into
the triangles defined by its colors. -/
theorem triangleDecomposition_of_extension (hregular : ∀ v, G.degree v = k)
    (c : G.EdgeColoring k) (hc : H.Extends c₀ c) :
    (H.encoded c₀).HasTriangleDecomposition :=
  ⟨Extension.triangles c hc, Extension.isTriangleDecomposition c hc hregular⟩

/-- Extending the specified coloring is equivalent to decomposing the
actual encoded tripartite graph into triangles. -/
theorem extension_iff_triangleDecomposition (hregular : ∀ v, G.degree v = k) :
    (∃ c : G.EdgeColoring k, H.Extends c₀ c) ↔
      (H.encoded c₀).HasTriangleDecomposition := by
  constructor
  · rintro ⟨c,hc⟩
    exact H.triangleDecomposition_of_extension c₀ hregular c hc
  · exact H.exists_extension_of_triangleDecomposition c₀

end Overfull.Dense.Encoding.SimplePart
