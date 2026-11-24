import Overfull.Dense.Encoding.Model

/-!
# Colorings and triangles in the actual encoding

All colorings here are functions on actual edge copies. The simple part is
represented by its injective copy map; colors on its complement are fixed.
-/

namespace Overfull.Dense.Encoding.SimplePart

open Finset Classical
open TripartiteGraph

variable {A B E : Type*} [Fintype A] [Fintype B]
variable {G : Multigraph (A ⊕ B) E} (H : SimplePart G) {k : ℕ}

/-- A proper coloring of the simple part using only colors available in
the prescribed complementary coloring. -/
structure AvailableColoring (c₀ : H.remainder.EdgeColoring k) where
  color : H.Edge → Fin k
  available_left : ∀ e, c₀.Available (.inl e.val.1) (color e)
  available_right : ∀ e, c₀.Available (.inr e.val.2) (color e)
  proper : ∀ e f, color e = color f →
    (e.val.1 = f.val.1 ∨ e.val.2 = f.val.2) → e = f

@[simp] theorem edgeOfMem_edgeMap (e : H.Edge) (he : H.edgeMap e ∈ H.edges) :
    H.edgeOfMem (H.edgeMap e) he = e := by
  apply H.edgeMap.injective
  exact H.edgeMap_edgeOfMem _ _

omit [Fintype A] [Fintype B] in
@[simp] theorem map_mem_left (e : H.Edge) (a : A) :
    Sum.inl a ∈ G.edge (H.edgeMap e) ↔ e.val.1 = a := by
  rw [H.map_edge]
  simp [eq_comm]

omit [Fintype A] [Fintype B] in
@[simp] theorem map_mem_right (e : H.Edge) (b : B) :
    Sum.inr b ∈ G.edge (H.edgeMap e) ↔ e.val.2 = b := by
  rw [H.map_edge]
  simp [eq_comm]

namespace AvailableColoring

variable {H} {c₀ : H.remainder.EdgeColoring k} (c : H.AvailableColoring c₀)

noncomputable def totalColor (e : E) : Fin k :=
  if he : e ∈ H.edges then c.color (H.edgeOfMem e he) else c₀.color ⟨e,he⟩

@[simp] theorem totalColor_map (e : H.Edge) :
    c.totalColor (H.edgeMap e) = c.color e := by
  simp only [totalColor, dif_pos (H.edgeMap_mem_edges e), H.edgeOfMem_edgeMap]

@[simp] theorem totalColor_remaining (e : {e : E // e ∉ H.edges}) :
    c.totalColor e.val = c₀.color e := by
  simp only [totalColor, dif_neg e.property]

theorem totalColor_proper {e f : E} {v : A ⊕ B}
    (hcolor : c.totalColor e = c.totalColor f)
    (he : v ∈ G.edge e) (hf : v ∈ G.edge f) : e = f := by
  by_cases heH : e ∈ H.edges
  · obtain ⟨x, rfl⟩ := (H.mem_edges e).mp heH
    by_cases hfH : f ∈ H.edges
    · obtain ⟨y, rfl⟩ := (H.mem_edges f).mp hfH
      apply congrArg H.edgeMap
      apply c.proper x y (by simpa only [c.totalColor_map] using hcolor)
      cases v with
      | inl a => exact Or.inl ((H.map_mem_left x a).mp he |>.trans
          ((H.map_mem_left y a).mp hf).symm)
      | inr b => exact Or.inr ((H.map_mem_right x b).mp he |>.trans
          ((H.map_mem_right y b).mp hf).symm)
    · have hcf : c.color x = c₀.color ⟨f,hfH⟩ := by
        rw [c.totalColor_map] at hcolor
        simpa only [totalColor, dif_neg hfH] using hcolor
      exfalso
      cases v with
      | inl a =>
        have hxa := (H.map_mem_left x a).mp he
        apply c.available_left x
        exact ⟨⟨f,hfH⟩, by simpa only [hxa] using hf, hcf.symm⟩
      | inr b =>
        have hxb := (H.map_mem_right x b).mp he
        apply c.available_right x
        exact ⟨⟨f,hfH⟩, by simpa only [hxb] using hf, hcf.symm⟩
  · by_cases hfH : f ∈ H.edges
    · obtain ⟨y, rfl⟩ := (H.mem_edges f).mp hfH
      have hce : c₀.color ⟨e,heH⟩ = c.color y := by
        rw [c.totalColor_map] at hcolor
        simpa only [totalColor, dif_neg heH] using hcolor
      exfalso
      cases v with
      | inl a =>
        have hya := (H.map_mem_left y a).mp hf
        apply c.available_left y
        exact ⟨⟨e,heH⟩, by simpa only [hya] using he, hce⟩
      | inr b =>
        have hyb := (H.map_mem_right y b).mp hf
        apply c.available_right y
        exact ⟨⟨e,heH⟩, by simpa only [hyb] using he, hce⟩
    · have hce : c₀.color ⟨e,heH⟩ = c₀.color ⟨f,hfH⟩ := by
        simpa only [totalColor, dif_neg heH, dif_neg hfH] using hcolor
      exact congrArg Subtype.val (c₀.proper hce he hf)

/-- The actual extension, including the prescribed color of every parallel
edge copy in the complement. -/
noncomputable def extension : G.EdgeColoring k where
  color := c.totalColor
  proper := c.totalColor_proper

theorem extension_extends : H.Extends c₀ c.extension := by
  intro e
  exact c.totalColor_remaining e

end AvailableColoring

end Overfull.Dense.Encoding.SimplePart
