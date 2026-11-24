import Overfull.ColoringExtension.Finite
import Overfull.ColoringExtension.Balance

/-!
# Fixed exterior labels as forbidden vertices

For each target color, its fixed exterior edges forbid the vertices already
covered by that color. The load at a vertex bounds the forbidden labels of
an internal edge. Permutation and repair produce a feasible coloring, and
the subsequent exchanges balance its classes while preserving feasibility.
-/

noncomputable section

namespace Overfull.ColoringExtension

open Finset Classical
open Multigraph

variable {V E : Type*} {h r : ℕ}

/-- The labels forbidden at a vertex by the fixed per-color footprints. -/
def forbiddenColors (F : Fin h → Finset V) (v : V) : Finset (Fin h) :=
  univ.filter (fun i => v ∈ F i)

@[simp] theorem mem_forbiddenColors (F : Fin h → Finset V) (v : V) (i : Fin h) :
    i ∈ forbiddenColors F v ↔ v ∈ F i := by
  simp [forbiddenColors]

/-- A color is forbidden on an edge if it is forbidden at either endpoint. -/
def edgeForbiddens (G : Multigraph V E) (F : Fin h → Finset V)
    (e : E) : Finset (Fin h) :=
  forbiddenColors F (G.firstEnd e) ∪ forbiddenColors F (G.secondEnd e)

theorem mem_edgeForbiddens (G : Multigraph V E) (F : Fin h → Finset V)
    (e : E) (i : Fin h) :
    i ∈ edgeForbiddens G F e ↔ ∃ v, v ∈ G.edge e ∧ v ∈ F i := by
  simp only [edgeForbiddens, Finset.mem_union, mem_forbiddenColors]
  constructor
  · rintro (hu | hv)
    · exact ⟨G.firstEnd e, (G.incident_iff e _).mpr (Or.inl rfl), hu⟩
    · exact ⟨G.secondEnd e, (G.incident_iff e _).mpr (Or.inr rfl), hv⟩
  · rintro ⟨v, he, hv⟩
    rcases (G.incident_iff e v).mp he with hu | hw
    · exact Or.inl (hu.symm ▸ hv)
    · exact Or.inr (hw.symm ▸ hv)

theorem edgeForbiddens_card_le (G : Multigraph V E) (F : Fin h → Finset V)
    (a : ℕ) (hload : ∀ v, (forbiddenColors F v).card ≤ a) (e : E) :
    (edgeForbiddens G F e).card ≤ 2 * a := by
  exact (Finset.card_union_le _ _).trans (by
    have hu := hload (G.firstEnd e)
    have hv := hload (G.secondEnd e)
    omega)

variable [Fintype V] [Fintype E] {G : Multigraph V E}

omit [Fintype V] [Fintype E] in
theorem avoidsVertices_iff_edgeForbiddens (c : G.EdgeColoring h)
    (F : Fin h → Finset V) :
    c.AvoidsVertices F ↔ ∀ e, c.color e ∉ edgeForbiddens G F e := by
  rw [c.avoidsVertices_iff_incidence F]
  constructor
  · intro hc e he
    obtain ⟨v, hv, hF⟩ := (mem_edgeForbiddens G F e (c.color e)).mp he
    exact hc e v hv hF
  · intro hc e v hv hF
    exact hc e ((mem_edgeForbiddens G F e (c.color e)).mpr ⟨v, hv, hF⟩)

/-- The finite criterion supplies a feasible coloring for fixed exterior
footprints and then balances its actual internal color classes. -/
theorem exists_balanced_coloring_avoiding (c₀ : G.EdgeColoring r) (hrh : r ≤ h)
    (F : Fin h → Finset V) (a f t : ℕ)
    (hF : ∀ i, (F i).card ≤ f)
    (hload : ∀ v, (forbiddenColors F v).card ≤ a)
    (ht : 1 ≤ t) (htail : Fintype.card V * (2 * a) ^ t < t.factorial)
    (hslack : 2 * a + 2 * (t - 1) < h - r) :
    ∃ c : G.EdgeColoring h, c.AvoidsVertices F ∧
      ∀ i j, |((c.colorClass i).card : ℤ) - ((c.colorClass j).card : ℤ)| ≤ (f : ℤ) + 1 := by
  obtain ⟨c, hc⟩ := exists_avoiding_coloring c₀ hrh (edgeForbiddens G F)
    (2 * a) t ht (edgeForbiddens_card_le G F a hload) htail hslack
  exact c.exists_balanced_avoiding F f hF
    ((avoidsVertices_iff_edgeForbiddens c F).mpr hc)

end Overfull.ColoringExtension
