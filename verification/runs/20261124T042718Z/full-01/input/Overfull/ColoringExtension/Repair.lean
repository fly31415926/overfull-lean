import Overfull.ColoringExtension.Greedy
import Overfull.SparseColoring

/-!
# Repairing sparse conflicts with unused colors

Keep every permitted edge color and recolor only the actual conflicting
copies. An unused palette separates repaired edges from the unchanged
edges. All estimates remain valid for parallel edge copies.
-/

noncomputable section

namespace Overfull.ColoringExtension

open Finset Classical
open Multigraph

variable {V E : Type*} {G : Multigraph V E} [Fintype E] {k r h : ℕ}

/-- Actual edges whose tentative color is forbidden. -/
def conflictEdges (c : G.EdgeColoring k) (B : E → Finset (Fin k)) : Finset E :=
  univ.filter (fun e => c.color e ∈ B e)

@[simp] theorem mem_conflictEdges (c : G.EdgeColoring k)
    (B : E → Finset (Fin k)) (e : E) :
    e ∈ conflictEdges c B ↔ c.color e ∈ B e := by
  simp [conflictEdges]

/-- The degree of the actual conflict graph is its filtered incidence count. -/
theorem conflict_degree (c : G.EdgeColoring k) (B : E → Finset (Fin k)) (v : V) :
    (G.restrictEdges (conflictEdges c B)).degree v =
      ((G.incidenceEdges v).filter (fun e => c.color e ∈ B e)).card := by
  rw [G.restrictEdges_degree]
  congr 1
  ext e
  simp only [Finset.mem_inter, mem_conflictEdges, Finset.mem_filter]
  exact and_comm

/-- Recolor the conflict graph from unused colors, keeping every permitted
tentative color. The forbidden sets may depend arbitrarily on edge copies. -/
theorem repair_sparse_conflicts (c : G.EdgeColoring k)
    (B : E → Finset (Fin k)) (S : Finset (Fin k)) (b d : ℕ)
    (hB : ∀ e, (B e).card ≤ b) (hS : ∀ e, c.color e ∉ S)
    (hdegree : ∀ v,
      ((G.incidenceEdges v).filter (fun e => c.color e ∈ B e)).card ≤ d)
    (hslack : b + 2 * d < S.card) :
    ∃ c' : G.EdgeColoring k, (∀ e, c'.color e ∉ B e) ∧
      ∀ e, c.color e ∉ B e → c'.color e = c.color e := by
  let F := conflictEdges c B
  obtain ⟨a, ha⟩ := (G.restrictEdges F).exists_edgeColoring_avoiding S
    (fun e => B e.val) b d (fun e => hB e.val)
    (by intro v; simpa only [F, conflict_degree] using hdegree v) hslack
  let c' : G.EdgeColoring k := {
    color := fun e => if he : e ∈ F then a.color ⟨e, he⟩ else c.color e
    proper := by
      intro e f v hef hev hfv
      by_cases he : e ∈ F
      · by_cases hf : f ∈ F
        · have h : a.color ⟨e, he⟩ = a.color ⟨f, hf⟩ := by
            simpa only [dif_pos he, dif_pos hf] using hef
          exact congrArg Subtype.val (a.proper h hev hfv)
        · have h : a.color ⟨e, he⟩ = c.color f := by
            simpa only [dif_pos he, dif_neg hf] using hef
          exact (hS f (h ▸ (ha ⟨e, he⟩).1)).elim
      · by_cases hf : f ∈ F
        · have h : c.color e = a.color ⟨f, hf⟩ := by
            simpa only [dif_neg he, dif_pos hf] using hef
          exact (hS e (h.symm ▸ (ha ⟨f, hf⟩).1)).elim
        · apply c.proper (by simpa only [dif_neg he, dif_neg hf] using hef) hev hfv }
  refine ⟨c', ?_, ?_⟩
  · intro e
    by_cases he : e ∈ F
    · simpa only [c', dif_pos he] using (ha ⟨e, he⟩).2
    · have hb : c.color e ∉ B e := by simpa only [F, mem_conflictEdges] using he
      simpa only [c', dif_neg he] using hb
  · intro e he
    have heF : e ∉ F := by simpa only [F, mem_conflictEdges] using he
    simp only [c', dif_neg heF]

/-- Injectively relabel an existing finite-palette edge coloring. -/
def relabel (c : G.EdgeColoring r) (f : Fin r ↪ Fin h) : G.EdgeColoring h where
  color e := f (c.color e)
  proper hij hev hfv := c.proper (f.injective hij) hev hfv

omit [Fintype E] in
@[simp] theorem relabel_color (c : G.EdgeColoring r) (f : Fin r ↪ Fin h) (e : E) :
    (relabel c f).color e = f (c.color e) := rfl

/-- Exactly the labels outside the image of the original palette. -/
def sparePalette (f : Fin r ↪ Fin h) : Finset (Fin h) :=
  (univ.map f)ᶜ

@[simp] theorem sparePalette_card (f : Fin r ↪ Fin h) :
    (sparePalette f).card = h - r := by
  simp only [sparePalette, Finset.card_compl, Finset.card_map,
    Finset.card_univ, Fintype.card_fin]

theorem not_mem_sparePalette (f : Fin r ↪ Fin h) (i : Fin r) :
    f i ∉ sparePalette f := by
  simp [sparePalette]

/-- The sparse-conflict repair for a relabeled original palette, with
the exact number of spare colors `h-r`. -/
theorem repair_relabeling (c : G.EdgeColoring r) (f : Fin r ↪ Fin h)
    (B : E → Finset (Fin h)) (b d : ℕ)
    (hB : ∀ e, (B e).card ≤ b)
    (hdegree : ∀ v,
      ((G.incidenceEdges v).filter (fun e => f (c.color e) ∈ B e)).card ≤ d)
    (hslack : b + 2 * d < h - r) :
    ∃ c' : G.EdgeColoring h, (∀ e, c'.color e ∉ B e) ∧
      ∀ e, f (c.color e) ∉ B e → c'.color e = f (c.color e) := by
  apply repair_sparse_conflicts (relabel c f) B (sparePalette f) b d hB
    (fun e => not_mem_sparePalette f (c.color e)) hdegree
  simpa only [sparePalette_card] using hslack

end Overfull.ColoringExtension
