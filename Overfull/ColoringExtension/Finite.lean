import Overfull.ColoringExtension.ConflictCount
import Overfull.ColoringExtension.Repair
import Mathlib.Data.Fin.Embedding

/-!
# Finite coloring with a bounded set of forbidden labels on each edge

An actual initial coloring, exact permutation counting, and deterministic
spare-palette repair give a feasible coloring. The numerical hypotheses
are finite inequalities, and no list-coloring theorem is assumed.
-/

namespace Overfull.ColoringExtension

open Finset Classical
open Multigraph

variable {V E : Type*} [Fintype V] [Fintype E]
variable {G : Multigraph V E} {r h : ℕ}

/-- An exact finite criterion for avoiding prescribed forbidden labels.
The construction retains every permitted color after a suitable injective
relabeling of the original palette. -/
theorem exists_avoiding_with_relabeling (c : G.EdgeColoring r)
    (f : Fin r ↪ Fin h) (B : E → Finset (Fin h)) (b t : ℕ)
    (ht : 1 ≤ t) (hB : ∀ e, (B e).card ≤ b)
    (htail : Fintype.card V * b ^ t < t.factorial)
    (hslack : b + 2 * (t - 1) < h - r) :
    ∃ σ : Equiv.Perm (Fin h), ∃ c' : G.EdgeColoring h,
      (∀ e, c'.color e ∉ B e) ∧
      ∀ e, σ (f (c.color e)) ∉ B e → c'.color e = σ (f (c.color e)) := by
  obtain ⟨σ, hσ⟩ := exists_sparse_conflicts G c f B b t ht hB htail
  let g : Fin r ↪ Fin h := f.trans σ.toEmbedding
  obtain ⟨c', hc', hkeep⟩ := repair_relabeling c g B b (t - 1) hB
    (by
      intro v
      change ((G.incidenceEdges v).filter
        (fun e => σ (f (c.color e)) ∈ B e)).card ≤ t - 1
      have hv := hσ v
      omega) hslack
  exact ⟨σ, c', hc', hkeep⟩

/-- The target palette need only contain the original palette and enough
spare labels for the sparse-conflict repair. -/
theorem exists_avoiding_coloring (c : G.EdgeColoring r) (hrh : r ≤ h)
    (B : E → Finset (Fin h)) (b t : ℕ)
    (ht : 1 ≤ t) (hB : ∀ e, (B e).card ≤ b)
    (htail : Fintype.card V * b ^ t < t.factorial)
    (hslack : b + 2 * (t - 1) < h - r) :
    ∃ c' : G.EdgeColoring h, ∀ e, c'.color e ∉ B e := by
  obtain ⟨_σ, c', hc', _⟩ := exists_avoiding_with_relabeling c
    (Fin.castLEEmb hrh) B b t ht hB htail hslack
  exact ⟨c', hc'⟩

/-- Add `s` colors to an existing coloring and avoid at most `b` prescribed
labels per edge under the exact factorial and slack conditions. -/
theorem exists_avoiding_with_spare_colors (c : G.EdgeColoring r)
    (s : ℕ) (B : E → Finset (Fin (r + s))) (b t : ℕ)
    (ht : 1 ≤ t) (hB : ∀ e, (B e).card ≤ b)
    (htail : Fintype.card V * b ^ t < t.factorial)
    (hslack : b + 2 * (t - 1) < s) :
    ∃ c' : G.EdgeColoring (r + s), ∀ e, c'.color e ∉ B e := by
  apply exists_avoiding_coloring c (Nat.le_add_right r s) B b t ht hB htail
  simpa only [Nat.add_sub_cancel_left] using hslack

end Overfull.ColoringExtension
