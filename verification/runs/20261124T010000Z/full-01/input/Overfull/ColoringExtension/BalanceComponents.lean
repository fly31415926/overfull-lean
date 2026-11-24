import Overfull.BalancedColoring

/-!
# Feasible two-color switches with forbidden vertices

For each color, a fixed set of vertices forbids that color. A component
with two more incidences of color `i` than color `j` can be switched
while preserving these constraints if it avoids the forbidden set for
`j`. The component is found by counting the components touched by that
fixed set; no choice of alternating paths is assumed.
-/

namespace Overfull.Multigraph.EdgeColoring

open Finset Classical
open scoped BigOperators

variable {V E : Type*} {G : Multigraph V E} {k : ℕ}

/-- A color is never used at one of its prescribed forbidden vertices. -/
def AvoidsVertices (c : G.EdgeColoring k) (F : Fin k → Finset V) : Prop :=
  ∀ i v, c.Covers i v → v ∉ F i

theorem avoidsVertices_iff_incidence (c : G.EdgeColoring k) (F : Fin k → Finset V) :
    c.AvoidsVertices F ↔ ∀ e v, v ∈ G.edge e → v ∉ F (c.color e) := by
  constructor
  · intro hc e v hv
    exact hc (c.color e) v ⟨e, rfl, hv⟩
  · intro hc i v hv
    obtain ⟨e, he, hev⟩ := hv
    simpa only [he] using hc e v hev

variable [Fintype V] [Fintype E]

/-- A two-color component has whole-vertex transfer `-2`, `0`, or `2`. -/
theorem component_transfer_univ_values (c : G.EdgeColoring k)
    (i j : Fin k) (hij : i ≠ j)
    (C : (c.twoColorGraph i j).ConnectedComponent) :
    c.transfer i j univ (c.componentVertices i j C) = -2 ∨
      c.transfer i j univ (c.componentVertices i j C) = 0 ∨
      c.transfer i j univ (c.componentVertices i j C) = 2 := by
  have h := c.component_transfers_allowed i j hij univ ∅ ∅
    (by simp) (by simp) (by simp) C
  have hz : c.transfer i j ∅ (c.componentVertices i j C) = 0 := by
    simp [transfer, coveredCount]
  rw [hz] at h
  rcases h with h | h | h | h | h | h | h | h | h <;> omega

/-- A positive excess greater than twice the number of forbidden
vertices supplies a positive component avoiding all those vertices. -/
theorem exists_transfer_two_component_avoiding (c : G.EdgeColoring k)
    (i j : Fin k) (hij : i ≠ j) (F : Finset V)
    (hgap : 2 * (F.card : ℤ) < c.coveredCount univ i - c.coveredCount univ j) :
    ∃ C : (c.twoColorGraph i j).ConnectedComponent,
      c.transfer i j univ (c.componentVertices i j C) = 2 ∧
        Disjoint (c.componentVertices i j C) F := by
  let T := F.image (c.twoColorGraph i j).connectedComponentMk
  have hcard : T.card ≤ F.card := Finset.card_image_le
  have havoid (C : (c.twoColorGraph i j).ConnectedComponent) (hC : C ∉ T) :
      Disjoint (c.componentVertices i j C) F := by
    apply Finset.disjoint_left.mpr
    intro v hv hF
    apply hC
    apply mem_image.mpr
    refine ⟨v, hF, ?_⟩
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff C v).mp
      ((c.mem_componentVertices i j C v).mp hv)
  by_contra hnone
  have hbound (C : (c.twoColorGraph i j).ConnectedComponent) :
      c.transfer i j univ (c.componentVertices i j C) ≤ if C ∈ T then 2 else 0 := by
    have hv := c.component_transfer_univ_values i j hij C
    by_cases hC : C ∈ T
    · rw [if_pos hC]
      rcases hv with hv | hv | hv <;> omega
    · rw [if_neg hC]
      have hn : c.transfer i j univ (c.componentVertices i j C) ≠ 2 :=
        fun h => hnone ⟨C, h, havoid C hC⟩
      rcases hv with hv | hv | hv <;> omega
  have hsum := Finset.sum_le_sum
    (fun C (_ : C ∈ (univ : Finset (c.twoColorGraph i j).ConnectedComponent)) => hbound C)
  have hsum' : (∑ C : (c.twoColorGraph i j).ConnectedComponent,
      c.transfer i j univ (c.componentVertices i j C)) ≤ (T.card : ℤ) * 2 := by
    simpa only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul] using hsum
  rw [c.sum_transfer_components] at hsum'
  have hcardZ : (T.card : ℤ) ≤ F.card := by exact_mod_cast hcard
  omega

/-- In a component of transfer two, every vertex covered by the smaller
color is already covered by the larger color. -/
theorem covers_left_of_transfer_two (c : G.EdgeColoring k)
    (i j : Fin k) (hij : i ≠ j)
    (C : (c.twoColorGraph i j).ConnectedComponent)
    (ht : c.transfer i j univ (c.componentVertices i j C) = 2)
    (v : V) (hv : v ∈ c.componentVertices i j C) (hjv : c.Covers j v) :
    c.Covers i v := by
  by_contra hiv
  let S := c.componentEndpoints i j C
  have hvS : v ∈ S := mem_filter.mpr ⟨hv, Or.inr ⟨hjv, hiv⟩⟩
  have hcard : (S.erase v).card ≤ 1 := by
    have h := c.componentEndpoints_card_le_two i j hij C
    have h' := Finset.card_erase_add_one hvS
    change S.card ≤ 2 at h
    omega
  have heq : c.transfer i j univ (c.componentVertices i j C) =
      ∑ w ∈ S, (c.coverIndicator i w - c.coverIndicator j w) := by
    simpa only [S, mem_univ, if_true] using c.transfer_eq_endpoint_sum i j univ C
  have hroot : c.coverIndicator i v - c.coverIndicator j v = -1 := by
    simp [coverIndicator, hiv, hjv]
  have hupper : (∑ w ∈ S.erase v, (c.coverIndicator i w - c.coverIndicator j w)) ≤
      ((S.erase v).card : ℤ) := by
    calc
      _ ≤ ∑ _w ∈ S.erase v, (1 : ℤ) := by
        apply Finset.sum_le_sum
        intro w _hw
        by_cases hi : c.Covers i w <;> by_cases hj : c.Covers j w <;>
          simp [coverIndicator, hi, hj]
      _ = _ := by simp
  have hsum := Finset.sum_erase_add S
    (fun w => c.coverIndicator i w - c.coverIndicator j w) hvS
  have hcardZ : ((S.erase v).card : ℤ) ≤ 1 := by exact_mod_cast hcard
  change (∑ w ∈ S.erase v, (c.coverIndicator i w - c.coverIndicator j w)) +
    (c.coverIndicator i v - c.coverIndicator j v) =
      ∑ w ∈ S, (c.coverIndicator i w - c.coverIndicator j w) at hsum
  rw [hroot, ← heq, ht] at hsum
  omega

/-- This switch changes only the internal coloring and continues to
avoid every fixed forbidden set. -/
theorem swapOn_avoidsVertices_of_transfer_two (c : G.EdgeColoring k)
    (F : Fin k → Finset V) (hc : c.AvoidsVertices F)
    (i j : Fin k) (hij : i ≠ j)
    (C : (c.twoColorGraph i j).ConnectedComponent)
    (ht : c.transfer i j univ (c.componentVertices i j C) = 2)
    (havoid : Disjoint (c.componentVertices i j C) (F j)) :
    (c.swapOn i j (c.componentVertices i j C) (c.component_closed i j C)).AvoidsVertices F := by
  intro r v hrv
  have hv := (c.swapOn_covers i j r (c.componentVertices i j C)
    (c.component_closed i j C) v).mp hrv
  by_cases hvC : v ∈ c.componentVertices i j C
  · rw [if_pos hvC] at hv
    by_cases hri : r = i
    · subst r
      rw [Equiv.swap_apply_left] at hv
      exact hc i v (c.covers_left_of_transfer_two i j hij C ht v hvC hv)
    · by_cases hrj : r = j
      · subst r
        exact fun hF => Finset.disjoint_left.mp havoid hvC hF
      · rw [Equiv.swap_apply_of_ne_of_ne hri hrj] at hv
        exact hc r v hv
  · rw [if_neg hvC] at hv
    exact hc r v hv

end Overfull.Multigraph.EdgeColoring
