import Overfull.Terminal.CentralFactorization
import Overfull.Terminal.OddGluing
import Overfull.NativeTerminal.ShoreFactorization

/-!
# Terminal coloring with exactly two odd covering cores

The supplied data are actual residual joining matchings, not a coloring or
factorization.  Their singleton cuts construct both apex degrees and the
central odd-cut certificate.  The central and odd-leaf colorings are obtained
from completed factorization theorems and glued on the original edge copies.
-/

noncomputable section

namespace Overfull.Terminal

open Finset Classical Multigraph SmallCuts BoundaryExtension NativeTerminal

set_option maxHeartbeats 1000000 in
theorem exists_uniform_two_odd_coloring (α ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ α / 64) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (V E : Type*) [Fintype E] (G : Multigraph V E)
        (U A B : Finset V) (C₀ : Core G U) (C₁ : Core G A) (C₂ : Core G B)
        (k : ℕ) (a : ℝ),
        Disjoint U A → Disjoint U B → Disjoint A B →
        (∀ v, v ∈ U ∨ v ∈ A ∨ v ∈ B) →
        Even U.card → Odd A.card → Odd B.card →
        m₀ ≤ U.card → m₀ ≤ A.card → m₀ ≤ B.card →
        (∀ v, G.degree v = k) →
        α * U.card ≤ (k : ℝ) → α * A.card ≤ (k : ℝ) → α * B.card ≤ (k : ℝ) →
        IsRobustExpander C₀.graph ν τ → IsRobustExpander C₁.graph ν τ →
        IsRobustExpander C₂.graph ν τ →
        a ≤ ε * U.card → a ≤ ε * A.card → a ≤ ε * B.card →
        (∀ v, (k : ℝ) - a ≤ (C₀.graph.degree v : ℝ)) →
        (∀ v, (k : ℝ) - a ≤ (C₁.graph.degree v : ℝ)) →
        (∀ v, (k : ℝ) - a ≤ (C₂.graph.degree v : ℝ)) →
        (M : Fin k → Finset E) → (∀ i, G.IsMatching (M i)) →
        Pairwise (fun i j => Disjoint (M i) (M j)) →
        univ.biUnion M = G.cutEdges A ∪ G.cutEdges B →
        (∀ i, (M i ∩ G.cutEdges A).card = 1) →
        (∀ i, (M i ∩ G.cutEdges B).card = 1) →
        Nonempty (G.EdgeColoring k) := by
  obtain ⟨εC,hεC,mC,hcentral⟩ := exists_uniform_central_coloring α ν τ hα hα1 hν hντ hτ
  have hτleaf : τ ≤ min α 1 / 16 := by rw [min_eq_left hα1]; linarith
  obtain ⟨εL,hεL,mL,hleaf⟩ := exists_uniform_shore_coloring α ν τ 0 hα hν hντ hτleaf
  refine ⟨min εC εL,lt_min hεC hεL,max mC mL,?_⟩
  intro V E _ G U A B C₀ C₁ C₂ k a hUA hUB hAB hcover hU hA hB
    hmU hmA hmB hregular hkU hkA hkB hrobU hrobA hrobB haU haA haB
    hdegU hdegA hdegB M hM hdisj hparts hcrossA hcrossB
  have hcutA : G.cutSize A = k := cutSize_of_matching_partition G A k M hdisj
    (by
      intro e he
      have hp : e ∈ univ.biUnion M := by rw [hparts]; exact mem_union_left _ he
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp hp
      exact ⟨i,hi⟩) hcrossA
  have hcutB : G.cutSize B = k := cutSize_of_matching_partition G B k M hdisj
    (by
      intro e he
      have hp : e ∈ univ.biUnion M := by rw [hparts]; exact mem_union_right _ he
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp hp
      exact ⟨i,hi⟩) hcrossB
  have haUC : a ≤ εC * U.card := haU.trans
    (mul_le_mul_of_nonneg_right (min_le_left εC εL) (Nat.cast_nonneg U.card))
  obtain ⟨c⟩ := hcentral (CentralVertex U) (CentralEdge G U A) (centralGraph G U A)
    (centralCoreVertices U) (centralCore C₀ A) k a
    (by simpa only [centralCoreVertices_card] using (le_max_left mC mL).trans hmU)
    (central_even_order U hU) (by simp)
    (central_regular G U A B k hUA hUB hAB hcover (fun v _ => hregular v) hcutA hcutB)
    (by simpa only [centralCoreVertices_card] using hkU)
    (centralCore_robust C₀ A ν τ hrobU)
    (by simpa only [centralCoreVertices_card] using haUC)
    (by intro v; rw [centralCore_degree]; exact hdegU _)
    (fun i => centralMatching G U A (M i))
    (fun i => centralMatching_isMatching G U A B hUA hUB hAB hcover (M i) (hM i)
      (hcrossA i).le (hcrossB i).le)
    (centralMatching_external_cover G U A B hUA hUB hAB hcover k M hparts)
  have haAL : a ≤ εL * A.card := haA.trans
    (mul_le_mul_of_nonneg_right (min_le_right εC εL) (Nat.cast_nonneg A.card))
  have haBL : a ≤ εL * B.card := haB.trans
    (mul_le_mul_of_nonneg_right (min_le_right εC εL) (Nat.cast_nonneg B.card))
  obtain ⟨_,hfactorA⟩ := hleaf V E G A A C₁ k a subset_rfl
    ((le_max_right mC mL).trans hmA) (by simp) (fun v _ => hregular v) hkA hrobA haAL hdegA
    (by ext e; simp)
  obtain ⟨_,hfactorB⟩ := hleaf V E G B B C₂ k a subset_rfl
    ((le_max_right mC mL).trans hmB) (by simp) (fun v _ => hregular v) hkB hrobB haBL hdegB
    (by ext e; simp)
  obtain ⟨cA⟩ := hfactorA hcutA hA (by intro e he v hv hvA; exact hvA)
  obtain ⟨cB⟩ := hfactorB hcutB hB (by intro e he v hv hvB; exact hvB)
  exact glue_central_and_odd_leaves G U A B k hUA hUB hAB hcover hcutA hcutB c cA cB

end Overfull.Terminal
