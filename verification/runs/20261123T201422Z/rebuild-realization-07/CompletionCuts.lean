import Overfull.NativeReserve.NativeCutWeights

/-!
# Whole-cut certificates survive internal core completion

Completing a boundary only adds copies internal to the two old cores.
Those copies cross no whole-core shore, so surviving cut-copy sets agree
exactly before and after completion.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical ForceMatching

variable {V E J : Type*} [Fintype E]

theorem completed_surviving_whole_cut_eq (G : Multigraph V E)
    (U₀ U₁ Z X : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hX : X ∈ wholeUnions (originalCores U₀ U₁) Z)
    (F N : J → Finset E) (T : Finset J)
    (hFN : ∀ j ∈ T, F j ⊆ N j)
    (hadded : ∀ j ∈ T, ∀ e ∈ N j,
      e ∈ F j ∨ e ∈ G.internalOn univ U₀ ∨ e ∈ G.internalOn univ U₁) :
    G.cutEdges X \ removedCopies N T = G.cutEdges X \ removedCopies F T := by
  ext e
  constructor
  · intro he
    obtain ⟨heX, heN⟩ := mem_sdiff.mp he
    refine mem_sdiff.mpr ⟨heX, ?_⟩
    intro heF
    obtain ⟨j, hj, heF⟩ := (mem_removedCopies F T e).mp heF
    exact heN ((mem_removedCopies N T e).mpr ⟨j, hj, hFN j hj heF⟩)
  · intro he
    obtain ⟨heX, heF⟩ := mem_sdiff.mp he
    refine mem_sdiff.mpr ⟨heX, ?_⟩
    intro heN
    obtain ⟨j, hj, heN⟩ := (mem_removedCopies N T e).mp heN
    have hcut : e ∈ G.cutOn (N j) X := by
      rw [cutOn_eq_inter]
      exact mem_inter.mpr ⟨heN, heX⟩
    rw [completed_native_cutOn_eq G U₀ U₁ Z X h01 h0Z h1Z hX
      (F j) (N j) (hFN j hj) (hadded j hj), cutOn_eq_inter] at hcut
    exact heF ((mem_removedCopies F T e).mpr ⟨j, hj, (mem_inter.mp hcut).1⟩)

theorem completed_residual_whole_cutSize (G : Multigraph V E)
    (U₀ U₁ Z X : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hX : X ∈ wholeUnions (originalCores U₀ U₁) Z)
    (F N : J → Finset E) (T : Finset J)
    (hFN : ∀ j ∈ T, F j ⊆ N j)
    (hadded : ∀ j ∈ T, ∀ e ∈ N j,
      e ∈ F j ∨ e ∈ G.internalOn univ U₀ ∨ e ∈ G.internalOn univ U₁) :
    (residualGraph G N T).cutSize X = (residualGraph G F T).cutSize X := by
  rw [residual_cutSize, residual_cutSize,
    completed_surviving_whole_cut_eq G U₀ U₁ Z X h01 h0Z h1Z hX F N T hFN hadded]

theorem completed_whole_cut_certificates (G : Multigraph V E)
    (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (F N : J → Finset E) (T : Finset J)
    (hFN : ∀ j ∈ T, F j ⊆ N j)
    (hadded : ∀ j ∈ T, ∀ e ∈ N j,
      e ∈ F j ∨ e ∈ G.internalOn univ U₀ ∨ e ∈ G.internalOn univ U₁)
    (h : ℕ) (a : ℝ)
    (hodd : ∀ X ∈ wholeUnions (originalCores U₀ U₁) Z, X.card%2=1 →
      h ≤ (residualGraph G F T).cutSize X)
    (heven : ∀ X ∈ wholeUnions (originalCores U₀ U₁) Z, X.card%2=0 →
      2*a ≤ ((residualGraph G F T).cutSize X : ℝ) ∨
        G.cutEdges X \ removedCopies F T = G.cutEdges X) :
    (∀ X ∈ wholeUnions (originalCores U₀ U₁) Z, X.card%2=1 →
      h ≤ (residualGraph G N T).cutSize X) ∧
    (∀ X ∈ wholeUnions (originalCores U₀ U₁) Z, X.card%2=0 →
      2*a ≤ ((residualGraph G N T).cutSize X : ℝ) ∨
        G.cutEdges X \ removedCopies N T = G.cutEdges X) := by
  constructor
  · intro X hX hp
    rw [completed_residual_whole_cutSize G U₀ U₁ Z X h01 h0Z h1Z hX F N T hFN hadded]
    exact hodd X hX hp
  · intro X hX hp
    rw [completed_residual_whole_cutSize G U₀ U₁ Z X h01 h0Z h1Z hX F N T hFN hadded,
      completed_surviving_whole_cut_eq G U₀ U₁ Z X h01 h0Z h1Z hX F N T hFN hadded]
    exact heven X hX hp

end Overfull.NativeReserve
