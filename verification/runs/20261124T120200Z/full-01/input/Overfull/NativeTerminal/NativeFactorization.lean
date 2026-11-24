import Overfull.NativeTerminal.Factorization
import Overfull.NativeTerminal.PrefixGeometry

/-!
# Factorization of the actual protected native residual

All assigned-shore geometry is derived from the selected original reserve
copies.  The uniform terminal theorem constructs the coloring of the actual
twice-residual graph under its retained robust-core estimates.
-/

noncomputable section

namespace Overfull.NativeTerminal

open Finset Classical SmallCuts NativeReserve AssignedParts FourOdd

/-- Uniformly factor every endpoint-preserving native residual whose external
image is exactly the selected reserve union. All shore hypotheses are derived. -/
theorem exists_uniform_native_image_factorization (α ν τ : ℝ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ min α 1 / 16) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (V E F : Type*) [Fintype E] [Fintype F]
        (G : Multigraph V E) (H : Multigraph V F) (U₀ U₁ Z : Finset V)
        (M : Finset E) (r k : ℕ) (Q : NativeReserve.BoundaryPacking G U₀ U₁ Z M r)
        (q : Fin k → Fin r) (ι : CopyEmbedding G H)
        (C₀ : Core H U₀) (C₁ : Core H U₁) (a : ℝ),
        G.IsPerfectMatching M → Disjoint U₀ U₁ → Disjoint U₀ Z → Disjoint U₁ Z →
        (∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) → Z.card ≤ 2 → Function.Injective q →
        (externalCopies H U₀ U₁).image ι.map = BoundaryPacking.selectedUnion Q q →
        m₀ ≤ U₀.card → m₀ ≤ U₁.card → (∀ v, H.degree v = k) →
        α * U₀.card ≤ (k : ℝ) → α * U₁.card ≤ (k : ℝ) →
        IsRobustExpander C₀.graph ν τ → IsRobustExpander C₁.graph ν τ →
        a ≤ ε * U₀.card → a ≤ ε * U₁.card →
        (∀ v, (k : ℝ)-a ≤ (C₀.graph.degree v : ℝ)) →
        (∀ v, (k : ℝ)-a ≤ (C₁.graph.degree v : ℝ)) →
        Nonempty (H.EdgeColoring k) := by
  obtain ⟨ε,hε,m₀,hfactor⟩ := exists_uniform_two_shore_factorization α ν τ 2 hα hν hντ hτ
  refine ⟨ε,hε,m₀,?_⟩
  intro V E F _ _ G H U₀ U₁ Z M r k Q q ι C₀ C₁ a hM h01 h0Z h1Z hcover hZ hq
    himage hm₀ hm₁ hregular hdense₀ hdense₁ hrob₀ hrob₁ ha₀ ha₁ hdegree₀ hdegree₁
  let A₀ := corePart G M Z U₀
  let A₁ := corePart G M Z U₁
  let B := pairPart G M Z
  obtain ⟨hc₀,_hc₁,hcuts,hpair,hstar₀,hstar₁⟩ :=
    residual_geometry Q hM h01 h0Z h1Z hcover hZ q ι himage hq
  have hpar : A₀.card % 2 = A₁.card % 2 := by
    dsimp only [A₀,A₁]
    rw [perfectMatching_shore_card_parity G hM,
      perfectMatching_shore_card_parity G hM,
      coreParts_cutOn_eq G (hM.isMatching G) U₀ U₁ Z h01 h0Z h1Z hcover]
  have hcase : (Even A₀.card ∧ Even A₁.card ∧ H.cutEdges A₀ = ∅) ∨
      (Odd A₀.card ∧ Odd A₁.card ∧ H.cutSize A₀ = k) := by
    by_cases hp : A₀.card % 2 = 0
    · refine Or.inl ⟨Nat.even_iff.mpr hp,Nat.even_iff.mpr (hpar.symm.trans hp),?_⟩
      apply card_eq_zero.mp
      change H.cutSize A₀ = 0
      simpa only [A₀,hp,mul_zero] using hc₀
    · have hp' : A₀.card % 2 = 1 := by omega
      refine Or.inr ⟨Nat.odd_iff.mpr hp',Nat.odd_iff.mpr (hpar.symm.trans hp'),?_⟩
      simpa only [A₀,hp',mul_one] using hc₀
  exact hfactor V F H U₀ U₁ A₀ A₁ B C₀ C₁ k a
    (coreParts_disjoint G (hM.isMatching G) U₀ U₁ Z h01 h0Z h1Z)
    (corePart_pairPart_disjoint G (hM.isMatching G) U₀ Z h0Z)
    (corePart_pairPart_disjoint G (hM.isMatching G) U₁ Z h1Z)
    (coreParts_cover G hM U₀ U₁ Z hcover)
    (core_subset_corePart G M Z U₀) (core_subset_corePart G M Z U₁)
    hm₀ hm₁ ((corePart_sdiff_card_le G M Z U₀).trans hZ)
    ((corePart_sdiff_card_le G M Z U₁).trans hZ)
    ((card_le_card (pairPart_subset G M Z)).trans hZ)
    hpair hregular hdense₀ hdense₁ hrob₀ hrob₁ ha₀ ha₁ hdegree₀ hdegree₁
    hstar₀ hstar₁ hcuts hcase

/-- The concrete native prefix residual is colorable from the exact image
remainder returned by prefix completion and its retained core estimates. -/
theorem exists_uniform_native_residual_factorization (α ν τ : ℝ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ min α 1 / 16) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (V E J K : Type*) [Fintype E]
        (G : Multigraph V E) (U₀ U₁ Z : Finset V) (M : Finset E)
        (r k : ℕ) (Q : NativeReserve.BoundaryPacking G U₀ U₁ Z M r)
        (q : Fin k → Fin r) (N : J → Finset E) (T : Finset J)
        (W : K → Finset {e : E // e ∉ removedCopies N T}) (S : Finset K)
        (C₀ : Core (residualGraph (residualGraph G N T) W S) U₀)
        (C₁ : Core (residualGraph (residualGraph G N T) W S) U₁) (a : ℝ),
        G.IsPerfectMatching M → Disjoint U₀ U₁ → Disjoint U₀ Z → Disjoint U₁ Z →
        (∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) → Z.card ≤ 2 → Function.Injective q →
        (∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ)) →
        (survivingCopies (removedCopies W S)
          (joiningCopies (residualGraph G N T) (assignedLabel G M U₀ U₁ Z) ∪
            exceptionalCopies (residualGraph G N T) univ Z)).image Subtype.val =
          univ.biUnion (fun i => Q.residualBoundary N T (q i)) →
        m₀ ≤ U₀.card → m₀ ≤ U₁.card →
        (∀ v, (residualGraph (residualGraph G N T) W S).degree v = k) →
        α * U₀.card ≤ (k : ℝ) → α * U₁.card ≤ (k : ℝ) →
        IsRobustExpander C₀.graph ν τ → IsRobustExpander C₁.graph ν τ →
        a ≤ ε * U₀.card → a ≤ ε * U₁.card →
        (∀ v, (k : ℝ)-a ≤ (C₀.graph.degree v : ℝ)) →
        (∀ v, (k : ℝ)-a ≤ (C₁.graph.degree v : ℝ)) →
        Nonempty ((residualGraph (residualGraph G N T) W S).EdgeColoring k) := by
  obtain ⟨ε,hε,m₀,hfactor⟩ := exists_uniform_native_image_factorization α ν τ hα hν hντ hτ
  refine ⟨ε,hε,m₀,?_⟩
  intro V E J K _ G U₀ U₁ Z M r k Q q N T W S C₀ C₁ a hM h01 h0Z h1Z hcover hZ hq
    havoid hrem hm₀ hm₁ hregular hdense₀ hdense₁ hrob₀ hrob₁ ha₀ ha₁ hdegree₀ hdegree₁
  exact hfactor V E _ G (residualGraph (residualGraph G N T) W S) U₀ U₁ Z M r k Q q
    (twiceResidualEmbedding G N T W S) C₀ C₁ a hM h01 h0Z h1Z hcover hZ hq
    (twiceResidual_external_image G U₀ U₁ Z hM h01 h0Z h1Z hcover r k Q q N T havoid W S hrem)
    hm₀ hm₁ hregular hdense₀ hdense₁ hrob₀ hrob₁ ha₀ ha₁ hdegree₀ hdegree₁

end Overfull.NativeTerminal
