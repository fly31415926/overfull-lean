import Overfull.NativeTerminal.NativeFactorization
import Overfull.NativeTerminal.TerminalParameters
import Overfull.NativeTerminal.Reassembly
import Overfull.NativeCore.NativePrefix

/-!
# Completing the entire native residual factorization

The nonprotected colors are first completed to actual perfect matchings.
The protected residual is then factored through its exact native shore
geometry.  Reassembly colors every original residual copy with its degree.
All error and order parameters are chosen before the host and its reserve.
-/

noncomputable section

namespace Overfull.NativeTerminal

open Finset Classical SmallCuts NativeReserve NativeCore AssignedParts FourOdd

set_option maxHeartbeats 1200000 in
/-- Uniformly factor the actual native residual from its reserve and two
robust old cores. No terminal coloring or protected factorization is an input. -/
theorem exists_uniform_native_remaining_factorization (α β ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ α/240) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (V E J : Type*) [Fintype V] [Fintype E]
        (G : Multigraph V E) (U₀ U₁ Z : Finset V) (M : Finset E)
        (r : ℕ) (Q : BoundaryPacking G U₀ U₁ Z M r)
        (N : J → Finset E) (T : Finset J) (h : ℕ) (a : ℝ)
        (C₀ : Core (residualGraph G N T) U₀)
        (C₁ : Core (residualGraph G N T) U₁),
        n₀ ≤ Fintype.card V → G.IsPerfectMatching M →
        Disjoint U₀ U₁ → Disjoint U₀ Z → Disjoint U₁ Z →
        (∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) → Z.card ≤ 2 →
        β * Fintype.card V ≤ U₀.card → β * Fintype.card V ≤ U₁.card →
        α * Fintype.card V / 30 ≤ r → r ≤ h →
        (∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ)) →
        (∀ v, (residualGraph G N T).degree v = h) →
        (∀ X : Finset V, ¬ (residualGraph G N T).IsOverfull h X) →
        IsRobustExpander C₀.graph ν τ → IsRobustExpander C₁.graph ν τ →
        (∀ v, (h : ℝ)-a ≤ (C₀.graph.degree v : ℝ)) →
        (∀ v, (h : ℝ)-a ≤ (C₁.graph.degree v : ℝ)) →
        max a ((h : ℝ)-r) ≤ δ * Fintype.card V →
        Nonempty ((residualGraph G N T).EdgeColoring h) := by
  obtain ⟨hσ,hσhalf,hσsmall⟩ := terminal_robust_range α hα hα1
  obtain ⟨δ₀,θ₀,hδ₀,hθ₀,nPrefix,hnPrefix,hprefix⟩ :=
    exists_uniform_native_unprotected_prefix α β ν τ (α/3840)
      hα hα1 hβ hν hντ hτ hσ hσhalf
  let θ := min θ₀ (α/3840)
  have hθ : 0 < θ := lt_min hθ₀ hσ
  have hθrange : θ ≤ α/3840 := min_le_right _ _
  obtain ⟨ε,hε,m₀,hterminal⟩ :=
    exists_uniform_native_residual_factorization (α/120) θ (α/3840)
      (div_pos hα (by norm_num)) hθ hθrange hσsmall
  obtain ⟨δ,hδ,hδ₀',n₀,hn₀,hnBase,hparams⟩ :=
    exists_uniform_terminal_parameters α β ε δ₀ hα hβ hε hδ₀ m₀ nPrefix
  refine ⟨δ,hδ,n₀,hn₀,?_⟩
  intro V E J _ _ G U₀ U₁ Z M r Q N T h a C₀ C₁ hn hM h01 h0Z h1Z
    hcover hZ hsize₀ hsize₁ hr hrh havoid hregular hno hrob₀ hrob₁ hdegree₀ hdegree₁ herror
  let H := residualGraph G N T
  have hnPrefix' : nPrefix ≤ Fintype.card V := hnBase.trans hn
  have herror₀ : max a ((h : ℝ)-r) ≤ δ₀ * Fintype.card V := herror.trans
    (mul_le_mul_of_nonneg_right hδ₀' (Nat.cast_nonneg _))
  have ha : a ≤ δ * Fintype.card V := (le_max_left _ _).trans herror
  obtain ⟨hm₀,hdensity₀,ha₀⟩ := hparams (Fintype.card V) U₀.card r a
    hn hsize₀ (card_le_univ U₀) hr ha
  obtain ⟨hm₁,hdensity₁,ha₁⟩ := hparams (Fintype.card V) U₁.card r a
    hn hsize₁ (card_le_univ U₁) hr ha
  obtain ⟨q,W,C₀',C₁',hq,hWm,hWd,_hWA,hWregular,hWrob₀,hWrob₁,hWdegree₀,hWdegree₁,
    _hrem,_hsurvive,himage⟩ :=
    hprefix V E J G U₀ U₁ Z M r Q N T h a C₀ C₁ hnPrefix' hM h01 h0Z h1Z
      hcover hZ hsize₀ hsize₁ hr hrh havoid hregular hno hrob₀ hrob₁
      hdegree₀ hdegree₁ herror₀
  have hterminalRob₀ : IsRobustExpander C₀'.graph θ (α/3840) :=
    IsRobustExpander.mono_parameter _ hWrob₀ (min_le_left _ _)
  have hterminalRob₁ : IsRobustExpander C₁'.graph θ (α/3840) :=
    IsRobustExpander.mono_parameter _ hWrob₁ (min_le_left _ _)
  obtain ⟨c⟩ := hterminal V E J (Fin (h-r/2)) G U₀ U₁ Z M r (r/2) Q q N T W univ
    C₀' C₁' a hM h01 h0Z h1Z hcover hZ hq havoid himage hm₀ hm₁
    hWregular hdensity₀ hdensity₁ hterminalRob₀ hterminalRob₁ ha₀ ha₁ hWdegree₀ hWdegree₁
  have hremain : h-r/2+r/2 = h :=
    Nat.sub_add_cancel ((Nat.div_le_self r 2).trans hrh)
  have cH := reassembledColoring H W (fun j => (hWm j).isMatching H) c
  exact ⟨hremain ▸ cH⟩

end Overfull.NativeTerminal
