import Overfull.TerminalFourTwoOdd.PrefixResult
import Overfull.Terminal.FourPalette
import Overfull.TerminalFourEven.Parameters
import Overfull.ResidualPalette.JoiningBounds

/-! Uniform original-host terminal prefixes for four covering robust cores. -/

noncomputable section

namespace Overfull.TerminalFourTwoOdd

open Finset Classical SimpleGraph FourOdd NativeReserve ForeignPackingSchedule
open CircuitPatterns ForceMatching Terminal TerminalFourEven

universe u

set_option maxHeartbeats 1200000 in
/-- The output robustness precedes every requested final error and core-order
threshold. All joining pieces and all completed perfect matchings are constructed
from the original regular host. No residual coloring is an input. -/
theorem exists_uniform_four_two_odd_prefix (α ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ α/8) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ τ/2 ∧
      ∀ η : ℝ, 0 < η → ∀ mFinal : ℕ,
        ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
          ∀ (V : Type u) [Fintype V] (G : SimpleGraph V)
            (U : Fin 4 → Finset V) (H : ∀ i, SimpleGraph (U i))
            (label : V → Fin 4) (x y : Fin 4) (h : ℕ) (a : ℝ),
            n₀ ≤ Fintype.card V →
            (∀ i, labelShore label {i} = U i) → x ≠ y →
            (∀ i, (U i).card % 2 = if i=x ∨ i=y then 1 else 0) →
            (∀ v, G.degree v = h) → α*Fintype.card V ≤ (h : ℝ) →
            (∀ X : Finset V, ¬ IsOverfull G h X) →
            Pairwise (fun i j => Disjoint (U i) (U j)) →
            (∀ v, ∃ i, v ∈ U i) →
            (∀ i, α*Fintype.card V ≤ ((U i).card : ℝ)) →
            (∀ i, H i ≤ G.induce (U i : Set V)) →
            (∀ i, IsRobustExpander (H i) ν τ) →
            (∀ i v, (h : ℝ)-a ≤ ((H i).degree v : ℝ)) →
            0 ≤ a → a+1 ≤ ε*Fintype.card V →
            ∃ P : FourTwoOddPrefix G U H label x y h a θ (τ/2),
              (∀ i, mFinal ≤ (U i).card) ∧
              ((α/2)*Fintype.card V ≤ ((h-P.rounds : ℕ) : ℝ)) ∧
              (∀ i, a ≤ η*(U i).card) := by
  obtain ⟨Pack⟩ := exists_epoch_parameters.{u} α (α/2) τ ν
    hα hα1 (by positivity) hν hντ hτ
  refine ⟨Pack.output, Pack.output_pos, Pack.output_le, ?_⟩
  intro η hη mFinal
  obtain ⟨ε, hε, n₀, hn₀, _hbase, hbounds⟩ :=
    exists_four_prefix_parameters α Pack.error (η*α) hα Pack.error_pos (mul_pos hη hα)
      (max Pack.order mFinal) 0
  refine ⟨ε, hε, n₀, hn₀, ?_⟩
  intro V _ G U H label x y h a hn hparts hxy hparity hregular hdensity hno hdisj hcover hsize hembed
    hrobust hdegree ha herror
  let n := Fintype.card V
  let r := prefixRounds h
  let L := prefixCapacity α (Pack.error/2) n
  have herror' : a ≤ ε*n := by dsimp [n]; linarith
  have bounds (i : Fin 4) : FourPrefixBounds α Pack.error (η*α) n (U i).card h
      (max Pack.order mFinal) a :=
    hbounds n (U i).card h a hn (hsize i) (card_le_univ _) hdensity ha herror'
  have hrh : r ≤ h := (bounds 0).rounds_le
  have hfinalOrder (i : Fin 4) : mFinal ≤ (U i).card :=
    (le_max_right _ _).trans (bounds i).order
  have hfinalDensity : (α/2)*Fintype.card V ≤ ((h-r : ℕ) : ℝ) := by
    have hh := (bounds 0).density
    change α*Fintype.card V/2 ≤ ((h-r : ℕ) : ℝ) at hh
    linarith
  have hnpos : 0 < Fintype.card V := lt_of_lt_of_le hn₀ hn
  obtain ⟨v₀⟩ := Fintype.card_pos_iff.mp hnpos
  have hhn : h ≤ n := by
    have hh := G.degree_lt_card_verts v₀
    rw [hregular] at hh
    exact hh.le
  have hfinalError (i : Fin 4) : a ≤ η*(U i).card := by
    have hh := (bounds i).final_error
    have hs : ((h-r : ℕ) : ℝ) ≤ n := by exact_mod_cast (Nat.sub_le h r).trans hhn
    have hs' := mul_le_mul_of_nonneg_left hs (mul_pos hη hα).le
    have hm := mul_le_mul_of_nonneg_left (hsize i) hη.le
    dsimp [r] at hs'
    nlinarith only [hh, hs', hm]
  have hregularM : ∀ v, (Multigraph.ofSimpleGraph G).degree v = h := by
    simpa only [Multigraph.ofSimpleGraph_degree] using hregular
  have hnoM : ∀ X : Finset V, ¬ (Multigraph.ofSimpleGraph G).IsOverfull h X := by
    intro X
    simpa only [Multigraph.IsOverfull, Multigraph.ofSimpleGraph_internalEdges] using hno X
  have hjoinDegree (v : V) :
      (Multigraph.ofSimpleGraph G).degreeOn (joiningCopies (Multigraph.ofSimpleGraph G) label) v ≤
        ⌊a⌋₊ := by
    obtain ⟨i, hi⟩ := hcover v
    let C := ForceMatching.embeddedCore G (U i) (H i) (hembed i)
    have hl : ∀ w ∈ U i, label w = i := by
      intro w hw
      rw [← hparts i] at hw
      simpa only [mem_labelShore, mem_singleton] using hw
    have hh := joining_degree_le_core_error (Multigraph.ofSimpleGraph G) label (U i) C i hl
      h a hregularM (hdegree i) ⟨v,hi⟩
    rw [← joiningGraph_degree_eq]
    exact Nat.le_floor hh
  have makeCompletion (p : Fin 4 → ℕ)
      (B : PrefixPalette (Multigraph.ofSimpleGraph G) label r (2*L) p)
      (hp : ∀ i, (U i).card % 2 = p i) :
      Nonempty (BoundaryCompletion G U H (B.simpleBoundary G) r h a Pack.output (τ/2)) := by
    apply exists_prefix_completion α (α/2) ν τ Pack G U H label hparts hdisj hcover hembed
      h r (2*L) a p B hregular hrobust hdegree
    · exact fun i => (le_max_left _ _).trans (bounds i).order
    · intro i
      have hh : ((U i).card : ℝ) ≤ n := by exact_mod_cast card_le_univ (U i)
      exact (mul_le_mul_of_nonneg_left hh hα.le).trans hdensity
    · exact fun i => (bounds i).error
    · exact fun i => (bounds i).horizon
    · exact fun i => (bounds i).footprint
    · exact hp
  obtain ⟨D⟩ := exists_fourTwoOddJoining_decomposition
    (Multigraph.ofSimpleGraph G) label x y hxy h (by decide) hregularM hnoM (fun i => by
      have hf : univ.filter (fun v => label v = i) = U i := by
        simpa only [labelShore, mem_singleton] using hparts i
      rw [hf]
      exact hparity i)
  obtain ⟨B,hBcard,hBP⟩ := exists_four_two_odd_prefix_palette
    (Multigraph.ofSimpleGraph G) label D hrh hjoinDegree
    (bounds 0).capacity_pos (bounds 0).margin (bounds 0).budget
  obtain ⟨C⟩ := makeCompletion (fun i => if i=x ∨ i=y then 1 else 0) B hparity
  refine ⟨{
    rounds := r
    rounds_le := hrh
    boundary := B.simpleBoundary G
    completion := C
    remaining := B.remaining
    remaining_nonempty := B.remaining_nonempty
    remaining_matching := B.remaining_matching
    remaining_disjoint := B.remaining_disjoint
    remaining_eq := remaining_joining_copies G U H label hparts B C
    remaining_card := hBcard
    remaining_cut := by
      intro M hM i hi
      simpa only [hparts] using D.primary_cut_eq_one M (hBP hM) i hi
    remaining_parity := by
      intro M hM i
      have hp := D.primary_odd_cut_iff M (hBP hM) i
      rw [hparts] at hp
      rw [hparity]
      by_cases hi : i=x ∨ i=y
      · rw [if_pos hi]
        exact Nat.odd_iff.mp (hp.mpr hi)
      · rw [if_neg hi]
        have hh := hp.not.mpr hi
        rw [Nat.odd_iff] at hh
        omega
  }, hfinalOrder,hfinalDensity,hfinalError⟩

end Overfull.TerminalFourTwoOdd
