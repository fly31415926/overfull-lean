import Overfull.TerminalFourOdd.PrefixResult
import Overfull.TerminalFourOdd.Selection
import Overfull.Terminal.Parameters
import Overfull.ResidualPalette.JoiningBounds

/-! Uniform original-host terminal prefixes for four odd covering robust cores. -/

noncomputable section

namespace Overfull.TerminalFourOdd

open Finset Classical SimpleGraph FourOdd NativeReserve ForeignPackingSchedule
open CircuitPatterns ForceMatching Terminal Compression

universe u

set_option maxHeartbeats 1200000 in
/-- The output robustness precedes every requested final error and core-order
threshold. All joining pieces and all completed perfect matchings are constructed
from the original regular host. No residual coloring is an input. -/
theorem exists_uniform_four_odd_prefix (α ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ α/8) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ τ/2 ∧
      ∀ η : ℝ, 0 < η → ∀ mFinal : ℕ,
        ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
          ∀ (V : Type u) [Fintype V] (G : SimpleGraph V)
            (U : Fin 4 → Finset V) (H : ∀ i, SimpleGraph (U i))
            (label : V → Fin 4) (h r₀ : ℕ) (a : ℝ) (F : Finset LabelPair),
            n₀ ≤ Fintype.card V →
            (∀ i, labelShore label {i} = U i) → (∀ i, (U i).card % 2 = 1) →
            (∀ v, G.degree v = h) → α*Fintype.card V ≤ (h : ℝ) →
            (∀ X : Finset V, ¬ IsOverfull G h X) →
            Pairwise (fun i j => Disjoint (U i) (U j)) →
            (∀ v, ∃ i, v ∈ U i) →
            (∀ i, α*Fintype.card V ≤ ((U i).card : ℝ)) →
            (∀ i, H i ≤ G.induce (U i : Set V)) →
            (∀ i, IsRobustExpander (H i) ν τ) →
            (∀ i v, (h : ℝ)-a ≤ ((H i).degree v : ℝ)) →
            0 ≤ a → a+1 ≤ ε*Fintype.card V →
            LabelForestShape F →
            (∀ p ∈ F, r₀ ≤ (pairPool (joiningQuotient (Multigraph.ofSimpleGraph G) label) p).card) →
            (h : ℝ)-r₀ ≤ ε*Fintype.card V →
            ∃ P : FourOddPrefix G U H label h a θ (τ/2),
              (∀ i, mFinal ≤ (U i).card) ∧
              (∀ i, (α/2)*(U i).card ≤ ((h-P.rounds : ℕ) : ℝ)) ∧
              (∀ i, a ≤ η*(U i).card) := by
  obtain ⟨Pack⟩ := exists_epoch_parameters.{u} α (α/2) τ ν
    hα hα1 (by positivity) hν hντ hτ
  refine ⟨Pack.output, Pack.output_pos, Pack.output_le, ?_⟩
  intro η hη mFinal
  obtain ⟨ε, hε, n₀, hn₀, hbase, hbounds⟩ :=
    exists_prefix_parameters α Pack.error (η*α) hα Pack.error_pos (mul_pos hη hα)
      (max Pack.order mFinal) ⌈4/α⌉₊
  let ε₀ := min ε (α/1000)
  have hε₀ : 0 < ε₀ := lt_min hε (by positivity)
  refine ⟨ε₀, hε₀, n₀, hn₀, ?_⟩
  intro V _ G U H label h r₀ a F hn hparts hodd hregular hdensity hno hdisj hcover hsize hembed
    hrobust hdegree ha herror hF hsupply hreserve
  letI : DecidableEq G.edgeSet := fun e f => propDecidable (e = f)
  let n := Fintype.card V
  let r := prefixRounds h
  let L := prefixCapacity α Pack.error n
  have herror' : a ≤ ε*n := by
    have hh := mul_le_mul_of_nonneg_right (min_le_left ε (α/1000))
      (Nat.cast_nonneg (Fintype.card V))
    dsimp [n, ε₀] at *
    linarith
  have hsmall : 1000*a ≤ (h : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right (min_le_right ε (α/1000))
      (Nat.cast_nonneg (Fintype.card V))
    dsimp [ε₀] at herror
    nlinarith
  have hnearly : 999*h ≤ 1000*r₀ := by
    have hh := mul_le_mul_of_nonneg_right (min_le_right ε (α/1000))
      (Nat.cast_nonneg (Fintype.card V))
    dsimp [ε₀] at hreserve
    have hr : (999 : ℝ)*h ≤ 1000*r₀ := by nlinarith
    exact_mod_cast hr
  have bounds (i : Fin 4) : PrefixBounds α Pack.error (η*α) n (U i).card h
      (max Pack.order mFinal) a :=
    hbounds n (U i).card h a hn (hsize i) (card_le_univ _) hdensity ha herror'
  have hrh : r ≤ h := (bounds 0).rounds_le
  have hfour : 4 ≤ h := by
    have hceil : (4 : ℝ)/α ≤ n := (Nat.le_ceil (4/α)).trans
      (Nat.cast_le.mpr (hbase.trans hn))
    have hd : (4 : ℝ) ≤ h := by
      have hh := (div_le_iff₀ hα).mp hceil
      dsimp [n] at hh
      nlinarith
    exact_mod_cast hd
  have hfourr : 4*r ≤ h := by dsimp [r,prefixRounds]; omega
  have hfinalOrder (i : Fin 4) : mFinal ≤ (U i).card :=
    (le_max_right _ _).trans (bounds i).order
  have hfinalDensity (i : Fin 4) : (α/2)*(U i).card ≤ ((h-r : ℕ) : ℝ) := by
    have hh := (bounds i).density
    have hm : ((U i).card : ℝ) ≤ n := by exact_mod_cast card_le_univ (U i)
    have hm' := mul_le_mul_of_nonneg_left hm hα.le
    dsimp [r]
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
  have hjoinDegreeReal (v : V) :
      ((Multigraph.ofSimpleGraph G).degreeOn (joiningCopies (Multigraph.ofSimpleGraph G) label) v : ℝ) ≤
        a := by
    obtain ⟨i, hi⟩ := hcover v
    let C := ForceMatching.embeddedCore G (U i) (H i) (hembed i)
    have hl : ∀ w ∈ U i, label w = i := by
      intro w hw
      rw [← hparts i] at hw
      simpa only [mem_labelShore, mem_singleton] using hw
    have hh := joining_degree_le_core_error (Multigraph.ofSimpleGraph G) label (U i) C i hl
      h a hregularM (hdegree i) ⟨v,hi⟩
    rw [← joiningGraph_degree_eq]
    exact hh
  have hjoinDegree (v : V) :
      (Multigraph.ofSimpleGraph G).degreeOn (joiningCopies (Multigraph.ofSimpleGraph G) label) v ≤
        ⌊a⌋₊ := Nat.le_floor (hjoinDegreeReal v)
  have makeCompletion (p : Fin 4 → ℕ)
      (B : PrefixPalette (Multigraph.ofSimpleGraph G) label r L p)
      (hp : ∀ i, (U i).card % 2 = p i) :
      Nonempty (BoundaryCompletion G U H (B.simpleBoundary G) r h a Pack.output (τ/2)) := by
    apply exists_prefix_completion α (α/2) ν τ Pack G U H label hparts hdisj hcover hembed
      h r L a p B hregular hrobust hdegree
    · exact fun i => (le_max_left _ _).trans (bounds i).order
    · intro i
      have hh : ((U i).card : ℝ) ≤ n := by exact_mod_cast card_le_univ (U i)
      exact (mul_le_mul_of_nonneg_left hh hα.le).trans hdensity
    · exact fun i => (bounds i).error
    · exact fun i => (bounds i).horizon
    · exact fun i => (bounds i).footprint
    · exact hp
  obtain ⟨D⟩ := exists_joining_decomposition (Multigraph.ofSimpleGraph G) label
    h r₀ a ha hregularM hnoM (fun i => by
      have heq : univ.filter (fun v => label v = i) = U i := by
        simpa only [labelShore, mem_singleton] using hparts i
      simpa only [heq] using hodd i)
    hjoinDegreeReal F hF hsupply hsmall hnearly
  obtain ⟨S,hSP,hS,hselection⟩ := exists_primary_center_or_singleton_selection
    (Multigraph.ofSimpleGraph G) label D.primary D.primary_profile r
      (by simpa only [D.primary_card] using hfourr)
  obtain ⟨B,hB,hBcard⟩ := exists_prefix_palette_of_selected (Multigraph.ofSimpleGraph G)
    label D S hSP hS hjoinDegree (bounds 0).capacity_pos (bounds 0).margin (bounds 0).budget
  have hBP : B.remaining ⊆ D.primary := by rw [hB]; exact sdiff_subset
  obtain ⟨C⟩ := makeCompletion (fun _ => 1) B hodd
  exact ⟨{
    rounds := r
    rounds_eq := rfl
    rounds_le := hrh
    boundary := B.simpleBoundary G
    completion := C
    remaining := B.remaining
    remaining_card := hBcard
    remaining_nonempty := B.remaining_nonempty
    remaining_card_le := fun M hM => D.primary_card_le M (hBP hM)
    remaining_matching := B.remaining_matching
    remaining_disjoint := B.remaining_disjoint
    remaining_eq := remaining_joining_copies G U H label hparts B C
    remaining_profile := fun M hM => D.primary_profile M (hBP hM)
    geometry := by simpa only [hB] using hselection
  }, hfinalOrder, hfinalDensity, hfinalError⟩

end Overfull.TerminalFourOdd
