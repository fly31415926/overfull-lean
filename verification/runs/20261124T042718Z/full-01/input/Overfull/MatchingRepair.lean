import Overfull.MatchingRepairStep
import Overfull.MatchingRepairLoad
import Overfull.MatchingRepairAccounting
import Overfull.MatchingRepairParameters
import Overfull.MatchingRepairFamily

/-!
# Repairing a bounded family of almost perfect matchings

The internal reserve incidences have a fixed integral capacity. The
prescribed uncovered sets account for the endpoint incidences. Each
matching is completed in the actual unused reserve, protecting every
covered vertex already at the internal capacity.
-/

namespace Overfull.MatchingRepair

open Finset Classical SimpleGraph
open scoped BigOperators
open BipartitePackingAccounting OrdinaryPackingWorking MatchingRepairLoad

variable {V I : Type*} [Fintype V]

structure Invariant (G R : SimpleGraph V) (M N : I → G.Subgraph)
    (X Y : I → Finset V) (T : Finset I) (m ℓ : ℕ) (μ δ : ℝ) : Prop where
  matching : ∀ i ∈ T, (N i).IsMatching
  verts : ∀ i ∈ T, (N i).verts = (X i : Set V)ᶜ
  edges : ∀ i ∈ T, (N i).spanningCoe ≤ (M i).spanningCoe ⊔ R
  disjoint : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
    Disjoint (N i).spanningCoe (N j).spanningCoe
  capacity : ∀ v, internalLoad G R N Y T v ≤ Nat.floor ((μ/2)*m)
  total : (∑ v, (reserveLoad G R N T v : ℝ)) ≤ T.card * ℓ * δ * m

theorem invariant_empty (G R : SimpleGraph V) (M : I → G.Subgraph)
    (X Y : I → Finset V) (m ℓ : ℕ) (μ δ : ℝ) :
    Invariant G R M M X Y ∅ m ℓ μ δ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp
  · simp
  · intro v; simp
  · simp

theorem Invariant.load_le [Fintype I] {G R : SimpleGraph V}
    {M N : I → G.Subgraph} {X Y : I → Finset V} {T : Finset I}
    {m ℓ : ℕ} {μ δ : ℝ} (hN : Invariant G R M N X Y T m ℓ μ δ)
    (hμ : 0 ≤ μ) (hδμ : δ ≤ μ/2)
    (hY : ∀ v, (endpointCount Y univ v : ℝ) ≤ δ*m) (v : V) :
    (reserveLoad G R N T v : ℝ) ≤ μ*m := by
  have hh := actual_load_le_internal_add_endpoints G R N Y T
    hN.matching hN.disjoint v
  have hhR : (reserveLoad G R N T v : ℝ) ≤
      internalLoad G R N Y T v + endpointCount Y T v := by exact_mod_cast hh
  have hc : (internalLoad G R N Y T v : ℝ) ≤ Nat.floor ((μ/2)*m) := by
    exact_mod_cast hN.capacity v
  have hf := Nat.floor_le (show 0 ≤ (μ/2)*(m : ℝ) by positivity)
  have he : (endpointCount Y T v : ℝ) ≤ endpointCount Y univ v := by
    exact_mod_cast endpointCount_mono Y T univ (subset_univ T) v
  have hd := mul_le_mul_of_nonneg_right hδμ (Nat.cast_nonneg m (α := ℝ))
  linarith only [hhR, hc, hf, he, hY v, hd]

theorem Invariant.internal_total_le [Fintype I] {G R : SimpleGraph V}
    {M N : I → G.Subgraph} {X Y : I → Finset V} {T : Finset I}
    {m ℓ : ℕ} {μ δ b : ℝ} (hN : Invariant G R M N X Y T m ℓ μ δ)
    (hδ : 0 ≤ δ) (hI : (Fintype.card I : ℝ) ≤ b*m) :
    (∑ v, (internalLoad G R N Y T v : ℝ)) ≤ b*ℓ*δ*(m : ℝ)^2 := by
  have hcard : (T.card : ℝ) ≤ Fintype.card I := by exact_mod_cast card_le_univ T
  have hc : (T.card : ℝ) ≤ b*m := hcard.trans hI
  have ht := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ (ℓ : ℝ)*δ*m by positivity)
  calc
    _ ≤ ∑ v, (reserveLoad G R N T v : ℝ) := by
      exact_mod_cast total_internal_le_actual G R N Y T hN.disjoint
    _ ≤ T.card*ℓ*δ*m := hN.total
    _ ≤ b*ℓ*δ*(m : ℝ)^2 := by nlinarith only [ht]

theorem reserve_union_degree (G R : SimpleGraph V) (N : I → G.Subgraph)
    (T : Finset I) (v : V) :
    (edgeUnion (fun i => (N i).spanningCoe ⊓ R) T).degree v =
      reserveLoad G R N T v := by
  have heq : edgeUnion (fun i => (N i).spanningCoe ⊓ R) T =
      R ⊓ edgeUnion (fun i => (N i).spanningCoe) T := by
    ext x y
    simp only [edgeUnion_adj, SimpleGraph.inf_adj]
    aesop
  simp only [reserveLoad, ← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card, heq]

set_option maxHeartbeats 2000000 in
/-- Uniform reserve repair. The matchings are constructed from the actual
reserve graph, and both degree bounds concern unions of actual edges. -/
theorem reserve_repair (b ζ ν τ : ℝ)
    (hb : 0 < b) (hζ : 0 < ζ) (hν : 0 < ν) (hντ : ν ≤ 4*τ)
    (hτ : τ ≤ 1/16) (hτζ : 16*τ ≤ ζ/3) :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
      ∃ δ : ℝ, 0 < δ ∧ ∃ m₀ : ℕ,
        ∀ (V : Type*) [Fintype V] [DecidableEq V]
          (G R : SimpleGraph V), R ≤ G → ∀ (m r : ℕ),
          Fintype.card V = m → m₀ ≤ m → Even m → (r : ℝ) ≤ b*m →
          (∀ v, ζ*m ≤ (R.degree v : ℝ)) → IsRobustExpander R ν τ →
          ∀ (M : Fin r → G.Subgraph) (X : Fin r → Finset V),
            (∀ i, (M i).IsMatching) →
            Pairwise (fun i j => Disjoint (M i).spanningCoe (M j).spanningCoe) →
            (∀ i, Disjoint (M i).spanningCoe R) →
            (∀ i, (M i).verts ⊆ (X i : Set V)ᶜ) →
            (∀ i, Even (X i).card) →
            (∀ i, ((X i).card : ℝ) ≤ δ*m) →
            (∀ i, ((uncoveredOutside G (M i) (X i)).card : ℝ) ≤ δ*m) →
            (∀ v, ((univ.filter (fun i : Fin r =>
              v ∈ uncoveredOutside G (M i) (X i))).card : ℝ) ≤ δ*m) →
            ∃ N : Fin r → G.Subgraph,
              (∀ i, (N i).IsMatching) ∧
              (∀ i, (N i).verts = (X i : Set V)ᶜ) ∧
              (∀ i, (N i).spanningCoe ≤ (M i).spanningCoe ⊔ R) ∧
              Pairwise (fun i j => Disjoint (N i).spanningCoe (N j).spanningCoe) ∧
              (∀ v, ((edgeUnion (fun i => (N i).spanningCoe ⊓ R) univ).degree v : ℝ)
                ≤ μ*m) ∧
              (∀ v, ((edgeUnion (fun i => (M i).spanningCoe \ (N i).spanningCoe)
                univ).degree v : ℝ) ≤ μ*m) := by
  classical
  obtain ⟨ξ, hξ, nCut, hcomplete⟩ :=
    MatchingRepairStep.exists_protected_completion ζ ν τ hζ hν hντ hτ hτζ
  let ℓ := Nat.ceil (2/ξ) + 2
  let μ₀ := min ν ζ / 4
  have hμ₀ : 0 < μ₀ := by dsimp [μ₀]; positivity
  refine ⟨μ₀, hμ₀, ?_⟩
  intro μ hμ hμsmall
  have hμν : μ ≤ ν/4 := by
    have hh := min_le_left ν ζ
    dsimp [μ₀] at hμsmall
    linarith only [hh, hμsmall]
  have hμζ : μ ≤ ζ/4 := by
    have hh := min_le_right ν ζ
    dsimp [μ₀] at hμsmall
    linarith only [hh, hμsmall]
  obtain ⟨δ, hδ, hδν, hδζ, hδμ, hδhalf, hδbudget⟩ :=
    MatchingRepairParameters.exists_error b ζ ν μ ξ ℓ hb hζ hν hμ hξ
  obtain ⟨m₀, hm₀⟩ :=
    MatchingRepairParameters.exists_order_threshold μ ξ ζ nCut hμ hξ hζ
  refine ⟨δ, hδ, m₀, ?_⟩
  intro V _ _ G R hRG m r hV hmLarge hmeven hr hRmin hRexpand
    M X hM hMdisj hMR hMX hXeven hXsize hYsize hYinc
  obtain ⟨hnCut, hm, hμm, hηm⟩ := hm₀ m hmLarge
  let Y : Fin r → Finset V := fun i => uncoveredOutside G (M i) (X i)
  have hYend : ∀ v, (endpointCount Y univ v : ℝ) ≤ δ*m := by
    intro v
    have heq : endpointCount Y univ v =
        (univ.filter (fun i : Fin r => v ∈ uncoveredOutside G (M i) (X i))).card := by
      unfold endpointCount
      apply congrArg Finset.card
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Y]
    rw [heq]
    exact hYinc v
  have hI : (Fintype.card (Fin r) : ℝ) ≤ b*m := by simpa only [Fintype.card_fin] using hr
  have hfamily : ∀ T : Finset (Fin r), ∃ N : Fin r → G.Subgraph,
      Invariant G R M N X Y T m ℓ μ δ := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact ⟨M, invariant_empty G R M X Y m ℓ μ δ⟩
    | @insert i T hi ih =>
      obtain ⟨N, hN⟩ := ih
      let U := edgeUnion (fun j => (N j).spanningCoe) T
      let P := R \ U
      let u := internalLoad G R N Y T
      let cap := Nat.floor ((μ/2)*m)
      let Z := univ.filter (fun v => v ∈ (M i).verts ∧ u v = cap)
      have hZ (v : V) (hv : v ∈ Z) : v ∈ (M i).verts :=
        (Finset.mem_filter.mp hv).2.1
      have htotal : (∑ v, (u v : ℝ)) ≤ (b*ℓ)*δ*(m : ℝ)^2 :=
        hN.internal_total_le hδ.le hI
      have hZcard₀ : (Z.card : ℝ) ≤ 2*(b*ℓ)*δ*m/(μ/2) :=
        BipartitePackingBounds.saturated_vertices_bound u Z m (μ/2) (b*ℓ) δ hm
          (by positivity) (by nlinarith only [hμm])
          (fun v hv => (Finset.mem_filter.mp hv).2.2) htotal
      have hZcard : (Z.card : ℝ) ≤ 4*b*ℓ*δ*m/μ := by
        convert hZcard₀ using 1
        ring
      have hload (v : V) : (reserveLoad G R N T v : ℝ) ≤ μ*m :=
        hN.load_le hμ.le (by linarith only [hδμ, hμ]) hYend v
      have hloss (v : V) : (R.degree v : ℝ) ≤ P.degree v + μ*m := by
        have hh := unused_reserve_degree G R N T v
        have hhR : (P.degree v : ℝ) + reserveLoad G R N T v = R.degree v := by
          simp only [← SimpleGraph.card_neighborSet_eq_degree,
            ← Nat.card_eq_fintype_card] at hh ⊢
          exact_mod_cast hh
        linarith only [hhR, hload v]
      have hparity : Even (m - (X i).card) := by
        have hm2 := Nat.even_iff.mp hmeven
        have hx2 := Nat.even_iff.mp (hXeven i)
        rw [Nat.even_iff]
        omega
      have hbudget : (2 : ℝ)*Z.card + ℓ*(Y i).card ≤ min ξ (ζ/3)*m/16 := by
        have hy := mul_le_mul_of_nonneg_left (hYsize i) (Nat.cast_nonneg ℓ (α := ℝ))
        have hz := mul_le_mul_of_nonneg_left hZcard (by norm_num : (0 : ℝ) ≤ 2)
        have hsmall := mul_le_mul_of_nonneg_right hδbudget (Nat.cast_nonneg m (α := ℝ))
        change (2 : ℝ)*Z.card + ℓ*(uncoveredOutside G (M i) (X i)).card ≤ _
        calc
          _ ≤ 2*(4*b*ℓ*δ*m/μ) + ℓ*(δ*m) := add_le_add hz hy
          _ = (8*b*ℓ/μ + ℓ)*δ*m := by ring
          _ ≤ min ξ (ζ/3)/16*m := hsmall
          _ = _ := by ring
      obtain ⟨L, hL, hLverts, hLedges, hLzero, hLone, hLtotal⟩ :=
        hcomplete V G R P hRG sdiff_le (M i) (hM i) (hMR i) (X i) Z (hMX i) hZ
          m ℓ μ δ hnCut hm hV hparity hμ.le hδ.le
          (by linarith only [hμν, hν]) (by linarith only [hμζ, hδζ])
          hδν hδhalf hRmin hRexpand
          (by simpa only [← SimpleGraph.card_neighborSet_eq_degree,
            ← Nat.card_eq_fintype_card] using hloss)
          (hXsize i) le_rfl hηm hbudget
      have hdisj : ∀ j ∈ insert i T, ∀ k ∈ insert i T, j ≠ k →
          Disjoint (Function.update N i L j).spanningCoe
            (Function.update N i L k).spanningCoe := by
        exact MatchingRepairFamily.update_pairwise_disjoint G R M N T i L hi
          hMdisj hMR hN.disjoint hN.edges hLedges
      have hzero (v : V) (hv : v ∉ Y i) (hs : u v = cap) :
          (L.spanningCoe ⊓ R).degree v = 0 := by
        by_cases hvX : v ∈ X i
        · exact hLzero v (mem_union_left Z hvX)
        · have hvM : v ∈ (M i).verts := by
            by_contra hvm
            apply hv
            simp only [Y, uncoveredOutside, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hvX, hvm⟩
          exact hLzero v (mem_union_right (X i) (Finset.mem_filter.mpr
            ⟨mem_univ v, hvM, hs⟩))
      let N' := Function.update N i L
      have hN' (j : Fin r) (hj : j ∈ T) : N' j = N j := by
        exact Function.update_of_ne (by intro heq; subst j; exact hi hj) _ _
      refine ⟨N', ?_, ?_, ?_, hdisj, ?_, ?_⟩
      · intro j hj
        rcases mem_insert.mp hj with rfl | hj
        · simpa only [N', Function.update_self] using hL
        · rw [hN' j hj]
          exact hN.matching j hj
      · intro j hj
        rcases mem_insert.mp hj with rfl | hj
        · simpa only [N', Function.update_self] using hLverts
        · rw [hN' j hj]
          exact hN.verts j hj
      · intro j hj
        rcases mem_insert.mp hj with rfl | hj
        · simp only [N', Function.update_self]
          exact hLedges.trans (sup_le_sup_left sdiff_le _)
        · rw [hN' j hj]
          exact hN.edges j hj
      · exact internalLoad_update_insert_le_capacity G R N Y T i L hi cap
          hN.capacity hLone hzero
      · have htotalEq := total_actual_load_update_insert G R N T i L hi hdisj
        have htotalEqR : (∑ v, (reserveLoad G R N' (insert i T) v : ℝ)) =
            (∑ v, (reserveLoad G R N T v : ℝ)) +
              ∑ v, ((L.spanningCoe ⊓ R).degree v : ℝ) := by exact_mod_cast htotalEq
        have hLtotalR : (∑ v, ((L.spanningCoe ⊓ R).degree v : ℝ)) ≤
            (ℓ : ℝ)*(Y i).card := by exact_mod_cast hLtotal
        have hy := mul_le_mul_of_nonneg_left (hYsize i) (Nat.cast_nonneg ℓ (α := ℝ))
        have htotalOld := hN.total
        rw [card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
        change (∑ v, (reserveLoad G R N' (insert i T) v : ℝ)) ≤ _
        change (ℓ : ℝ)*(Y i).card ≤ ℓ*(δ*m) at hy
        nlinarith only [htotalEqR, hLtotalR, hy, htotalOld]
  obtain ⟨N, hN⟩ := hfamily univ
  have hused (v : V) :
      ((edgeUnion (fun i => (N i).spanningCoe ⊓ R) univ).degree v : ℝ) ≤ μ*m := by
    have hh := hN.load_le hμ.le (by linarith only [hδμ, hμ]) hYend v
    rw [← reserve_union_degree G R N univ v] at hh
    exact hh
  refine ⟨N, fun i => hN.matching i (mem_univ i),
    fun i => hN.verts i (mem_univ i), fun i => hN.edges i (mem_univ i),
    fun i j hij => hN.disjoint i (mem_univ i) j (mem_univ j) hij, hused, ?_⟩
  intro v
  have hh := MatchingRepairAccounting.released_union_degree_le G R M N univ
    (fun i _ => hM i) hN.matching
    (fun i hi => by rw [hN.verts i hi]; exact hMX i) hN.edges
    (fun i _ j _ hij => hMdisj hij) hN.disjoint v
  have hhR :
      ((edgeUnion (fun i => (M i).spanningCoe \ (N i).spanningCoe) univ).degree v : ℝ) ≤
        (edgeUnion (fun i => (N i).spanningCoe ⊓ R) univ).degree v := by exact_mod_cast hh
  exact hhR.trans (hused v)

end Overfull.MatchingRepair
