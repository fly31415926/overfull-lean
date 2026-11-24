import Overfull.SmallCuts
import Overfull.MultigraphColoring

/-!
# Odd cuts with one exterior vertex

The small-cut theorem rules out overfull sets in an even-order regular
multigraph whose robust simple core omits at most one vertex. All cuts and
degrees count actual edge copies. No factorization hypothesis is used.
-/

namespace Overfull.OneCore

open Finset Classical
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype V] in
theorem cutSize_singleton (G : Multigraph V E) (v : V) :
    G.cutSize {v} = G.degree v := by
  have hempty : G.internalEdges {v} = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨h₁, h₂⟩ := (G.mem_internalEdges {v} e).mp he
    exact G.endpoints_distinct e
      ((Finset.mem_singleton.mp h₁).trans (Finset.mem_singleton.mp h₂).symm)
  simpa only [Finset.sum_singleton, hempty, Finset.card_empty, mul_zero, zero_add]
    using (G.degree_sum_on {v}).symm

omit [Fintype V] in
/-- For a regular multigraph, the odd-cut inequalities exclude every
overfull set, including the even sets in the definition. -/
theorem no_overfull_of_odd_cuts (G : Multigraph V E) (k : ℕ)
    (hregular : ∀ v, G.degree v = k)
    (hcuts : ∀ X : Finset V, X.card % 2 = 1 → k ≤ G.cutSize X) :
    ∀ X : Finset V, ¬ G.IsOverfull k X := by
  intro X hX
  have hsum := G.degree_sum_on X
  simp only [hregular, Finset.sum_const, smul_eq_mul] at hsum
  have hdivision : X.card = 2 * (X.card / 2) + X.card % 2 := by omega
  change k * (X.card / 2) < (G.internalEdges X).card at hX
  by_cases hodd : X.card % 2 = 1
  · have hcut := hcuts X hodd
    rw [hodd] at hdivision
    nlinarith
  · have heven : X.card % 2 = 0 := by omega
    rw [heven] at hdivision
    nlinarith

omit [Fintype E] in
/-- An odd shore with at most one core vertex is a singleton when at most
one vertex lies outside the core. -/
theorem odd_small_core_shore (U X : Finset V)
    (hout : Uᶜ.card ≤ 1) (hodd : X.card % 2 = 1)
    (hcore : (X ∩ U).card ≤ 1) :
    ∃ v : V, X = {v} := by
  have hsub : X \ U ⊆ Uᶜ := by
    intro v hv
    exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hv).2
  have hparts := Finset.card_inter_add_card_sdiff X U
  have hdiff := (Finset.card_le_card hsub).trans hout
  apply Finset.card_eq_one.mp
  omega

/-- The only possible odd small-cut shores are singletons. This finite
counting bridge is independent of how the cut classification was proved. -/
theorem odd_cuts_of_minority_bound (G : Multigraph V E) (U : Finset V) (k : ℕ)
    (hregular : ∀ v, G.degree v = k)
    (heven : Fintype.card V % 2 = 0) (hout : Uᶜ.card ≤ 1)
    (hsmall : ∀ X : Finset V, G.cutSize X < k →
      min (X ∩ U).card (U \ X).card ≤ 1) :
    ∀ X : Finset V, X.card % 2 = 1 → k ≤ G.cutSize X := by
  intro X hodd
  by_contra h
  have hlt : G.cutSize X < k := Nat.lt_of_not_ge h
  rcases min_le_iff.mp (hsmall X hlt) with hleft | hright
  · obtain ⟨v, rfl⟩ := odd_small_core_shore U X hout hodd hleft
    rw [cutSize_singleton, hregular] at hlt
    exact (Nat.lt_irrefl k) hlt
  · have hcompl : Xᶜ.card % 2 = 1 := by
      have hparts := Finset.card_add_card_compl X
      omega
    have heq : Xᶜ ∩ U = U \ X := by ext v; simp [and_comm]
    obtain ⟨v, hv⟩ := odd_small_core_shore U Xᶜ hout hcompl (by rwa [heq])
    have hcut := G.cutSize_compl X
    rw [hv, cutSize_singleton, hregular] at hcut
    omega

/-- A uniform robust-core criterion with density and error measured against
the whole host order. -/
theorem exists_one_exterior_cut_threshold (α ν τ : ℝ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ α / 10) :
    ∃ n₀ : ℕ, ∀ (V E : Type*) [Fintype V] [Fintype E]
      (G : Multigraph V E) (U : Finset V) (C : SmallCuts.Core G U) (k : ℕ) (a : ℝ),
      n₀ ≤ Fintype.card V → Fintype.card V % 2 = 0 → Uᶜ.card ≤ 1 →
      (∀ v, G.degree v = k) → (k : ℝ) ≤ 2 * Fintype.card V →
      α * Fintype.card V ≤ k → 0 ≤ a → a ≤ α * Fintype.card V / 10 →
      IsRobustExpander C.graph ν τ →
      (∀ v, (k : ℝ) - a ≤ C.graph.degree v) →
      (∀ X : Finset V, X.card % 2 = 1 → k ≤ G.cutSize X) ∧
      (∀ X : Finset V, ¬ G.IsOverfull k X) := by
  obtain ⟨n₀, hsmall⟩ := SmallCuts.small_cut_lemma α (1/2) ν τ
    hα (by norm_num) hν (hν.trans_le hντ) hντ hτ
  refine ⟨max n₀ 2, ?_⟩
  intro V E _ _ G U C k a hn heven hout hregular hkhi hklo ha haSmall hrob hdegree
  have hn₀ : n₀ ≤ Fintype.card V := (le_max_left _ _).trans hn
  have htwo : 2 ≤ Fintype.card V := (le_max_right _ _).trans hn
  have hsize : (1/2 : ℝ) * Fintype.card V ≤ U.card := by
    have hcard := Finset.card_add_card_compl U
    have hbound : Fintype.card V ≤ 2 * U.card := by omega
    have hreal : (Fintype.card V : ℝ) ≤ 2 * U.card := by exact_mod_cast hbound
    linarith
  have hminority : ∀ X : Finset V, G.cutSize X < k →
      min (X ∩ U).card (U \ X).card ≤ 1 := by
    intro X hcut
    have hcutReal : (G.cutSize X : ℝ) ≤ (k : ℝ) + 0 := by
      exact_mod_cast hcut.le
    have hresult := hsmall V E Unit G (fun _ => U) (fun _ => C)
      (by intro i j hij; exact (hij (Subsingleton.elim _ _)).elim)
      k (fun v => by rw [hregular v]) hkhi hklo a 0 ha le_rfl haSmall
      (by positivity) hn₀ (fun _ => hsize) (fun _ => hrob) (fun _ => hdegree)
      X hcutReal
    simpa only [Finset.univ_unique, Finset.sum_singleton] using hresult.1
  have hcuts := odd_cuts_of_minority_bound G U k hregular heven hout hminority
  exact ⟨hcuts, no_overfull_of_odd_cuts G k hregular hcuts⟩

/-- The version used after contracting an odd core's exterior: all degree
and error bounds use the core order. The host upper-degree bound is derived
from the simple core, and the host density from the one-vertex complement. -/
theorem robust_one_exterior_no_overfull (α ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν)
    (hντ : ν ≤ τ) (hτ : τ ≤ α / 20) :
    ∃ m₀ : ℕ, ∀ (V E : Type*) [Fintype V] [Fintype E]
      (G : Multigraph V E) (U : Finset V) (C : SmallCuts.Core G U) (k : ℕ) (a : ℝ),
      m₀ ≤ U.card → Fintype.card V % 2 = 0 → Uᶜ.card ≤ 1 →
      (∀ v, G.degree v = k) → α * U.card ≤ k →
      0 ≤ a → a ≤ α * U.card / 20 → IsRobustExpander C.graph ν τ →
      (∀ v, (k : ℝ) - a ≤ C.graph.degree v) →
      (∀ X : Finset V, X.card % 2 = 1 → k ≤ G.cutSize X) ∧
      (∀ X : Finset V, ¬ G.IsOverfull k X) := by
  obtain ⟨n₀, hcut⟩ := exists_one_exterior_cut_threshold (α/2) ν τ
    (by positivity) hν hντ (by linarith)
  refine ⟨max n₀ 1, ?_⟩
  intro V E _ _ G U C k a hm heven hout hregular hk ha haSmall hrob hdegree
  have hm₀ : n₀ ≤ U.card := (le_max_left _ _).trans hm
  have hmpos : 0 < U.card := by have := (le_max_right n₀ 1).trans hm; omega
  have hUn : U.card ≤ Fintype.card V := Finset.card_le_univ U
  have hUnR : (U.card : ℝ) ≤ Fintype.card V := by exact_mod_cast hUn
  have hcard := Finset.card_add_card_compl U
  have hnm : Fintype.card V ≤ 2 * U.card := by omega
  have hnmR : (Fintype.card V : ℝ) ≤ 2 * U.card := by exact_mod_cast hnm
  have hlo : α / 2 * Fintype.card V ≤ (k : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hnmR hα.le]
  have herror : a ≤ α / 2 * Fintype.card V / 10 := by
    nlinarith [mul_le_mul_of_nonneg_left hUnR hα.le]
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hmpos
  have hsimple := C.graph.degree_lt_card_verts (⟨v, hv⟩ : U)
  simp only [Fintype.card_coe] at hsimple
  have hsimpleR : (C.graph.degree ⟨v, hv⟩ : ℝ) < U.card := by exact_mod_cast hsimple
  have haBound : a ≤ (U.card : ℝ) / 20 := by
    nlinarith [mul_le_mul_of_nonneg_right hα1 (Nat.cast_nonneg U.card)]
  have hhi : (k : ℝ) ≤ 2 * Fintype.card V := by
    have hd := hdegree ⟨v, hv⟩
    linarith
  exact hcut V E G U C k a (hm₀.trans hUn) heven hout hregular
    hhi hlo ha herror hrob hdegree

end Overfull.OneCore
