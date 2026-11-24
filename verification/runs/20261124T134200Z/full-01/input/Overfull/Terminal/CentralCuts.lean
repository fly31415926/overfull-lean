import Overfull.OneCore.Cuts

/-!
# Odd-cut certificates from actual exterior matching classes

If exactly `k` matchings cover every copy outside a simple core, any shore
with at most one core vertex has no overfull internal multiplicity.  The
small-cut theorem applies to that shore or its complement.  This supplies
the central two-apex no-overfull certificate without assuming a coloring.
-/

noncomputable section

namespace Overfull.Terminal

open Finset Classical SmallCuts Multigraph OneCore

variable {V E : Type*} [Fintype V] [Fintype E]

/-- A shore with at most one core vertex has all its internal copies in
the supplied actual matching classes. No disjointness assumption is needed. -/
theorem small_core_shore_not_overfull (G : Multigraph V E) (U : Finset V) (k : ℕ)
    (M : Fin k → Finset E) (hM : ∀ i, G.IsMatching (M i))
    (hcover : ∀ e, e ∉ G.internalEdges U → ∃ i, e ∈ M i)
    (X : Finset V) (hX : (X ∩ U).card ≤ 1) : ¬ G.IsOverfull k X := by
  have hout {e : E} (he : e ∈ G.internalEdges X) : e ∉ G.internalEdges U := by
    intro hi
    have hx := (G.mem_internalEdges X e).mp he
    have hu := (G.mem_internalEdges U e).mp hi
    exact G.endpoints_distinct e
      (Finset.card_le_one.mp hX _ (mem_inter.mpr ⟨hx.1,hu.1⟩)
        _ (mem_inter.mpr ⟨hx.2,hu.2⟩))
  have hsub : G.internalEdges X ⊆ univ.biUnion (fun i => G.internalEdges X ∩ M i) := by
    intro e he
    obtain ⟨i,hi⟩ := hcover e (hout he)
    exact mem_biUnion.mpr ⟨i,mem_univ i,mem_inter.mpr ⟨he,hi⟩⟩
  apply not_lt_of_ge
  calc
    (G.internalEdges X).card ≤ (univ.biUnion (fun i => G.internalEdges X ∩ M i)).card :=
      card_le_card hsub
    _ ≤ ∑ i : Fin k, (G.internalEdges X ∩ M i).card := card_biUnion_le
    _ ≤ ∑ _i : Fin k, X.card / 2 :=
      sum_le_sum (fun i _ => (hM i).internal_edges_card_le G X)
    _ = k * (X.card / 2) := by simp

theorem small_core_odd_cut_lower_bound (G : Multigraph V E) (U : Finset V) (k : ℕ)
    (hregular : ∀ v, G.degree v = k)
    (M : Fin k → Finset E) (hM : ∀ i, G.IsMatching (M i))
    (hcover : ∀ e, e ∉ G.internalEdges U → ∃ i, e ∈ M i)
    (X : Finset V) (hodd : X.card % 2 = 1) (hX : (X ∩ U).card ≤ 1) :
    k ≤ G.cutSize X := by
  have hinside := Nat.le_of_not_gt (small_core_shore_not_overfull G U k M hM hcover X hX)
  have hsum := G.degree_sum_on X
  simp only [hregular,sum_const,smul_eq_mul] at hsum
  have hdivision : X.card = 2 * (X.card / 2) + 1 := by omega
  nlinarith

theorem no_overfull_of_external_matchings_and_minority (G : Multigraph V E)
    (U : Finset V) (k : ℕ) (hregular : ∀ v, G.degree v = k)
    (heven : Fintype.card V % 2 = 0)
    (M : Fin k → Finset E) (hM : ∀ i, G.IsMatching (M i))
    (hcover : ∀ e, e ∉ G.internalEdges U → ∃ i, e ∈ M i)
    (hsmall : ∀ X : Finset V, G.cutSize X < k →
      min (X ∩ U).card (U \ X).card ≤ 1) :
    ∀ X : Finset V, ¬ G.IsOverfull k X := by
  apply no_overfull_of_odd_cuts G k hregular
  intro X hodd
  by_contra h
  have hlt : G.cutSize X < k := Nat.lt_of_not_ge h
  rcases min_le_iff.mp (hsmall X hlt) with hleft | hright
  · exact (not_lt_of_ge (small_core_odd_cut_lower_bound G U k hregular M hM hcover X hodd hleft)) hlt
  · have hcompl : Xᶜ.card % 2 = 1 := by
      have hparts := Finset.card_add_card_compl X
      omega
    have heq : Xᶜ ∩ U = U \ X := by ext v; simp [and_comm]
    have hcut := small_core_odd_cut_lower_bound G U k hregular M hM hcover Xᶜ hcompl (by
      rwa [heq])
    rw [G.cutSize_compl] at hcut
    omega

theorem exists_two_exterior_cut_threshold (α ν τ : ℝ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ α / 10) :
    ∃ n₀ : ℕ, ∀ (V E : Type*) [Fintype V] [Fintype E]
      (G : Multigraph V E) (U : Finset V) (C : Core G U) (k : ℕ) (a : ℝ),
      n₀ ≤ Fintype.card V → Fintype.card V % 2 = 0 → Uᶜ.card ≤ 2 →
      (∀ v, G.degree v = k) → (k : ℝ) ≤ 2 * Fintype.card V →
      α * Fintype.card V ≤ k → 0 ≤ a → a ≤ α * Fintype.card V / 10 →
      IsRobustExpander C.graph ν τ →
      (∀ v, (k : ℝ) - a ≤ C.graph.degree v) →
      (M : Fin k → Finset E) → (∀ i, G.IsMatching (M i)) →
      (∀ e, e ∉ G.internalEdges U → ∃ i, e ∈ M i) →
      ∀ X : Finset V, ¬ G.IsOverfull k X := by
  obtain ⟨n₀,hsmall⟩ := SmallCuts.small_cut_lemma α (1/2) ν τ
    hα (by norm_num) hν (hν.trans_le hντ) hντ hτ
  refine ⟨max n₀ 4,?_⟩
  intro V E _ _ G U C k a hn heven hout hregular hkhi hklo ha haSmall hrob hdegree M hM hcover
  have hn₀ : n₀ ≤ Fintype.card V := (le_max_left _ _).trans hn
  have hfour : 4 ≤ Fintype.card V := (le_max_right _ _).trans hn
  have hsize : (1/2 : ℝ) * Fintype.card V ≤ U.card := by
    have hcard := Finset.card_add_card_compl U
    have hbound : Fintype.card V ≤ 2 * U.card := by omega
    have hreal : (Fintype.card V : ℝ) ≤ 2 * U.card := by exact_mod_cast hbound
    linarith
  apply no_overfull_of_external_matchings_and_minority G U k hregular heven M hM hcover
  intro X hcut
  have hcutReal : (G.cutSize X : ℝ) ≤ (k : ℝ) + 0 := by exact_mod_cast hcut.le
  have hresult := hsmall V E Unit G (fun _ => U) (fun _ => C)
    (by intro i j hij; exact (hij (Subsingleton.elim _ _)).elim)
    k (fun v => by rw [hregular v]) hkhi hklo a 0 ha le_rfl haSmall
    (by positivity) hn₀ (fun _ => hsize) (fun _ => hrob) (fun _ => hdegree) X hcutReal
  simpa only [Finset.univ_unique,Finset.sum_singleton] using hresult.1

/-- Core-normalized two-apex no-overfullness from the actual exterior
matching cover. The host degree upper bound follows from its simple core. -/
theorem robust_two_exterior_no_overfull (α ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν)
    (hντ : ν ≤ τ) (hτ : τ ≤ α / 20) :
    ∃ m₀ : ℕ, ∀ (V E : Type*) [Fintype V] [Fintype E]
      (G : Multigraph V E) (U : Finset V) (C : Core G U) (k : ℕ) (a : ℝ),
      m₀ ≤ U.card → Fintype.card V % 2 = 0 → Uᶜ.card ≤ 2 →
      (∀ v, G.degree v = k) → α * U.card ≤ k →
      0 ≤ a → a ≤ α * U.card / 20 → IsRobustExpander C.graph ν τ →
      (∀ v, (k : ℝ) - a ≤ C.graph.degree v) →
      (M : Fin k → Finset E) → (∀ i, G.IsMatching (M i)) →
      (∀ e, e ∉ G.internalEdges U → ∃ i, e ∈ M i) →
      ∀ X : Finset V, ¬ G.IsOverfull k X := by
  obtain ⟨n₀,hcut⟩ := exists_two_exterior_cut_threshold (α/2) ν τ
    (by positivity) hν hντ (by linarith)
  refine ⟨max n₀ 2,?_⟩
  intro V E _ _ G U C k a hm heven hout hregular hk ha haSmall hrob hdegree M hM hcover
  have hm₀ : n₀ ≤ U.card := (le_max_left _ _).trans hm
  have hmtwo : 2 ≤ U.card := (le_max_right _ _).trans hm
  have hUn : U.card ≤ Fintype.card V := Finset.card_le_univ U
  have hUnR : (U.card : ℝ) ≤ Fintype.card V := by exact_mod_cast hUn
  have hcard := Finset.card_add_card_compl U
  have hnm : Fintype.card V ≤ 2 * U.card := by omega
  have hnmR : (Fintype.card V : ℝ) ≤ 2 * U.card := by exact_mod_cast hnm
  have hlo : α / 2 * Fintype.card V ≤ (k : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hnmR hα.le]
  have herror : a ≤ α / 2 * Fintype.card V / 10 := by
    nlinarith [mul_le_mul_of_nonneg_left hUnR hα.le]
  obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0 < U.card by omega)
  have hsimple := C.graph.degree_lt_card_verts (⟨v,hv⟩ : U)
  simp only [Fintype.card_coe] at hsimple
  have hsimpleR : (C.graph.degree ⟨v,hv⟩ : ℝ) < U.card := by exact_mod_cast hsimple
  have haBound : a ≤ (U.card : ℝ) / 20 := by
    nlinarith [mul_le_mul_of_nonneg_right hα1 (Nat.cast_nonneg U.card)]
  have hhi : (k : ℝ) ≤ 2 * Fintype.card V := by
    have hd := hdegree ⟨v,hv⟩
    linarith
  exact hcut V E G U C k a (hm₀.trans hUn) heven hout hregular
    hhi hlo ha herror hrob hdegree M hM hcover

end Overfull.Terminal
