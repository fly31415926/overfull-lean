import Overfull.Replacement.SmallShores
import Overfull.Replacement.Parameters
import Overfull.Replacement.Construction

/-!
# Replacing a dense core by a robust graph

Lemma 3.3. A sufficiently dense core of even order can be replaced by an
actual simple robust expander. The replacement preserves the maximum-degree
bound and every overfull-set inequality, and retains the entire exterior.
All constants are chosen before the graph and the core.
-/

namespace Overfull

open Finset Classical SimpleGraph Replacement
open scoped BigOperators

set_option maxHeartbeats 1000000 in
/-- The robust replacement of Lemma 3.3, with an explicit sufficient range
for the fixed robustness scale. The core is carried by its actual vertex
subtype, and the returned ambient graph is the specified edge replacement. -/
theorem robust_core_replacement (β τ : ℝ)
    (hβ : 0 < β) (hτ : 0 < τ) (hτβ : τ ≤ β/16) (hτquarter : τ ≤ 1/4) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ ξ : ℝ, 0 < ξ ∧ ∃ n₀ : ℕ,
      ∀ (V : Type*) [Fintype V] [DecidableEq V],
      ∀ (G : SimpleGraph V) (U : Finset V) (H : SimpleGraph U) (k m : ℕ) (a : ℝ),
        n₀ ≤ Fintype.card V → (∀ v, G.degree v ≤ k) →
        β*Fintype.card V ≤ k → (∀ X : Finset V, ¬ IsOverfull G k X) →
        U.card = 2*m → β*Fintype.card V ≤ m → H ≤ G.induce (U : Set V) →
        (∀ v, (k : ℝ)-a ≤ H.degree v) → 0 ≤ a → a+1 ≤ ξ*Fintype.card V →
        ∃ H' : SimpleGraph U, ∃ G' : SimpleGraph V,
          G' = (G \ lift U H) ⊔ lift U H' ∧
          Disjoint (lift U H') (G \ lift U H) ∧
          IsRobustExpander H' μ τ ∧ (∀ v, (k : ℝ)-2*a-1 ≤ H'.degree v) ∧
          (∀ v, G'.degree v ≤ k) ∧ (∀ X : Finset V, ¬ IsOverfull G' k X) ∧
          G \ lift U H ≤ G' := by
  let ρ := min (β/2) (1/2)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρone : ρ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨ν,hν,nReal,hrealize⟩ := balanced_robust_realization ρ τ hρ hρone
    hτ (by linarith)
  let μ := ν/2
  have hμ : 0 < μ := by dsimp [μ]; positivity
  obtain ⟨ξ,hξ,n₁,hparameters⟩ :=
    exists_replacement_parameters β μ τ nReal hβ hμ hτ.le hτβ
  refine ⟨μ,hμ,ξ,hξ,max 1 n₁,?_⟩
  intro V _ _ G U H k m a hn hdegree hk hno hU hm hH hHdegree ha haξ
  let n := Fintype.card V
  have hnpos : 0 < n := by dsimp [n]; omega
  have hnposR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hβn : 0 < β*n := mul_pos hβ hnposR
  have hmpos : 0 < m := by
    have hh : (0 : ℝ) < m := hβn.trans_le hm
    exact_mod_cast hh
  have hUpos : 0 < U.card := by omega
  have hUnonempty := Finset.card_pos.mp hUpos
  letI : Nonempty U := ⟨⟨hUnonempty.choose,hUnonempty.choose_spec⟩⟩
  have hqn : U.card ≤ n := Finset.card_le_univ U
  have hqlo : 2*β*n ≤ (U.card : ℝ) := by
    have hUR : (U.card : ℝ) = 2*m := by exact_mod_cast hU
    nlinarith only [hm,hUR]
  obtain ⟨v₀,hmin⟩ := H.exists_minimal_degree_vertex
  have hkupper : (k : ℝ) ≤ U.card+a := by
    have hh := hHdegree v₀
    have hd := H.degree_lt_card_verts v₀
    rw [Fintype.card_coe] at hd
    have hdR : (H.degree v₀ : ℝ) < U.card := by
      exact_mod_cast hd
    linarith
  obtain ⟨_,hqReal,hnbig,haβ,haμ,hab,hτq,hquad,ham⟩ :=
    hparameters n U.card k a ((le_max_right _ _).trans hn)
      hqn hqlo hk ha haξ hkupper
  have hminR : (k : ℝ)-a ≤ H.minDegree := by
    rw [hmin]
    exact hHdegree v₀
  have hminpos : 1 ≤ H.minDegree := by
    have hh : (1 : ℝ) ≤ H.minDegree := by linarith
    exact_mod_cast hh
  let r := H.minDegree-1
  have hradd : r+1 = H.minDegree := Nat.sub_add_cancel hminpos
  have hraddR : (r : ℝ)+1 = H.minDegree := by exact_mod_cast hradd
  have hr : (k : ℝ)-a-1 ≤ r := by linarith only [hminR,hraddR]
  have hrβ : β*n/2 ≤ (r : ℝ) := by linarith only [hr,hk,haβ]
  have hρq : ρ*U.card ≤ (r : ℝ) := by
    have h₁ := mul_le_mul_of_nonneg_right (show ρ ≤ β/2 from min_le_left _ _)
      (Nat.cast_nonneg U.card (α := ℝ))
    have h₂ := mul_le_mul_of_nonneg_left
      (show (U.card : ℝ) ≤ n by exact_mod_cast hqn) (show 0 ≤ β/2 by positivity)
    linarith only [h₁,h₂,hrβ]
  have hrq : r ≤ U.card-1 := by
    have hh := H.minDegree_lt_card
    rw [Fintype.card_coe] at hh
    dsimp [r]
    omega
  have hevenq : Even U.card := ⟨m,by omega⟩
  have heven : Even (∑ _v : Fin U.card, r) := by
    simpa using hevenq.mul_right r
  obtain ⟨R₀,hR₀,hR₀robust⟩ := hrealize U.card hqReal (fun _ => r)
    (fun _ => hρq) (fun _ => hrq) (fun _ _ => Nat.le_succ r) heven
  let e : U ≃ Fin U.card := (Fintype.equivFin U).trans
    (Equiv.cast (congrArg Fin (Fintype.card_coe U)))
  let R := R₀.comap e
  have hR (v : U) : R.degree v = r := by
    have hh := (RobustRealization.comap_equiv_degree R₀ e v).trans (hR₀ (e v))
    simpa only [R, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hh
  have hRrobust : IsRobustExpander R ν τ :=
    RobustRealization.robust_comap_equiv R₀ e ν τ hR₀robust
  have hHlower (v : U) : r+1 ≤ H.degree v := by
    rw [hradd]
    exact H.minDegree_le_degree v
  have hHupper (v : U) : H.degree v ≤ k :=
    (SimpleGraph.degree_le_of_le hH).trans ((induced_degree_le G U v).trans (hdegree v.val))
  have hmr : k ≤ m+r := by
    have hmR : (U.card : ℝ)/2 = m := by rw [hU]; push_cast; ring
    have hh : (k : ℝ) ≤ m+r := by rw [hmR] at ham; linarith only [ham,hr]
    exact_mod_cast hh
  have hnewrobust : IsRobustExpander (core G U H R) μ τ := by
    have hh := core_robust G U H R k a ν μ τ hH hdegree hHdegree hRrobust hμ.le haμ
    have heq : ν-μ = μ := by dsimp [μ]; ring
    rw [heq] at hh
    exact hh
  have hnewdegree (v : U) : (k : ℝ)-2*a-1 ≤ (core G U H R).degree v :=
    core_degree_lower G U H R k r a hH hdegree hHdegree hR hr v
  have hgraphdegree (v : V) : (graph G U H R).degree v ≤ k :=
    (graph_degree_le G U H R hH
      (fun w => by rw [hR w]; exact (Nat.le_succ r).trans (hHlower w)) v).trans (hdegree v)
  have hcuts (S : Finset U) (hS : 2 ≤ S.card) (hSc : 2 ≤ Sᶜ.card) :
      k < (Multigraph.ofSimpleGraph (core G U H R)).cutSize S := by
    have hh := AuxiliaryCompletion.core_cut_gt_of_ranges (core G U H R)
      k (2*a+1) μ τ hμ.le hab
      (by simpa only [Fintype.card_coe] using hτq)
      (by simpa only [Fintype.card_coe] using hquad)
      (fun v => by simpa only [sub_add_eq_sub_sub] using hnewdegree v)
      hnewrobust S hS hSc
    exact_mod_cast hh
  have hsmall (S : Finset U) (hS : S.card ≤ 1 ∨ Sᶜ.card ≤ 1) :
      (internalEdges (core G U H R) S).card ≤ (internalEdges H S).card := by
    exact (internal_count_mono (core_le G U H R) S).trans
      (regular_small_shore_comparison H R m r k
        (by simpa only [Fintype.card_coe] using hU) hR hHlower hHupper hmr S hS)
  refine ⟨core G U H R,graph G U H R,rfl,
    (exterior_disjoint_core G U H R).symm,hnewrobust,hnewdegree,hgraphdegree,?_,
    exterior_le G U H R⟩
  exact no_overfull_of_core_cuts G U H R k hH hgraphdegree hno hcuts hsmall

end Overfull
