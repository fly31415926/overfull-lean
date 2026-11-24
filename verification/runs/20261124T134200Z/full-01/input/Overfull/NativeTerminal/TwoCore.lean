import Overfull.NativeTerminal.NativeCompletion
import Overfull.ResidualPalette.UniformJoining

/-!
# Factorization of an original host with two robust cores

The reserve, the nonprotected matching prefix, the terminal coloring, and
both reassemblies are constructed from the original host hypotheses. All
constants precede the host and its edge-copy type. The error convention
`a + 1` allows zero original core deficit while supplying the positive
error required by the native reserve selection.
-/

noncomputable section

namespace Overfull

open Finset Classical SmallCuts NativeReserve NativeTerminal

/-- The original two-core branch with at most two exceptional vertices.
Neither a representative, a reserve, a complementary coloring, nor a
residual factorization is an input to this theorem. -/
theorem two_core_two_exception_factorization (α β ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ α/8) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (V E : Type*) [Fintype V] [Fintype E] (G : Multigraph V E) (k : ℕ)
        (U₀ U₁ Z : Finset V) (C₀ : Core G U₀) (C₁ : Core G U₁) (a : ℝ),
        n₀ ≤ Fintype.card V → Even (Fintype.card V) →
        α * Fintype.card V ≤ k →
        β * Fintype.card V ≤ U₀.card → β * Fintype.card V ≤ U₁.card →
        Disjoint U₀ U₁ → Disjoint U₀ Z → Disjoint U₁ Z →
        (∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) → Z.card ≤ 2 →
        (∀ v, G.degree v = k) → (∀ X : Finset V, ¬ G.IsOverfull k X) →
        IsRobustExpander C₀.graph ν τ → IsRobustExpander C₁.graph ν τ →
        a + 1 ≤ ε * Fintype.card V →
        (∀ v, (k : ℝ) - a ≤ (C₀.graph.degree v : ℝ)) →
        (∀ v, (k : ℝ) - a ≤ (C₁.graph.degree v : ℝ)) →
        Nonempty (G.EdgeColoring k) := by
  let σ := α/960
  have hσ : 0 < σ := by dsimp only [σ]; positivity
  have hσhalf : σ < 1/2 := by dsimp only [σ]; linarith only [hα1]
  have hσsmall : σ ≤ α/300 := by dsimp only [σ]; linarith only [hα]
  have hσprefix : σ ≤ α/240 := by dsimp only [σ]; linarith only [hα]
  obtain ⟨θ,hθ,hθσ,hreserve⟩ :=
    exists_uniform_native_reserve_completion_with_small_joining α β ν τ σ
      hα hα1 hβ hν hντ hτ hσ hσhalf hσsmall
  obtain ⟨δ,hδ,nPrefix,hnPrefix,hfinish⟩ :=
    exists_uniform_native_remaining_factorization α β θ σ
      hα hα1 hβ hθ hθσ hσprefix
  obtain ⟨ε,hε,nReserve,hnReserve,hconstruct⟩ := hreserve δ hδ
  let n₀ := max nPrefix nReserve
  have hn₀ : 0 < n₀ := hnPrefix.trans_le (le_max_left _ _)
  refine ⟨ε,hε,n₀,hn₀,?_⟩
  intro V E _ _ G k U₀ U₁ Z C₀ C₁ a hn _hEven hk hU₀ hU₁
    h01 h0Z h1Z hcover hZ hregular hno hrob₀ hrob₁ ha hcore₀ hcore₁
  have hnP : nPrefix ≤ Fintype.card V := (le_max_left _ _).trans hn
  have hnR : nReserve ≤ Fintype.card V := (le_max_right _ _).trans hn
  have hnpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn₀.trans_le hn
  have hUpos : 0 < U₀.card := by
    exact_mod_cast (mul_pos hβ hnpos).trans_le hU₀
  obtain ⟨v,hv⟩ := card_pos.mp hUpos
  have hupp : (C₀.graph.degree ⟨v,hv⟩ : ℝ) ≤ k := by
    exact_mod_cast (OneCore.core_degree_le C₀ ⟨v,hv⟩).trans_eq (hregular v)
  have ha0 : 0 ≤ a := by linarith only [hcore₀ ⟨v,hv⟩,hupp]
  have haPos : 0 < a+1 := by linarith only [ha0]
  have hdegree₀ : ∀ v, (k : ℝ)-(a+1) ≤ (C₀.graph.degree v : ℝ) := by
    intro v
    linarith only [hcore₀ v]
  have hdegree₁ : ∀ v, (k : ℝ)-(a+1) ≤ (C₁.graph.degree v : ℝ) := by
    intro v
    linarith only [hcore₁ v]
  obtain ⟨r,h,q,M,Q,N,C₀',C₁',hM,hr,hcount,hrh,_hmargin,
    hNperfect,hNdisj,hNavoid,hRregular,hRno,hRrob₀,hRrob₁,hRdegree₀,hRdegree₁,
    _hjoining,hmax,_hpalette,_hnat,_hnatmargin⟩ :=
    hconstruct V E G k U₀ U₁ Z C₀ C₁ (a+1) hnR hk hU₀ hU₁
      h01 h0Z h1Z hcover hZ hregular hno hrob₀ hrob₁ haPos ha hdegree₀ hdegree₁
  have hrDensity : α * Fintype.card V / 30 ≤ (r : ℝ) :=
    (div_le_div_of_nonneg_right hk (by norm_num : (0 : ℝ) ≤ 30)).trans hr
  obtain ⟨cRest⟩ := hfinish V E (Fin q) G U₀ U₁ Z M r Q N univ h (a+1)
    C₀' C₁' hnP hM h01 h0Z h1Z hcover hZ hU₀ hU₁ hrDensity hrh
    (fun j _ => hNavoid j) hRregular hRno hRrob₀ hRrob₁ hRdegree₀ hRdegree₁ hmax
  let c := reassembledColoring G N (fun j => (hNperfect j).isMatching G) cRest
  have hsum : q+h=k := by omega
  exact ⟨hsum ▸ c⟩

/-- The two-core conclusion as an exact partition of every original edge
copy into `k` pairwise disjoint perfect matchings. -/
theorem two_core_two_exception_one_factorization (α β ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ α/8) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (V E : Type*) [Fintype V] [Fintype E] (G : Multigraph V E) (k : ℕ)
        (U₀ U₁ Z : Finset V) (C₀ : Core G U₀) (C₁ : Core G U₁) (a : ℝ),
        n₀ ≤ Fintype.card V → Even (Fintype.card V) →
        α * Fintype.card V ≤ k →
        β * Fintype.card V ≤ U₀.card → β * Fintype.card V ≤ U₁.card →
        Disjoint U₀ U₁ → Disjoint U₀ Z → Disjoint U₁ Z →
        (∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) → Z.card ≤ 2 →
        (∀ v, G.degree v = k) → (∀ X : Finset V, ¬ G.IsOverfull k X) →
        IsRobustExpander C₀.graph ν τ → IsRobustExpander C₁.graph ν τ →
        a + 1 ≤ ε * Fintype.card V →
        (∀ v, (k : ℝ) - a ≤ (C₀.graph.degree v : ℝ)) →
        (∀ v, (k : ℝ) - a ≤ (C₁.graph.degree v : ℝ)) →
        ∃ F : Fin k → Finset E,
          (∀ i, G.IsPerfectMatching (F i)) ∧
          Pairwise (fun i j => Disjoint (F i) (F j)) ∧
          univ.biUnion F = univ := by
  obtain ⟨ε,hε,n₀,hn₀,hfactor⟩ :=
    two_core_two_exception_factorization α β ν τ hα hα1 hβ hν hντ hτ
  refine ⟨ε,hε,n₀,hn₀,?_⟩
  intro V E _ _ G k U₀ U₁ Z C₀ C₁ a hn hEven hk hU₀ hU₁
    h01 h0Z h1Z hcover hZ hregular hno hrob₀ hrob₁ ha hcore₀ hcore₁
  obtain ⟨c⟩ := hfactor V E G k U₀ U₁ Z C₀ C₁ a hn hEven hk hU₀ hU₁
    h01 h0Z h1Z hcover hZ hregular hno hrob₀ hrob₁ ha hcore₀ hcore₁
  exact BoundedExterior.exists_oneFactorization_of_coloring G k hregular c

end Overfull
