import Overfull.TerminalFourTwoOdd.CutCertificates
import Overfull.NativeTerminal.BoundedInput

/-! Uniform two-core central factorization certified by actual joining matchings. -/

noncomputable section

namespace Overfull.TerminalFourTwoOdd

open Finset Classical Multigraph SmallCuts NativeReserve ForceMatching

theorem exists_uniform_two_core_central_coloring (α ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ α/64) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ (V E : Type*) [Fintype V] [Fintype E]
        (G : Multigraph V E) (U W Z : Finset V) (C₀ : Core G U) (C₁ : Core G W)
        (k : ℕ) (a : ℝ),
        n₀ ≤ Fintype.card V → Even (Fintype.card V) →
        Disjoint U W → Disjoint U Z → Disjoint W Z →
        (∀ v, v ∈ U ∨ v ∈ W ∨ v ∈ Z) → Z.card ≤ 2 →
        (∀ v, G.degree v = k) → α*Fintype.card V ≤ (k : ℝ) →
        α*Fintype.card V ≤ (U.card : ℝ) → α*Fintype.card V ≤ (W.card : ℝ) →
        IsRobustExpander C₀.graph ν τ → IsRobustExpander C₁.graph ν τ →
        a ≤ ε*Fintype.card V →
        (∀ v, (k : ℝ)-a ≤ (C₀.graph.degree v : ℝ)) →
        (∀ v, (k : ℝ)-a ≤ (C₁.graph.degree v : ℝ)) →
        (M : Fin k → Finset E) → (∀ j, G.IsMatching (M j)) →
        Pairwise (fun i j => Disjoint (M i) (M j)) →
        (∀ e, e ∉ G.internalEdges U → e ∉ G.internalEdges W → ∃ j, e ∈ M j) →
        (∀ j, Z ⊆ G.edgeSupport (M j)) →
        (∀ j, Even (U \ G.edgeSupport (M j)).card) →
        (∀ j, Even (W \ G.edgeSupport (M j)).card) →
        Nonempty (G.EdgeColoring k) := by
  have hτfactor : τ ≤ min α (min α 1)/16 := by
    rw [min_eq_left hα1,min_self]
    linarith
  obtain ⟨η,hη,mfactor,_hmfactor,hfactor⟩ := bounded_input_factorization α α ν τ
    hα hα hν hντ hτfactor
  obtain ⟨mcut,hmcut⟩ := exists_order_threshold α ν hα hν
  let ε := min (α/10) (η/2)
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  refine ⟨ε,hε,max (max mcut mfactor) (max 1 ⌈2/η⌉₊),?_⟩
  intro V E _ _ G U W Z C₀ C₁ k a hn heven hUW hUZ hWZ hcover hZ
    hregular hk hU hW hrobU hrobW ha hdegU hdegW M hM hdM hcoverM hZM hparU hparW
  have hncut : mcut ≤ Fintype.card V :=
    (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hnfactor : mfactor ≤ Fintype.card V :=
    (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hn1 : 1 ≤ Fintype.card V :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnceil : ⌈2/η⌉₊ ≤ Fintype.card V :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hnpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have hUpos : 0 < U.card := by
    have hh := (mul_pos hα hnpos).trans_le hU
    exact_mod_cast hh
  obtain ⟨v,hv⟩ := card_pos.mp hUpos
  have hdeglt : (C₀.graph.degree ⟨v,hv⟩ : ℝ) < U.card := by
    exact_mod_cast C₀.graph.degree_lt_card_verts ⟨v,hv⟩
  have hUn : (U.card : ℝ) ≤ Fintype.card V := by exact_mod_cast card_le_univ U
  have hasmall : a ≤ α*Fintype.card V/10 := by
    have hh := ha.trans (mul_le_mul_of_nonneg_right (min_le_left (α/10) (η/2))
      (Nat.cast_nonneg (Fintype.card V)))
    dsimp [ε] at ha
    linarith
  have hkhi : (k : ℝ) ≤ 2*Fintype.card V := by
    have hd := hdegU ⟨v,hv⟩
    have haBound : a ≤ (Fintype.card V : ℝ)/10 := by
      nlinarith [mul_le_mul_of_nonneg_right hα1 (Nat.cast_nonneg (Fintype.card V))]
    linarith
  let parts : Fin 2 → Finset V := ![U,W]
  let cores : ∀ i, Core G (parts i) := ![C₀,C₁]
  have hparts : Pairwise (fun i j => Disjoint (parts i) (parts j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [parts,Disjoint.symm]
  have hpartsZ : ∀ i, Disjoint (parts i) Z := by
    intro i
    fin_cases i
    · exact hUZ
    · exact hWZ
  have hwholeCover (X : Finset V) (hX : X ∈ wholeUnions parts Z) :
      G.cutEdges X ⊆ univ.biUnion M := by
    apply whole_cut_covered G parts Z hparts hpartsZ _ ?_ X hX
    intro e he
    obtain ⟨j,hj⟩ := hcoverM e (he 0) (he 1)
    exact mem_biUnion.mpr ⟨j,mem_univ _,hj⟩
  have hwholeParity (X : Finset V) (hX : X ∈ wholeUnions parts Z) (j : Fin k) :
      (G.cutOn (M j) X).card % 2 = X.card % 2 := by
    apply whole_matching_cut_parity G parts Z hparts (M j) (hM j) (hZM j) ?_ X hX
    intro i
    fin_cases i
    · exact hparU j
    · exact hparW j
  have hno : ∀ X : Finset V, ¬ G.IsOverfull k X := by
    apply no_overfull_of_whole_cut_bounds G parts Z hparts hpartsZ
      (fun v => by rcases hcover v with h | h | h
                   · exact Or.inr ⟨0,h⟩
                   · exact Or.inr ⟨1,h⟩
                   · exact Or.inl h)
      k hregular cores α α ν τ a hα hα hν (hν.trans_le hντ).le
      (by linarith) hk hkhi hasmall (hmcut _ hncut)
    · intro i
      fin_cases i
      · exact hU
      · exact hW
    · intro i
      fin_cases i
      · exact hrobU
      · exact hrobW
    · intro i v
      fin_cases i
      · exact hdegU v
      · exact hdegW v
    · intro X hX hodd
      exact matching_partition_odd_cut G k M hdM X (hwholeCover X hX)
        (fun j => (hwholeParity X hX j).trans hodd)
    · intro X hX hevenX v
      exact toggle_safe_of_incidence G k hregular X v
        (matching_partition_even_incidence G k M hM hdM X (hwholeCover X hX)
          (fun j => (hwholeParity X hX j).trans hevenX) v)
  have hone : 1 ≤ η/2*Fintype.card V := by
    have hceil : (2/η : ℝ) ≤ Fintype.card V :=
      (Nat.le_ceil _).trans (by exact_mod_cast hnceil)
    have hh := (div_le_iff₀ hη).mp hceil
    nlinarith
  have haη : a ≤ η/2*Fintype.card V := ha.trans
    (mul_le_mul_of_nonneg_right (min_le_right (α/10) (η/2)) (Nat.cast_nonneg _))
  exact hfactor V E G k a hnfactor heven hregular hk hno (by linarith)
    (Or.inr ⟨U,W,Z,C₀,C₁,hUW,hUZ,hWZ,hcover,hZ,hU,hW,hrobU,hrobW,hdegU,hdegW⟩)

end Overfull.TerminalFourTwoOdd
