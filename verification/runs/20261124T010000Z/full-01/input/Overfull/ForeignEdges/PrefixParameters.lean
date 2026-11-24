import Overfull.ForeignEdges.GlobalParameters
import Overfull.ForeignEdges.SmallCutRefinement

/-!
# Usable scalar bounds at every actual prefix

The retained-degree and error bounds supply all density, reserve, marking,
and coloring inequalities in the same normalization.  The configured
refinement theorem applies those inequalities to an actual triggering cut
and returns the next preselected robust input parameter.
-/

namespace Overfull.ForeignEpochParameters

open Finset Classical SimpleGraph SafePrescription MatchingProbability

/-- Scalar consequences in the normalization used by safe preparation,
packing, and the actual small-cut refinement theorem. -/
structure PrefixScalarBounds (α : ℝ) (n m k₀ h t : ℕ) (a : ℝ) : Prop where
  initial_pos : 0 < k₀
  degree_pos : 0 < h
  density : (α/256)*n ≤ h
  core_order : (α/256)*n ≤ m
  upper_degree : (h : ℝ) ≤ 2*n
  safe_reserve : (k₀ : ℝ)/1024 < h
  cluster_reserve : (t : ℝ)+1+markingThreshold*k₀ < h
  assignment_degree : 4*a ≤ 3*h
  error_small : a ≤ (α/256)*n/10
  cut_small : ((2*(t+markedLimit+boundaryLimit+30) : ℕ) : ℝ) ≤ (α/256)*n/10
  cut_le_initial : 2*(t+markedLimit+boundaryLimit+30) ≤ k₀
  recorded_cut : (h : ℝ)+((2*(t+markedLimit+boundaryLimit+30) : ℕ) : ℝ) ≤ 2*k₀
  reserve_density : (α/1024)*m ≤ (h : ℝ)/4
  horizon : 3*h/4 ≤ Nat.floor ((h : ℝ)-(α/1024)*m)

/-- All inequalities hold uniformly at any prefix retaining the global
factor `1/256`. The exceptional order is an arbitrary input. -/
theorem prefix_scalar_bounds (α : ℝ) (n m k₀ h t : ℕ) (a : ℝ)
    (hn : 0 < n) (hα : 0 < α)
    (hdensity : α*n ≤ k₀) (hk₀n : k₀ ≤ n)
    (hretained : k₀ ≤ 256*h) (hhk₀ : h ≤ k₀)
    (hmn : m ≤ n) (hm : (α/2)*n ≤ m) (ha : 0 ≤ a)
    (herror : a+(t : ℝ)+1 ≤ (α/256)*n/10)
    (hcut : ((2*(t+markedLimit+boundaryLimit+30) : ℕ) : ℝ) ≤ (α/256)*n/10) :
    PrefixScalarBounds α n m k₀ h t a := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hk₀R : (0 : ℝ) < k₀ := (mul_pos hα hnR).trans_le hdensity
  have hk₀ : 0 < k₀ := by exact_mod_cast hk₀R
  have hretainedR : (k₀ : ℝ) ≤ 256*h := by exact_mod_cast hretained
  have hhk₀R : (h : ℝ) ≤ k₀ := by exact_mod_cast hhk₀
  have hk₀nR : (k₀ : ℝ) ≤ n := by exact_mod_cast hk₀n
  have hhR : (0 : ℝ) < h := by linarith
  have hh : 0 < h := by exact_mod_cast hhR
  have hβn : (α/256)*n ≤ h := by nlinarith only [hdensity,hretainedR]
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have haSmall : a ≤ (α/256)*n/10 := by linarith only [herror,ht]
  have hmark : (t : ℝ)+1+markingThreshold*k₀ < h := by
    dsimp only [markingThreshold]
    nlinarith only [herror,ha,hβn,hretainedR,hhR]
  have hcutInitialR : ((2*(t+markedLimit+boundaryLimit+30) : ℕ) : ℝ) ≤ k₀ := by
    have hαn : 0 ≤ α*(n : ℝ) := (mul_pos hα hnR).le
    nlinarith only [hcut,hdensity,hαn]
  have hreserve := common_reserve α (α/1024) n m k₀ h
    (by positivity) le_rfl hmn hdensity hretained
  refine ⟨hk₀,hh,hβn,?_,?_,strict_safe_reserve k₀ h hk₀ hretained,hmark,
    ?_,haSmall,hcut,by exact_mod_cast hcutInitialR,?_,hreserve,
    color_horizon_le_packing_horizon h m (α/1024) hreserve⟩
  · have hαn : 0 ≤ α*(n : ℝ) := (mul_pos hα hnR).le
    nlinarith only [hm,hαn]
  · linarith only [hhk₀R,hk₀nR,hnR]
  · nlinarith only [haSmall,hβn,hhR]
  · linarith only [hhk₀R,hcutInitialR]

variable {V I : Type*} [Fintype V] [Fintype I]

/-- An actual triggering cut has a concrete refinement at any current
epoch, including the fourth one.  No subsequent epoch index is required. -/
theorem RestartParameters.refine_current {α τ ν₀ : ℝ}
    (P : RestartParameters α τ ν₀) (j : Fin 4)
    (hα : 0 < α) (hα1 : α ≤ 1) (hτ : τ ≤ (α/256)/1000)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (H : ∀ i, SimpleGraph (U i))
    (Z Z₀ : Finset V) (c : V → Fin 4) (p : I → Fin 4) (X : Finset V)
    (h k₀ : ℕ) (a : ℝ)
    (hn : 0 < Fintype.card V) (hdensity : α*Fintype.card V ≤ k₀)
    (hk₀n : k₀ ≤ Fintype.card V) (hretained : k₀ ≤ 256*h) (hhk₀ : h ≤ k₀)
    (ha : 0 ≤ a)
    (herror : a+(Z.card : ℝ)+1 ≤ (α/256)*Fintype.card V/10)
    (hcutBudget : ((2*(Z.card+markedLimit+boundaryLimit+30) : ℕ) : ℝ) ≤
      (α/256)*Fintype.card V/10)
    (hI : Fintype.card I ≤ 4)
    (hdisjoint : Pairwise (fun i l => Disjoint (U i) (U l)))
    (hUZ : ∀ i, Disjoint (U i) Z) (hZ₀ : Z₀ ⊆ Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hlabel : ∀ i v, v ∈ U i → c v = p i)
    (htrigger : ∃ i l, p i = p l ∧ ¬ (coreMajority U X i ↔ coreMajority U X l))
    (hregular : ∀ v, G.degree v = h)
    (hembed : ∀ i, H i ≤ G.induce (U i : Set V))
    (hdegree : ∀ i v, (h : ℝ)-a ≤ ((H i).degree v : ℝ))
    (hrobust : ∀ i, IsRobustExpander (H i) (P.output j) (τ/2))
    (hsize : ∀ i, (α/2)*Fintype.card V ≤ ((U i).card : ℝ))
    (hlarge : 3 < (P.output j)^2*(α/256)^2*Fintype.card V)
    (hcut : (cutCount (univ : Finset G.edgeSet) X : ℝ) ≤
      h+((2*(Z.card+markedLimit+boundaryLimit+30) : ℕ) : ℝ)) :
    Nonempty (ForeignRefinement.RefinementStep G U H Z Z₀ c p X h a
      (P.output j) (τ/2) (markingThreshold*k₀)) := by
  have hτpos : 0 < τ := (P.input_pos j).trans_le (P.input_le j)
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hself : (α/2)*Fintype.card V ≤ (Fintype.card V : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hα1 hnR.le
    nlinarith only [hh,hnR]
  have B := prefix_scalar_bounds α (Fintype.card V) (Fintype.card V) k₀ h Z.card a
    hn hα hdensity hk₀n hretained hhk₀ le_rfl hself ha herror hcutBudget
  have hβ : 0 < α/256 := by positivity
  have houtput1 : P.output j ≤ 1 := by
    have hh := P.output_le j
    linarith only [hh,hτ,hα1]
  have hsizeβ (i : I) : (α/256)*Fintype.card V ≤ ((U i).card : ℝ) := by
    have hh := hsize i
    have hαn := mul_pos hα hnR
    nlinarith only [hh,hαn]
  obtain ⟨S⟩ := ForeignRefinement.exists_small_cut_refinement
    G U H Z Z₀ c p X h (α/256) (α/256) a
      ((2*(Z.card+markedLimit+boundaryLimit+30) : ℕ) : ℝ)
      (P.output j) (τ/2) (markingThreshold*k₀)
    hI hdisjoint hUZ hZ₀ hcover hlabel htrigger hregular B.cluster_reserve
    hembed hdegree hrobust hβ hβ (P.output_pos j) houtput1
    (by linarith only [hτpos]) (by linarith only [hτ,hα])
    B.density B.upper_degree B.error_small B.cut_small hlarge hsizeβ hcut
  exact ⟨S⟩

/-- The concrete refinement at a prefix has exactly the next robust
parameter fixed by the restart schedule. Its moved vertices, marking,
labels, and surviving graphs are those constructed from the actual cut. -/
theorem RestartParameters.refine_at_prefix {α τ ν₀ : ℝ}
    (P : RestartParameters α τ ν₀) (j : Fin 3)
    (hα : 0 < α) (hα1 : α ≤ 1) (hτ : τ ≤ (α/256)/1000)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (H : ∀ i, SimpleGraph (U i))
    (Z Z₀ : Finset V) (c : V → Fin 4) (p : I → Fin 4) (X : Finset V)
    (h k₀ : ℕ) (a : ℝ)
    (hn : 0 < Fintype.card V) (hdensity : α*Fintype.card V ≤ k₀)
    (hk₀n : k₀ ≤ Fintype.card V) (hretained : k₀ ≤ 256*h) (hhk₀ : h ≤ k₀)
    (ha : 0 ≤ a)
    (herror : a+(Z.card : ℝ)+1 ≤ (α/256)*Fintype.card V/10)
    (hcutBudget : ((2*(Z.card+markedLimit+boundaryLimit+30) : ℕ) : ℝ) ≤
      (α/256)*Fintype.card V/10)
    (hI : Fintype.card I ≤ 4)
    (hdisjoint : Pairwise (fun i l => Disjoint (U i) (U l)))
    (hUZ : ∀ i, Disjoint (U i) Z) (hZ₀ : Z₀ ⊆ Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hlabel : ∀ i v, v ∈ U i → c v = p i)
    (htrigger : ∃ i l, p i = p l ∧ ¬ (coreMajority U X i ↔ coreMajority U X l))
    (hregular : ∀ v, G.degree v = h)
    (hembed : ∀ i, H i ≤ G.induce (U i : Set V))
    (hdegree : ∀ i v, (h : ℝ)-a ≤ ((H i).degree v : ℝ))
    (hrobust : ∀ i, IsRobustExpander (H i) (P.output ⟨j.val,by omega⟩) (τ/2))
    (hsize : ∀ i, (α/2)*Fintype.card V ≤ ((U i).card : ℝ))
    (hlarge : 3 < (P.output ⟨j.val,by omega⟩)^2*(α/256)^2*Fintype.card V)
    (hcut : (cutCount (univ : Finset G.edgeSet) X : ℝ) ≤
      h+((2*(Z.card+markedLimit+boundaryLimit+30) : ℕ) : ℝ)) :
    ∃ S : ForeignRefinement.RefinementStep G U H Z Z₀ c p X h a
        (P.output ⟨j.val,by omega⟩) (τ/2) (markingThreshold*k₀),
      ∀ i, IsRobustExpander
        (ForeignRefinement.survivingCore (U i) S.moved (H i))
        (P.input ⟨j.val+1,by omega⟩) τ := by
  obtain ⟨S⟩ := P.refine_current ⟨j.val,by omega⟩ hα hα1 hτ
    G U H Z Z₀ c p X h k₀ a hn hdensity hk₀n hretained hhk₀ ha herror
    hcutBudget hI hdisjoint hUZ hZ₀ hcover hlabel htrigger hregular
    hembed hdegree hrobust hsize hlarge hcut
  refine ⟨S,?_⟩
  intro i
  have hR := S.core_robust i
  rw [P.next j]
  convert hR using 1
  ring

end Overfull.ForeignEpochParameters
