import Overfull.ForeignEdges.ProcessState
import Overfull.ForeignEdges.PrefixParameters

/-!
# One original parameter choice for every actual process state

The original graph-order threshold and core error are chosen before the
graph, its exceptional set, and every restart.  The actual core-loss and
exceptional-growth fields of an entry state then supply all preparation,
packing, and refinement budgets, including the degree reserve at every
prefix of its epoch.
-/

namespace Overfull.ForeignProcess

open Finset Classical ForeignEpochParameters ForeignConcatenation

variable {V I : Type*} [Fintype V] [Fintype I]
variable {α τ ν₀ : ℝ} {G₀ : SimpleGraph V} {U₀ : I → Finset V}
variable {Zinit : Finset V} {k₀ : ℕ} {a₀ : ℝ}
variable {P : RestartParameters α τ ν₀} {j : Fin 4}

/-- All numerical hypotheses for an actual epoch entry and every one of
its possible matching prefixes.  The core and exceptional orders here
are the cardinalities of the sets stored in the actual entry. -/
structure EntryBounds (E : Entry G₀ U₀ Zinit k₀ a₀ P j) : Prop where
  order_pos : 0 < Fintype.card V
  error_nonneg : 0 ≤ a₀+(j.val : ℝ)
  safe_order : P.safeOrder j ≤ Fintype.card V
  safe_error : a₀+(j.val : ℝ)+(E.Z.card : ℝ)+1 ≤ P.safeError j*Fintype.card V
  core_size : ∀ i, (α/2)*Fintype.card V ≤ ((E.U i).card : ℝ)
  packing_order : ∀ i, P.packingOrder j ≤ (E.U i).card
  packing_error : ∀ i,
    a₀+(j.val : ℝ)+(E.Z.card : ℝ)+1 ≤ P.packingError j*(E.U i).card
  packing_footprint : ∀ i,
    ((2*(boundaryLimit+E.Z.card+3) : ℕ) : ℝ) ≤ P.packingError j*(E.U i).card
  small_error : a₀+(j.val : ℝ)+(E.Z.card : ℝ)+1 ≤
    (α/256)*Fintype.card V/10
  small_cut : ((2*(E.Z.card+markedLimit+boundaryLimit+30) : ℕ) : ℝ) ≤
    (α/256)*Fintype.card V/10
  robust_large : 3 < (P.output j)^2*(α/256)^2*Fintype.card V
  degree_reserve : ∀ s ≤ 3*E.h/4, k₀ ≤ 256*(E.h-s)
  ambient_prefix : ∀ s ≤ 3*E.h/4,
    PrefixScalarBounds α (Fintype.card V) (Fintype.card V) k₀ (E.h-s)
      E.Z.card (a₀+(j.val : ℝ))
  core_prefix : ∀ s ≤ 3*E.h/4, ∀ i,
    PrefixScalarBounds α (Fintype.card V) (E.U i).card k₀ (E.h-s)
      E.Z.card (a₀+(j.val : ℝ))

end Overfull.ForeignProcess

namespace Overfull.ForeignEpochParameters

open Finset Classical ForeignProcess ForeignConcatenation

/-- A single original choice supplies every local hypothesis for every
actual entry of the four-epoch process.  In particular the varying core
types and exceptional orders are quantified after the parameter choice. -/
theorem RestartParameters.exists_process_parameters {α τ ν₀ : ℝ}
    (P : RestartParameters α τ ν₀) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ {V I : Type*} [Fintype V] [Fintype I]
        (G₀ : SimpleGraph V) (U₀ : I → Finset V) (Zinit : Finset V)
        (k₀ : ℕ) (a₀ : ℝ) (j : Fin 4) (E : Entry G₀ U₀ Zinit k₀ a₀ P j),
        n₀ ≤ Fintype.card V → α*Fintype.card V ≤ k₀ → k₀ ≤ Fintype.card V →
        (∀ i, α*Fintype.card V ≤ ((U₀ i).card : ℝ)) →
        0 ≤ a₀ → a₀+(Zinit.card : ℝ)+1 ≤ ε*Fintype.card V → EntryBounds E := by
  obtain ⟨ε,hε,n₀,huniform⟩ := P.uniform_initial_parameters hα
  refine ⟨ε,hε,n₀,?_⟩
  intro V I _ _ G₀ U₀ Zinit k₀ a₀ j E hn hdensity hk₀n hsize ha₀ hbudget
  have hj : j.val ≤ 3 := by omega
  have herrorShift : a₀+(j.val : ℝ) ≤ a₀+3 := by
    exact add_le_add_left (by exact_mod_cast hj) a₀
  have hexceptional : E.Z.card ≤ Zinit.card+3 := by
    have hh := E.exceptional_card
    omega
  have hself : α*Fintype.card V ≤ (Fintype.card V : ℝ) := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hα1 (Nat.cast_nonneg (Fintype.card V))
  obtain ⟨hnpos,_,_,hambient⟩ :=
    huniform (Fintype.card V) (Fintype.card V) Zinit.card E.Z.card j.val
      a₀ (a₀+(j.val : ℝ)) hn le_rfl hself hj ha₀ herrorShift hexceptional hbudget
  obtain ⟨_,hsafeOrder,_,_,hsafe,hsmall,hcut,hlarge⟩ := hambient j
  have hcore (i : I) :
      (α/2)*Fintype.card V ≤ ((E.U i).card : ℝ) ∧
      P.packingOrder j ≤ (E.U i).card ∧
      a₀+(j.val : ℝ)+(E.Z.card : ℝ)+1 ≤ P.packingError j*(E.U i).card ∧
      ((2*(boundaryLimit+E.Z.card+3) : ℕ) : ℝ) ≤ P.packingError j*(E.U i).card := by
    obtain ⟨_,hretained,_,hstage⟩ :=
      huniform (Fintype.card V) (U₀ i).card Zinit.card E.Z.card j.val
        a₀ (a₀+(j.val : ℝ)) hn (card_le_univ _) (hsize i) hj
        ha₀ herrorShift hexceptional hbudget
    obtain ⟨horder,_,hpack,hfootprint,_⟩ := hstage j
    have hactual := E.core_card_lower i
    have hactualR : (((U₀ i).card-j.val : ℕ) : ℝ) ≤ (E.U i).card := by
      exact_mod_cast hactual
    have hmul := mul_le_mul_of_nonneg_left hactualR (P.packingError_pos j).le
    exact ⟨hretained.trans hactualR,horder.trans hactual,hpack.trans hmul,
      hfootprint.trans hmul⟩
  have ha : 0 ≤ a₀+(j.val : ℝ) := add_nonneg ha₀ (Nat.cast_nonneg _)
  have hreserve (s : ℕ) (hs : s ≤ 3*E.h/4) : k₀ ≤ 256*(E.h-s) := by
    have hh := within_epoch_degree_reserve k₀ E.h j.val s E.retained_degree hs
    have hpower : 4^(j.val+1) ≤ 256 := by
      have hjlt := j.isLt
      interval_cases j.val <;> norm_num
    exact hh.trans (Nat.mul_le_mul_right _ hpower)
  have hdegree (s : ℕ) : E.h-s ≤ k₀ := (Nat.sub_le _ _).trans E.degree_le
  have hselfHalf : (α/2)*Fintype.card V ≤ (Fintype.card V : ℝ) := by
    have hnR : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    nlinarith only [hself,hnR]
  refine ⟨hnpos,ha,hsafeOrder,hsafe,fun i => (hcore i).1,
    fun i => (hcore i).2.1,fun i => (hcore i).2.2.1,
    fun i => (hcore i).2.2.2,hsmall,hcut,hlarge,hreserve,?_,?_⟩
  · intro s hs
    exact prefix_scalar_bounds α (Fintype.card V) (Fintype.card V) k₀
      (E.h-s) E.Z.card (a₀+(j.val : ℝ)) hnpos hα hdensity hk₀n
      (hreserve s hs) (hdegree s) le_rfl hselfHalf ha hsmall hcut
  · intro s hs i
    exact prefix_scalar_bounds α (Fintype.card V) (E.U i).card k₀
      (E.h-s) E.Z.card (a₀+(j.val : ℝ)) hnpos hα hdensity hk₀n
      (hreserve s hs) (hdegree s) (card_le_univ _) (hcore i).1 ha hsmall hcut

end Overfull.ForeignEpochParameters
