import Overfull.NativeReserve.Realization
import Overfull.AssignedParts.SignaturePools
import Overfull.AssignedParts.CompressionCuts
import Overfull.OneCore.Complement

/-!
# Native pools and endpoint bounds from the embedded simple cores

Every pool retains individual original copies, including parallel copies
of the exceptional pair. Core incidence is bounded by the complementary
degree of the embedded core.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical AssignedParts
open scoped BigOperators

variable {V E : Type*}

inductive PoolKind (Z : Finset V)
  | pair
  | exception (z : ↥Z) (i : Fin 2)
  | crossing
  deriving DecidableEq, Fintype

variable (G : Multigraph V E) [Fintype E]

def poolCopies (U₀ U₁ Z : Finset V) : PoolKind Z → Finset E
  | .pair => G.internalOn univ Z
  | .exception z i => exceptionCorePool G z.val (if i = 0 then U₀ else U₁)
  | .crossing => coreCrossingPool G U₀ U₁

def poolSpecial (Z : Finset V) : PoolKind Z → Finset V
  | .pair => Z
  | .exception z _ => {z.val}
  | .crossing => ∅

def poolArity {Z : Finset V} : PoolKind Z → ℕ
  | .pair => 0
  | .exception _ _ => 1
  | .crossing => 2

private theorem core_choice_disjoint (U₀ U₁ Z : Finset V)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z) (i : Fin 2) :
    Disjoint (if i = 0 then U₀ else U₁) Z := by
  split_ifs <;> assumption

theorem poolCopies_specialEnds (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hZ : Z.card ≤ 2) (p : PoolKind Z) (e : E)
    (he : e ∈ poolCopies G U₀ U₁ Z p) :
    specialEnds G Z e = poolSpecial Z p := by
  cases p with
  | pair =>
    have hends := (mem_filter.mp he).2
    have hsub : (G.edge e).toFinset ⊆ Z := by
      intro v hv
      rcases (G.incident_iff e v).mp (by simpa using hv) with h | h
      · exact h ▸ hends.1
      · exact h ▸ hends.2
    have heq : (G.edge e).toFinset = Z := eq_of_subset_of_card_le hsub (by
      simpa only [Sym2.card_toFinset_of_not_isDiag _ (G.loopless e)] using hZ)
    simp only [specialEnds, poolSpecial, heq, inter_self]
  | exception z i =>
    obtain ⟨_, hz, ho⟩ := mem_filter.mp he
    have hno : G.otherEnd z.val e ∉ Z :=
      fun hh => disjoint_left.mp (core_choice_disjoint U₀ U₁ Z h0Z h1Z i) ho hh
    ext v
    rw [mem_specialEnds, G.edge_eq_otherEnd z.val e hz]
    simp only [Sym2.mem_iff, poolSpecial, mem_singleton]
    constructor
    · rintro ⟨hv | hv, hvZ⟩
      · exact hv
      · exact (hno (hv ▸ hvZ)).elim
    · intro hv
      subst v
      exact ⟨Or.inl rfl, z.property⟩
  | crossing =>
    have hends := (mem_coreCrossings_iff G univ U₀ U₁ h01 e).mp he |>.2
    apply eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨hev, hvZ⟩ := (mem_specialEnds G Z e v).mp hv
    rcases (G.incident_iff e v).mp hev with h | h <;>
      rcases hends with hh | hh
    · exact disjoint_left.mp h0Z hh.1 (h.symm ▸ hvZ)
    · exact disjoint_left.mp h1Z hh.1 (h.symm ▸ hvZ)
    · exact disjoint_left.mp h1Z hh.2 (h.symm ▸ hvZ)
    · exact disjoint_left.mp h0Z hh.2 (h.symm ▸ hvZ)

theorem poolCopies_disjoint_core (U₀ U₁ Z U : Finset V)
    (_h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hU : U = U₀ ∨ U = U₁) (C : SmallCuts.Core G U) (p : PoolKind Z) :
    Disjoint (poolCopies G U₀ U₁ Z p) (OneCore.coreEdges C) := by
  apply disjoint_left.mpr
  intro e he heC
  have hend {v : V} (hv : v ∈ G.edge e) : v ∈ U := OneCore.coreEdges_endpoint C heC hv
  have hUZ : Disjoint U Z := by rcases hU with rfl | rfl <;> assumption
  cases p with
  | pair =>
    exact disjoint_left.mp hUZ (hend ((G.incident_iff e _).mpr (Or.inl rfl)))
      (mem_filter.mp he).2.1
  | exception z i =>
    exact disjoint_left.mp hUZ (hend (mem_filter.mp he).2.1) z.property
  | crossing =>
    obtain ⟨he0, he1⟩ := mem_inter.mp he
    rcases hU with rfl | rfl
    · have hcut := (G.mem_cutOn univ _ e).mp he0 |>.2
      exact hcut (propext ⟨fun _ => hend ((G.incident_iff e _).mpr (Or.inr rfl)),
        fun _ => hend ((G.incident_iff e _).mpr (Or.inl rfl))⟩)
    · have hcut := (G.mem_cutOn univ _ e).mp he1 |>.2
      exact hcut (propext ⟨fun _ => hend ((G.incident_iff e _).mpr (Or.inr rfl)),
        fun _ => hend ((G.incident_iff e _).mpr (Or.inl rfl))⟩)

theorem pool_core_incidence_le_error {U : Finset V} (C : SmallCuts.Core G U)
    (A : Finset E) (hA : Disjoint A (OneCore.coreEdges C))
    (k : ℕ) (a : ℝ) (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ v, (k : ℝ)-a ≤ (C.graph.degree v : ℝ)) (v : ↥U) :
    (G.degreeOn A v.val : ℝ) ≤ a := by
  have hle : G.degreeOn A v.val ≤
      (G.restrictEdges (OneCore.coreEdges C)ᶜ).degree v.val := by
    rw [Multigraph.restrictEdges_degree]
    apply card_le_card
    intro e he
    obtain ⟨heA, hev⟩ := mem_filter.mp he
    exact mem_inter.mpr ⟨mem_compl.mpr (fun heC => disjoint_left.mp hA heA heC),
      (G.mem_incidenceEdges _ _).mpr hev⟩
  exact (Nat.cast_le.mpr hle).trans (OneCore.complement_degree_le_error C k a hregular hdegree v)

theorem poolCopies_pairwiseDisjoint (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hZ : Z.card ≤ 2) :
    Pairwise (fun p q => Disjoint (poolCopies G U₀ U₁ Z p) (poolCopies G U₀ U₁ Z q)) := by
  intro p q hpq
  apply disjoint_left.mpr
  intro e hep heq
  have hs := (poolCopies_specialEnds G U₀ U₁ Z h01 h0Z h1Z hZ p e hep).symm.trans
    (poolCopies_specialEnds G U₀ U₁ Z h01 h0Z h1Z hZ q e heq)
  have hpair (h : e ∈ poolCopies G U₀ U₁ Z .pair) : Z.card = 2 := by
    have hh := poolCopies_specialEnds G U₀ U₁ Z h01 h0Z h1Z hZ .pair e h
    have hsub : (G.edge e).toFinset ⊆ Z := by
      intro v hv
      rcases (G.incident_iff e v).mp (by simpa using hv) with hv | hv
      · exact hv ▸ (mem_filter.mp h).2.1
      · exact hv ▸ (mem_filter.mp h).2.2
    have hc : (G.edge e).toFinset.card ≤ Z.card := card_le_card hsub
    rw [Sym2.card_toFinset_of_not_isDiag _ (G.loopless e)] at hc
    omega
  cases p <;> cases q
  · exact hpq rfl
  · have hh := congrArg card hs
    simp only [poolSpecial, card_singleton] at hh
    have := hpair hep
    omega
  · have hh := congrArg card hs
    simp only [poolSpecial, card_empty] at hh
    have := hpair hep
    omega
  · have hh := congrArg card hs
    simp only [poolSpecial, card_singleton] at hh
    have := hpair heq
    omega
  · rename_i z i w j
    have hzw : z = w := Subtype.ext (singleton_injective hs)
    subst w
    have ho := (mem_filter.mp hep).2.2
    have ho' := (mem_filter.mp heq).2.2
    have hij : i = j := by
      by_contra hij
      fin_cases i <;> fin_cases j <;> simp_all
      · exact disjoint_left.mp h01 ho ho'
      · exact disjoint_left.mp h01 ho' ho
    exact hpq (hij ▸ rfl)
  · have hh := congrArg card hs
    simp [poolSpecial] at hh
  · have hh := congrArg card hs
    simp only [poolSpecial, card_empty] at hh
    have := hpair heq
    omega
  · have hh := congrArg card hs
    simp [poolSpecial] at hh
  · exact hpq rfl

theorem compressedBoundary_exists_pool (M : Finset E) (U₀ U₁ Z : Finset V)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    {e : E} (he : e ∈ compressedBoundary G M U₀ U₁ Z) :
    ∃ p : PoolKind Z, e ∈ poolCopies G U₀ U₁ Z p := by
  rcases mem_union.mp he with he | he
  · obtain ⟨_, hz⟩ := (mem_exceptionalCopies G M Z e).mp he
    obtain ⟨z, hzZ, hze⟩ : ∃ z, z ∈ Z ∧ z ∈ G.edge e := by
      rcases hz with hz | hz
      · exact ⟨_, hz, (G.incident_iff _ _).mpr (Or.inl rfl)⟩
      · exact ⟨_, hz, (G.incident_iff _ _).mpr (Or.inr rfl)⟩
    rcases hcover (G.otherEnd z e) with h0 | h1 | hZ
    · exact ⟨.exception ⟨z,hzZ⟩ 0, mem_filter.mpr ⟨mem_univ _, hze, by simpa using h0⟩⟩
    · exact ⟨.exception ⟨z,hzZ⟩ 1, mem_filter.mpr ⟨mem_univ _, hze, by simpa using h1⟩⟩
    · exact ⟨.pair, G.mem_internalOn_of_incident_otherEnd (mem_univ _) hze hzZ hZ⟩
  · obtain ⟨he0, he1⟩ := mem_inter.mp (paritySelection_subset _ he)
    exact ⟨.crossing, mem_inter.mpr
      ⟨(G.mem_cutOn univ U₀ e).mpr ⟨mem_univ _, (G.mem_cutOn M U₀ e).mp he0 |>.2⟩,
       (G.mem_cutOn univ U₁ e).mpr ⟨mem_univ _, (G.mem_cutOn M U₁ e).mp he1 |>.2⟩⟩⟩

end Overfull.NativeReserve
