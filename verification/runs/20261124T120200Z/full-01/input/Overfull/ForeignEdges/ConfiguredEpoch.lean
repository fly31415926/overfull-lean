import Overfull.ForeignEdges.Epoch
import Overfull.ForeignEdges.ProcessParameters

/-!
# Configuring an actual epoch from a process entry

The entry bounds supply every scalar hypothesis of the epoch constructor.
The packing rules are chosen from the actual initial core graphs, before
any transcript, and the prescribed classes come from a fresh maximizing
assignment in the actual entry graph.  All static fields of the resulting
setup reduce definitionally to the entry and the fixed restart parameters.
-/

namespace Overfull.ForeignProcess

open Finset Classical SimpleGraph ForceMatching SafePrescription MatchingProbability
open ForeignEpochParameters ForeignEpoch ForeignPhase ForeignRuleCompletion ForeignAssignment

universe u v
variable {V : Type u} {I : Type v} [Fintype V] [Fintype I]
variable {α τ ν₀ : ℝ} {G₀ : SimpleGraph V} {U₀ : I → Finset V}
variable {Zinit : Finset V} {k₀ : ℕ} {a₀ : ℝ}
variable {P : RestartParameters.{u,u,v} α τ ν₀} {j : Fin 4}

namespace Entry

/-- Every actual initial core degree is bounded above by the regular
ambient degree, using its graph embedding. -/
theorem core_degree_upper (E : Entry G₀ U₀ Zinit k₀ a₀ P j)
    (i : I) (v : E.U i) : ((E.H i).degree v : ℝ) ≤ E.h := by
  have hle := (Replacement.lift (E.U i) (E.H i)).degree_le_of_le (v := v.val)
    (Replacement.lift_le (E.U i) (E.H i) E.G (E.core_embed i))
  rw [Replacement.lift_degree,E.regular] at hle
  exact_mod_cast hle

/-- Certified core rules exist for the current entry graphs.  Their
certificates quantify over all future consistent admissible transcripts. -/
theorem exists_core_rules (E : Entry G₀ U₀ Zinit k₀ a₀ P j)
    (B : EntryBounds E) :
    ∃ rule : ∀ i, (s : ℕ) →
        (Fin s → Finset (E.U i) × (E.H i).Subgraph) →
        Finset (E.U i) → (E.H i).Subgraph,
      ∀ i, RuleCertificate (E.H i)
        (Nat.floor ((E.h : ℝ)-(α/1024)*(E.U i).card))
        (P.packingError j) (P.output j) (τ/2) (rule i) := by
  have hΔ (i : I) : (α/256)*(E.U i).card ≤ (E.h : ℝ) := by
    have hr := (B.core_prefix 0 (Nat.zero_le _) i).reserve_density
    simp only [Nat.sub_zero] at hr
    linarith only [hr]
  have hdegree (i : I) (v : E.U i) :
      |((E.H i).degree v : ℝ)-(E.h : ℝ)| ≤ P.packingError j*(E.U i).card := by
    have hl := E.core_degree i v
    have hu := E.core_degree_upper i v
    have he := B.packing_error i
    have hZ : (0 : ℝ) ≤ E.Z.card := Nat.cast_nonneg _
    rw [abs_of_nonpos (sub_nonpos.mpr hu)]
    linarith only [hl,he,hZ]
  exact exists_certified_core_rules E.U E.H (α/256) (α/1024) (P.input j) τ
    (P.packingError j) (P.output j) (P.packingOrder j) (P.packing j) E.h
    B.packing_order E.core_robust hΔ hdegree

/-- Install a chosen certified rule and actual prescribed classes into
the epoch constructor. Every non-proof field is explicitly fixed here. -/
noncomputable def setup (E : Entry G₀ U₀ Zinit k₀ a₀ P j)
    (hI : Fintype.card I ≤ 4) (B : EntryBounds E)
    (rule : ∀ i, (s : ℕ) →
      (Fin s → Finset (E.U i) × (E.H i).Subgraph) →
      Finset (E.U i) → (E.H i).Subgraph)
    (hcertificate : ∀ i, RuleCertificate (E.H i)
      (Nat.floor ((E.h : ℝ)-(α/1024)*(E.U i).card))
      (P.packingError j) (P.output j) (τ/2) (rule i))
    (classes : ℕ → Finset E.G.edgeSet)
    (hclasses : ∀ s < 3*E.h/4, ∀ R : SimpleGraph V,
      (currentClass E.G R (classes s)).IsMatching ∧
      (∀ u v, (currentClass E.G R (classes s)).Adj u v → u ∈ E.Z ∨ v ∈ E.Z) ∧
      (∀ u v, (currentClass E.G R (classes s)).Adj u v → E.c u = E.c v)) :
    Setup E.G E.U E.H := by
  have hτ : 0 < τ := (P.input_pos j).trans_le (P.input_le j)
  refine {
    Z := E.Z
    marked := E.marked
    vertexLabel := E.c
    coreLabel := E.p
    initialDegree := E.h
    originalDegree := k₀
    markedBound := markedLimit
    density := α/256
    safeNu := min (P.input j) (P.output j)
    safeRange := τ
    packingError := P.packingError j
    packingOutput := P.output j
    packingRange := τ/2
    safeError := P.safeError j
    safeOrder := P.safeOrder j
    coreError := a₀+(j.val : ℝ)
    horizon := fun i => Nat.floor ((E.h : ℝ)-(α/1024)*(E.U i).card)
    rule := rule
    classes := classes
    preparation := P.preparation j
    certificate := hcertificate
    nu_pos := lt_min (P.input_pos j) (P.output_pos j)
    nu_le_output := min_le_right _ _
    range_le := by linarith only [hτ]
    horizon_le := ?_
    order_le := B.safe_order
    core_count := hI
    disjoint := E.core_disjoint
    core_exceptional_disjoint := E.core_exceptional_disjoint
    marked_subset := E.marked_subset
    marked_card := E.marked_card_le hI
    cover := E.cover
    labels := E.homogeneous
    regular := E.regular
    degree_le_original := E.degree_le
    density_reserve := (B.ambient_prefix (3*E.h/4) le_rfl).density
    strict_reserve := (B.ambient_prefix (3*E.h/4) le_rfl).safe_reserve
    no_overfull := E.no_overfull
    error_nonneg := B.error_nonneg
    safe_budget := B.safe_error
    core_size := fun i => (B.core_prefix 0 (Nat.zero_le _) i).core_order
    core_embed := E.core_embed
    core_degree := E.core_degree
    packing_budget := ?_
    crossing := E.crossing_card_le hI
    foreign_degree := ?_
    class_properties := hclasses
  }
  · intro i
    simpa only [Nat.sub_zero] using (B.core_prefix 0 (Nat.zero_le _) i).horizon
  · intro i
    have he := B.packing_error i
    have hZ : (0 : ℝ) ≤ E.Z.card := Nat.cast_nonneg _
    linarith only [he,hZ]
  · intro v hv hvm
    have he := E.cross_degree v hv hvm
    dsimp only [markingThreshold] at he
    linarith only [he]

end Entry

/-- The chosen fresh assignment, color classes, and certified fixed rules
for an actual process entry. Its setup is a definition, so all static
entry and parameter projections remain transparent. -/
structure FreshEpoch (E : Entry G₀ U₀ Zinit k₀ a₀ P j)
    (B : EntryBounds E) (hI : Fintype.card I ≤ 4) where
  assignment : V → I
  classes : ℕ → Finset E.G.edgeSet
  rule : ∀ i, (s : ℕ) →
    (Fin s → Finset (E.U i) × (E.H i).Subgraph) →
    Finset (E.U i) → (E.H i).Subgraph
  certificate : ∀ i, RuleCertificate (E.H i)
    (Nat.floor ((E.h : ℝ)-(α/1024)*(E.U i).card))
    (P.packingError j) (P.output j) (τ/2) (rule i)
  maximizing : ∀ v ∈ E.Z \ E.marked, E.p (assignment v) = E.c v ∧
    ∀ i, E.p i = E.c v → (coreNeighbors E.G E.U v i).card ≤
      (coreNeighbors E.G E.U v (assignment v)).card
  class_union : (range (3*E.h/4)).biUnion classes =
    foreignEdges E.G E.U (E.Z \ E.marked) E.c E.p assignment
  class_properties : ∀ s < 3*E.h/4, ∀ R : SimpleGraph V,
    (currentClass E.G R (classes s)).IsMatching ∧
    (∀ u v, (currentClass E.G R (classes s)).Adj u v → u ∈ E.Z ∨ v ∈ E.Z) ∧
    (∀ u v, (currentClass E.G R (classes s)).Adj u v → E.c u = E.c v)

/-- The configured epoch retains the entry fields definitionally. -/
noncomputable def FreshEpoch.setup
    {E : Entry G₀ U₀ Zinit k₀ a₀ P j} {B : EntryBounds E}
    {hI : Fintype.card I ≤ 4} (D : FreshEpoch E B hI) : Setup E.G E.U E.H :=
  E.setup hI B D.rule D.certificate D.classes D.class_properties

/-- Every bounded actual entry admits a fresh maximizing assignment,
actual classes, and fixed rules chosen before the epoch transcript. -/
theorem Entry.exists_fresh_epoch [Nonempty I]
    (E : Entry G₀ U₀ Zinit k₀ a₀ P j) (hI : Fintype.card I ≤ 4)
    (B : EntryBounds E) : Nonempty (FreshEpoch E B hI) := by
  have hrepresented : ∀ v ∈ E.Z \ E.marked, ∃ i, E.p i = E.c v := by
    intro v hv
    obtain ⟨i,hi⟩ := E.represented v (mem_sdiff.mp hv).2
    exact ⟨i,hi.symm⟩
  have hdisjoint (i : I) : Disjoint (E.U i) (E.Z \ E.marked) :=
    (E.core_exceptional_disjoint i).mono_right sdiff_subset
  have hsmall : 4*(a₀+(j.val : ℝ)) ≤ 3*(E.h : ℝ) := by
    simpa only [Nat.sub_zero] using (B.ambient_prefix 0 (Nat.zero_le _)).assignment_degree
  obtain ⟨rule,hcertificate⟩ := E.exists_core_rules B
  obtain ⟨assignment,classes,hmax,hunion,hclasses,_hdeletions⟩ :=
    exists_fresh_phase_data E.G E.U (E.Z \ E.marked) E.Z E.c E.p sdiff_subset
      E.homogeneous E.core_disjoint hdisjoint hI hrepresented E.H E.core_embed
      E.h (a₀+(j.val : ℝ)) E.regular E.core_degree hsmall
  exact ⟨{
    assignment := assignment
    classes := classes
    rule := rule
    certificate := hcertificate
    maximizing := hmax
    class_union := hunion
    class_properties := hclasses
  }⟩

end Overfull.ForeignProcess
