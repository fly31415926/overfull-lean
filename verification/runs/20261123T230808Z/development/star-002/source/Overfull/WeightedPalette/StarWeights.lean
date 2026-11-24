import Overfull.AssignedParts.SignaturePools
import Overfull.ResidualPalette.PaletteGrouping

/-!
# Actual star-copy weights of joining pieces

The weight at an exceptional vertex counts original copies to its assigned
old core whose old-core endpoint is occupied by a joining piece. Occupying
the exceptional vertex itself does not block the whole star. The weights
retain parallel multiplicities, have a local support bound, and satisfy a
global incidence bound for an edge-disjoint family of pieces.
-/

noncomputable section

namespace Overfull.WeightedPalette

open Finset Classical
open scoped BigOperators

variable {V E I : Type*} (G : Multigraph V E) [Fintype E]

/-- Actual star copies blocked at their old-core endpoint by a piece. -/
def starBlockedCopies (z : V) (U : Finset V) (M : Finset E) : Finset E :=
  (AssignedParts.exceptionCorePool G z U).filter
    (fun e => G.otherEnd z e ∈ G.edgeSupport M)

/-- The natural weight counts blocked original copies, including parallel copies. -/
def starWeight (z : V) (U : Finset V) (M : Finset E) : ℕ :=
  (starBlockedCopies G z U M).card

@[simp] theorem mem_starBlockedCopies (z : V) (U : Finset V) (M : Finset E) (e : E) :
    e ∈ starBlockedCopies G z U M ↔
      e ∈ AssignedParts.exceptionCorePool G z U ∧
        G.otherEnd z e ∈ G.edgeSupport M := by
  simp only [starBlockedCopies, mem_filter]

/-- The assignment pool is exactly the actual incidence set to the old core. -/
theorem exceptionCorePool_eq_edgesTo (z : V) (U : Finset V) :
    AssignedParts.exceptionCorePool G z U = G.edgesTo z U := by
  ext e
  simp [AssignedParts.exceptionCorePool]

/-- Only occupied old-core endpoints determine the blocked star copies. -/
theorem starBlockedCopies_eq_edgesTo (z : V) (U : Finset V) (M : Finset E) :
    starBlockedCopies G z U M = G.edgesTo z (U ∩ G.edgeSupport M) := by
  ext e
  simp only [mem_starBlockedCopies, exceptionCorePool_eq_edgesTo,
    Multigraph.mem_edgesTo, mem_inter]
  tauto

/-- Every blocked copy remains an original member of the assigned star pool. -/
theorem starBlockedCopies_subset (z : V) (U : Finset V) (M : Finset E) :
    starBlockedCopies G z U M ⊆ AssignedParts.exceptionCorePool G z U :=
  filter_subset _ _

/-- The blocked-copy count is the exact sum of parallel multiplicities
over occupied vertices of the original core. -/
theorem starWeight_eq_sum_parallel (z : V) (U : Finset V) (M : Finset E) :
    starWeight G z U M =
      ∑ v ∈ U ∩ G.edgeSupport M, (G.parallelEdges z v).card := by
  rw [starWeight, starBlockedCopies_eq_edgesTo]
  have hf (v : V) (hv : v ∈ U ∩ G.edgeSupport M) :
      (G.edgesTo z (U ∩ G.edgeSupport M)).filter (fun e => G.otherEnd z e = v) =
        G.parallelEdges z v := by
    ext e
    simp only [mem_filter, Multigraph.mem_edgesTo, Multigraph.mem_parallelEdges]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, h.2.symm ▸ hv⟩, h.2⟩
  calc
    _ = ∑ v ∈ U ∩ G.edgeSupport M,
        ((G.edgesTo z (U ∩ G.edgeSupport M)).filter
          (fun e => G.otherEnd z e = v)).card :=
      card_eq_sum_card_fiberwise (fun e he => ((G.mem_edgesTo z _ e).mp he).2)
    _ = _ := sum_congr rfl (fun v hv => congrArg card (hf v hv))

/-- A multiplicity bound at old-core vertices controls the actual blocked
copies by the occupied part of the old core. -/
theorem starWeight_le_inter_support_mul (z : V) (U : Finset V) (M : Finset E)
    (b : ℕ) (hparallel : ∀ v ∈ U, (G.parallelEdges z v).card ≤ b) :
    starWeight G z U M ≤ (U ∩ G.edgeSupport M).card * b := by
  rw [starWeight_eq_sum_parallel]
  calc
    _ ≤ ∑ _v ∈ U ∩ G.edgeSupport M, b :=
      sum_le_sum (fun v hv => hparallel v (mem_inter.mp hv).1)
    _ = _ := by simp

/-- The local weight retains multiplicity and costs at most one bound
per support vertex. -/
theorem starWeight_le_support_mul (z : V) (U : Finset V) (M : Finset E)
    (b : ℕ) (hparallel : ∀ v ∈ U, (G.parallelEdges z v).card ≤ b) :
    starWeight G z U M ≤ (G.edgeSupport M).card * b :=
  (starWeight_le_inter_support_mul G z U M b hparallel).trans
    (Nat.mul_le_mul_right b (card_le_card inter_subset_right))

/-- An actual piece of at most three copies has star weight at most `6b`. -/
theorem starWeight_le_six_mul (z : V) (U : Finset V) (M : Finset E)
    (b : ℕ) (hparallel : ∀ v ∈ U, (G.parallelEdges z v).card ≤ b)
    (hsize : M.card ≤ 3) : starWeight G z U M ≤ 6 * b :=
  (starWeight_le_support_mul G z U M b hparallel).trans
    (Nat.mul_le_mul_right b (G.edgeSupport_card_le_six hsize))

/-- A prescribed primary piece of at most two copies has weight at most `4b`. -/
theorem starWeight_le_four_mul (z : V) (U : Finset V) (M : Finset E)
    (b : ℕ) (hparallel : ∀ v ∈ U, (G.parallelEdges z v).card ≤ b)
    (hsize : M.card ≤ 2) : starWeight G z U M ≤ 4 * b := by
  apply (starWeight_le_support_mul G z U M b hparallel).trans
  apply Nat.mul_le_mul_right b
  exact (G.edgeSupport_card_le M).trans (Nat.mul_le_mul_left 2 hsize)

/-- Double-count the family weight by original star copies and the load
at each copy's old-core endpoint. -/
theorem sum_starWeight_eq_sum_support_load [Fintype I]
    (z : V) (U : Finset V) (M : I → Finset E) :
    (∑ i, starWeight G z U (M i)) =
      ∑ e ∈ AssignedParts.exceptionCorePool G z U,
        (univ.filter (fun i => G.otherEnd z e ∈ G.edgeSupport (M i))).card := by
  simp only [starWeight, starBlockedCopies, card_eq_sum_ones, sum_filter]
  exact sum_comm

/-- A support-load bound controls the total resource weight by the actual
number of star copies. -/
theorem sum_starWeight_le_of_support_load [Fintype I]
    (z : V) (U : Finset V) (M : I → Finset E) (D : ℕ)
    (hload : ∀ v ∈ U, (univ.filter (fun i => v ∈ G.edgeSupport (M i))).card ≤ D) :
    (∑ i, starWeight G z U (M i)) ≤
      D * (AssignedParts.exceptionCorePool G z U).card := by
  rw [sum_starWeight_eq_sum_support_load]
  calc
    _ ≤ ∑ _e ∈ AssignedParts.exceptionCorePool G z U, D := by
      apply sum_le_sum
      intro e he
      apply hload
      exact ((G.mem_edgesTo z U e).mp ((exceptionCorePool_eq_edgesTo G z U) ▸ he)).2
    _ = _ := by simp [Nat.mul_comm]

/-- Edge-disjoint pieces contained in a set of bounded old-core degree
have total star weight at most `D` times the original star-pool size. -/
theorem sum_starWeight_le_of_degreeOn [Fintype I]
    (z : V) (U : Finset V) (M : I → Finset E) (S : Finset E) (D : ℕ)
    (hdisjoint : Pairwise (fun i j => Disjoint (M i) (M j)))
    (hsubset : ∀ i, M i ⊆ S) (hdegree : ∀ v ∈ U, G.degreeOn S v ≤ D) :
    (∑ i, starWeight G z U (M i)) ≤
      D * (AssignedParts.exceptionCorePool G z U).card := by
  apply sum_starWeight_le_of_support_load G z U M D
  intro v hv
  exact (G.family_support_load_le_degreeOn M S hdisjoint hsubset v).trans (hdegree v hv)

/-- The whole assigned star pool has at most the actual degree of its exception. -/
theorem exceptionCorePool_card_le_degree (z : V) (U : Finset V) :
    (AssignedParts.exceptionCorePool G z U).card ≤ G.degree z := by
  rw [exceptionCorePool_eq_edgesTo]
  exact card_le_card (filter_subset _ _)

/-- A degree cap on the exceptional vertex turns the exact pool-size
estimate into the uniform budget `D * h`. -/
theorem sum_starWeight_le_mul_degree_bound [Fintype I]
    (z : V) (U : Finset V) (M : I → Finset E) (S : Finset E) (D h : ℕ)
    (hdisjoint : Pairwise (fun i j => Disjoint (M i) (M j)))
    (hsubset : ∀ i, M i ⊆ S) (hdegree : ∀ v ∈ U, G.degreeOn S v ≤ D)
    (hz : G.degree z ≤ h) : (∑ i, starWeight G z U (M i)) ≤ D * h :=
  (sum_starWeight_le_of_degreeOn G z U M S D hdisjoint hsubset hdegree).trans
    (Nat.mul_le_mul_left D ((exceptionCorePool_card_le_degree G z U).trans hz))

/-- Blocking at the old-core endpoint commutes with arbitrary finite unions
of pieces. This statement does not require disjointness or matching assumptions. -/
theorem starBlockedCopies_biUnion (z : V) (U : Finset V)
    (T : Finset I) (M : I → Finset E) :
    starBlockedCopies G z U (T.biUnion M) =
      T.biUnion (fun i => starBlockedCopies G z U (M i)) := by
  ext e
  constructor
  · intro he
    obtain ⟨hpool, hv⟩ := (mem_starBlockedCopies G z U _ e).mp he
    obtain ⟨f, hf, hfv⟩ := (G.mem_edgeSupport _ _).mp hv
    obtain ⟨i, hi, hfi⟩ := mem_biUnion.mp hf
    exact mem_biUnion.mpr ⟨i, hi, (mem_starBlockedCopies G z U _ e).mpr
      ⟨hpool, (G.mem_edgeSupport _ _).mpr ⟨f, hfi, hfv⟩⟩⟩
  · intro he
    obtain ⟨i, hi, he⟩ := mem_biUnion.mp he
    obtain ⟨hpool, hv⟩ := (mem_starBlockedCopies G z U _ e).mp he
    obtain ⟨f, hf, hfv⟩ := (G.mem_edgeSupport _ _).mp hv
    exact (mem_starBlockedCopies G z U _ e).mpr
      ⟨hpool, (G.mem_edgeSupport _ _).mpr ⟨f, mem_biUnion.mpr ⟨i, hi, hf⟩, hfv⟩⟩

/-- The sum of piece weights bounds the actual copies blocked by their
whole union, even when their supports overlap. -/
theorem starWeight_biUnion_le (z : V) (U : Finset V)
    (T : Finset I) (M : I → Finset E) :
    starWeight G z U (T.biUnion M) ≤ ∑ i ∈ T, starWeight G z U (M i) := by
  simp only [starWeight, starBlockedCopies_biUnion]
  exact card_biUnion_le

/-- A weighted palette budget controls the actual star copies blocked by
the complete grouped color class. -/
theorem starWeight_groupedCopies_le [Fintype I] {h : ℕ}
    (z : V) (U : Finset V) (M : I → Finset E) (c : I → Fin h) (i : Fin h) :
    starWeight G z U (NativeReserve.groupedCopies M c i) ≤
      ∑ j ∈ univ.filter (fun j => c j = i), starWeight G z U (M j) :=
  starWeight_biUnion_le G z U _ M

end Overfull.WeightedPalette
