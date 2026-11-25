import Overfull.NativeReserve.WeightedPacking
import Overfull.AssignedParts.PartnerSignatures

/-!
# Native reserves with all exceptional partners retained

The finite partner code allows any exceptional set of size at most five.
The selected boundaries are actual compressed perfect matchings, not merely
independent numerical supplies for each pair. Each boundary has at most six
copies. The heavy code may have zero, one, or two exceptional matching pairs.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical AssignedParts AssignedParts.NativeWeights CircuitPatterns
open scoped BigOperators

variable {V E : Type*}

/-- Actual disjoint compressed boundaries with an unchanged partner code. -/
structure PartnerBoundaryPacking (G : Multigraph V E) (U₀ U₁ Z : Finset V)
    (M : Finset E) (r : ℕ) where
  parent : Fin r → Finset E
  perfect : ∀ i, G.IsPerfectMatching (parent i)
  sameSignature : ∀ i, partnerSignature G (parent i) U₀ Z = partnerSignature G M U₀ Z
  disjoint : Pairwise (fun i j =>
    Disjoint (compressedBoundary G (parent i) U₀ U₁ Z)
      (compressedBoundary G (parent j) U₀ U₁ Z))

namespace PartnerBoundaryPacking

variable {G : Multigraph V E} {U₀ U₁ Z : Finset V} {M : Finset E} {r : ℕ}
  (Q : PartnerBoundaryPacking G U₀ U₁ Z M r)

def boundary (i : Fin r) : Finset E := compressedBoundary G (Q.parent i) U₀ U₁ Z

theorem isMatching (i : Fin r) : G.IsMatching (Q.boundary i) :=
  compressedBoundary_isMatching G ((Q.perfect i).isMatching G) U₀ U₁ Z

theorem card_le (i : Fin r) : (Q.boundary i).card ≤ Z.card + 1 :=
  compressedBoundary_card_le G ((Q.perfect i).isMatching G) U₀ U₁ Z

theorem exceptional_degree (i : Fin r) {z : V} (hz : z ∈ Z) :
    G.degreeOn (Q.boundary i) z = 1 :=
  compressedBoundary_exceptional_degree G (Q.perfect i) U₀ U₁ Z hz

theorem assignedParts (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (i : Fin r) :
    corePart G (Q.parent i) Z U₀ = corePart G M Z U₀ ∧
      corePart G (Q.parent i) Z U₁ = corePart G M Z U₁ ∧
      pairPart G (Q.parent i) Z = pairPart G M Z :=
  assignedParts_eq_of_partnerSignature_eq G (Q.perfect i) hM U₀ U₁ Z
    h01 h0Z h1Z hcover (Q.sameSignature i)

/-- Each original exceptional pair receives one actual parallel copy from
every reserved boundary, with distinct copies at different reserve indices. -/
theorem exists_pair_injection (hM : G.IsPerfectMatching M)
    (e : G.internalOn M Z) :
    ∃ g : Fin r → E, Function.Injective g ∧
      ∀ i, g i ∈ Q.boundary i ∧ G.edge (g i) = G.edge e.val := by
  have hex (i : Fin r) : ∃ f ∈ Q.boundary i, G.edge f = G.edge e.val := by
    obtain ⟨f, hf, heq⟩ := exists_parallel_of_partnerSignature_eq G hM (Q.perfect i)
      U₀ Z (Q.sameSignature i).symm e.property
    refine ⟨f, ?_, heq⟩
    exact compressedBoundary_retains_exceptional G (Q.parent i) U₀ U₁ Z
      ((mem_exceptionalCopies G (Q.parent i) Z f).mpr
        ⟨(mem_filter.mp hf).1, Or.inl (mem_filter.mp hf).2.1⟩)
  choose g hg using hex
  refine ⟨g, ?_, hg⟩
  intro i j hij
  by_contra hn
  exact disjoint_left.mp (Q.disjoint hn) (hg i).1 (hij.symm ▸ (hg j).1)

end PartnerBoundaryPacking

variable {S : Type*} [Fintype S] {G : Multigraph V E} {k : ℕ}
  (D : MultigraphMatchingProbability.Distribution G k S)

def partnerSignatureWeight (U₀ Z : Finset V) (p : PartnerSignature Z) : ℝ :=
  aggregateWeight (scaledWeight D) (fun s => partnerSignature G (D.matching s) U₀ Z) p

theorem partnerSignatureWeight_nonneg (U₀ Z : Finset V) (p : PartnerSignature Z) :
    0 ≤ partnerSignatureWeight D U₀ Z p :=
  aggregateWeight_nonneg _ (scaledWeight_nonneg D) _ p

theorem partnerSignatureWeight_sum (U₀ Z : Finset V) :
    ∑ p, partnerSignatureWeight D U₀ Z p = k := aggregateWeight_total D _

/-- Selection considers the entire finite code space, without assuming
that the heavy representative has any particular number of pair components. -/
theorem exists_heavy_partner_signature (hk : 0 < k) (U₀ Z : Finset V)
    (hZ : Z.card ≤ 5) :
    ∃ s, 0 < scaledWeight D s ∧
      (k : ℝ) / (7 ^ 5 : ℕ) ≤
        partnerSignatureWeight D U₀ Z (partnerSignature G (D.matching s) U₀ Z) := by
  obtain ⟨p, s, hs, hpos, hw⟩ := exists_heavy_code D hk
    (fun s => partnerSignature G (D.matching s) U₀ Z) (7 ^ 5) (by norm_num)
    (card_partnerSignature_le_seven_pow_five Z hZ)
  exact ⟨s, hpos, by simpa [partnerSignatureWeight, hs] using hw⟩

/-- The same native weight simultaneously packs whole actual boundaries. -/
theorem exists_partner_boundaryPacking (hk : 0 < k) (U₀ U₁ Z : Finset V)
    (s : S) (r : ℕ)
    (hweight : (r : ℝ) * (Z.card + 1) ≤
      partnerSignatureWeight D U₀ Z (partnerSignature G (D.matching s) U₀ Z)) :
    Nonempty (PartnerBoundaryPacking G U₀ U₁ Z (D.matching s) r) := by
  obtain ⟨f, hf, hd⟩ := exists_disjoint_selected_family D hk
    (fun t => partnerSignature G (D.matching t) U₀ Z)
    (fun t => compressedBoundary G (D.matching t) U₀ U₁ Z)
    (fun t => compressedBoundary_subset G (D.matching t) U₀ U₁ Z)
    (partnerSignature G (D.matching s) U₀ Z) (Z.card + 1) (by omega)
    (fun t => compressedBoundary_card_le G ((D.perfect t).isMatching G) U₀ U₁ Z)
    r (by simpa only [Nat.cast_add, Nat.cast_one] using hweight)
  exact ⟨⟨fun i => D.matching (f i), fun i => D.perfect (f i), hf, hd⟩⟩

theorem linear_partner_reserve_bounds (k : ℕ) (hk : 201684 ≤ k) :
    (k : ℝ) / 201684 ≤ (⌊(k : ℝ) / 100842⌋₊ : ℝ) ∧
      6 * (⌊(k : ℝ) / 100842⌋₊ : ℝ) ≤ (k : ℝ) / 16807 := by
  have hlo := Nat.lt_floor_add_one ((k : ℝ) / 100842)
  have hhi := Nat.floor_le (show (0 : ℝ) ≤ k / 100842 by positivity)
  have hkR : (201684 : ℝ) ≤ k := by exact_mod_cast hk
  constructor <;> nlinarith

/-- A regular non-overfull host constructs a linear disjoint reserve with
all partner identities. No heavy pattern or pair supply is assumed. -/
theorem exists_linear_partner_boundary_reserve [Fintype V] [Fintype E]
    (G : Multigraph V E) (k : ℕ) (hk : 201684 ≤ k)
    (hregular : ∀ v, G.degree v = k)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull k X)
    (U₀ U₁ Z : Finset V) (hZ : Z.card ≤ 5) :
    ∃ (r : ℕ) (M : Finset E), G.IsPerfectMatching M ∧ (k : ℝ) / 201684 ≤ r ∧
      Nonempty (PartnerBoundaryPacking G U₀ U₁ Z M r) := by
  obtain ⟨S, hS, ⟨D⟩⟩ := MultigraphMatchingProbability.exists_distribution (G := G)
    (show 0 < k by omega) hregular hno
  letI := hS
  obtain ⟨s, _, hs⟩ := exists_heavy_partner_signature D (by omega) U₀ Z hZ
  obtain ⟨hr, hb⟩ := linear_partner_reserve_bounds k hk
  refine ⟨⌊(k : ℝ) / 100842⌋₊, D.matching s, D.perfect s, hr, ?_⟩
  apply exists_partner_boundaryPacking D (by omega) U₀ U₁ Z s
  have hZreal : (Z.card : ℝ) + 1 ≤ 6 := by exact_mod_cast (show Z.card + 1 ≤ 6 by omega)
  have hmul := mul_le_mul_of_nonneg_left hZreal
    (Nat.cast_nonneg ⌊(k : ℝ) / 100842⌋₊ : (0 : ℝ) ≤ _)
  norm_num at hs
  nlinarith

end Overfull.NativeReserve
