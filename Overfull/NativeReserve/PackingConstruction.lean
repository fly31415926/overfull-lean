import Overfull.NativeReserve.WeightedPacking
import Overfull.AssignedParts.NativePatternConstruction

/-!
# An actual disjoint reserve with one native assignment signature

The reserve consists of compressed boundaries of original perfect matchings.
Each boundary has at most three copies when there are at most two exceptions.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical AssignedParts AssignedParts.NativeWeights
open scoped BigOperators

variable {V E : Type*}

/-- Parent matchings certify the signature and parity of the small boundaries.
Disjointness is required only for those boundaries. -/
structure BoundaryPacking (G : Multigraph V E) (U₀ U₁ Z : Finset V)
    (M : Finset E) (r : ℕ) where
  parent : Fin r → Finset E
  perfect : ∀ i, G.IsPerfectMatching (parent i)
  sameSignature : ∀ i, coarseSignature G (parent i) U₀ Z = coarseSignature G M U₀ Z
  disjoint : Pairwise (fun i j =>
    Disjoint (compressedBoundary G (parent i) U₀ U₁ Z)
      (compressedBoundary G (parent j) U₀ U₁ Z))

namespace BoundaryPacking

variable {G : Multigraph V E} {U₀ U₁ Z : Finset V} {M : Finset E} {r : ℕ}
  (Q : BoundaryPacking G U₀ U₁ Z M r)

def boundary (i : Fin r) : Finset E := compressedBoundary G (Q.parent i) U₀ U₁ Z

theorem isMatching (i : Fin r) : G.IsMatching (Q.boundary i) :=
  compressedBoundary_isMatching G ((Q.perfect i).isMatching G) U₀ U₁ Z

theorem pairwise_disjoint : Pairwise (fun i j => Disjoint (Q.boundary i) (Q.boundary j)) :=
  Q.disjoint

theorem card_le (i : Fin r) : (Q.boundary i).card ≤ Z.card+1 :=
  compressedBoundary_card_le G ((Q.perfect i).isMatching G) U₀ U₁ Z

theorem exceptional_degree (i : Fin r) {z : V} (hz : z ∈ Z) :
    G.degreeOn (Q.boundary i) z = 1 :=
  compressedBoundary_exceptional_degree G (Q.perfect i) U₀ U₁ Z hz

theorem retains_internal_pairs (i : Fin r) :
    G.internalOn (Q.boundary i) Z = G.internalOn (Q.parent i) Z :=
  compressedBoundary_internalOn G (Q.parent i) U₀ U₁ Z

theorem assignedLabel (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2) (i : Fin r) :
    AssignedParts.assignedLabel G (Q.boundary i) U₀ U₁ Z =
      AssignedParts.assignedLabel G M U₀ U₁ Z := by
  rw [boundary, compressedBoundary_assignedLabel]
  exact assignedLabel_eq_of_signature_eq G (Q.perfect i) hM U₀ U₁ Z
    h01 h0Z h1Z hcover hZ (Q.sameSignature i)

theorem uncovered_even
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (i : Fin r) :
    Even (U₀ \ G.edgeSupport (Q.boundary i)).card ∧
      Even (U₁ \ G.edgeSupport (Q.boundary i)).card :=
  compressedBoundary_uncovered_even G (Q.perfect i) U₀ U₁ Z h01 h0Z h1Z hcover

theorem crossing_card (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2) (i : Fin r) :
    (G.cutOn (Q.boundary i) U₀ ∩ G.cutOn (Q.boundary i) U₁).card =
      (G.cutOn M U₀ ∩ G.cutOn M U₁).card % 2 := by
  rw [boundary, compressedBoundary_coreCrossing_card G U₀ U₁ Z h01 h0Z h1Z]
  exact coreCrossing_parity_eq_of_signature_eq G (Q.perfect i) hM U₀ U₁ Z
    h01 h0Z h1Z hcover hZ (Q.sameSignature i)

end BoundaryPacking

variable {S : Type*} [Fintype S] {G : Multigraph V E} {k : ℕ}
  (D : MultigraphMatchingProbability.Distribution G k S)

/-- Native weight directly packs the compressed original copies. -/
theorem exists_boundaryPacking (hk : 0 < k) (U₀ U₁ Z : Finset V)
    (hZ : Z.card ≤ 2) (s : S) (r : ℕ)
    (hweight : (r : ℝ)*3 ≤ signatureWeight D U₀ Z
      (coarseSignature G (D.matching s) U₀ Z)) :
    Nonempty (BoundaryPacking G U₀ U₁ Z (D.matching s) r) := by
  obtain ⟨f, hf, hd⟩ := exists_disjoint_selected_family D hk
    (fun t => coarseSignature G (D.matching t) U₀ Z)
    (fun t => compressedBoundary G (D.matching t) U₀ U₁ Z)
    (fun t => compressedBoundary_subset G (D.matching t) U₀ U₁ Z)
    (coarseSignature G (D.matching s) U₀ Z) 3 (by omega)
    (fun t => (compressedBoundary_card_le G ((D.perfect t).isMatching G)
      U₀ U₁ Z).trans (by omega)) r hweight
  exact ⟨⟨fun i => D.matching (f i), fun i => D.perfect (f i), hf, hd⟩⟩

theorem linear_boundary_reserve_bounds (k : ℕ) (hk : 30 ≤ k) :
    (k : ℝ)/30 ≤ (⌊(k : ℝ)/15⌋₊ : ℝ) ∧
      3*(⌊(k : ℝ)/15⌋₊ : ℝ) ≤ (k : ℝ)/5 := by
  have hlo := Nat.lt_floor_add_one ((k : ℝ)/15)
  have hhi := Nat.floor_le (show (0 : ℝ) ≤ k/15 by positivity)
  have hkR : (30 : ℝ) ≤ k := by exact_mod_cast hk
  constructor <;> nlinarith

/-- A linear native reserve is available without any hypothesis about a
later residual or a fractional decomposition of that residual. -/
theorem exists_linear_boundary_reserve [Fintype V] [Fintype E]
    (G : Multigraph V E) (k : ℕ) (hk : 30 ≤ k)
    (hregular : ∀ v, G.degree v = k)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull k X)
    (U₀ U₁ Z : Finset V) (hZ : Z.card ≤ 2) :
    ∃ r M, G.IsPerfectMatching M ∧ (k : ℝ)/30 ≤ r ∧
      Nonempty (BoundaryPacking G U₀ U₁ Z M r) := by
  obtain ⟨S, _, ⟨D⟩⟩ := MultigraphMatchingProbability.exists_distribution G
    (show 0 < k by omega) hregular hno
  obtain ⟨s, _, hs⟩ := exists_heavy_signature D (by omega) U₀ Z hZ
  obtain ⟨hr, hb⟩ := linear_boundary_reserve_bounds k hk
  refine ⟨⌊(k : ℝ)/15⌋₊, D.matching s, D.perfect s, hr, ?_⟩
  apply exists_boundaryPacking D (by omega) U₀ U₁ Z hZ s
  nlinarith

end Overfull.NativeReserve
