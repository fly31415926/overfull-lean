import Std

/-!
# Finite Petersen-graph certificates

The vertices are `x₀,…,x₄,w₀,…,w₄`.  The outer edges are `xᵢxᵢ₊₁`,
the inner edges are `wᵢwᵢ₊₂`, and the spokes are `xᵢwᵢ`, with indices
modulo five. A mask in `Fin 32` describes a subset of one five-edge family.

All finite certificates below use ordinary `decide`, whose proof term is
checked by Lean's kernel. There is no `native_decide`, `sorry`, or added axiom.
These are finite ingredients of the sharpness proof; they do not by themselves
formalize the clique-expansion construction or the main asymptotic theorem.
-/

namespace Overfull.Sharpness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Membership of index `i` in the subset encoded by the binary mask. -/
def bit (mask i : Nat) : Nat := if mask.testBit i then 1 else 0

/-- Number of selected elements in a five-element set. -/
def count5 (mask : Nat) : Nat :=
  bit mask 0 + bit mask 1 + bit mask 2 + bit mask 3 + bit mask 4

/-- Outer-cycle edges incident with `xᵢ`. -/
def outerIncidence (mask : Nat) (i : Fin 5) : Nat :=
  bit mask i.val + bit mask ((i.val + 4) % 5)

/-- Inner-cycle edges incident with `wᵢ`. -/
def innerIncidence (mask : Nat) (i : Fin 5) : Nat :=
  bit mask i.val + bit mask ((i.val + 3) % 5)

/-- The outer and inner cycle matchings leave precisely the same indices free
for spokes. -/
def Compatible (outer inner : Fin 32) : Prop :=
  ∀ i : Fin 5,
    outerIncidence outer.val i ≤ 1 ∧
    innerIncidence inner.val i ≤ 1 ∧
    outerIncidence outer.val i = innerIncidence inner.val i

instance (outer inner : Fin 32) : Decidable (Compatible outer inner) :=
  inferInstanceAs (Decidable (∀ i : Fin 5,
    outerIncidence outer.val i ≤ 1 ∧
    innerIncidence inner.val i ≤ 1 ∧
    outerIncidence outer.val i = innerIncidence inner.val i))

/-- Exact degree-one conditions for a Petersen perfect matching, with its three
edge families encoded separately. -/
def IsPerfectMatching (outer inner spokes : Fin 32) : Prop :=
  ∀ i : Fin 5,
    outerIncidence outer.val i + bit spokes.val i.val = 1 ∧
    innerIncidence inner.val i + bit spokes.val i.val = 1

/-- The finite classification needed in Section 7: a compatible pair contains
either no cycle edges or two edges from each cycle. -/
theorem compatible_counts :
    ∀ outer inner : Fin 32, Compatible outer inner →
      (count5 outer.val = 0 ∧ count5 inner.val = 0) ∨
      (count5 outer.val = 2 ∧ count5 inner.val = 2) := by
  decide

theorem perfect_matching_compatible (outer inner spokes : Fin 32)
    (h : IsPerfectMatching outer inner spokes) : Compatible outer inner := by
  intro i
  have hi := h i
  constructor
  · omega
  constructor
  · omega
  · omega

/-- Every Petersen perfect matching has zero or four nonspoke edges. -/
theorem perfect_matching_nonspoke_count (outer inner spokes : Fin 32)
    (h : IsPerfectMatching outer inner spokes) :
    count5 outer.val + count5 inner.val = 0 ∨
      count5 outer.val + count5 inner.val = 4 := by
  have hc := compatible_counts outer inner (perfect_matching_compatible outer inner spokes h)
  rcases hc with ⟨ho, hi⟩ | ⟨ho, hi⟩
  · omega
  · omega

/-- A matching pattern records the two cycle-edge sets of a perfect matching.
The compatible condition uniquely determines its spoke incidences. -/
structure MatchingPattern where
  outer : Fin 32
  inner : Fin 32
  compatible : Compatible outer inner

def nonspokeCount (p : MatchingPattern) : Nat := count5 p.outer.val + count5 p.inner.val

theorem pattern_count (p : MatchingPattern) : nonspokeCount p = 0 ∨ nonspokeCount p = 4 := by
  have h := compatible_counts p.outer p.inner p.compatible
  unfold nonspokeCount
  rcases h with ⟨ho, hi⟩ | ⟨ho, hi⟩
  · omega
  · omega

/-- Sum of a natural-valued function over a list. Defined explicitly to keep
the arithmetic proof independent of any finite-set library. -/
def total {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | p :: ps => f p + total f ps

def outerCoverage (ps : List MatchingPattern) (i : Nat) : Nat :=
  total (fun p => bit p.outer.val i) ps

def innerCoverage (ps : List MatchingPattern) (i : Nat) : Nat :=
  total (fun p => bit p.inner.val i) ps

theorem total_nonspoke_eq (ps : List MatchingPattern) :
    total nonspokeCount ps =
      outerCoverage ps 0 + outerCoverage ps 1 + outerCoverage ps 2 +
      outerCoverage ps 3 + outerCoverage ps 4 +
      innerCoverage ps 0 + innerCoverage ps 1 + innerCoverage ps 2 +
      innerCoverage ps 3 + innerCoverage ps 4 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simp only [total, outerCoverage, innerCoverage, nonspokeCount, count5] at *
      omega

theorem total_nonspoke_mod_four (ps : List MatchingPattern) :
    total nonspokeCount ps % 4 = 0 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      have hc := pattern_count p
      simp only [total]
      rcases hc with hc | hc
      · rw [hc]
        simpa using ih
      · rw [hc, Nat.add_mod]
        simpa using ih

/-- No finite list of Petersen matching patterns covers each of the ten cycle
edges exactly once. This is the nonspoke obstruction, independent of the
positive multiplicity assigned to each spoke. -/
theorem no_nonspoke_decomposition (ps : List MatchingPattern)
    (houter : ∀ i : Fin 5, outerCoverage ps i.val = 1)
    (hinner : ∀ i : Fin 5, innerCoverage ps i.val = 1) : False := by
  have ht := total_nonspoke_eq ps
  have hm := total_nonspoke_mod_four ps
  have ho0 := houter ⟨0, by decide⟩
  have ho1 := houter ⟨1, by decide⟩
  have ho2 := houter ⟨2, by decide⟩
  have ho3 := houter ⟨3, by decide⟩
  have ho4 := houter ⟨4, by decide⟩
  have hi0 := hinner ⟨0, by decide⟩
  have hi1 := hinner ⟨1, by decide⟩
  have hi2 := hinner ⟨2, by decide⟩
  have hi3 := hinner ⟨3, by decide⟩
  have hi4 := hinner ⟨4, by decide⟩
  simp only at ho0 ho1 ho2 ho3 ho4 hi0 hi1 hi2 hi3 hi4
  omega

/-- Number of vertices in the subset of the ten Petersen vertices encoded by
the mask. Vertices 0,...,4 are the outer cycle, and 5,...,9 the inner cycle. -/
def vertexCount (mask : Nat) : Nat :=
  count5 mask + bit mask 5 + bit mask 6 + bit mask 7 + bit mask 8 + bit mask 9

def crosses (mask u v : Nat) : Nat := if bit mask u = bit mask v then 0 else 1

def spokeCut (mask : Nat) : Nat :=
  crosses mask 0 5 + crosses mask 1 6 + crosses mask 2 7 +
  crosses mask 3 8 + crosses mask 4 9

def nonspokeCut (mask : Nat) : Nat :=
  crosses mask 0 1 + crosses mask 1 2 + crosses mask 2 3 +
  crosses mask 3 4 + crosses mask 4 0 +
  crosses mask 5 7 + crosses mask 6 8 + crosses mask 7 9 +
  crosses mask 8 5 + crosses mask 9 6

def petersenCut (mask : Nat) : Nat := nonspokeCut mask + spokeCut mask

/-- Every odd vertex subset has Petersen cut at least three and crosses the
spoke perfect matching at least once. -/
theorem odd_cut_certificate :
    ∀ mask : Fin 1024, vertexCount mask.val % 2 = 1 →
      3 ≤ petersenCut mask.val ∧ 1 ≤ spokeCut mask.val := by
  decide

/-- Adding `Δ-3` extra copies of every spoke gives every odd cut size at
least `Δ`. This part of the weighted Petersen assertion holds for every
integer `Δ ≥ 3`, without a parity assumption. -/
theorem weighted_odd_cut (Δ : Nat) (hΔ : 3 ≤ Δ) (mask : Fin 1024)
    (hodd : vertexCount mask.val % 2 = 1) :
    Δ ≤ petersenCut mask.val + (Δ - 3) * spokeCut mask.val := by
  obtain ⟨hc, hs⟩ := odd_cut_certificate mask hodd
  have hp : Δ - 3 ≤ (Δ - 3) * spokeCut mask.val := by
    have hmul := Nat.mul_le_mul_left (Δ - 3) hs
    simpa using hmul
  omega

end Overfull.Sharpness
