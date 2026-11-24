import Overfull.ForeignEdges.ColorClasses
import Overfull.SafePrescription.Construction

/-!
# Actual edge accounting during a foreign-edge phase

All color classes use the edge copies of one fixed phase-start host. A class
is restricted to the edges still present when it is processed. The final
bound follows from the actual graph differences, so edges removed by earlier
or later matchings are counted correctly. After a refinement the next phase
may start with an entirely new foreign graph and coloring.
-/

namespace Overfull.ForeignPhase

open Finset Classical SimpleGraph MatchingProbability Compression
open BipartitePackingAccounting
open scoped BigOperators

variable {V : Type*} [Fintype V]

/-- Edges of a fixed host class that are still in the current graph. -/
noncomputable def survivingEdges (G R : SimpleGraph V)
    (A : Finset G.edgeSet) : Finset G.edgeSet :=
  A.filter (fun e => e.val ∈ R.edgeSet)

omit [Fintype V] in
@[simp] theorem mem_survivingEdges (G R : SimpleGraph V)
    (A : Finset G.edgeSet) (e : G.edgeSet) :
    e ∈ survivingEdges G R A ↔ e ∈ A ∧ e.val ∈ R.edgeSet := by
  simp [survivingEdges]

omit [Fintype V] in
theorem survivingEdges_mono (G R Q : SimpleGraph V)
    (A : Finset G.edgeSet) (hRQ : R ≤ Q) :
    survivingEdges G R A ⊆ survivingEdges G Q A := by
  intro e he
  exact (mem_survivingEdges G Q A e).mpr
    ⟨((mem_survivingEdges G R A e).mp he).1,
      SimpleGraph.edgeSet_mono hRQ ((mem_survivingEdges G R A e).mp he).2⟩

theorem survivingEdges_sdiff (G R : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset G.edgeSet) (N : G.Subgraph) :
    survivingEdges G (R \ N.spanningCoe) A =
      survivingEdges G R A \ matchingEdges N := by
  ext e
  simp [survivingEdges, matchingEdges, SimpleGraph.edgeSet_sdiff]
  change (e ∈ A ∧ e.val ∈ R.edgeSet ∧ e.val ∉ N.edgeSet) ↔
    ((e ∈ A ∧ e.val ∈ R.edgeSet) ∧ e.val ∉ N.edgeSet)
  tauto

/-- The same selected edges viewed in their current, possibly smaller, host. -/
def currentClass (G R : SimpleGraph V) (A : Finset G.edgeSet) : R.Subgraph :=
  SafePrescription.rehost G R (selectedMatching G (survivingEdges G R A))
    (by
      rintro u v ⟨huv, he⟩
      exact ((mem_survivingEdges G R A ⟨s(u,v),huv⟩).mp he).2)

theorem currentClass_isMatching (G R : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset G.edgeSet) (hA : (Multigraph.ofSimpleGraph G).IsMatching A) :
    (currentClass G R A).IsMatching := by
  apply SafePrescription.rehost_isMatching
  apply selectedMatching_isMatching G (selectedMatching G A)
    (ForeignColoring.selectedMatching_isMatching_of_edge_copies G A hA)
  rw [selectedMatching_edges]
  exact filter_subset _ _

omit [Fintype V] in
/-- Cardinality comparison across the change of ambient host is exact. -/
theorem currentClass_loss (G R : SimpleGraph V) (A : Finset G.edgeSet)
    (N : R.Subgraph) :
    ((currentClass G R A).edgeSet \ N.edgeSet).ncard =
      (survivingEdges G (R \ N.spanningCoe) A).card := by
  let B := survivingEdges G (R \ N.spanningCoe) A
  have heq : Subtype.val '' (B : Set G.edgeSet) =
      (currentClass G R A).edgeSet \ N.edgeSet := by
    ext e
    constructor
    · rintro ⟨f, hf, rfl⟩
      obtain ⟨hfA, hfR, hfN⟩ :=
        (show f ∈ A ∧ f.val ∈ R.edgeSet ∧ f.val ∉ N.edgeSet by
          simpa [B, survivingEdges, SimpleGraph.edgeSet_sdiff] using hf)
      refine ⟨?_, hfN⟩
      change f.val ∈ (selectedMatching G (survivingEdges G R A)).edgeSet
      exact (selectedMatching_mem_edge G _ f).mpr
        ((mem_survivingEdges G R A f).mpr ⟨hfA, hfR⟩)
    · rintro ⟨he, heN⟩
      have heG : e ∈ G.edgeSet :=
        (selectedMatching G (survivingEdges G R A)).edgeSet_subset he
      let f : G.edgeSet := ⟨e, heG⟩
      have hf := (selectedMatching_mem_edge G (survivingEdges G R A) f).mp he
      refine ⟨f, ?_, rfl⟩
      simpa [B, survivingEdges, SimpleGraph.edgeSet_sdiff] using
        (show f ∈ A ∧ f.val ∈ R.edgeSet ∧ f.val ∉ N.edgeSet from
          ⟨((mem_survivingEdges G R A f).mp hf).1,
            ((mem_survivingEdges G R A f).mp hf).2, heN⟩)
  rw [← heq, Set.ncard_image_of_injective _ Subtype.val_injective,
    Set.ncard_coe_finset]

/-- The actual residual after deleting a prefix of host matchings. -/
def afterDeletions (G : SimpleGraph V) (N : ℕ → G.Subgraph) (s : ℕ) : SimpleGraph V :=
  G \ edgeUnion (fun j => (N j).spanningCoe) (range s)

omit [Fintype V] in
@[simp] theorem afterDeletions_zero (G : SimpleGraph V) (N : ℕ → G.Subgraph) :
    afterDeletions G N 0 = G := by
  ext u v
  simp [afterDeletions]

omit [Fintype V] in
theorem afterDeletions_succ (G : SimpleGraph V) (N : ℕ → G.Subgraph) (s : ℕ) :
    afterDeletions G N (s+1) = afterDeletions G N s \ (N s).spanningCoe := by
  ext u v
  simp only [afterDeletions, SimpleGraph.sdiff_adj, edgeUnion_adj,
    mem_range, Nat.lt_succ_iff]
  constructor
  · rintro ⟨hG, hn⟩
    refine ⟨⟨hG, ?_⟩, ?_⟩
    · rintro ⟨j, hj, he⟩
      exact hn ⟨j, hj.le, he⟩
    · intro he
      exact hn ⟨s, le_rfl, he⟩
  · rintro ⟨⟨hG, hn⟩, hs⟩
    refine ⟨hG, ?_⟩
    rintro ⟨j, hj, he⟩
    rcases lt_or_eq_of_le hj with hj | rfl
    · exact hn ⟨j, hj, he⟩
    · exact hs he

omit [Fintype V] in
theorem afterDeletions_antitone (G : SimpleGraph V) (N : ℕ → G.Subgraph)
    {s t : ℕ} (hst : s ≤ t) : afterDeletions G N t ≤ afterDeletions G N s := by
  rintro u v ⟨hG, hn⟩
  refine ⟨hG, ?_⟩
  rintro ⟨j, hj, he⟩
  exact hn ⟨j, mem_range.mpr ((mem_range.mp hj).trans_le hst), he⟩

/-- Per-class bounded loss implies the bound for the actual final union.
The graph in each hypothesis is the exact unused graph at that round. -/
theorem surviving_color_union_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (N : ℕ → G.Subgraph) (d c : ℕ) (A : ℕ → Finset G.edgeSet)
    (hloss : ∀ j < d,
      (survivingEdges G (afterDeletions G N j) (A j) \ matchingEdges (N j)).card ≤ c) :
    (survivingEdges G (afterDeletions G N d) ((range d).biUnion A)).card ≤ c*d := by
  have hunion : survivingEdges G (afterDeletions G N d) ((range d).biUnion A) =
      (range d).biUnion (fun j => survivingEdges G (afterDeletions G N d) (A j)) := by
    ext e
    simp only [mem_survivingEdges, mem_biUnion]
    aesop
  have hclass (j : ℕ) (hj : j ∈ range d) :
      (survivingEdges G (afterDeletions G N d) (A j)).card ≤ c := by
    calc
      _ ≤ (survivingEdges G (afterDeletions G N (j+1)) (A j)).card :=
        card_le_card (survivingEdges_mono G _ _ _
          (afterDeletions_antitone G N (Nat.succ_le_of_lt (mem_range.mp hj))))
      _ = (survivingEdges G (afterDeletions G N j) (A j) \ matchingEdges (N j)).card := by
        rw [afterDeletions_succ, survivingEdges_sdiff]
      _ ≤ c := hloss j (mem_range.mp hj)
  calc
    _ = ((range d).biUnion (fun j => survivingEdges G (afterDeletions G N d) (A j))).card :=
      congrArg card hunion
    _ ≤ ∑ j ∈ range d, (survivingEdges G (afterDeletions G N d) (A j)).card := card_biUnion_le
    _ ≤ ∑ _j ∈ range d, c := sum_le_sum hclass
    _ = c*d := by simp [Nat.mul_comm]

/-- A complete phase leaves at most the per-color allowance times its
number of colors. Its new coloring need not be related to an earlier phase. -/
theorem complete_phase_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (N : ℕ → G.Subgraph) (d c : ℕ) (A : ℕ → Finset G.edgeSet)
    (F : Finset G.edgeSet) (hclasses : (range d).biUnion A = F)
    (hloss : ∀ j < d,
      (survivingEdges G (afterDeletions G N j) (A j) \ matchingEdges (N j)).card ≤ c) :
    (survivingEdges G (afterDeletions G N d) F).card ≤ c*d := by
  rw [← hclasses]
  exact surviving_color_union_card_le G N d c A hloss

/-- The set-cardinality loss returned by safe prescription supplies the
phase bound directly, even though each prescribed class has its own current
ambient graph. -/
theorem complete_phase_card_le_of_prescribed_loss
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (N : ℕ → G.Subgraph) (d c : ℕ) (A : ℕ → Finset G.edgeSet)
    (F : Finset G.edgeSet) (hclasses : (range d).biUnion A = F)
    (hused : ∀ j < d, (N j).spanningCoe ≤ afterDeletions G N j)
    (hloss : ∀ j < d,
      ((currentClass G (afterDeletions G N j) (A j)).edgeSet \
        (N j).edgeSet).ncard ≤ c) :
    (survivingEdges G (afterDeletions G N d) F).card ≤ c*d := by
  apply complete_phase_card_le G N d c A F hclasses
  intro j hj
  let Q := SafePrescription.rehost G (afterDeletions G N j) (N j)
    (fun _ _ he => hused j hj he)
  have heq := currentClass_loss G (afterDeletions G N j) (A j) Q
  change ((currentClass G (afterDeletions G N j) (A j)).edgeSet \
    (N j).edgeSet).ncard =
      (survivingEdges G (afterDeletions G N j \
        (N j).spanningCoe) (A j)).card at heq
  rw [← survivingEdges_sdiff, ← heq]
  exact hloss j hj

/-- A phase with at most three quarters as many rounds as its initial
degree retains at least a quarter, including all rounding effects. -/
theorem phase_degree_reserve (h s : ℕ) (hs : s ≤ 3*h/4) :
    s ≤ h ∧ h ≤ 4*(h-s) := by omega

/-- Four successive phases, including interrupted ones, retain a factor
of at least 1/256. -/
theorem four_phase_degree_reserve (h : ℕ → ℕ) (rounds : ℕ → ℕ)
    (hsteps : ∀ j < 4, h (j+1) = h j - rounds j)
    (hrounds : ∀ j < 4, rounds j ≤ 3*h j/4) :
    h 0 ≤ 256*h 4 := by
  have h0 := (phase_degree_reserve (h 0) (rounds 0) (hrounds 0 (by omega))).2
  have h1 := (phase_degree_reserve (h 1) (rounds 1) (hrounds 1 (by omega))).2
  have h2 := (phase_degree_reserve (h 2) (rounds 2) (hrounds 2 (by omega))).2
  have h3 := (phase_degree_reserve (h 3) (rounds 3) (hrounds 3 (by omega))).2
  rw [← hsteps 0 (by omega)] at h0
  rw [← hsteps 1 (by omega)] at h1
  rw [← hsteps 2 (by omega)] at h2
  rw [← hsteps 3 (by omega)] at h3
  norm_num at h0 h1 h2 h3
  omega

end Overfull.ForeignPhase
