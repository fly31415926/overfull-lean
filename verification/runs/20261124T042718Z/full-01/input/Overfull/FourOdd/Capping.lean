import Overfull.FourOdd.Basic
import Overfull.FourOdd.Pools

/-!
# Safe truncation of off-forest joining pools

Each discarded piece is an actual two-edge matching. The retained pools
preserve all projected parities. Prescribed forest pools remain intact;
the other pools have at most `B+1` copies, and any changed pool retains at
least `B`. This also preserves every required singleton-label cut bound.
-/

noncomputable section

namespace Overfull.FourOdd

open Finset Classical Compression CircuitPatterns
open scoped BigOperators

variable {V E : Type*} [Fintype E]

/-- All cap choices retain actual copies and their discarded partitions. -/
structure CappedPools (G : Multigraph V E) (Q : Multigraph (Fin 4) E)
    (F0 : Finset LabelPair) (B : ℕ) where
  kept : LabelPair → Finset E
  subset : ∀ p, kept p ⊆ pairPool Q p
  fixed : ∀ p ∈ F0, kept p = pairPool Q p
  cap_bound : ∀ p, p ∉ F0 → (kept p).card ≤ B + 1
  full_or_large : ∀ p, kept p = pairPool Q p ∨ B ≤ (kept p).card
  parity : ∀ p, (kept p).card % 2 = (pairPool Q p).card % 2
  discarded : ∀ p, Decomposition G Q.edgeLabelPair (pairPool Q p \ kept p) 0

namespace CappedPools

variable {G : Multigraph V E} {Q : Multigraph (Fin 4) E}
    {F0 : Finset LabelPair} {B : ℕ} (P : CappedPools G Q F0 B)

def retained : Finset E := (univ : Finset LabelPair).biUnion P.kept

theorem kept_disjoint {p q : LabelPair} (hpq : p ≠ q) :
    Disjoint (P.kept p) (P.kept q) :=
  selected_pairPool_disjoint Q P.kept P.subset hpq

theorem degree_eq_sum (i : Fin 4) :
    Q.degreeOn P.retained i =
      ∑ p ∈ univ.filter (fun p : LabelPair => i ∈ p.val), (P.kept p).card :=
  degreeOn_selected_pairPool Q P.kept P.subset i

theorem degree_parity (i : Fin 4) :
    Q.degreeOn P.retained i % 2 = Q.degree i % 2 :=
  selected_pairPool_degree_parity Q P.kept P.subset P.parity i

/-- Combine every discarded pool partition with its exact original-copy
coverage. No primary pieces are introduced by truncation. -/
def discardedDecomposition :
    Decomposition G Q.edgeLabelPair (univ \ P.retained) 0 := by
  let R := Classical.choice (Decomposition.exists_biUnion univ
    (fun p => pairPool Q p \ P.kept p) (fun _ => 0) P.discarded (by
      intro p _ q _ hpq
      exact (pairPool_disjoint Q hpq).mono sdiff_subset sdiff_subset))
  exact R.cast (pairPool_sdiff_selected_cover Q P.kept P.subset) (by simp)

theorem incident_fixed_exists (hF0 : LabelForestShape F0) (i : Fin 4) :
    ∃ p ∈ F0, i ∈ p.val := by
  have hp := ((labelForestShape_iff F0).mp hF0).2 i
  have hpos : 0 < pairDegree F0 i := by omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  exact ⟨p, (mem_filter.mp hp).1, (mem_filter.mp hp).2⟩

/-- The singleton-label cut bound survives all cap choices. If an
incident off-forest pool changed, its retained reserve supplements an
unchanged prescribed pool; otherwise the entire original cut remains. -/
theorem degree_lower {h r0 : ℕ} (hF0 : LabelForestShape F0)
    (hsupply : ∀ p ∈ F0, r0 ≤ (pairPool Q p).card)
    (hlower : ∀ i, h ≤ Q.degree i) (hreserve : h ≤ r0 + B) (i : Fin 4) :
    h ≤ Q.degreeOn P.retained i := by
  let A : Finset LabelPair := univ.filter (fun p => i ∈ p.val)
  by_cases hall : ∀ p ∈ A, P.kept p = pairPool Q p
  · have heq : Q.degreeOn P.retained i = Q.degree i := by
      rw [P.degree_eq_sum, degree_eq_sum_pairPool]
      apply sum_congr rfl
      intro p hp
      rw [hall p hp]
    rw [heq]
    exact hlower i
  · push_neg at hall
    obtain ⟨p, hpA, hpchanged⟩ := hall
    have hlarge : B ≤ (P.kept p).card :=
      (P.full_or_large p).resolve_left hpchanged
    obtain ⟨q, hqF, hqi⟩ := incident_fixed_exists hF0 i
    have hqA : q ∈ A := mem_filter.mpr ⟨mem_univ _, hqi⟩
    have hpq : p ≠ q := by
      intro heq
      apply hpchanged
      rw [heq]
      exact P.fixed q hqF
    have hsub : ({p, q} : Finset LabelPair) ⊆ A := by
      intro r hr
      rcases mem_insert.mp hr with rfl | hr
      · exact hpA
      · exact mem_singleton.mp hr ▸ hqA
    have hsum := sum_le_sum_of_subset_of_nonneg hsub
      (fun _ _ _ => Nat.zero_le _) (f := fun r => (P.kept r).card)
    have hq : r0 ≤ (P.kept q).card := by
      rw [P.fixed q hqF]
      exact hsupply q hqF
    have hsum' : (P.kept p).card + (P.kept q).card ≤
        ∑ r ∈ A, (P.kept r).card := by
      simpa only [sum_insert (show p ∉ ({q} : Finset LabelPair) by simpa using hpq),
        sum_singleton] using hsum
    rw [P.degree_eq_sum]
    change h ≤ ∑ r ∈ A, (P.kept r).card
    omega

end CappedPools

/-- Construct all six safe cap choices from ordinary bipartite edge
coloring in the actual pair pools. -/
theorem exists_cappedPools [Fintype V] (G : Multigraph V E)
    (label : V → Fin 4)
    (hjoin : ∀ e, label (G.firstEnd e) ≠ label (G.secondEnd e))
    (F0 : Finset LabelPair) (B : ℕ) (hdegree : ∀ v, G.degree v ≤ B) :
    Nonempty (CappedPools G (G.labelQuotient label hjoin) F0 B) := by
  let Q := G.labelQuotient label hjoin
  have hlocal (p : LabelPair) : ∃ S : Finset E,
      S ⊆ pairPool Q p ∧ (p ∈ F0 → S = pairPool Q p) ∧
      (p ∉ F0 → S.card ≤ B + 1) ∧
      (S = pairPool Q p ∨ B ≤ S.card) ∧
      S.card % 2 = (pairPool Q p).card % 2 ∧
      Nonempty (Decomposition G Q.edgeLabelPair (pairPool Q p \ S) 0) := by
    by_cases hp : p ∈ F0
    · refine ⟨pairPool Q p, subset_rfl, fun _ => rfl,
        fun hn => (hn hp).elim, Or.inl rfl, rfl, ?_⟩
      exact ⟨(Decomposition.empty G Q.edgeLabelPair).cast (by simp) rfl⟩
    · obtain ⟨S, hsub, hcap, hfull, hpar, ⟨R⟩⟩ :=
        exists_capped_singletons_and_pairs_on G (pairPool Q p)
          (pairPool_bipartite G label hjoin p) B
          (fun v => (restrictEdges_degree_le_original G _ v).trans (hdegree v))
      refine ⟨S, hsub, fun hf => (hp hf).elim, fun _ => hcap,
        hfull, hpar.symm, ⟨Decomposition.ofPairPartition R ?_⟩⟩
      intro M hM e he f hf
      exact ((mem_pairPool Q p e).mp ((mem_sdiff.mp (R.part_subset hM he)).1)).trans
        ((mem_pairPool Q p f).mp ((mem_sdiff.mp (R.part_subset hM hf)).1)).symm
  choose S hsub hfixed hcap hfull hpar hdiscard using hlocal
  exact ⟨{
    kept := S
    subset := hsub
    fixed := hfixed
    cap_bound := hcap
    full_or_large := hfull
    parity := hpar
    discarded := fun p => Classical.choice (hdiscard p) }⟩

end Overfull.FourOdd
