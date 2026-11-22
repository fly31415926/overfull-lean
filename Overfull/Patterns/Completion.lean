import Overfull.ForeignEdges.EpochState

/-!
# Simultaneous completion of a fixed boundary family

Each core rule is run on the already prescribed forbidden sets. The
admissibility proof uses the original edge-disjoint boundary family.
Ambient perfect matchings are then assembled from the actual local rule
outputs. Safety of odd cuts is a separate conclusion to prove elsewhere.
-/

namespace Overfull.Patterns

open Finset Classical SimpleGraph ForceMatching ForeignIncidence
open ForeignRuleCompletion ForeignTranscript ForeignCompletion ForeignPhase
open BipartitePackingAccounting BipartitePackingOnline

variable {Input Output : Type*}

/-- The infinite transcript of a fixed input sequence and one fixed rule. -/
def fixedTranscript
    (rule : (s : ℕ) → (Fin s → Input × Output) → Input → Output)
    (input : ℕ → Input) (j : ℕ) : Input × Output :=
  (input j, rule j (run rule input j) (input j))

theorem fixedTranscript_prefix
    (rule : (s : ℕ) → (Fin s → Input × Output) → Input → Output)
    (input : ℕ → Input) (s : ℕ) :
    transcriptPrefix (fixedTranscript rule input) s = run rule input s := by
  induction s with
  | zero => exact prefix_zero (fixedTranscript rule input)
  | succ s ih =>
    rw [prefix_succ, ih]
    rfl

theorem fixedTranscript_consistent
    (rule : (s : ℕ) → (Fin s → Input × Output) → Input → Output)
    (input : ℕ → Input) (j : ℕ) :
    (fixedTranscript rule input j).2 =
      rule j (transcriptPrefix (fixedTranscript rule input) j)
        (fixedTranscript rule input j).1 := by
  rw [fixedTranscript_prefix]
  rfl

variable {V I : Type*} [Fintype V]

/-- Original pairwise edge-disjointness already bounds every prefix input's
load. No earlier ambient completion is assumed in this lemma. -/
theorem fixed_boundary_allowed (G : SimpleGraph V) (U : Finset V)
    (H : SimpleGraph U) (hH : H ≤ G.induce (U : Set V))
    (F : ℕ → G.Subgraph) (q k : ℕ) (a ε : ℝ)
    (T : ℕ → Finset U × H.Subgraph)
    (hinputs : ∀ j < q, (T j).1 = coveredCore U G (F j))
    (hF : ∀ j < q, (F j).IsMatching)
    (hdisj : ∀ i < q, ∀ j < q, i ≠ j → Disjoint (F i).spanningCoe (F j).spanningCoe)
    (hno : ∀ j < q, ∀ u v, u ∈ U → v ∈ U → ¬ (F j).Adj u v)
    (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ v, (k : ℝ)-a ≤ H.degree v)
    (ha : a ≤ ε*U.card)
    (heven : ∀ j < q, Even (((U : Set V) \ (F j).verts).ncard))
    (hsize : ∀ j < q, ((coveredCore U G (F j)).card : ℝ) ≤ ε*U.card)
    (s : ℕ) (hs : s < q) :
    OrdinaryPackingStrategy.Allowed H (Fintype.card U) ε s
      (transcriptPrefix T s) (T s).1 := by
  rw [hinputs s hs]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Fintype.card_coe] using coveredCore_parity U G (F s) (heven s hs)
  · simpa only [Fintype.card_coe] using hsize s hs
  · intro v
    have hcount := footprintCount_le_real_error U G H hH F (range s)
      (fun j hj => hF j ((mem_range.mp hj).trans hs))
      (fun i hi j hj hij => hdisj i ((mem_range.mp hi).trans hs)
        j ((mem_range.mp hj).trans hs) hij)
      (fun j hj => hno j ((mem_range.mp hj).trans hs)) k a hregular hdegree v
    have heq := history_incidence_eq_footprint U G H F s (transcriptPrefix T s)
      (fun j => hinputs j.val (j.isLt.trans hs)) v
    convert hcount.trans ha using 1
    · rw [← heq]
      congr 2
      ext j
      simp only [mem_filter, mem_univ]
    · simp only [Fintype.card_coe]

omit [Fintype V] in
/-- Exact local restrictions rule out every possible overlap of completed
matchings: two boundary edges, a boundary and an internal edge, or two
internal edges. -/
theorem completed_family_disjoint (G : SimpleGraph V) (U : I → Finset V)
    (H : ∀ i, SimpleGraph (U i)) (F N : ℕ → G.Subgraph)
    (C : ∀ i, ℕ → (H i).Subgraph) (q : ℕ)
    (hFdisj : ∀ j < q, ∀ l < q, j ≠ l → Disjoint (F j).spanningCoe (F l).spanningCoe)
    (hCdisj : ∀ i, ∀ j < q, ∀ l < q, j ≠ l →
      Disjoint (C i j).spanningCoe (C i l).spanningCoe)
    (hno : ∀ j < q, ∀ i u v, u ∈ U i → v ∈ U i → ¬ (F j).Adj u v)
    (hedges : ∀ j < q, ∀ u v, (N j).Adj u v →
      (F j).Adj u v ∨ ∃ i, u ∈ U i ∧ v ∈ U i)
    (hlocal : ∀ j < q, ∀ i,
      (N j).spanningCoe.induce (U i : Set V) = (C i j).spanningCoe) :
    ∀ j < q, ∀ l < q, j ≠ l → Disjoint (N j).spanningCoe (N l).spanningCoe := by
  intro j hj l hl hjl
  apply disjoint_iff_inf_le.mpr
  rintro u v ⟨hjuv, hluv⟩
  have hinternal (i : I) (hu : u ∈ U i) (hv : v ∈ U i) : False := by
    have hjC : (C i j).Adj ⟨u,hu⟩ ⟨v,hv⟩ := by
      change (C i j).spanningCoe.Adj _ _
      rw [← hlocal j hj i]
      exact hjuv
    have hlC : (C i l).Adj ⟨u,hu⟩ ⟨v,hv⟩ := by
      change (C i l).spanningCoe.Adj _ _
      rw [← hlocal l hl i]
      exact hluv
    exact (hCdisj i j hj l hl hjl).le_bot ⟨hjC,hlC⟩
  rcases hedges j hj u v hjuv with hjF | ⟨i,hu,hv⟩
  · rcases hedges l hl u v hluv with hlF | ⟨i,hu,hv⟩
    · exact (hFdisj j hj l hl hjl).le_bot ⟨hjF,hlF⟩
    · exact (hno j hj i u v hu hv hjF).elim
  · exact (hinternal i hu hv).elim

/-- The exact original-host completion family and all its residual cores. -/
structure BoundaryCompletion (G : SimpleGraph V) (U : I → Finset V)
    (H : ∀ i, SimpleGraph (U i)) (F : ℕ → G.Subgraph)
    (q k : ℕ) (a θ σ : ℝ) where
  full : ℕ → G.Subgraph
  core : ∀ i, ℕ → (H i).Subgraph
  perfect : ∀ j < q, (full j).IsPerfectMatching
  contains : ∀ j < q, F j ≤ full j
  added_internal : ∀ j < q, ∀ u v, (full j).Adj u v →
    (F j).Adj u v ∨ ∃ i, u ∈ U i ∧ v ∈ U i
  local_edges : ∀ j < q, ∀ i,
    (full j).spanningCoe.induce (U i : Set V) = (core i j).spanningCoe
  present : ∀ j < q, (full j).spanningCoe ≤ afterDeletions G full j
  residual_regular : ∀ s ≤ q, ∀ v, (afterDeletions G full s).degree v = k-s
  core_robust : ∀ s ≤ q, ∀ i,
    IsRobustExpander (remainingCore (U i) (H i) (core i) (range s)) θ σ
  core_embedded : ∀ s ≤ q, ∀ i,
    remainingCore (U i) (H i) (core i) (range s) ≤
      (afterDeletions G full s).induce (U i : Set V)
  core_degree : ∀ s ≤ q, ∀ i v,
    (k : ℝ)-s-a ≤ (remainingCore (U i) (H i) (core i) (range s)).degree v ∧
      ((remainingCore (U i) (H i) (core i) (range s)).degree v : ℝ) ≤ k-s

set_option maxHeartbeats 300000 in
/-- Certified core rules complete any fixed admissible boundary family.
The input hypotheses are actual matchings, edge disjointness, core error,
footprints and parity; all intermediate admissibility is proved here. -/
theorem exists_boundary_completion (G : SimpleGraph V)
    (U : I → Finset V) (Z : Finset V) (H : ∀ i, SimpleGraph (U i))
    (hH : ∀ i, H i ≤ G.induce (U i : Set V))
    (F : ℕ → G.Subgraph) (q k : ℕ) (a ε θ σ : ℝ)
    (rule : ∀ i, (s : ℕ) → (Fin s → Finset (U i) × (H i).Subgraph) →
      Finset (U i) → (H i).Subgraph)
    (limit : I → ℕ)
    (hcertificate : ∀ i, RuleCertificate (H i) (limit i) ε θ σ (rule i))
    (hlimit : ∀ i, q ≤ limit i)
    (hdisjoint : ∀ i l, i ≠ l → Disjoint (U i) (U l))
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hF : ∀ j < q, (F j).IsMatching)
    (hZ : ∀ j < q, (Z : Set V) ⊆ (F j).verts)
    (hFdisj : ∀ j < q, ∀ l < q, j ≠ l → Disjoint (F j).spanningCoe (F l).spanningCoe)
    (hno : ∀ j < q, ∀ i u v, u ∈ U i → v ∈ U i → ¬ (F j).Adj u v)
    (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ i v, (k : ℝ)-a ≤ (H i).degree v)
    (ha : ∀ i, a ≤ ε*(U i).card)
    (heven : ∀ j < q, ∀ i, Even (((U i : Set V) \ (F j).verts).ncard))
    (hsize : ∀ j < q, ∀ i, ((coveredCore (U i) G (F j)).card : ℝ) ≤ ε*(U i).card) :
    Nonempty (BoundaryCompletion G U H F q k a θ σ) := by
  let S : ∀ i, ℕ → Finset (U i) := fun i j => coveredCore (U i) G (F j)
  let T : ∀ i, ℕ → Finset (U i) × (H i).Subgraph :=
    fun i => fixedTranscript (rule i) (S i)
  have hinputs (i : I) (j : ℕ) : (T i j).1 = coveredCore (U i) G (F j) := rfl
  have hconsistent (i : I) (j : ℕ) :
      (T i j).2 = rule i j (transcriptPrefix (T i) j) (T i j).1 :=
    fixedTranscript_consistent (rule i) (S i) j
  have hallowed (i : I) (j : ℕ) (hj : j < q) :
      OrdinaryPackingStrategy.Allowed (H i) (Fintype.card (U i)) ε j
        (transcriptPrefix (T i) j) (T i j).1 :=
    fixed_boundary_allowed G (U i) (H i) (hH i) F q k a ε (T i)
      (fun j _ => hinputs i j) hF hFdisj (fun j hj => hno j hj i)
      hregular (hdegree i) (ha i) (fun j hj => heven j hj i) (fun j hj => hsize j hj i) j hj
  have hcert (i : I) (s : ℕ) (hs : s ≤ q) :=
    hcertificate i (T i) s (hs.trans (hlimit i))
      (fun j _ => hconsistent i j) (fun j hj => hallowed i j (hj.trans_le hs))
  let C : ∀ i, ℕ → (H i).Subgraph := fun i j => (T i j).2
  have hC (i : I) (j : ℕ) (hj : j < q) : (C i j).IsMatching :=
    (hcert i q le_rfl).1.1 ⟨j,hj⟩
  have hCverts (i : I) (j : ℕ) (hj : j < q) :
      (C i j).verts = (coveredCore (U i) G (F j) : Set (U i))ᶜ :=
    (hcert i q le_rfl).1.2.1 ⟨j,hj⟩
  have hCdisj (i : I) (j : ℕ) (hj : j < q) (l : ℕ) (hl : l < q) (hjl : j ≠ l) :
      Disjoint (C i j).spanningCoe (C i l).spanningCoe := by
    have hp := (hcert i q le_rfl).1.2.2
    have hh := @hp (⟨j,hj⟩ : Fin q) ⟨l,hl⟩ (fun he => hjl (congrArg Fin.val he))
    exact hh
  let N : ℕ → G.Subgraph := fun j => assembledMatching G (F j)
    (fun i => embedCoreMatching G (U i) (H i) (hH i) (C i j))
  have hN (j : ℕ) (hj : j < q) : (N j).IsPerfectMatching :=
    assembledMatching_perfect G U Z (F j) _ hdisjoint hcover (hF j hj) (hZ j hj)
      (fun i => embedCoreMatching_isMatching G (U i) (H i) (hH i) (C i j) (hC i j hj))
      (fun i => embedCoreMatching_verts G (U i) (H i) (hH i) (F j) (C i j) (hCverts i j hj))
  have hcontains (j : ℕ) : F j ≤ N j := assembledMatching_contains G (F j) _
  have hedges (j : ℕ) (_hj : j < q) (u v : V) (huv : (N j).Adj u v) :
      (F j).Adj u v ∨ ∃ i, u ∈ U i ∧ v ∈ U i := by
    rcases huv with hFuv | ⟨i,hi⟩
    · exact Or.inl hFuv
    · obtain ⟨hu,hv,_⟩ := embedCoreMatching_edge G (U i) (H i) (hH i) (C i j) hi
      exact Or.inr ⟨i,hu,hv⟩
  have hlocal (j : ℕ) (hj : j < q) (i : I) :
      (N j).spanningCoe.induce (U i : Set V) = (C i j).spanningCoe :=
    assembledMatching_induce_eq G U H hH (F j) (fun i => C i j) hdisjoint (hno j hj) i
  have hNdisj := completed_family_disjoint G U H F N C q hFdisj hCdisj hno hedges hlocal
  have hpresent (j : ℕ) (hj : j < q) : (N j).spanningCoe ≤ afterDeletions G N j := by
    intro u v huv
    refine ⟨(N j).adj_sub huv, ?_⟩
    rintro ⟨l,hl,hluv⟩
    have hlj := mem_range.mp hl
    exact (hNdisj j hj l (hlj.trans hj) (Nat.ne_of_gt hlj)).le_bot ⟨huv,hluv⟩
  refine ⟨⟨N,C,hN,(fun j _ => hcontains j),hedges,hlocal,hpresent,?_,?_,?_,?_⟩⟩
  · intro s hs v
    have hh := (perfect_deletion_regular G N s k hregular
      (fun j hj => hN j (hj.trans_le hs)) (fun j hj => hpresent j (hj.trans_le hs)) v).2
    simpa only [afterDeletions, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hh
  · intro s hs i
    have hr := (hcert i s hs).2
    unfold unusedGraph at hr
    rw [ForeignEpoch.prefix_edgeUnion_eq_range] at hr
    convert hr using 1
  · intro s hs i
    exact remainingCore_le_residual (U i) G (H i) (hH i) (C i) N (range s)
      (fun j hj => hlocal j ((mem_range.mp hj).trans_le hs) i)
  · intro s hs i v
    have h := remainingCore_real_degree_bounds (U i) G (H i) (hH i) F (C i) (range s)
      (fun j hj => hF j ((mem_range.mp hj).trans_le hs))
      (fun j hj l hl hjl => hFdisj j ((mem_range.mp hj).trans_le hs)
        l ((mem_range.mp hl).trans_le hs) hjl)
      (fun j hj => hno j ((mem_range.mp hj).trans_le hs) i)
      (fun j hj => hC i j ((mem_range.mp hj).trans_le hs))
      (fun j hj l hl hjl => hCdisj i j ((mem_range.mp hj).trans_le hs)
        l ((mem_range.mp hl).trans_le hs) hjl)
      (fun j hj => hCverts i j ((mem_range.mp hj).trans_le hs)) k a hregular (hdegree i) v
    simpa only [card_range] using h

end Overfull.Patterns
