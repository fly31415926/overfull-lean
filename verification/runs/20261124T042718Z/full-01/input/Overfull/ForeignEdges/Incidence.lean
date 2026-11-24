import Overfull.ForceMatching.Assembly
import Overfull.Replacement.Graph

/-!
# Actual exterior incidence in a packing phase

The forbidden set in a core consists of the vertices already covered by the
partial ambient matching.  Across edge-disjoint partial matchings these
appearances consume distinct exterior edges of the initial graph.  The
incidence budget and the degrees of the whole unused core therefore follow
from graph edges rather than an additional hypothesis about the budget.
-/

namespace Overfull.ForeignIncidence

open Finset Classical SimpleGraph
open BipartitePackingAccounting ForceMatching
open scoped BigOperators

variable {V J : Type*} [Fintype V]

/-- Number of presented partial matchings covering a given core vertex. -/
noncomputable def footprintCount (U : Finset V) (G : SimpleGraph V)
    (F : J → G.Subgraph) (T : Finset J) (v : U) : ℕ :=
  (T.filter (fun j => v ∈ coveredCore U G (F j))).card

theorem footprintCount_eq_union_degree (U : Finset V) (G : SimpleGraph V)
    (F : J → G.Subgraph) (T : Finset J)
    (hF : ∀ j ∈ T, (F j).IsMatching)
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      Disjoint (F i).spanningCoe (F j).spanningCoe) (v : U) :
    footprintCount U G F T v =
      (edgeUnion (fun j => (F j).spanningCoe) T).degree v.val := by
  rw [edgeUnion_degree_eq_sum _ _ hdisj]
  simp_rw [footprintCount, mem_coveredCore]
  symm
  calc
    _ = ∑ j ∈ T, if v.val ∈ (F j).verts then 1 else 0 :=
      Finset.sum_congr rfl (fun j hj => matching_degree G (F j) (hF j hj) v.val)
    _ = _ := by simp

omit [Fintype V] in
/-- Every used partial-matching edge is outside the chosen core graph. -/
theorem partial_union_le_exterior (U : Finset V) (G : SimpleGraph V)
    (H : SimpleGraph U) (F : J → G.Subgraph) (T : Finset J)
    (hno : ∀ j ∈ T, ∀ u v, u ∈ U → v ∈ U → ¬ (F j).Adj u v) :
    edgeUnion (fun j => (F j).spanningCoe) T ≤ G \ Replacement.lift U H := by
  rintro u v ⟨j,hj,huv⟩
  refine ⟨(F j).adj_sub huv,?_⟩
  intro hH
  have hmem := Replacement.lift_adj_mem U H hH
  exact hno j hj u v hmem.1 hmem.2 huv

/-- The actual footprint appearances use distinct edges in the exterior.
The core need not be induced: any retained core subgraph gives a budget. -/
theorem footprintCount_add_core_degree_le (U : Finset V) (G : SimpleGraph V)
    (H : SimpleGraph U) (hH : H ≤ G.induce (U : Set V))
    (F : J → G.Subgraph) (T : Finset J)
    (hF : ∀ j ∈ T, (F j).IsMatching)
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      Disjoint (F i).spanningCoe (F j).spanningCoe)
    (hno : ∀ j ∈ T, ∀ u v, u ∈ U → v ∈ U → ¬ (F j).Adj u v)
    (v : U) : footprintCount U G F T v + H.degree v ≤ G.degree v.val := by
  have hle := SimpleGraph.degree_le_of_le
    (partial_union_le_exterior U G H F T hno) (v := v.val)
  have hid := degree_sdiff_add_of_le G (Replacement.lift U H)
    (Replacement.lift_le U H G hH) v.val
  rw [Replacement.lift_degree] at hid
  rw [footprintCount_eq_union_degree U G F T hF hdisj]
  omega

/-- Regularity and the initial core error give the adaptive incidence budget. -/
theorem footprintCount_le_error (U : Finset V) (G : SimpleGraph V)
    (H : SimpleGraph U) (hH : H ≤ G.induce (U : Set V))
    (F : J → G.Subgraph) (T : Finset J)
    (hF : ∀ j ∈ T, (F j).IsMatching)
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      Disjoint (F i).spanningCoe (F j).spanningCoe)
    (hno : ∀ j ∈ T, ∀ u v, u ∈ U → v ∈ U → ¬ (F j).Adj u v)
    (k a : ℕ) (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ v, k ≤ H.degree v + a) (v : U) :
    footprintCount U G F T v ≤ a := by
  have hcount := footprintCount_add_core_degree_le U G H hH F T hF hdisj hno v
  rw [hregular] at hcount
  have hdeg := hdegree v
  omega

/-- The complete unused original core, including its unused reserve edges. -/
def remainingCore (U : Finset V) (H : SimpleGraph U)
    (C : J → H.Subgraph) (T : Finset J) : SimpleGraph U :=
  H \ edgeUnion (fun j => (C j).spanningCoe) T

theorem remainingCore_degree_identity (U : Finset V) (G : SimpleGraph V)
    (H : SimpleGraph U) (F : J → G.Subgraph) (C : J → H.Subgraph) (T : Finset J)
    (hC : ∀ j ∈ T, (C j).IsMatching)
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      Disjoint (C i).spanningCoe (C j).spanningCoe)
    (hverts : ∀ j ∈ T, (C j).verts = (coveredCore U G (F j) : Set U)ᶜ)
    (v : U) :
    (remainingCore U H C T).degree v + T.card =
      H.degree v + footprintCount U G F T v := by
  have hle : edgeUnion (fun j => (C j).spanningCoe) T ≤ H :=
    edgeUnion_le _ _ _ (fun j _ => (C j).spanningCoe_le)
  have hres := degree_sdiff_add_of_le H _ hle v
  have huse := matchingUnion_degree_add_missing H C T hC hdisj v
  have hcount : missingCount H C T v = footprintCount U G F T v := by
    unfold missingCount footprintCount
    apply congrArg Finset.card
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hj,hv⟩
      refine ⟨hj,?_⟩
      simpa only [hverts j hj,Set.mem_compl_iff,Finset.mem_coe,not_not] using hv
    · rintro ⟨hj,hv⟩
      refine ⟨hj,?_⟩
      simpa only [hverts j hj,Set.mem_compl_iff,Finset.mem_coe,not_not] using hv
  rw [hcount] at huse
  have hres' : (remainingCore U H C T).degree v +
      (edgeUnion (fun j => (C j).spanningCoe) T).degree v = H.degree v := by
    simpa only [remainingCore, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hres
  have huse' : (edgeUnion (fun j => (C j).spanningCoe) T).degree v +
      footprintCount U G F T v = T.card := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using huse
  omega

/-- The two bounds retain the original error through an entire phase. -/
theorem remainingCore_degree_bounds (U : Finset V) (G : SimpleGraph V)
    (H : SimpleGraph U) (hH : H ≤ G.induce (U : Set V))
    (F : J → G.Subgraph) (C : J → H.Subgraph) (T : Finset J)
    (hF : ∀ j ∈ T, (F j).IsMatching)
    (hFdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      Disjoint (F i).spanningCoe (F j).spanningCoe)
    (hno : ∀ j ∈ T, ∀ u v, u ∈ U → v ∈ U → ¬ (F j).Adj u v)
    (hC : ∀ j ∈ T, (C j).IsMatching)
    (hCdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      Disjoint (C i).spanningCoe (C j).spanningCoe)
    (hverts : ∀ j ∈ T, (C j).verts = (coveredCore U G (F j) : Set U)ᶜ)
    (k a : ℕ) (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ v, k ≤ H.degree v + a) (v : U) :
    k ≤ (remainingCore U H C T).degree v + T.card + a ∧
      (remainingCore U H C T).degree v + T.card ≤ k := by
  have hid := remainingCore_degree_identity U G H F C T hC hCdisj hverts v
  have hcount := footprintCount_add_core_degree_le U G H hH F T hF hFdisj hno v
  rw [hregular] at hcount
  have hdeg := hdegree v
  constructor <;> omega

omit [Fintype V] in
/-- Restricting an assembled matching to a core gives exactly its local
completion, because the partial matching has no internal core edges. -/
theorem assembledMatching_induce_eq {I : Type*} (G : SimpleGraph V)
    (U : I → Finset V) (H : ∀ i, SimpleGraph (U i))
    (hH : ∀ i, H i ≤ G.induce (U i : Set V))
    (F : G.Subgraph) (C : ∀ i, (H i).Subgraph)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hno : ∀ i u v, u ∈ U i → v ∈ U i → ¬ F.Adj u v)
    (i : I) :
    (assembledMatching G F
      (fun j => embedCoreMatching G (U j) (H j) (hH j) (C j))).spanningCoe.induce
        (U i : Set V) = (C i).spanningCoe := by
  ext u v
  change (F.Adj u.val v.val ∨
    ∃ j, (embedCoreMatching G (U j) (H j) (hH j) (C j)).Adj u.val v.val) ↔
      (C i).Adj u v
  constructor
  · intro h
    rcases h with hF | ⟨j,hj⟩
    · exact (hno i u.val v.val u.property v.property hF).elim
    · obtain ⟨x,y,hxy,hx,hy⟩ := hj
      change x.val = u.val at hx
      change y.val = v.val at hy
      have hxi : x.val ∈ U i := hx.symm ▸ u.property
      have hji : j = i := by
        by_contra hne
        exact Finset.disjoint_left.mp (hdisjoint j i hne) x.property hxi
      subst j
      have hx' : x = u := Subtype.ext hx
      have hy' : y = v := Subtype.ext hy
      simpa only [hx',hy'] using hxy
  · intro h
    exact Or.inr ⟨i,u,v,h,rfl,rfl⟩

omit [Fintype V] in
/-- An exact description of the induced ambient matching makes the whole
unused original core an actual subgraph of the ambient residual. -/
theorem remainingCore_le_residual (U : Finset V) (G : SimpleGraph V)
    (H : SimpleGraph U) (hH : H ≤ G.induce (U : Set V))
    (C : J → H.Subgraph) (N : J → G.Subgraph) (T : Finset J)
    (hlocal : ∀ j ∈ T, (N j).spanningCoe.induce (U : Set V) = (C j).spanningCoe) :
    remainingCore U H C T ≤
      (G \ edgeUnion (fun j => (N j).spanningCoe) T).induce (U : Set V) := by
  intro u v h
  refine ⟨hH h.1,?_⟩
  rintro ⟨j,hj,hN⟩
  apply h.2
  refine ⟨j,hj,?_⟩
  change ((N j).spanningCoe.induce (U : Set V)).Adj u v at hN
  simpa only [hlocal j hj] using hN

omit [Fintype V] in
/-- For an initially induced core the residual embedding is an equality. -/
theorem remainingCore_induced_eq (U : Finset V) (G : SimpleGraph V)
    (C : J → (G.induce (U : Set V)).Subgraph)
    (N : J → G.Subgraph) (T : Finset J)
    (hlocal : ∀ j ∈ T, (N j).spanningCoe.induce (U : Set V) = (C j).spanningCoe) :
    remainingCore U (G.induce (U : Set V)) C T =
      (G \ edgeUnion (fun j => (N j).spanningCoe) T).induce (U : Set V) := by
  apply le_antisymm (remainingCore_le_residual U G _ le_rfl C N T hlocal)
  intro u v h
  refine ⟨h.1,?_⟩
  rintro ⟨j,hj,hC⟩
  apply h.2
  refine ⟨j,hj,?_⟩
  change ((N j).spanningCoe.induce (U : Set V)).Adj u v
  simpa only [hlocal j hj] using hC

omit [Fintype V] in
/-- Successive deletion itself proves that the ambient matching graphs
are edge-disjoint. -/
theorem deletion_sequence_pairwise (G : SimpleGraph V)
    (N : ℕ → G.Subgraph) (q : ℕ)
    (hpresent : ∀ j < q, (N j).spanningCoe ≤
      G \ edgeUnion (fun i => (N i).spanningCoe) (range j)) :
    ∀ i ∈ range q, ∀ j ∈ range q, i ≠ j →
      Disjoint (N i).spanningCoe (N j).spanningCoe := by
  intro i hi j hj hij
  apply disjoint_iff_inf_le.mpr
  rintro u v ⟨hiuv,hjuv⟩
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact (hpresent j (mem_range.mp hj) hjuv).2 ⟨i,mem_range.mpr hij,hiuv⟩
  · exact (hpresent i (mem_range.mp hi) hiuv).2 ⟨j,mem_range.mpr hji,hjuv⟩

omit [Fintype V] in
/-- Partial matchings contained in successively deleted ambient matchings
also consume distinct actual edges. -/
theorem deletion_sequence_partial_pairwise (G : SimpleGraph V)
    (F N : ℕ → G.Subgraph) (q : ℕ)
    (hFN : ∀ j < q, (F j).spanningCoe ≤ (N j).spanningCoe)
    (hpresent : ∀ j < q, (N j).spanningCoe ≤
      G \ edgeUnion (fun i => (N i).spanningCoe) (range j)) :
    ∀ i ∈ range q, ∀ j ∈ range q, i ≠ j →
      Disjoint (F i).spanningCoe (F j).spanningCoe := by
  intro i hi j hj hij
  exact (deletion_sequence_pairwise G N q hpresent i hi j hj hij).mono
    (hFN i (mem_range.mp hi)) (hFN j (mem_range.mp hj))

/-- Every perfect matching removes exactly one degree at each vertex;
the exact residual identity also proves that the deletion count is feasible. -/
theorem perfect_deletion_degree_identity (G : SimpleGraph V)
    (N : ℕ → G.Subgraph) (q : ℕ)
    (hN : ∀ j < q, (N j).IsPerfectMatching)
    (hpresent : ∀ j < q, (N j).spanningCoe ≤
      G \ edgeUnion (fun i => (N i).spanningCoe) (range j)) (v : V) :
    (G \ edgeUnion (fun j => (N j).spanningCoe) (range q)).degree v + q =
      G.degree v := by
  have hle : edgeUnion (fun j => (N j).spanningCoe) (range q) ≤ G :=
    edgeUnion_le _ _ _ (fun j _ => (N j).spanningCoe_le)
  have hres := degree_sdiff_add_of_le G _ hle v
  have hsum := edgeUnion_degree_eq_sum (fun j => (N j).spanningCoe) (range q)
    (deletion_sequence_pairwise G N q hpresent) v
  have hdeg (j : ℕ) (hj : j ∈ range q) : (N j).spanningCoe.degree v = 1 := by
    rw [matching_degree G (N j) (hN j (mem_range.mp hj)).1]
    have hv : v ∈ (N j).verts := (hN j (mem_range.mp hj)).2 v
    simp only [if_pos hv]
  have hsum' : (edgeUnion (fun j => (N j).spanningCoe) (range q)).degree v = q := by
    rw [hsum]
    calc
      _ = ∑ _j ∈ range q, 1 := sum_congr rfl hdeg
      _ = q := by simp
  omega

/-- The natural-number degree of a regular residual, with no separate
assumption that the sequence length is at most the initial degree. -/
theorem perfect_deletion_regular (G : SimpleGraph V)
    (N : ℕ → G.Subgraph) (q k : ℕ)
    (hregular : ∀ v, G.degree v = k)
    (hN : ∀ j < q, (N j).IsPerfectMatching)
    (hpresent : ∀ j < q, (N j).spanningCoe ≤
      G \ edgeUnion (fun i => (N i).spanningCoe) (range j)) (v : V) :
    q ≤ k ∧ (G \ edgeUnion (fun j => (N j).spanningCoe) (range q)).degree v = k-q := by
  have hid := perfect_deletion_degree_identity G N q hN hpresent v
  rw [hregular] at hid
  constructor <;> omega

/-- The adaptive budget is obtained from a genuine ambient deletion
sequence, not postulated as an extra condition on the forbidden sets. -/
theorem deletion_sequence_footprint_le_error (U : Finset V) (G : SimpleGraph V)
    (H : SimpleGraph U) (hH : H ≤ G.induce (U : Set V))
    (F N : ℕ → G.Subgraph) (q k a : ℕ)
    (hF : ∀ j < q, (F j).IsMatching)
    (hFN : ∀ j < q, (F j).spanningCoe ≤ (N j).spanningCoe)
    (hpresent : ∀ j < q, (N j).spanningCoe ≤
      G \ edgeUnion (fun i => (N i).spanningCoe) (range j))
    (hno : ∀ j < q, ∀ u v, u ∈ U → v ∈ U → ¬ (F j).Adj u v)
    (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ v, k ≤ H.degree v + a) (v : U) :
    footprintCount U G F (range q) v ≤ a := by
  apply footprintCount_le_error U G H hH F (range q)
    (fun j hj => hF j (mem_range.mp hj))
    (deletion_sequence_partial_pairwise G F N q hFN hpresent)
    (fun j hj => hno j (mem_range.mp hj)) k a hregular hdegree

omit [Fintype V] in
/-- The currently presented partial matching need not have a completion
yet. Its presence in the current residual suffices to make the enlarged
partial-matching prefix edge-disjoint. -/
theorem partial_prefix_pairwise (G : SimpleGraph V)
    (F N : ℕ → G.Subgraph) (q : ℕ)
    (hFN : ∀ j < q, (F j).spanningCoe ≤ (N j).spanningCoe)
    (hpresent : ∀ j ≤ q, (F j).spanningCoe ≤
      G \ edgeUnion (fun i => (N i).spanningCoe) (range j)) :
    ∀ i ∈ range (q+1), ∀ j ∈ range (q+1), i ≠ j →
      Disjoint (F i).spanningCoe (F j).spanningCoe := by
  intro i hi j hj hij
  have hiq : i ≤ q := by simpa only [mem_range, Nat.lt_succ_iff] using hi
  have hjq : j ≤ q := by simpa only [mem_range, Nat.lt_succ_iff] using hj
  apply disjoint_iff_inf_le.mpr
  rintro u v ⟨hiuv,hjuv⟩
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact (hpresent j hjq hjuv).2
      ⟨i,mem_range.mpr hij,hFN i (hij.trans_le hjq) hiuv⟩
  · exact (hpresent i hiq hiuv).2
      ⟨j,mem_range.mpr hji,hFN j (hji.trans_le hiq) hjuv⟩

/-- The incidence condition for a new adaptive input follows before
constructing that input's core completion. -/
theorem next_footprint_le_error (U : Finset V) (G : SimpleGraph V)
    (H : SimpleGraph U) (hH : H ≤ G.induce (U : Set V))
    (F N : ℕ → G.Subgraph) (q k a : ℕ)
    (hF : ∀ j ≤ q, (F j).IsMatching)
    (hFN : ∀ j < q, (F j).spanningCoe ≤ (N j).spanningCoe)
    (hpresent : ∀ j ≤ q, (F j).spanningCoe ≤
      G \ edgeUnion (fun i => (N i).spanningCoe) (range j))
    (hno : ∀ j ≤ q, ∀ u v, u ∈ U → v ∈ U → ¬ (F j).Adj u v)
    (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ v, k ≤ H.degree v + a) (v : U) :
    footprintCount U G F (range (q+1)) v ≤ a := by
  apply footprintCount_le_error U G H hH F (range (q+1))
    (fun j hj => hF j (by simpa only [mem_range, Nat.lt_succ_iff] using hj))
    (partial_prefix_pairwise G F N q hFN hpresent)
    (fun j hj => hno j (by simpa only [mem_range, Nat.lt_succ_iff] using hj))
    k a hregular hdegree

/-- A real core-error bound can be used directly by the adaptive packing
interface, with no rounding loss. -/
theorem footprintCount_le_real_error (U : Finset V) (G : SimpleGraph V)
    (H : SimpleGraph U) (hH : H ≤ G.induce (U : Set V))
    (F : J → G.Subgraph) (T : Finset J)
    (hF : ∀ j ∈ T, (F j).IsMatching)
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      Disjoint (F i).spanningCoe (F j).spanningCoe)
    (hno : ∀ j ∈ T, ∀ u v, u ∈ U → v ∈ U → ¬ (F j).Adj u v)
    (k : ℕ) (a : ℝ) (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ v, (k : ℝ) - a ≤ H.degree v) (v : U) :
    (footprintCount U G F T v : ℝ) ≤ a := by
  have hcount := footprintCount_add_core_degree_le U G H hH F T hF hdisj hno v
  rw [hregular] at hcount
  have hcount' : (footprintCount U G F T v : ℝ) + H.degree v ≤ k := by
    exact_mod_cast hcount
  have hdeg := hdegree v
  linarith

omit [Fintype V] in
/-- Edge disjointness of ambient completions transfers to their exact
restrictions in a core. -/
theorem local_pairwise_of_ambient (U : Finset V) (G : SimpleGraph V)
    (H : SimpleGraph U) (C : J → H.Subgraph) (N : J → G.Subgraph) (T : Finset J)
    (hlocal : ∀ j ∈ T, (N j).spanningCoe.induce (U : Set V) = (C j).spanningCoe)
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      Disjoint (N i).spanningCoe (N j).spanningCoe) :
    ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      Disjoint (C i).spanningCoe (C j).spanningCoe := by
  intro i hi j hj hij
  apply disjoint_iff_inf_le.mpr
  rintro u v ⟨hiuv,hjuv⟩
  have hiN : (N i).Adj u.val v.val := by
    change ((N i).spanningCoe.induce (U : Set V)).Adj u v
    simpa only [hlocal i hi] using hiuv
  have hjN : (N j).Adj u.val v.val := by
    change ((N j).spanningCoe.induce (U : Set V)).Adj u v
    simpa only [hlocal j hj] using hjuv
  exact (hdisj i hi j hj hij).le_bot ⟨hiN,hjN⟩

omit [Fintype V] in
/-- Concrete core embedding for a family assembled from partial matchings
and local completions; the induced-graph identity is supplied by construction. -/
theorem assembled_remainingCore_le_residual {I : Type*} (G : SimpleGraph V)
    (U : I → Finset V) (H : ∀ i, SimpleGraph (U i))
    (hH : ∀ i, H i ≤ G.induce (U i : Set V))
    (F : J → G.Subgraph) (C : J → ∀ i, (H i).Subgraph) (T : Finset J)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hno : ∀ j ∈ T, ∀ i u v, u ∈ U i → v ∈ U i → ¬ (F j).Adj u v)
    (i : I) :
    remainingCore (U i) (H i) (fun j => C j i) T ≤
      (G \ edgeUnion (fun j =>
        (assembledMatching G (F j) (fun l =>
          embedCoreMatching G (U l) (H l) (hH l) (C j l))).spanningCoe) T).induce
            (U i : Set V) := by
  apply remainingCore_le_residual (U i) G (H i) (hH i) (fun j => C j i)
  intro j hj
  exact assembledMatching_induce_eq G U H hH (F j) (C j) hdisjoint (hno j hj) i

/-- The phase preserves a real core error exactly, as required by the
safe-completion interface. -/
theorem remainingCore_real_degree_bounds (U : Finset V) (G : SimpleGraph V)
    (H : SimpleGraph U) (hH : H ≤ G.induce (U : Set V))
    (F : J → G.Subgraph) (C : J → H.Subgraph) (T : Finset J)
    (hF : ∀ j ∈ T, (F j).IsMatching)
    (hFdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      Disjoint (F i).spanningCoe (F j).spanningCoe)
    (hno : ∀ j ∈ T, ∀ u v, u ∈ U → v ∈ U → ¬ (F j).Adj u v)
    (hC : ∀ j ∈ T, (C j).IsMatching)
    (hCdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      Disjoint (C i).spanningCoe (C j).spanningCoe)
    (hverts : ∀ j ∈ T, (C j).verts = (coveredCore U G (F j) : Set U)ᶜ)
    (k : ℕ) (a : ℝ) (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ v, (k : ℝ)-a ≤ H.degree v) (v : U) :
    (k : ℝ)-T.card-a ≤ (remainingCore U H C T).degree v ∧
      ((remainingCore U H C T).degree v : ℝ) ≤ k-T.card := by
  have hid := remainingCore_degree_identity U G H F C T hC hCdisj hverts v
  have hidR : ((remainingCore U H C T).degree v : ℝ) + T.card =
      H.degree v + footprintCount U G F T v := by exact_mod_cast hid
  have hcount := footprintCount_add_core_degree_le U G H hH F T hF hFdisj hno v
  rw [hregular] at hcount
  have hcountR : (footprintCount U G F T v : ℝ) + H.degree v ≤ k := by
    exact_mod_cast hcount
  have hdeg := hdegree v
  have hnonneg : 0 ≤ (footprintCount U G F T v : ℝ) := Nat.cast_nonneg _
  constructor <;> linarith

end Overfull.ForeignIncidence
