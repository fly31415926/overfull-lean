import Overfull.MatchingPolytope
import Overfull.MultigraphMatchingProbability

/-!
# König's edge-coloring theorem for finite bipartite multigraphs

Parallel edges are distinct elements of the edge type. A matching covering
all vertices of maximum degree is obtained from the actual matching polytope.
Deleting this matching reduces the degree bound, and induction adds one color.
-/

namespace Overfull.Multigraph

open Finset Classical

variable {V E : Type*}

/-- A proper coloring of the actual edge copies with `k` colors. -/
structure EdgeColoring (G : Multigraph V E) (k : ℕ) where
  color : E → Fin k
  proper : ∀ {e f : E} {v : V}, color e = color f →
    v ∈ G.edge e → v ∈ G.edge f → e = f

/-- A bipartition labels each vertex by one of two sides, and every edge
has its endpoints on different sides. -/
def IsBipartite (G : Multigraph V E) : Prop :=
  ∃ side : V → Bool, ∀ e, side (G.firstEnd e) ≠ side (G.secondEnd e)

private noncomputable def endpointOnSide (G : Multigraph V E)
    (side : V → Bool) (t : Bool) (e : E) : V :=
  if side (G.firstEnd e) = t then G.firstEnd e else G.secondEnd e

private theorem endpointOnSide_incident (G : Multigraph V E)
    (side : V → Bool) (t : Bool) (e : E) :
    endpointOnSide G side t e ∈ G.edge e := by
  rw [G.incident_iff]
  unfold endpointOnSide
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem endpointOnSide_label (G : Multigraph V E)
    (side : V → Bool) (hside : ∀ e, side (G.firstEnd e) ≠ side (G.secondEnd e))
    (t : Bool) (e : E) :
    side (endpointOnSide G side t e) = t := by
  have h := hside e
  cases h₁ : side (G.firstEnd e) <;>
    cases h₂ : side (G.secondEnd e) <;> cases t <;> simp_all [endpointOnSide]

variable [Fintype E]

/-- Each internal edge has exactly one endpoint on the indicated side.
Counting its chosen endpoint bounds the number of internal edge copies. -/
theorem internal_edges_le_bipartition_side (G : Multigraph V E)
    (side : V → Bool) (hside : ∀ e, side (G.firstEnd e) ≠ side (G.secondEnd e))
    (k : ℕ) (hdegree : ∀ v, G.degree v ≤ k)
    (X : Finset V) (t : Bool) :
    (G.internalEdges X).card ≤ k * (X.filter (fun v => side v = t)).card := by
  have hmap : Set.MapsTo (endpointOnSide G side t) (G.internalEdges X)
      (X.filter (fun v => side v = t)) := by
    intro e he
    have hx := (G.mem_internalEdges X e).mp he
    apply Finset.mem_filter.mpr
    refine ⟨?_, endpointOnSide_label G side hside t e⟩
    unfold endpointOnSide
    split_ifs
    · exact hx.1
    · exact hx.2
  calc
    _ = ∑ v ∈ X.filter (fun v => side v = t),
        ((G.internalEdges X).filter (fun e => endpointOnSide G side t e = v)).card :=
      Finset.card_eq_sum_card_fiberwise hmap
    _ ≤ ∑ _v ∈ X.filter (fun v => side v = t), k := by
      apply Finset.sum_le_sum
      intro v _
      have hsub : (G.internalEdges X).filter (fun e => endpointOnSide G side t e = v) ⊆
          G.incidenceEdges v := by
        intro e he
        rw [G.mem_incidenceEdges]
        have hh := endpointOnSide_incident G side t e
        rwa [(Finset.mem_filter.mp he).2] at hh
      exact (Finset.card_le_card hsub).trans (hdegree v)
    _ = _ := by simp [Nat.mul_comm]

/-- The degree bound in a bipartite multigraph rules out every overfull set,
with parallel edge copies counted separately. -/
theorem bipartite_not_overfull (G : Multigraph V E) (hG : G.IsBipartite)
    (k : ℕ) (hdegree : ∀ v, G.degree v ≤ k) (X : Finset V) :
    ¬ G.IsOverfull k X := by
  obtain ⟨side, hside⟩ := hG
  have hleft := internal_edges_le_bipartition_side G side hside k hdegree X false
  have hright := internal_edges_le_bipartition_side G side hside k hdegree X true
  have hpartition :
      (X.filter (fun v => side v = false)).card +
        (X.filter (fun v => side v = true)).card = X.card := by
    calc
      _ = ∑ v ∈ X, (1 : ℕ) := by
        simp only [Finset.card_filter, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro v _
        cases side v <;> simp
      _ = _ := by simp
  have hbound : (G.internalEdges X).card ≤ k * (X.card / 2) := by
    by_cases h : (X.filter (fun v => side v = false)).card ≤
        (X.filter (fun v => side v = true)).card
    · have hsmall : (X.filter (fun v => side v = false)).card ≤ X.card / 2 := by omega
      exact hleft.trans (Nat.mul_le_mul_left k hsmall)
    · have hsmall : (X.filter (fun v => side v = true)).card ≤ X.card / 2 := by omega
      exact hright.trans (Nat.mul_le_mul_left k hsmall)
  exact not_lt_of_ge hbound

variable [Fintype V]

/-- A bipartite multigraph has a matching covering all vertices whose degree
attains the positive upper bound. -/
theorem exists_matching_covers_degree (G : Multigraph V E) (hG : G.IsBipartite)
    {k : ℕ} (hk : 0 < k) (hdegree : ∀ v, G.degree v ≤ k) :
    ∃ M : Finset E, G.IsMatching M ∧
      ∀ v, G.degree v = k → ∃ e ∈ M, v ∈ G.edge e := by
  obtain ⟨ι, inst, w, M, hw, hsum, hM, _, hcover⟩ :=
    G.exists_uniform_matching_distribution hk hdegree (G.bipartite_not_overfull hG k hdegree)
  letI := inst
  have hpositive : 0 < ∑ i, w i := by rw [hsum]; norm_num
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => hw i)).mp hpositive
  exact ⟨M i, hM i, fun v hv => hcover v hv i hi⟩


/-- König's edge-coloring theorem for finite loopless bipartite multigraphs.
Every edge copy receives one of the `k` colors, and incident distinct copies
receive different colors. -/
theorem exists_edgeColoring_of_bipartite (G : Multigraph V E)
    (hG : G.IsBipartite) (k : ℕ) (hdegree : ∀ v, G.degree v ≤ k) :
    Nonempty (G.EdgeColoring k) := by
  classical
  induction k generalizing E with
  | zero =>
      have hedge (e : E) : False := by
        have he : G.firstEnd e ∈ G.edge e := (G.incident_iff e (G.firstEnd e)).mpr (Or.inl rfl)
        have hpos : 0 < G.degree (G.firstEnd e) :=
          Finset.card_pos.mpr ⟨e, (G.mem_incidenceEdges (G.firstEnd e) e).mpr he⟩
        have hbound := hdegree (G.firstEnd e)
        omega
      refine ⟨⟨fun e => False.elim (hedge e), ?_⟩⟩
      intro e
      exact False.elim (hedge e)
  | succ k ih =>
      obtain ⟨M, hM, hcover⟩ := G.exists_matching_covers_degree hG (Nat.succ_pos k) hdegree
      let R := Overfull.MultigraphMatchingProbability.remainingGraph G M
      have hRdegree (v : V) : R.degree v ≤ k := by
        have hpart := Overfull.MultigraphMatchingProbability.remaining_degree_add_selected
          (G := G) M v
        change R.degree v + (M.filter (fun e => v ∈ G.edge e)).card = G.degree v at hpart
        have hbound := hdegree v
        by_cases hv : G.degree v = k + 1
        · obtain ⟨e, he, hev⟩ := hcover v hv
          have hpos : 0 < (M.filter (fun e => v ∈ G.edge e)).card :=
            Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hev⟩⟩
          omega
        · omega
      have hR : R.IsBipartite := by
        obtain ⟨side, hside⟩ := hG
        exact ⟨side, fun e => hside e.val⟩
      obtain ⟨c⟩ := ih R hR hRdegree
      let color : E → Fin (k + 1) := fun e =>
        if he : e ∈ M then Fin.last k else (c.color ⟨e, he⟩).castSucc
      refine ⟨⟨color, ?_⟩⟩
      intro e f v hef hev hfv
      by_cases he : e ∈ M
      · by_cases hf : f ∈ M
        · exact hM e he f hf v hev hfv
        · have hh : Fin.last k = (c.color ⟨f, hf⟩).castSucc := by
            simpa only [color, dif_pos he, dif_neg hf] using hef
          exact False.elim ((Fin.castSucc_ne_last (c.color ⟨f, hf⟩)) hh.symm)
      · by_cases hf : f ∈ M
        · have hh : (c.color ⟨e, he⟩).castSucc = Fin.last k := by
            simpa only [color, dif_neg he, dif_pos hf] using hef
          exact False.elim ((Fin.castSucc_ne_last (c.color ⟨e, he⟩)) hh)
        · have hh : (c.color ⟨e, he⟩).castSucc = (c.color ⟨f, hf⟩).castSucc := by
            simpa only [color, dif_neg he, dif_neg hf] using hef
          have heq := c.proper (Fin.castSucc_injective k hh) hev hfv
          exact congrArg Subtype.val heq

omit [Fintype V] in
/-- Every proper edge coloring uses at least as many colors as the degree
of any vertex. This counts distinct parallel copies separately. -/
theorem EdgeColoring.degree_le {G : Multigraph V E} {k : ℕ}
    (c : G.EdgeColoring k) (v : V) : G.degree v ≤ k := by
  classical
  have hinj : Set.InjOn c.color (G.incidenceEdges v) := by
    intro e he f hf hef
    exact c.proper hef ((G.mem_incidenceEdges v e).mp he) ((G.mem_incidenceEdges v f).mp hf)
  have hc := Finset.card_image_iff.mpr hinj
  calc
    G.degree v = ((G.incidenceEdges v).image c.color).card := hc.symm
    _ ≤ Fintype.card (Fin k) := Finset.card_le_univ _
    _ = k := Fintype.card_fin k

/-- A finite loopless bipartite multigraph admits a proper `k`-edge-coloring
if and only if all its vertex degrees are at most `k`. -/
theorem konig_edgeColoring_iff (G : Multigraph V E) (hG : G.IsBipartite) (k : ℕ) :
    Nonempty (G.EdgeColoring k) ↔ ∀ v, G.degree v ≤ k := by
  constructor
  · rintro ⟨c⟩ v
    exact c.degree_le v
  · exact G.exists_edgeColoring_of_bipartite hG k

end Overfull.Multigraph


