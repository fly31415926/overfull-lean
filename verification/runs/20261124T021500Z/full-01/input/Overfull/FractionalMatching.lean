import Overfull.Basic
import Overfull.External.PerfectBMatching
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Analysis.Convex.Combination

/-!
# Fractional perfect matchings in regular graphs

The edge coordinates in this file are the actual unordered edges of a finite
simple graph. The imported perfect b-matching polytope theorem is applied with
unit demand at every vertex. Its integral points are then interpreted as
mathlib perfect-matching subgraphs, rather than as abstract incidence data.
-/

namespace Overfull.FractionalMatching

open Finset Classical

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

/-- Choose an orientation of each actual edge, only to use the endpoint-based
statement of the imported polytope theorem. -/
noncomputable def firstEnd (e : G.edgeSet) : V := e.val.out.1

noncomputable def secondEnd (e : G.edgeSet) : V := e.val.out.2

theorem edge_eq (e : G.edgeSet) : s(firstEnd e, secondEnd e) = e.val := by
  exact e.val.out_eq

theorem endpoint_adj (e : G.edgeSet) : G.Adj (firstEnd e) (secondEnd e) := by
  change s(firstEnd e, secondEnd e) ∈ G.edgeSet
  simpa only [edge_eq] using e.property

theorem endpoints_distinct (e : G.edgeSet) : firstEnd e ≠ secondEnd e :=
  (endpoint_adj e).ne

theorem incident_iff (e : G.edgeSet) (v : V) :
    v ∈ e.val ↔ firstEnd e = v ∨ secondEnd e = v := by
  rw [← edge_eq e, Sym2.mem_iff]
  exact or_congr eq_comm eq_comm

/-- The spanning subgraph selected by the coordinates that equal one. -/
def selectedSubgraph (z : G.edgeSet → ℝ) : G.Subgraph where
  verts := Set.univ
  Adj v w := ∃ h : G.Adj v w, z (⟨s(v, w), h⟩ : G.edgeSet) = 1
  adj_sub := fun h => h.choose
  edge_vert := fun _ => Set.mem_univ _
  symm := by
    intro v w h
    obtain ⟨hvw, hz⟩ := h
    refine ⟨hvw.symm, ?_⟩
    have he : (⟨s(w, v), hvw.symm⟩ : G.edgeSet) = ⟨s(v, w), hvw⟩ :=
      Subtype.ext Sym2.eq_swap
    rw [he]
    exact hz

/-- An indicator is indexed by the original graph's actual edge subtype. -/
noncomputable def matchingIndicator (M : G.Subgraph) (e : G.edgeSet) : ℝ :=
  if e.val ∈ M.edgeSet then 1 else 0

/-- The set of indicator vectors of mathlib perfect-matching subgraphs. -/
def perfectMatchingIndicators (G : SimpleGraph V) : Set (G.edgeSet → ℝ) :=
  {z | ∃ M : G.Subgraph, M.IsPerfectMatching ∧ z = matchingIndicator M}

theorem selected_mem_edge_iff (z : G.edgeSet → ℝ) (e : G.edgeSet) :
    e.val ∈ (selectedSubgraph z).edgeSet ↔ z e = 1 := by
  rcases e with ⟨e, he⟩
  obtain ⟨v, w⟩ := e
  change (∃ h : G.Adj v w, z (⟨s(v, w), h⟩ : G.edgeSet) = 1) ↔
    z (⟨s(v, w), he⟩ : G.edgeSet) = 1
  exact ⟨fun ⟨_, hz⟩ => hz, fun hz => ⟨he, hz⟩⟩

theorem selected_indicator_eq (z : G.edgeSet → ℝ)
    (hz : ∀ e, z e = 0 ∨ z e = 1) :
    matchingIndicator (selectedSubgraph z) = z := by
  funext e
  simp only [matchingIndicator, selected_mem_edge_iff]
  rcases hz e with h | h <;> simp [h]

variable [Fintype V] [DecidableRel G.Adj]

/-- The incidence count used by the endpoint encoding is the actual graph
degree. -/
theorem incident_card (v : V) :
    (univ.filter (fun e : G.edgeSet => firstEnd e = v ∨ secondEnd e = v)).card =
      G.degree v := by
  let S := univ.filter (fun e : G.edgeSet => firstEnd e = v ∨ secondEnd e = v)
  have himage : S.image Subtype.val = G.incidenceFinset v := by
    ext e
    constructor
    · intro he
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
      apply (G.mem_incidenceFinset v d.val).mpr
      exact ⟨d.property, (incident_iff d v).mpr (Finset.mem_filter.mp hd).2⟩
    · intro he
      have he' := (G.mem_incidenceFinset v e).mp he
      exact Finset.mem_image.mpr ⟨⟨e, he'.1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (incident_iff ⟨e, he'.1⟩ v).mp he'.2⟩, rfl⟩
  calc
    S.card = (S.image Subtype.val).card :=
      (Finset.card_image_of_injective S Subtype.val_injective).symm
    _ = G.degree v := by rw [himage, G.card_incidenceFinset_eq_degree]

/-- The endpoint encoding's internal edges are exactly the project's actual
internal-edge finset. -/
theorem inside_eq (X : Finset V) :
    Lovasz.BMatch.inside firstEnd secondEnd (univ : Finset G.edgeSet) X =
      internalEdges G X := by
  ext e
  simp only [Lovasz.BMatch.inside, internalEdges, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [← edge_eq e]
  simp only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff, Finset.singleton_subset_iff]

/-- In a positive regular graph the uniform edge vector satisfies every
vertex degree equation of the perfect-matching polytope. -/
theorem uniform_degree (hk : 0 < k) (hregular : ∀ v, G.degree v = k) (v : V) :
    Lovasz.BMatch.dsum firstEnd secondEnd (univ : Finset G.edgeSet)
      (fun _ => (1 : ℝ) / k) v = 1 := by
  simp only [Lovasz.BMatch.dsum, Finset.sum_const, nsmul_eq_mul, incident_card, hregular]
  exact mul_one_div_cancel (by exact_mod_cast hk.ne')

/-- No-overfullness supplies all odd-cut inequalities for the uniform vector.
This verifies the graph hypotheses of the imported polytope theorem. -/
theorem uniform_mem_fractional_polytope (hk : 0 < k)
    (hregular : ∀ v, G.degree v = k)
    (hno : ∀ X : Finset V, ¬ IsOverfull G k X) :
    (fun _ : G.edgeSet => (1 : ℝ) / k) ∈
      Lovasz.BMatch.PS firstEnd secondEnd univ (fun _ : V => 1) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨fun _ => div_nonneg zero_le_one hkR.le, ?_, ?_, ?_⟩
  · intro e he
    exact False.elim (he (Finset.mem_univ e))
  · intro v
    simpa only [Nat.cast_one] using uniform_degree hk hregular v
  · intro X hodd
    have hoddcard : Odd X.card := by simpa only [Finset.sum_const, nsmul_eq_mul,
      Nat.mul_one] using hodd
    have hcard : X.card = 2 * (X.card / 2) + 1 := by
      have hmod := Nat.odd_iff.mp hoddcard
      omega
    have hbound : (internalEdges G X).card ≤ k * (X.card / 2) :=
      Nat.not_lt.mp (hno X)
    have hboundR : ((internalEdges G X).card : ℝ) * ((1 : ℝ) / k) ≤ (X.card / 2 : ℕ) := by
      rw [mul_one_div, div_le_iff₀ hkR]
      exact_mod_cast (hbound.trans_eq (Nat.mul_comm k (X.card / 2)))
    have hhand := Lovasz.BMatch.handshake firstEnd secondEnd (univ : Finset G.edgeSet)
      (fun e _ => endpoints_distinct e) X (fun _ => (1 : ℝ) / k)
    simp only [uniform_degree hk hregular, Finset.sum_const, nsmul_eq_mul,
      mul_one, inside_eq] at hhand
    have hcardR : (X.card : ℝ) = 2 * (X.card / 2 : ℕ) + 1 := by exact_mod_cast hcard
    simp only [Finset.sum_const, nsmul_eq_mul]
    nlinarith

/-- Every integral point with unit vertex demands selects exactly one actual
edge at each vertex. -/
theorem integral_unique_incident {z : G.edgeSet → ℝ}
    (hz : z ∈ Lovasz.BMatch.IS firstEnd secondEnd univ (fun _ : V => 1)) (v : V) :
    ∃! e : G.edgeSet, v ∈ e.val ∧ z e = 1 := by
  let S := univ.filter (fun e : G.edgeSet => v ∈ e.val ∧ z e = 1)
  have hsum : (S.card : ℝ) = 1 := by
    calc
      (S.card : ℝ) = ∑ e ∈ univ.filter (fun e : G.edgeSet =>
          firstEnd e = v ∨ secondEnd e = v), if z e = 1 then (1 : ℝ) else 0 := by
        simp only [Finset.sum_boole, Finset.filter_filter, ← incident_iff]
        rfl
      _ = Lovasz.BMatch.dsum firstEnd secondEnd univ z v := by
        unfold Lovasz.BMatch.dsum
        apply Finset.sum_congr rfl
        intro e he
        rcases hz.1 e with h | h <;> simp [h]
      _ = 1 := by simpa only [Nat.cast_one] using hz.2.2 v
  have hcard : S.card = 1 := by exact_mod_cast hsum
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcard
  have hemem : e ∈ S := by rw [he]; exact Finset.mem_singleton_self _
  refine ⟨e, (Finset.mem_filter.mp hemem).2, ?_⟩
  intro d hd
  have hdmem : d ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩
  simpa only [he, Finset.mem_singleton] using hdmem

/-- An integral point of the imported polytope gives an actual perfect matching
in mathlib's graph-theoretic sense. -/
theorem selectedSubgraph_isPerfectMatching {z : G.edgeSet → ℝ}
    (hz : z ∈ Lovasz.BMatch.IS firstEnd secondEnd univ (fun _ : V => 1)) :
    (selectedSubgraph z).IsPerfectMatching := by
  apply SimpleGraph.Subgraph.isPerfectMatching_iff.mpr
  intro v
  obtain ⟨e, he, hunique⟩ := integral_unique_incident hz v
  obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp he.1
  have hvw : G.Adj v w := by
    change s(v, w) ∈ G.edgeSet
    simpa only [← hw] using e.property
  have hew : (⟨s(v, w), hvw⟩ : G.edgeSet) = e := Subtype.ext hw.symm
  refine ⟨w, ⟨hvw, by simpa only [hew] using he.2⟩, ?_⟩
  intro u hu
  obtain ⟨hvu, hzu⟩ := hu
  have heu : (⟨s(v, u), hvu⟩ : G.edgeSet) = e :=
    hunique _ ⟨by simp, hzu⟩
  have hpair : s(v, u) = s(v, w) :=
    (congrArg (fun a : G.edgeSet => a.val) heu).trans hw
  rcases Sym2.eq_iff.mp hpair with ⟨_, huw⟩ | ⟨hvw', huv⟩
  · exact huw
  · exact huv.trans hvw'

/-- Integral points are indicators of actual perfect matchings. -/
theorem integral_subset_matchingIndicators :
    Lovasz.BMatch.IS firstEnd secondEnd (univ : Finset G.edgeSet) (fun _ : V => 1) ⊆
      perfectMatchingIndicators G := by
  intro z hz
  exact ⟨selectedSubgraph z, selectedSubgraph_isPerfectMatching hz,
    (selected_indicator_eq z hz.1).symm⟩

/-- A genuine perfect matching has indicator-weighted degree one at each
vertex in the endpoint encoding. -/
theorem perfectMatching_indicator_degree (M : G.Subgraph) (hM : M.IsPerfectMatching)
    (v : V) :
    Lovasz.BMatch.dsum firstEnd secondEnd (univ : Finset G.edgeSet)
      (matchingIndicator M) v = 1 := by
  obtain ⟨w, hvw, hunique⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM v
  let e₀ : G.edgeSet := ⟨s(v, w), M.adj_sub hvw⟩
  have hS : univ.filter (fun e : G.edgeSet => v ∈ e.val ∧ e.val ∈ M.edgeSet) = {e₀} := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hve, heM⟩
      obtain ⟨u, hu⟩ := Sym2.mem_iff_exists.mp hve
      have hvu : M.Adj v u := by
        change s(v, u) ∈ M.edgeSet
        simpa only [← hu] using heM
      have huw := hunique u hvu
      apply Subtype.ext
      calc
        e.val = s(v, u) := hu
        _ = s(v, w) := by rw [huw]
    · intro he
      subst e
      exact ⟨by simp [e₀], hvw⟩
  unfold Lovasz.BMatch.dsum
  simp only [matchingIndicator, Finset.sum_boole, Finset.filter_filter, ← incident_iff]
  rw [hS]
  simp

/-- Indicators of genuine perfect matchings satisfy the imported integral
polytope definition. -/
theorem matchingIndicator_mem_integral (M : G.Subgraph) (hM : M.IsPerfectMatching) :
    matchingIndicator M ∈
      Lovasz.BMatch.IS firstEnd secondEnd (univ : Finset G.edgeSet) (fun _ : V => 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    simp only [matchingIndicator]
    split_ifs <;> simp
  · intro e he
    exact False.elim (he (Finset.mem_univ e))
  · intro v
    simpa only [Nat.cast_one] using perfectMatching_indicator_degree M hM v

/-- The integral points of the imported unit-demand polytope are exactly the
indicators of the graph's actual perfect matchings. -/
theorem integral_eq_matchingIndicators :
    Lovasz.BMatch.IS firstEnd secondEnd (univ : Finset G.edgeSet) (fun _ : V => 1) =
      perfectMatchingIndicators G := by
  apply Set.Subset.antisymm integral_subset_matchingIndicators
  rintro z ⟨M, hM, rfl⟩
  exact matchingIndicator_mem_integral M hM

/-- For a positive regular simple graph with no overfull set, uniform edge
weights lie in the convex hull of its actual perfect-matching indicators. -/
theorem uniform_mem_convexHull (hk : 0 < k) (hregular : ∀ v, G.degree v = k)
    (hno : ∀ X : Finset V, ¬ IsOverfull G k X) :
    (fun _ : G.edgeSet => (1 : ℝ) / k) ∈ convexHull ℝ (perfectMatchingIndicators G) := by
  have hgood : Lovasz.BMatch.Good firstEnd secondEnd
      (univ : Finset G.edgeSet) (fun _ : V => 1) :=
    ⟨fun e _ => endpoints_distinct e, fun _ _ => Or.inl rfl⟩
  have hpoly := Lovasz.BMatch.thmA _ firstEnd secondEnd (univ : Finset G.edgeSet)
    (fun _ : V => 1) rfl hgood (uniform_mem_fractional_polytope hk hregular hno)
  exact convexHull_mono integral_subset_matchingIndicators hpoly

/-- A finite probability distribution on actual perfect matchings in which
each edge has marginal probability exactly `1/k`. This is the probabilistic
form of the matching-polytope input used in the manuscript. -/
theorem exists_perfectMatching_distribution (hk : 0 < k)
    (hregular : ∀ v, G.degree v = k)
    (hno : ∀ X : Finset V, ¬ IsOverfull G k X) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (M : ι → G.Subgraph),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      (∀ i, (M i).IsPerfectMatching) ∧
      ∀ e : G.edgeSet,
        ∑ i ∈ univ.filter (fun i => e.val ∈ (M i).edgeSet), w i = (1 : ℝ) / k := by
  obtain ⟨ι, inst, w, z, hw, hsum, hz, hcoords⟩ :=
    mem_convexHull_iff_exists_fintype.mp (uniform_mem_convexHull hk hregular hno)
  letI := inst
  change ∀ i, ∃ M : G.Subgraph, M.IsPerfectMatching ∧ z i = matchingIndicator M at hz
  choose M hM hMz using hz
  refine ⟨ι, inst, w, M, hw, hsum, hM, ?_⟩
  intro e
  have he := congrArg (fun a : G.edgeSet → ℝ => a e) hcoords
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at he
  calc
    (∑ i ∈ univ.filter (fun i => e.val ∈ (M i).edgeSet), w i) =
        ∑ i, w i * matchingIndicator (M i) e := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      simp only [matchingIndicator]
      split_ifs <;> simp
    _ = ∑ i, w i * z i e := by simp only [hMz]
    _ = (1 : ℝ) / k := he

/-- In particular, every positive regular graph with no overfull set has an
actual perfect matching. -/
theorem exists_perfectMatching (hk : 0 < k) (hregular : ∀ v, G.degree v = k)
    (hno : ∀ X : Finset V, ¬ IsOverfull G k X) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  have hnonempty : (convexHull ℝ (perfectMatchingIndicators G)).Nonempty :=
    ⟨_, uniform_mem_convexHull hk hregular hno⟩
  obtain ⟨z, M, hM, _⟩ := convexHull_nonempty_iff.mp hnonempty
  exact ⟨M, hM⟩

end Overfull.FractionalMatching
