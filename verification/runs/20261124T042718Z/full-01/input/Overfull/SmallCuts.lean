import Overfull.Multigraph
import Overfull.CutCounting
import Overfull.RobustExpansion
import Mathlib.Data.Real.Archimedean

/-!
# Small cuts through disjoint robust cores

The host has a separate type of edge copies and may have parallel edges.
Each specified simple core is embedded into the host by an injective map
of its actual edges, preserving their endpoints.
-/

namespace Overfull

open Finset Classical

namespace SmallCuts

section SimpleCuts

variable {W : Type*} [Fintype W] [DecidableEq W]
variable (G : SimpleGraph W) [DecidableRel G.Adj]

theorem simple_cut_boundary (X : Finset W) :
    (Multigraph.ofSimpleGraph G).cutSize X =
      ∑ v ∈ X, (G.neighborFinset v \ X).card := by
  have h := (Multigraph.ofSimpleGraph G).degree_sum_on X
  simp only [Multigraph.ofSimpleGraph_degree, Multigraph.ofSimpleGraph_internalEdges] at h
  have h' := internal_edges_add_boundary G X
  omega

theorem simple_cut_outside (X : Finset W) :
    (Multigraph.ofSimpleGraph G).cutSize X =
      ∑ v ∈ Xᶜ, (G.neighborFinset v ∩ X).card := by
  rw [← Multigraph.cutSize_compl, simple_cut_boundary]
  simp only [Finset.sdiff_eq_inter_compl, compl_compl]

/-- Robust expansion forces a quadratic cut across every set in the tested range. -/
theorem robust_cut_lower_bound (ν τ : ℝ) (hν : 0 ≤ ν)
    (hrobust : IsRobustExpander G ν τ) (X : Finset W)
    (hlo : τ * Fintype.card W ≤ (X.card : ℝ))
    (hhi : (X.card : ℝ) ≤ (1 - τ) * Fintype.card W) :
    ν^2 * (Fintype.card W : ℝ)^2 ≤ (Multigraph.ofSimpleGraph G).cutSize X := by
  let R := robustNeighbors G ν X
  have hex := hrobust X hlo hhi
  have hRpart := Finset.card_inter_add_card_sdiff R X
  have hRinter := Finset.card_le_card (Finset.inter_subset_right : R ∩ X ⊆ X)
  have hRcount : (R.card : ℝ) ≤ X.card + (R \ X).card := by
    exact_mod_cast (show R.card ≤ X.card + (R \ X).card by omega)
  have hRlower : ν * Fintype.card W ≤ ((R \ X).card : ℝ) := by
    change (X.card : ℝ) + ν * Fintype.card W ≤ R.card at hex
    linarith
  have hsub : R \ X ⊆ Xᶜ := by
    intro v hv
    exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hv).2
  have hsum : (∑ v ∈ R \ X, ((G.neighborFinset v ∩ X).card : ℝ)) ≤
      ∑ v ∈ Xᶜ, ((G.neighborFinset v ∩ X).card : ℝ) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
  have hlower : ((R \ X).card : ℝ) * (ν * Fintype.card W) ≤
      ∑ v ∈ R \ X, ((G.neighborFinset v ∩ X).card : ℝ) := by
    calc
      _ = ∑ _v ∈ R \ X, ν * Fintype.card W := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro v hv
        exact (mem_robustNeighbors G ν X v).mp (Finset.mem_sdiff.mp hv).1
  have hmul := mul_le_mul_of_nonneg_right hRlower
    (mul_nonneg hν (Nat.cast_nonneg (Fintype.card W)))
  have heq : ((Multigraph.ofSimpleGraph G).cutSize X : ℝ) =
      ∑ v ∈ Xᶜ, ((G.neighborFinset v ∩ X).card : ℝ) := by
    exact_mod_cast simple_cut_outside G X
  rw [← heq] at hsum
  nlinarith

/-- Simplicity bounds the neighbors that a shore vertex can have on its own shore. -/
theorem cut_lower_bound_degree (d : ℝ) (hdegree : ∀ v, d ≤ (G.degree v : ℝ))
    (X : Finset W) :
    (X.card : ℝ) * (d - X.card + 1) ≤ (Multigraph.ofSimpleGraph G).cutSize X := by
  have hvertex (v : W) (hv : v ∈ X) :
      d - X.card + 1 ≤ ((G.neighborFinset v \ X).card : ℝ) := by
    have hpos : 1 ≤ X.card := Finset.card_pos.mpr ⟨v,hv⟩
    have hsub : G.neighborFinset v ∩ X ⊆ X.erase v := by
      intro w hw
      rcases Finset.mem_inter.mp hw with ⟨hwG, hwX⟩
      exact Finset.mem_erase.mpr ⟨(G.mem_neighborFinset v w).mp hwG |>.ne.symm, hwX⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hv] at hcard
    have hpart := Finset.card_inter_add_card_sdiff (G.neighborFinset v) X
    rw [SimpleGraph.card_neighborFinset_eq_degree] at hpart
    have hreal : (G.degree v : ℝ) + 1 ≤
        X.card + (G.neighborFinset v \ X).card := by
      exact_mod_cast (show G.degree v + 1 ≤ X.card + (G.neighborFinset v \ X).card by omega)
    linarith [hdegree v]
  calc
    _ = ∑ _v ∈ X, (d - X.card + 1) := by simp; ring
    _ ≤ ∑ v ∈ X, ((G.neighborFinset v \ X).card : ℝ) :=
      Finset.sum_le_sum hvertex
    _ = _ := by exact_mod_cast (simple_cut_boundary G X).symm

end SimpleCuts

/-- A simple graph on an actual vertex set, with each edge embedded as a
specified edge copy of the host multigraph. -/
structure Core {V E : Type*} (G : Multigraph V E) (U : Finset V) where
  graph : SimpleGraph U
  edgeMap : graph.edgeSet ↪ E
  map_edge : ∀ e, G.edge (edgeMap e) = Sym2.map Subtype.val e.val

section EmbeddedCores

variable {V E : Type*} [Fintype V] [Fintype E]
variable {G : Multigraph V E} {U : Finset V}

noncomputable def shore (U X : Finset V) : Finset U :=
  univ.filter (fun v => v.val ∈ X)

omit [Fintype V] in
@[simp] theorem mem_shore (U X : Finset V) (v : U) :
    v ∈ shore U X ↔ v.val ∈ X := by simp [shore]

omit [Fintype V] in
theorem shore_card (U X : Finset V) : (shore U X).card = (X ∩ U).card := by
  have himage : (shore U X).image Subtype.val = X ∩ U := by
    ext v
    simp only [Finset.mem_image, mem_shore, Finset.mem_inter]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨hw, w.property⟩
    · rintro ⟨hvX,hvU⟩
      exact ⟨⟨v,hvU⟩, hvX, rfl⟩
  rw [← Finset.card_image_of_injective _ Subtype.val_injective, himage]

omit [Fintype V] in
theorem shore_compl_card (U X : Finset V) : (shore U X)ᶜ.card = (U \ X).card := by
  have himage : ((shore U X)ᶜ).image Subtype.val = U \ X := by
    ext v
    simp only [Finset.mem_image, Finset.mem_compl, mem_shore, Finset.mem_sdiff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.property, hw⟩
    · rintro ⟨hvU,hvX⟩
      exact ⟨⟨v,hvU⟩, hvX, rfl⟩
  rw [← Finset.card_image_of_injective _ Subtype.val_injective, himage]

namespace Core

noncomputable def mappedCut (C : Core G U) (X : Finset V) : Finset E :=
  ((Multigraph.ofSimpleGraph C.graph).cutEdges (shore U X)).map C.edgeMap

omit [Fintype V] in
theorem map_cut (C : Core G U) (X : Finset V) :
    C.mappedCut X ⊆ G.cutEdges X := by
  intro e he
  obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
  obtain ⟨v,w,hfedge,hv,hw⟩ :=
    (Multigraph.mem_cutEdges_iff (Multigraph.ofSimpleGraph C.graph) (shore U X) f).mp hf
  apply (G.mem_cutEdges_iff X (C.edgeMap f)).mpr
  refine ⟨v.val,w.val,?_,(mem_shore U X v).mp hv,?_⟩
  · rw [C.map_edge]
    change f.val = s(v,w) at hfedge
    rw [hfedge]
    rfl
  · exact fun h => hw ((mem_shore U X w).mpr h)

omit [Fintype V] [Fintype E] in
theorem mappedCut_endpoint (C : Core G U) (X : Finset V) {e : E}
    (he : e ∈ C.mappedCut X) : G.firstEnd e ∈ U := by
  obtain ⟨f, _, rfl⟩ := Finset.mem_map.mp he
  have h : G.firstEnd (C.edgeMap f) ∈ G.edge (C.edgeMap f) := by
    rw [← G.edge_eq]
    simp
  rw [C.map_edge] at h
  obtain ⟨v,_,hv⟩ := Sym2.mem_map.mp h
  rw [← hv]
  exact v.property

omit [Fintype V] [Fintype E] in
theorem mappedCut_card (C : Core G U) (X : Finset V) :
    (C.mappedCut X).card = (Multigraph.ofSimpleGraph C.graph).cutSize (shore U X) := by
  simp [mappedCut, Multigraph.cutSize]

omit [Fintype V] in
theorem cut_le (C : Core G U) (X : Finset V) :
    (Multigraph.ofSimpleGraph C.graph).cutSize (shore U X) ≤ G.cutSize X := by
  rw [← C.mappedCut_card]
  exact Finset.card_le_card (C.map_cut X)

end Core

omit [Fintype V] in
/-- Vertex-disjoint cores contribute disjoint sets of actual host edge copies. -/
theorem sum_core_cuts_le {I : Type*} [Fintype I] (U : I → Finset V)
    (C : ∀ i, Core G (U i)) (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (X : Finset V) :
    (∑ i, (Multigraph.ofSimpleGraph (C i).graph).cutSize (shore (U i) X)) ≤ G.cutSize X := by
  have hpair : (univ : Finset I).toSet.PairwiseDisjoint (fun i => (C i).mappedCut X) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro e hei hej
    exact Finset.disjoint_left.mp (hdisj hij)
      ((C i).mappedCut_endpoint X hei) ((C j).mappedCut_endpoint X hej)
  have hsub : (univ.biUnion (fun i => (C i).mappedCut X)) ⊆ G.cutEdges X := by
    intro e he
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp he
    exact (C i).map_cut X hi
  calc
    _ = ∑ i, ((C i).mappedCut X).card := by simp only [Core.mappedCut_card]
    _ = (univ.biUnion (fun i => (C i).mappedCut X)).card := (Finset.card_biUnion hpair).symm
    _ ≤ G.cutSize X := Finset.card_le_card hsub

end EmbeddedCores

section SmallerShore

variable {W : Type*} [Fintype W] [DecidableEq W]

noncomputable def smallerShore (X : Finset W) : Finset W :=
  if X.card ≤ Xᶜ.card then X else Xᶜ

theorem smallerShore_card (X : Finset W) :
    (smallerShore X).card = min X.card Xᶜ.card := by
  by_cases h : X.card ≤ Xᶜ.card
  · simp [smallerShore,h]
  · simp [smallerShore,h,min_eq_right (le_of_not_ge h)]

theorem smallerShore_card_le_half (X : Finset W) :
    2 * (smallerShore X).card ≤ Fintype.card W := by
  have hpart := Finset.card_compl_add_card X
  rw [smallerShore_card]
  have h₁ := min_le_left X.card Xᶜ.card
  have h₂ := min_le_right X.card Xᶜ.card
  omega

theorem smallerShore_cut {E : Type*} [Fintype E] (G : Multigraph W E)
    (X : Finset W) : G.cutSize (smallerShore X) = G.cutSize X := by
  unfold smallerShore
  split_ifs
  · rfl
  · exact G.cutSize_compl X

end SmallerShore

section MainLemma

variable {V E I : Type*} [Fintype V] [Fintype E] [Fintype I]

set_option maxHeartbeats 1000000 in
/-- An explicit form of the small-cut lemma. The order condition is sufficient
for every fixed positive `ν` and `c`; no simplicity of the host is required.
The host maximum-degree bound and the lower bounds on `a` and `b` are unnecessary. -/
theorem minority_sum_le_one (G : Multigraph V E) (U : I → Finset V)
    (C : ∀ i, Core G (U i)) (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (α c ν τ a b k : ℝ)
    (hα : 0 < α) (hc : 0 < c) (hν : 0 < ν) (hτ : 0 ≤ τ)
    (hτα : τ ≤ α / 10)
    (hklo : α * Fintype.card V ≤ k) (hkhi : k ≤ 2 * Fintype.card V)
    (ha : a ≤ α * Fintype.card V / 10) (hb : b ≤ α * Fintype.card V / 10)
    (hlarge : 3 < ν^2 * c^2 * (Fintype.card V : ℝ))
    (hsize : ∀ i, c * Fintype.card V ≤ ((U i).card : ℝ))
    (hrobust : ∀ i, IsRobustExpander (C i).graph ν τ)
    (hdegree : ∀ i v, k - a ≤ ((C i).graph.degree v : ℝ))
    (X : Finset V) (hcut : (G.cutSize X : ℝ) ≤ k + b) :
    (∑ i, min (X ∩ U i).card (U i \ X).card) ≤ 1 := by
  have hnNat : 0 < Fintype.card V := by
    by_contra h
    have hz : Fintype.card V = 0 := by omega
    norm_num [hz] at hlarge
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast hnNat
  have hkpos : (0 : ℝ) < k := lt_of_lt_of_le (mul_pos hα hn) hklo
  have hαle : α ≤ 2 := (mul_le_mul_iff_left₀ hn).mp (hklo.trans hkhi)
  have hτhalf : τ ≤ (1 : ℝ) / 2 := by linarith only [hτα, hαle]
  have hak : a ≤ k / 10 := by linarith only [ha,hklo]
  have hbk : b ≤ k / 10 := by linarith only [hb,hklo]
  let S := fun i => smallerShore (shore (U i) X)
  have hScut (i : I) :
      (Multigraph.ofSimpleGraph (C i).graph).cutSize (S i) =
        (Multigraph.ofSimpleGraph (C i).graph).cutSize (shore (U i) X) :=
    smallerShore_cut _ _
  have hShalf (i : I) : (2 : ℝ) * (S i).card ≤ (U i).card := by
    have h := smallerShore_card_le_half (shore (U i) X)
    simp only [Fintype.card_coe] at h
    exact_mod_cast h
  have hUle (i : I) : ((U i).card : ℝ) ≤ Fintype.card V := by
    exact_mod_cast Finset.card_le_univ (U i)
  have hSsmall (i : I) : ((S i).card : ℝ) < τ * (U i).card := by
    by_contra h
    have hlo : τ * Fintype.card (U i) ≤ ((S i).card : ℝ) := by
      simpa only [Fintype.card_coe] using le_of_not_gt h
    have hhi : ((S i).card : ℝ) ≤ (1 - τ) * Fintype.card (U i) := by
      simp only [Fintype.card_coe]
      nlinarith only [mul_nonneg (sub_nonneg.mpr hτhalf) (Nat.cast_nonneg (U i).card), hShalf i]
    have hquad := robust_cut_lower_bound (C i).graph ν τ hν.le (hrobust i) (S i) hlo hhi
    simp only [Fintype.card_coe] at hquad
    have hhost := (C i).cut_le X
    rw [← hScut i] at hhost
    have hhostReal : ((Multigraph.ofSimpleGraph (C i).graph).cutSize (S i) : ℝ) ≤
        G.cutSize X := by exact_mod_cast hhost
    have hsquare : c^2 * (Fintype.card V : ℝ)^2 ≤ ((U i).card : ℝ)^2 := by
      simpa only [mul_pow] using
        (sq_le_sq₀ (mul_nonneg hc.le hn.le) (Nat.cast_nonneg (U i).card)).mpr (hsize i)
    have hmul := mul_le_mul_of_nonneg_left hsquare (sq_nonneg ν)
    have hbig := mul_lt_mul_of_pos_right hlarge hn
    nlinarith only [hquad,hhostReal,hmul,hbig,hcut,hkhi,hbk]
  have hStenth (i : I) : ((S i).card : ℝ) ≤ k / 10 := by
    have hτU := mul_le_mul_of_nonneg_left (hUle i) hτ
    have hταn := mul_le_mul_of_nonneg_right hτα hn.le
    linarith only [hSsmall i,hτU,hταn,hklo]
  have hlinear (i : I) :
      (4 * k / 5) * (S i).card ≤
        (Multigraph.ofSimpleGraph (C i).graph).cutSize (shore (U i) X) := by
    have hd := cut_lower_bound_degree (C i).graph (k - a) (hdegree i) (S i)
    rw [hScut i] at hd
    have hcoef : 4 * k / 5 ≤ k - a - (S i).card + 1 := by
      linarith only [hStenth i,hak]
    have hmul := mul_le_mul_of_nonneg_left hcoef (Nat.cast_nonneg (S i).card)
    nlinarith only [hmul,hd]
  have hsum := sum_core_cuts_le U C hdisj X
  have hsumReal :
      (∑ i, ((Multigraph.ofSimpleGraph (C i).graph).cutSize (shore (U i) X) : ℝ)) ≤
        G.cutSize X := by exact_mod_cast hsum
  have hlinSum := Finset.sum_le_sum (s := (univ : Finset I)) (fun i _ => hlinear i)
  rw [← Finset.mul_sum] at hlinSum
  have hScard (i : I) : (S i).card = min (X ∩ U i).card (U i \ X).card := by
    simp only [S, smallerShore_card, shore_card, shore_compl_card]
  simp_rw [hScard] at hlinSum
  have hcast : (∑ i, ((min (X ∩ U i).card (U i \ X).card : ℕ) : ℝ)) =
      ((∑ i, min (X ∩ U i).card (U i \ X).card : ℕ) : ℝ) := by simp
  rw [hcast] at hlinSum
  by_contra h
  have htwo : 2 ≤ ∑ i, min (X ∩ U i).card (U i \ X).card := by omega
  have htwoReal : (2 : ℝ) ≤ (∑ i, min (X ∩ U i).card (U i \ X).card : ℕ) := by
    exact_mod_cast htwo
  have hmul := mul_le_mul_of_nonneg_left htwoReal (by positivity : (0 : ℝ) ≤ 4 * k / 5)
  nlinarith only [hmul,hlinSum,hsumReal,hcut,hbk,hkpos]

end MainLemma

/-- Choosing the larger side in each core gives an actual union of whole cores.
The total number of changed vertices is at most the sum of the minority sizes. -/
theorem union_of_cores_close {V I : Type*} [Fintype I]
    (U : I → Finset V) (X : Finset V)
    (hminority : (∑ i, min (X ∩ U i).card (U i \ X).card) ≤ 1) :
    ∃ A : Finset I,
      (((X ∩ univ.biUnion U) \ A.biUnion U) ∪
        ((A.biUnion U) \ (X ∩ univ.biUnion U))).card ≤ 1 := by
  let A : Finset I := univ.filter (fun i => ¬ (X ∩ U i).card ≤ (U i \ X).card)
  let T := fun i => if (X ∩ U i).card ≤ (U i \ X).card then X ∩ U i else U i \ X
  have hT (i : I) : (T i).card = min (X ∩ U i).card (U i \ X).card := by
    dsimp [T]
    split_ifs with h
    · exact (min_eq_left h).symm
    · exact (min_eq_right (le_of_not_ge h)).symm
  have hsub : ((X ∩ univ.biUnion U) \ A.biUnion U) ∪
      ((A.biUnion U) \ (X ∩ univ.biUnion U)) ⊆ univ.biUnion T := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨hvIn,hvOut⟩ := Finset.mem_sdiff.mp hv
      obtain ⟨hvX,hvW⟩ := Finset.mem_inter.mp hvIn
      obtain ⟨i,_,hvi⟩ := Finset.mem_biUnion.mp hvW
      have hi : (X ∩ U i).card ≤ (U i \ X).card := by
        by_contra h
        exact hvOut (Finset.mem_biUnion.mpr ⟨i,Finset.mem_filter.mpr ⟨mem_univ i,h⟩,hvi⟩)
      apply Finset.mem_biUnion.mpr
      exact ⟨i,mem_univ i,by simp [T,hi,hvX,hvi]⟩
    · obtain ⟨hvA,hvOut⟩ := Finset.mem_sdiff.mp hv
      obtain ⟨i,hiA,hvi⟩ := Finset.mem_biUnion.mp hvA
      have hi : ¬ (X ∩ U i).card ≤ (U i \ X).card := (Finset.mem_filter.mp hiA).2
      have hvX : v ∉ X := by
        intro hvX
        exact hvOut (Finset.mem_inter.mpr
          ⟨hvX,Finset.mem_biUnion.mpr ⟨i,mem_univ i,hvi⟩⟩)
      apply Finset.mem_biUnion.mpr
      exact ⟨i,mem_univ i,by simp [T,hi,hvi,hvX]⟩
  refine ⟨A,(Finset.card_le_card hsub).trans ?_⟩
  calc
    (univ.biUnion T).card ≤ ∑ i, (T i).card := Finset.card_biUnion_le
    _ = ∑ i, min (X ∩ U i).card (U i \ X).card := by simp_rw [hT]
    _ ≤ 1 := hminority

/-- A uniform order threshold exists for each fixed pair of positive parameters. -/
theorem exists_order_threshold (c ν : ℝ) (hc : 0 < c) (hν : 0 < ν) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 3 < ν^2 * c^2 * (n : ℝ) := by
  have hp : 0 < ν^2 * c^2 := mul_pos (sq_pos_of_pos hν) (sq_pos_of_pos hc)
  obtain ⟨n₀,hn₀⟩ := exists_nat_gt (3 / (ν^2 * c^2))
  refine ⟨n₀,fun n hn => ?_⟩
  have hnReal : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hlt : 3 / (ν^2 * c^2) < (n : ℝ) := hn₀.trans_le hnReal
  have h := (div_lt_iff₀ hp).mp hlt
  simpa only [mul_comm] using h

/-- Lemma `two:lem:small-cut`, including its union-of-whole-cores conclusion.
The order threshold depends only on the fixed parameters. Vertex and edge types
are quantified after the threshold, and parallel edge copies are retained. -/
theorem small_cut_lemma (α c ν τ : ℝ)
    (hα : 0 < α) (hc : 0 < c) (hν : 0 < ν) (hτ : 0 < τ)
    (_hντ : ν ≤ τ) (hτα : τ ≤ α / 10) :
    ∃ n₀ : ℕ, ∀ (V E I : Type*) [Fintype V] [Fintype E] [Fintype I]
      (G : Multigraph V E) (U : I → Finset V) (C : ∀ i, Core G (U i)),
      Pairwise (fun i j => Disjoint (U i) (U j)) →
      ∀ (k : ℝ), (∀ v, (G.degree v : ℝ) ≤ k) → k ≤ 2 * Fintype.card V →
      α * Fintype.card V ≤ k →
      ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b →
      a ≤ α * Fintype.card V / 10 → b ≤ α * Fintype.card V / 10 →
      n₀ ≤ Fintype.card V →
      (∀ i, c * Fintype.card V ≤ ((U i).card : ℝ)) →
      (∀ i, IsRobustExpander (C i).graph ν τ) →
      (∀ i v, k - a ≤ ((C i).graph.degree v : ℝ)) →
      ∀ X : Finset V, (G.cutSize X : ℝ) ≤ k + b →
        (∑ i, min (X ∩ U i).card (U i \ X).card) ≤ 1 ∧
        ∃ A : Finset I,
          (((X ∩ univ.biUnion U) \ A.biUnion U) ∪
            ((A.biUnion U) \ (X ∩ univ.biUnion U))).card ≤ 1 := by
  obtain ⟨n₀,hn₀⟩ := exists_order_threshold c ν hc hν
  refine ⟨n₀,?_⟩
  intro V E I _ _ _ G U C hdisj k _ hkhi hklo a b _ _ ha hb hn hsize hrobust hdegree X hcut
  have hminority := minority_sum_le_one G U C hdisj α c ν τ a b k hα hc hν hτ.le
    hτα hklo hkhi ha hb (hn₀ _ hn) hsize hrobust hdegree X hcut
  exact ⟨hminority, union_of_cores_close U X hminority⟩

end SmallCuts
end Overfull
