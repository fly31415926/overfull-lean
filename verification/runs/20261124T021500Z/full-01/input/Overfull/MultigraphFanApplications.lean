import Overfull.MultigraphFan

/-!
# Moving vertices out of a simple core

The core is an actual set of edge copies with distinct unordered endpoint
pairs. All exterior graphs are obtained by deleting those copies.
-/

namespace Overfull.Multigraph

open Finset Classical

variable {V E : Type*} [Fintype V] [Fintype E] (G : Multigraph V E)

/-- The first-fan conclusion from the actual degree bound inside the
candidate minimal graph. -/
theorem first_fan_of_core_degree (k a : ℕ) (U : Finset V) (F : Finset E)
    (hregular : ∀ v, G.degree v = k) (hF : (G.restrictEdges F).IsKMinimal k)
    (hcore : ∀ v ∈ U, (G.restrictEdges F).degree v ≤ a) (hka : 2 * a < k) :
    (G.restrictEdges F).internalEdges U = ∅ ∧
    ∀ x, 2 * a < (G.edgesTo x U).card →
      (G.restrictEdges F).edgesTo x U = ∅ ∧
      (G.restrictEdges F).degree x ≤ k - (G.edgesTo x U).card ∧
      (G.restrictEdges F).degree x < k := by
  constructor
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨hx,hv⟩ := ((G.restrictEdges F).mem_internalEdges U e).mp he
    have hsum := hF.endpoint_degree_sum e ((G.restrictEdges F).firstEnd e)
      ((G.restrictEdges F).secondEnd e) ((G.restrictEdges F).edge_eq e).symm
    have hdx := hcore _ hx
    have hdv := hcore _ hv
    omega
  · intro x hx
    have hsum := G.edgesTo_compl_card_add x U
    rw [hregular] at hsum
    have hout := G.restrictEdges_edgesTo_card_le F x Uᶜ
    have hnone : (G.restrictEdges F).edgesTo x U = ∅ := by
      apply hF.no_edgesTo_low_set x U a hcore hka.le
      intro v hv
      have hp := (G.restrictEdges F).parallelEdges_card_le_degree x v
      have hdv := hcore v hv
      omega
    refine ⟨hnone,?_,?_⟩
    · have h := (G.restrictEdges F).edgesTo_compl_card_add x U
      rw [hnone,Finset.card_empty,Nat.add_zero] at h
      omega
    · have h := (G.restrictEdges F).edgesTo_compl_card_add x U
      rw [hnone,Finset.card_empty,Nat.add_zero] at h
      omega

/-- Lemma 2.7, allowing a real exterior degree bound. The condition that
the deleted edges are supported on `U` is unnecessary for this conclusion. -/
theorem first_fan (k : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (U : Finset V) (H F : Finset E)
    (hregular : ∀ v, G.degree v = k) (hsub : F ⊆ Hᶜ)
    (hF : (G.restrictEdges F).IsKMinimal k)
    (hcore : ∀ v ∈ U, ((G.restrictEdges Hᶜ).degree v : ℝ) ≤ a)
    (hka : 2 * a < k) :
    (G.restrictEdges F).internalEdges U = ∅ ∧
    ∀ x, 2 * a < ((G.edgesTo x U).card : ℝ) →
      (G.restrictEdges F).edgesTo x U = ∅ ∧
      (G.restrictEdges F).degree x ≤ k - (G.edgesTo x U).card ∧
      (G.restrictEdges F).degree x < k := by
  have hfloor := Nat.floor_le ha
  have hcore' : ∀ v ∈ U, (G.restrictEdges F).degree v ≤ Nat.floor a := by
    intro v hv
    exact (G.restrictEdges_degree_mono hsub v).trans (Nat.le_floor (hcore v hv))
  have hka' : 2 * Nat.floor a < k := by
    have h : 2 * (Nat.floor a : ℝ) < k := by linarith
    exact_mod_cast h
  obtain ⟨hinside,houtside⟩ := G.first_fan_of_core_degree k (Nat.floor a) U F
    hregular hF hcore' hka'
  refine ⟨hinside,?_⟩
  intro x hx
  apply houtside x
  have h : 2 * (Nat.floor a : ℝ) < (G.edgesTo x U).card := by linarith
  exact_mod_cast h

omit [Fintype V] in
theorem internalEdges_iff_of_edge (e : E) (x v : V) (he : G.edge e = s(x,v))
    (U : Finset V) : e ∈ G.internalEdges U ↔ x ∈ U ∧ v ∈ U := by
  simp only [internalEdges, Finset.mem_filter, Finset.mem_univ, true_and, he,
    Sym2.toFinset_mk_eq, Finset.insert_subset_iff, Finset.singleton_subset_iff]

omit [Fintype V] in
/-- Simplicity of the distinguished core bounds its edge copies to a set
by the order of that set, even if the ambient graph has parallel edges. -/
theorem simple_core_edgesTo_card_le (H : Finset E) (hsimple : Set.InjOn G.edge H)
    (x : V) (Z : Finset V) : (H ∩ G.edgesTo x Z).card ≤ Z.card := by
  apply Finset.card_le_card_of_injOn (G.otherEnd x)
  · intro e he
    exact ((G.mem_edgesTo x Z e).mp (Finset.mem_inter.mp he).2).2
  · intro e he f hf hef
    obtain ⟨heH,heZ⟩ := Finset.mem_inter.mp he
    obtain ⟨hfH,hfZ⟩ := Finset.mem_inter.mp hf
    have hxe := ((G.mem_edgesTo x Z e).mp heZ).1
    have hxf := ((G.mem_edgesTo x Z f).mp hfZ).1
    apply hsimple heH hfH
    rw [G.edge_eq_otherEnd x e hxe, G.edge_eq_otherEnd x f hxf, hef]

omit [Fintype V] in
theorem selected_incidence_le_exterior_add (H L : Finset E)
    (hsimple : Set.InjOn G.edge H) (v : V) (Z : Finset V)
    (hcore : ∀ e ∈ L, e ∈ H → v ∈ G.edge e → G.otherEnd v e ∈ Z) :
    (L ∩ G.incidenceEdges v).card ≤ (G.restrictEdges Hᶜ).degree v + Z.card := by
  have hsub : L ∩ G.incidenceEdges v ⊆
      (Hᶜ ∩ G.incidenceEdges v) ∪ (H ∩ G.edgesTo v Z) := by
    intro e he
    obtain ⟨heL,hev⟩ := Finset.mem_inter.mp he
    by_cases heH : e ∈ H
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr
        ⟨heH,(G.mem_edgesTo v Z e).mpr
          ⟨(G.mem_incidenceEdges v e).mp hev,hcore e heL heH
            ((G.mem_incidenceEdges v e).mp hev)⟩⟩))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr
        ⟨Finset.mem_compl.mpr heH,hev⟩))
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [G.restrictEdges_degree]
  exact hc.trans (Nat.add_le_add_left (G.simple_core_edgesTo_card_le H hsimple v Z) _)

omit [Fintype V] in
/-- Degree control after moving the vertices of `Z` out of the core. -/
theorem moved_core_degree_le (H : Finset E) (U Z : Finset V)
    (hsupport : H ⊆ G.internalEdges U) (hsimple : Set.InjOn G.edge H)
    (v : V) (hv : v ∈ U \ Z) :
    (G.restrictEdges (H ∩ G.internalEdges (U \ Z))ᶜ).degree v ≤
      (G.restrictEdges Hᶜ).degree v + Z.card := by
  rw [G.restrictEdges_degree]
  apply G.selected_incidence_le_exterior_add H _ hsimple v Z
  intro e heL heH hev
  have heq := G.edge_eq_otherEnd v e hev
  have hotherU := ((G.internalEdges_iff_of_edge e v _ heq U).mp (hsupport heH)).2
  by_contra hn
  have heinner := (G.internalEdges_iff_of_edge e v _ heq (U \ Z)).mpr
    ⟨hv,Finset.mem_sdiff.mpr ⟨hotherU,hn⟩⟩
  exact (Finset.mem_compl.mp heL) (Finset.mem_inter.mpr ⟨heH,heinner⟩)

theorem core_outside_degree_le (H : Finset E) (U Z : Finset V)
    (hsupport : H ⊆ G.internalEdges U) (hsimple : Set.InjOn G.edge H) (v : V) :
    (G.edgesTo v (U \ Z)ᶜ).card ≤ (G.restrictEdges Hᶜ).degree v + Z.card := by
  have h := G.selected_incidence_le_exterior_add H (G.edgesTo v (U \ Z)ᶜ)
    hsimple v Z (by
      intro e heL heH hev
      have heq := G.edge_eq_otherEnd v e hev
      have hotherU := ((G.internalEdges_iff_of_edge e v _ heq U).mp (hsupport heH)).2
      have hnot := Finset.mem_compl.mp ((G.mem_edgesTo v (U \ Z)ᶜ e).mp heL).2
      by_contra hn
      exact hnot (Finset.mem_sdiff.mpr ⟨hotherU,hn⟩))
  have hsub : G.edgesTo v (U \ Z)ᶜ ⊆ G.incidenceEdges v := Finset.filter_subset _ _
  simpa only [Finset.inter_eq_left.mpr hsub] using h

/-- The bounded core move with a natural exterior degree bound. It only
requires maximum degree at most `k`, rather than regularity. -/
theorem bounded_core_move_nat (k a : ℕ) (U Z : Finset V) (H : Finset E)
    (hdegree : ∀ v, G.degree v ≤ k)
    (hsupport : H ⊆ G.internalEdges U) (hsimple : Set.InjOn G.edge H)
    (hcore : ∀ v ∈ U, (G.restrictEdges Hᶜ).degree v ≤ a)
    (hcolor : Nonempty ((G.restrictEdges Hᶜ).EdgeColoring k))
    (hka : 3 * (a + Z.card) < k) :
    Nonempty ((G.restrictEdges (H ∩ G.internalEdges (U \ Z))ᶜ).EdgeColoring k) ∧
    ∀ v ∈ U \ Z,
      (G.restrictEdges (H ∩ G.internalEdges (U \ Z))ᶜ).degree v ≤ a + Z.card := by
  let W := U \ Z
  let L := (H ∩ G.internalEdges W)ᶜ
  have hLdegree : ∀ v ∈ W, (G.restrictEdges L).degree v ≤ a + Z.card := by
    intro v hv
    exact (G.moved_core_degree_le H U Z hsupport hsimple v hv).trans
      (Nat.add_le_add_right (hcore v (Finset.mem_sdiff.mp hv).1) Z.card)
  refine ⟨?_,hLdegree⟩
  by_contra hnot
  obtain ⟨F,hFL,hF⟩ := G.exists_kMinimal_subset k hdegree L hnot
  have hFW : ∀ v ∈ W, (G.restrictEdges F).degree v ≤ a + Z.card := by
    intro v hv
    exact (G.restrictEdges_degree_mono hFL v).trans (hLdegree v hv)
  have hFU : ∀ v ∈ U, (G.restrictEdges F).degree v ≤ a + Z.card := by
    intro v hv
    have hout : ((G.restrictEdges F).edgesTo v Wᶜ).card ≤ a + Z.card :=
      (G.restrictEdges_edgesTo_card_le F v Wᶜ).trans
        ((G.core_outside_degree_le H U Z hsupport hsimple v).trans
          (Nat.add_le_add_right (hcore v hv) Z.card))
    have hnone : (G.restrictEdges F).edgesTo v W = ∅ := by
      apply hF.no_edgesTo_low_set v W (a + Z.card) hFW (by omega)
      intro w hw
      have hp := (G.restrictEdges F).parallelEdges_card_le_degree v w
      have hdw := hFW w hw
      omega
    have hsum := (G.restrictEdges F).edgesTo_compl_card_add v W
    rw [hnone,Finset.card_empty,Nat.add_zero] at hsum
    omega
  have hFH : F ⊆ Hᶜ := by
    intro e heF
    apply Finset.mem_compl.mpr
    intro heH
    obtain ⟨hx,hv⟩ := (G.mem_internalEdges U e).mp (hsupport heH)
    have hsum := hF.endpoint_degree_sum ⟨e,heF⟩ (G.firstEnd e) (G.secondEnd e)
      (G.edge_eq e).symm
    have hdx := hFU (G.firstEnd e) hx
    have hdv := hFU (G.secondEnd e) hv
    omega
  obtain ⟨c⟩ := hcolor
  exact hF.2.1 ⟨c.restrictEdgesSubset hFH⟩

/-- Lemma 2.8, with the manuscript's real bound and exact retained core.
The hypotheses distinguish the simple core from ambient parallel copies. -/
theorem bounded_core_move (k : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (U Z : Finset V) (H : Finset E)
    (hregular : ∀ v, G.degree v = k)
    (hsupport : H ⊆ G.internalEdges U) (hsimple : Set.InjOn G.edge H)
    (hcore : ∀ v ∈ U, ((G.restrictEdges Hᶜ).degree v : ℝ) ≤ a)
    (hcolor : Nonempty ((G.restrictEdges Hᶜ).EdgeColoring k))
    (hka : 3 * (a + Z.card) < k) :
    Nonempty ((G.restrictEdges (H ∩ G.internalEdges (U \ Z))ᶜ).EdgeColoring k) ∧
    ∀ v ∈ U \ Z,
      ((G.restrictEdges (H ∩ G.internalEdges (U \ Z))ᶜ).degree v : ℝ) ≤ a + Z.card := by
  have hfloor := Nat.floor_le ha
  have hka' : 3 * (Nat.floor a + Z.card) < k := by
    have h : (3 : ℝ) * (Nat.floor a + Z.card) < k := by linarith
    exact_mod_cast h
  obtain ⟨c,hdeg⟩ := G.bounded_core_move_nat k (Nat.floor a) U Z H
    (fun v => (hregular v).le) hsupport hsimple
    (fun v hv => Nat.le_floor (hcore v hv)) hcolor hka'
  refine ⟨c,?_⟩
  intro v hv
  have h := hdeg v hv
  have h' : ((G.restrictEdges (H ∩ G.internalEdges (U \ Z))ᶜ).degree v : ℝ) ≤
      Nat.floor a + Z.card := by exact_mod_cast h
  linarith

/-- Full Lemma 2.8, without a separate nonnegativity assumption on the
exterior degree bound.  If the core is nonempty, its degree bound implies
nonnegativity; if the core is empty, the supplied coloring already suffices. -/
theorem bounded_core_move_full (k : ℕ) (a : ℝ)
    (U Z : Finset V) (H : Finset E)
    (hregular : ∀ v, G.degree v = k)
    (hsupport : H ⊆ G.internalEdges U) (hsimple : Set.InjOn G.edge H)
    (hcore : ∀ v ∈ U, ((G.restrictEdges Hᶜ).degree v : ℝ) ≤ a)
    (hcolor : Nonempty ((G.restrictEdges Hᶜ).EdgeColoring k))
    (hka : 3 * (a + Z.card) < k) :
    Nonempty ((G.restrictEdges (H ∩ G.internalEdges (U \ Z))ᶜ).EdgeColoring k) ∧
    ∀ v ∈ U \ Z,
      ((G.restrictEdges (H ∩ G.internalEdges (U \ Z))ᶜ).degree v : ℝ) ≤ a + Z.card := by
  by_cases hU : U.Nonempty
  · obtain ⟨v, hv⟩ := hU
    have ha : 0 ≤ a := (Nat.cast_nonneg ((G.restrictEdges Hᶜ).degree v)).trans
      (hcore v hv)
    exact G.bounded_core_move k a ha U Z H hregular hsupport hsimple hcore hcolor hka
  · have hUempty : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
    have hHempty : H = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      have hv := ((G.mem_internalEdges U e).mp (hsupport he)).1
      exact Finset.notMem_empty _ (hUempty ▸ hv)
    refine ⟨?_, ?_⟩
    · obtain ⟨c⟩ := hcolor
      refine ⟨c.restrictEdgesSubset ?_⟩
      intro e _
      exact Finset.mem_compl.mpr (fun he => Finset.notMem_empty e (hHempty ▸ he))
    · intro v hv
      exact (Finset.notMem_empty v (hUempty ▸ (Finset.mem_sdiff.mp hv).1)).elim

end Overfull.Multigraph
