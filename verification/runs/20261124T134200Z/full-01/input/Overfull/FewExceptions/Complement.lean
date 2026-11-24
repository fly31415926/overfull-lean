import Overfull.MultigraphFanApplications
import Overfull.OneCore.Complement

/-!
# Coloring the complement of a core with at most three exterior vertices

All edge sets retain the original parallel copies. In a minimal
noncolorable restriction, the first fan removes every core incidence at
an exterior vertex having more than twice the core error in core edges.
No-overfullness bounds the entire exterior graph by the palette size.
If an exterior vertex has few core incidences, its exterior star accounts
for almost all those edges; deleting that vertex leaves a sparse graph.
The proved sparse-deletion coloring criterion then gives a contradiction.
-/

noncomputable section

namespace Overfull.FewExceptions

open Finset Classical

variable {V E : Type*} [Fintype V] [Fintype E] (G : Multigraph V E)

def internalAway (X : Finset V) (y : V) : Finset E :=
  (G.internalEdges X).filter (fun e => y ∉ G.edge e)

omit [Fintype V] in
theorem internalAway_eq (X : Finset V) (y : V) :
    internalAway G X y = G.internalEdges X \ G.incidenceEdges y := by
  ext e
  simp only [internalAway, Finset.mem_filter, Finset.mem_sdiff, G.mem_incidenceEdges]

omit [Fintype V] in
theorem degreeAway_le_degree (y x : V) : G.degreeAway y x ≤ G.degree x := by
  exact Finset.card_le_card Finset.sdiff_subset

omit [Fintype V] in
/-- Restricting actual copies cannot increase an induced edge count. -/
theorem restriction_internal_card_le (F : Finset E) (X : Finset V) :
    ((G.restrictEdges F).internalEdges X).card ≤ (G.internalEdges X).card := by
  apply Finset.card_le_card_of_injOn (fun e : F => e.val)
  · intro e he
    exact (G.mem_internalEdges X e.val).mpr
      (((G.restrictEdges F).mem_internalEdges X e).mp he)
  · intro e _ f _ h
    exact Subtype.ext h

omit [Fintype V] in
/-- The same comparison preserves deletion of a specified vertex. -/
theorem restriction_internal_away_card_le (F : Finset E) (X : Finset V) (y : V) :
    (internalAway (G.restrictEdges F) X y).card ≤ (internalAway G X y).card := by
  apply Finset.card_le_card_of_injOn (fun e : F => e.val)
  · intro e he
    obtain ⟨heX, hey⟩ := Finset.mem_filter.mp he
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact (G.mem_internalEdges X e.val).mpr
        (((G.restrictEdges F).mem_internalEdges X e).mp heX)
    · exact hey
  · intro e _ f _ h
    exact Subtype.ext h

omit [Fintype V] in
/-- The internal edges incident with an internal vertex are its edges to
that vertex set. -/
theorem internal_incidence_eq_edgesTo (X : Finset V) (y : V) (hy : y ∈ X) :
    G.internalEdges X ∩ G.incidenceEdges y = G.edgesTo y X := by
  ext e
  simp only [Finset.mem_inter, G.mem_incidenceEdges, G.mem_edgesTo]
  constructor
  · rintro ⟨heX, hye⟩
    exact ⟨hye, ((G.internalEdges_iff_of_edge e y _
      (G.edge_eq_otherEnd y e hye) X).mp heX).2⟩
  · rintro ⟨hye, hoX⟩
    exact ⟨(G.internalEdges_iff_of_edge e y _
      (G.edge_eq_otherEnd y e hye) X).mpr ⟨hy, hoX⟩, hye⟩

/-- At an exterior vertex, every edge avoiding `y` is either an exterior
edge avoiding `y` or an edge to the core. -/
theorem degreeAway_le_internal_away_add (U : Finset V) (y x : V) (hx : x ∉ U) :
    G.degreeAway y x ≤ (internalAway G Uᶜ y).card +
      (G.edgesTo x U).card := by
  have hsub : G.incidenceEdges x \ G.incidenceEdges y ⊆
      internalAway G Uᶜ y ∪ G.edgesTo x U := by
    intro e he
    obtain ⟨hxe, hye⟩ := Finset.mem_sdiff.mp he
    have hxe' := (G.mem_incidenceEdges x e).mp hxe
    by_cases ho : G.otherEnd x e ∈ U
    · exact Finset.mem_union.mpr (Or.inr ((G.mem_edgesTo x U e).mpr ⟨hxe', ho⟩))
    · apply Finset.mem_union.mpr
      apply Or.inl
      refine Finset.mem_filter.mpr ⟨?_, fun h => hye ((G.mem_incidenceEdges y e).mpr h)⟩
      exact (G.internalEdges_iff_of_edge e x _ (G.edge_eq_otherEnd x e hxe') Uᶜ).mpr
        ⟨Finset.mem_compl.mpr hx, Finset.mem_compl.mpr ho⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- If neither internal core edges nor exterior-to-core edges remain,
every surviving edge is internal to the exterior. -/
theorem internal_compl_eq_univ (U : Finset V)
    (hinside : G.internalEdges U = ∅)
    (houtside : ∀ x, x ∉ U → G.edgesTo x U = ∅) :
    G.internalEdges Uᶜ = univ := by
  have hforbid (e : E) (x v : V) (he : G.edge e = s(x,v)) (hx : x ∈ U) : False := by
    by_cases hv : v ∈ U
    · have hm := (G.internalEdges_iff_of_edge e x v he U).mpr ⟨hx,hv⟩
      rw [hinside] at hm
      exact Finset.notMem_empty _ hm
    · have hm : e ∈ G.edgesTo v U := by
        apply (G.mem_edgesTo v U e).mpr
        refine ⟨by simp [he], ?_⟩
        rw [G.otherEnd_eq_of_edge e v x (he.trans Sym2.eq_swap)]
        exact hx
      rw [houtside v hv] at hm
      exact Finset.notMem_empty _ hm
  apply Finset.eq_univ_of_forall
  intro e
  apply (G.mem_internalEdges Uᶜ e).mpr
  refine ⟨Finset.mem_compl.mpr ?_, Finset.mem_compl.mpr ?_⟩
  · exact fun hx => hforbid e _ _ (G.edge_eq e).symm hx
  · exact fun hx => hforbid e _ _ ((G.edge_eq e).symm.trans Sym2.eq_swap) hx

/-- A regular non-overfull host whose exterior contains at most `k` edges
has a colorable core complement when `k` exceeds 24 times the actual
complementary core degree. The exterior order may be arbitrary. -/
theorem complement_colorable_of_exterior_edge_bound
    (U : Finset V) (H : Finset E) (k a : ℕ)
    (hregular : ∀ v, G.degree v = k)
    (hsafe : ∀ X : Finset V, ¬ G.IsOverfull k X)
    (hint : (G.internalEdges Uᶜ).card ≤ k)
    (hcore : ∀ v ∈ U, (G.restrictEdges Hᶜ).degree v ≤ a)
    (hka : 24 * a < k) : Nonempty ((G.restrictEdges Hᶜ).EdgeColoring k) := by
  classical
  by_contra hn
  obtain ⟨F, hFsub, hF⟩ := G.exists_kMinimal_subset k
    (fun v => (hregular v).le) Hᶜ hn
  have hlow : ∀ v ∈ U, (G.restrictEdges F).degree v ≤ a := by
    intro v hv
    exact (G.restrictEdges_degree_mono hFsub v).trans (hcore v hv)
  obtain ⟨hinside, hfan⟩ := G.first_fan_of_core_degree k a U F hregular hF hlow
    (by omega)
  have hspokes (x : V) : ((G.restrictEdges F).edgesTo x U).card ≤ 2 * a := by
    by_cases hx : (G.edgesTo x U).card ≤ 2 * a
    · exact (G.restrictEdges_edgesTo_card_le F x U).trans hx
    · rw [(hfan x (by omega)).1]
      simp
  by_cases hsmall : ∃ y, y ∉ U ∧ (G.edgesTo y U).card ≤ 2 * a
  · obtain ⟨y, hy, hysmall⟩ := hsmall
    have haway : (internalAway G Uᶜ y).card ≤ 2 * a := by
      have hsplit := Finset.card_sdiff_add_card_inter
        (G.internalEdges Uᶜ) (G.incidenceEdges y)
      rw [← internalAway_eq] at hsplit
      rw [internal_incidence_eq_edgesTo G Uᶜ y (Finset.mem_compl.mpr hy)] at hsplit
      have hdegree := G.edgesTo_compl_card_add y U
      rw [hregular] at hdegree
      omega
    have hdelete : ∀ v, (G.restrictEdges F).degreeAway y v ≤ 4 * a := by
      intro v
      by_cases hv : v ∈ U
      · have hbound : (G.restrictEdges F).degreeAway y v ≤
            (G.restrictEdges F).degree v := degreeAway_le_degree (G.restrictEdges F) y v
        exact hbound.trans ((hlow v hv).trans (by omega))
      · have hb := degreeAway_le_internal_away_add (G.restrictEdges F) U y v hv
        have hi := (restriction_internal_away_card_le G F Uᶜ y).trans haway
        have hs := hspokes v
        omega
    have htri : ∀ X : Finset V, X.card = 3 → y ∈ X →
        ((G.restrictEdges F).internalEdges X).card ≤ k := by
      intro X hX _
      have hh : (G.internalEdges X).card ≤ k * (X.card / 2) :=
        Nat.le_of_not_gt (hsafe X)
      rw [hX] at hh
      norm_num at hh
      exact (restriction_internal_card_le G F X).trans hh
    exact hF.2.1 ((G.restrictEdges F).edgeColoring_sparse_vertex_deletion y k (4 * a)
      hF.1 hdelete htri (by omega))
  · have hout : ∀ x, x ∉ U → (G.restrictEdges F).edgesTo x U = ∅ := by
      intro x hx
      exact (hfan x (by
        have hh : ¬ (G.edgesTo x U).card ≤ 2 * a := fun h => hsmall ⟨x,hx,h⟩
        omega)).1
    have hall := internal_compl_eq_univ (G.restrictEdges F) U hinside hout
    have hcard : Fintype.card F ≤ k := by
      have hb := (restriction_internal_card_le G F Uᶜ).trans hint
      rwa [hall, Finset.card_univ] at hb
    obtain ⟨f⟩ : Nonempty (F ↪ Fin k) := Function.Embedding.nonempty_of_card_le
      (by simpa using hcard)
    apply hF.2.1
    refine ⟨⟨f, ?_⟩⟩
    intro e e' v he _ _
    exact f.injective he

/-- A regular non-overfull host with at most three exterior vertices has
a colorable core complement as soon as the palette exceeds 24 times the
actual complementary degree at a core vertex. No structure is assumed
on the deleted edge set beyond this degree condition. -/
theorem complement_colorable (U : Finset V) (H : Finset E) (k a : ℕ)
    (hregular : ∀ v, G.degree v = k)
    (hsafe : ∀ X : Finset V, ¬ G.IsOverfull k X)
    (houtside : Uᶜ.card ≤ 3)
    (hcore : ∀ v ∈ U, (G.restrictEdges Hᶜ).degree v ≤ a)
    (hka : 24 * a < k) : Nonempty ((G.restrictEdges Hᶜ).EdgeColoring k) := by
  apply complement_colorable_of_exterior_edge_bound G U H k a hregular hsafe ?_ hcore hka
  have hbound : (G.internalEdges Uᶜ).card ≤ k * (Uᶜ.card / 2) :=
    Nat.le_of_not_gt (hsafe Uᶜ)
  have hdiv : Uᶜ.card / 2 ≤ 1 := by omega
  exact hbound.trans ((Nat.mul_le_mul_left k hdiv).trans_eq (Nat.mul_one k))

/-- Real-error version of the actual-copy complementary coloring theorem. -/
theorem complement_colorable_real (U : Finset V) (H : Finset E) (k : ℕ) (a : ℝ)
    (hregular : ∀ v, G.degree v = k)
    (hsafe : ∀ X : Finset V, ¬ G.IsOverfull k X)
    (houtside : Uᶜ.card ≤ 3) (ha : 0 ≤ a)
    (hcore : ∀ v ∈ U, ((G.restrictEdges Hᶜ).degree v : ℝ) ≤ a)
    (hka : 24 * a < k) : Nonempty ((G.restrictEdges Hᶜ).EdgeColoring k) := by
  apply complement_colorable G U H k ⌊a⌋₊ hregular hsafe houtside
    (fun v hv => Nat.le_floor (hcore v hv))
  have hfloor := Nat.floor_le ha
  have hh : (24 : ℝ) * ⌊a⌋₊ < k := by linarith
  exact_mod_cast hh

/-- Embedded-core formulation: the complementary degree bound follows
from the actual regular host and the simple core degrees. -/
theorem core_complement_colorable (U : Finset V) (C : SmallCuts.Core G U)
    (k : ℕ) (a : ℝ) (hregular : ∀ v, G.degree v = k)
    (hsafe : ∀ X : Finset V, ¬ G.IsOverfull k X)
    (houtside : Uᶜ.card ≤ 3) (ha : 0 ≤ a)
    (hdegree : ∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ))
    (hka : 24 * a < k) :
    Nonempty ((G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k) := by
  apply complement_colorable_real G U (OneCore.coreEdges C) k a
    hregular hsafe houtside ha
  · intro v hv
    exact OneCore.complement_degree_le_error C k a hregular hdegree ⟨v,hv⟩
  · exact hka

end Overfull.FewExceptions
