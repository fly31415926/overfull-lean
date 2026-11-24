import Overfull.TutteBerge.Graph
import Mathlib.Tactic

/-!
# Matching deletion and component parity

Perfect matchings in the complement of a prescribed matching lift to
perfect matchings containing it. Deleting the covered vertices of an
actual matching removes an even number of vertices from every original
connected component.
-/

namespace Overfull.PrescribedMatching

open Finset Classical SimpleGraph

variable {V : Type*}

/-- Restrict the actual edges and covered vertices to an induced graph. -/
def restrictTo (G : SimpleGraph V) (M : G.Subgraph) (S : Set V) :
    (G.induce S).Subgraph where
  verts := Subtype.val ⁻¹' M.verts
  Adj v w := M.Adj v.val w.val
  adj_sub := M.adj_sub
  edge_vert := M.edge_vert
  symm := fun _ _ h => M.symm h

theorem restrictTo_isMatching (G : SimpleGraph V) (M : G.Subgraph)
    (hM : M.IsMatching) (S : Set V)
    (hclosed : ∀ v ∈ S, ∀ w, M.Adj v w → w ∈ S) :
    (restrictTo G M S).IsMatching := by
  intro v hv
  obtain ⟨w, hvw, huniq⟩ := hM hv
  refine ⟨⟨w, hclosed v v.property w hvw⟩, hvw, ?_⟩
  intro z hz
  exact Subtype.ext (huniq z hz)

theorem restrictTo_isPerfectMatching (G : SimpleGraph V) (M : G.Subgraph)
    (hM : M.IsPerfectMatching) (S : Set V)
    (hclosed : ∀ v ∈ S, ∀ w, M.Adj v w → w ∈ S) :
    (restrictTo G M S).IsPerfectMatching := by
  exact ⟨restrictTo_isMatching G M hM.1 S hclosed, fun v => hM.2 v⟩

/-- Deleting a submatching from a perfect matching leaves a perfect
matching on the complementary vertex set. -/
theorem restrict_complement_of_submatching (G : SimpleGraph V)
    (K M : G.Subgraph) (hK : K.IsPerfectMatching) (hM : M.IsMatching)
    (hMK : M ≤ K) :
    (restrictTo G K M.vertsᶜ).IsPerfectMatching := by
  apply restrictTo_isPerfectMatching G K hK M.vertsᶜ
  intro v hv w hvw hw
  obtain ⟨z, hwz, _⟩ := hM hw
  have hvz : v = z := hK.1.eq_of_adj_left (K.symm hvw) (hMK.2 hwz)
  exact hv (hvz ▸ M.edge_vert (M.symm hwz))

/-- An actual perfect matching in the remaining induced graph can be
united with the prescribed matching. -/
theorem complete_from_induced_complement (G : SimpleGraph V) (M : G.Subgraph)
    (hM : M.IsMatching) (N : (G.induce M.vertsᶜ).Subgraph)
    (hN : N.IsPerfectMatching) :
    ∃ K : G.Subgraph, K.IsPerfectMatching ∧ M ≤ K := by
  let P := N.map (SimpleGraph.Hom.comap Subtype.val G)
  have hP : P.IsMatching := hN.1.map _ Subtype.val_injective
  have hPM : P.verts = M.vertsᶜ := by
    change Subtype.val '' N.verts = M.vertsᶜ
    rw [hN.2.verts_eq_univ]
    exact Subtype.coe_image_univ _
  have hdisj : Disjoint M.support P.support := by
    apply Disjoint.mono M.support_subset_verts P.support_subset_verts
    rw [hPM]
    exact disjoint_compl_right
  refine ⟨M ⊔ P, ⟨hM.sup hP hdisj, ?_⟩, le_sup_left⟩
  intro v
  by_cases hv : v ∈ M.verts
  · exact Or.inl hv
  · exact Or.inr (hPM.symm ▸ hv)

/-- When every component survives and induced deletion does not split
connectivity between surviving vertices, inclusion gives the actual
bijection of connected components. -/
noncomputable def survivingComponentEquiv (G : SimpleGraph V) (S : Set V)
    (hreflect : ∀ u v : S, G.Reachable u v → (G.induce S).Reachable u v)
    (hsurvive : ∀ v : V, ∃ w : S, G.Reachable v w) :
    (G.induce S).ConnectedComponent ≃ G.ConnectedComponent :=
  Equiv.ofBijective (fun C => C.map (SimpleGraph.Hom.comap Subtype.val G)) (by
    constructor
    · intro C D
      refine C.ind (fun u => ?_)
      refine D.ind (fun v => ?_)
      intro huv
      exact ConnectedComponent.sound (hreflect u v (ConnectedComponent.exact huv))
    · intro C
      obtain ⟨v, rfl⟩ := C.exists_rep
      obtain ⟨w, hvw⟩ := hsurvive v
      exact ⟨(G.induce S).connectedComponentMk w, ConnectedComponent.sound hvw.symm⟩)

theorem survivingComponentEquiv_support (G : SimpleGraph V) (S : Set V)
    (hreflect : ∀ u v : S, G.Reachable u v → (G.induce S).Reachable u v)
    (hsurvive : ∀ v : V, ∃ w : S, G.Reachable v w)
    (C : (G.induce S).ConnectedComponent) :
    Subtype.val '' C.supp = (survivingComponentEquiv G S hreflect hsurvive C).supp ∩ S := by
  refine C.ind (fun u => ?_)
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hr := (ConnectedComponent.exact hw).map (SimpleGraph.Hom.comap Subtype.val G)
    exact ⟨ConnectedComponent.sound hr, w.property⟩
  · rintro ⟨hv, hvS⟩
    refine ⟨⟨v, hvS⟩, ?_, rfl⟩
    exact ConnectedComponent.sound (hreflect ⟨v, hvS⟩ u (ConnectedComponent.exact hv))

/-- The two actual successive vertex restrictions commute. -/
def induceSwapIso (G : SimpleGraph V) (S T : Set V) :
    (G.induce S).induce (Subtype.val ⁻¹' T) ≃g
      (G.induce T).induce (Subtype.val ⁻¹' S) where
  toFun v := ⟨⟨v.val.val, v.property⟩, v.val.property⟩
  invFun v := ⟨⟨v.val.val, v.property⟩, v.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- The induced complement and the vertex-deletion convention used by
Tutte's theorem describe the same graph. -/
def inducedComplementIso (G : SimpleGraph V) (X : Set V) :
    G.induce Xᶜ ≃g ((⊤ : G.Subgraph).deleteVerts X).coe where
  toFun v := ⟨v.val, ⟨Set.mem_univ _, v.property⟩⟩
  invFun v := ⟨v.val, v.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by
    intro v w
    change (v.val ∈ (Set.univ \ X) ∧ w.val ∈ (Set.univ \ X) ∧ G.Adj v.val w.val) ↔ _
    constructor
    · intro h
      exact h.2.2
    · intro h
      exact ⟨⟨Set.mem_univ _, v.property⟩, ⟨Set.mem_univ _, w.property⟩, h⟩

/-- Forget the deletion of the first set while retaining avoidance of the second. -/
def unionComplementInclusion (D X : Set V) (v : ↥((D ∪ X)ᶜ)) : ↥(Xᶜ) :=
  ⟨v.val, fun h => v.property (Or.inr h)⟩

def inducedUnionComplementIso (G : SimpleGraph V) (D X : Set V) :
    (G.induce Xᶜ).induce (Subtype.val ⁻¹' D)ᶜ ≃g G.induce (D ∪ X)ᶜ where
  toFun v := ⟨v.val.val, by
    rintro (hD | hX)
    · exact v.property hD
    · exact v.val.property hX⟩
  invFun v := ⟨⟨v.val, fun h => v.property (Or.inr h)⟩,
    fun h => v.property (Or.inl h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- Flatten deletion of vertices of a remaining induced graph. -/
def remainingDeletionIso (G : SimpleGraph V) (D : Set V)
    (Y : Set ↥(Dᶜ : Set V)) :
    ((G.induce Dᶜ).induce Yᶜ) ≃g G.induce (D ∪ Subtype.val '' Y)ᶜ where
  toFun v := ⟨v.val.val, by
    rintro (hD | ⟨w, hw, heq⟩)
    · exact v.val.property hD
    · have h : w = v.val := Subtype.ext heq
      exact v.property (h ▸ hw)⟩
  invFun v := ⟨⟨v.val, fun h => v.property (Or.inl h)⟩, by
    intro hY
    exact v.property (Or.inr ⟨⟨v.val, fun h => v.property (Or.inl h)⟩, hY, rfl⟩)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

variable [Fintype V]

/-- Matching edges never leave an original connected component, so the
covered set meets that component in an even number of vertices. -/
theorem matching_component_inter_even (G : SimpleGraph V) (M : G.Subgraph)
    (hM : M.IsMatching) (C : G.ConnectedComponent) :
    Even (M.verts ∩ C.supp).ncard := by
  classical
  have hh := (hM.induce_connectedComponent C).even_card
  simpa only [← Set.ncard_eq_toFinset_card', SimpleGraph.Subgraph.induce_verts] using hh

theorem matching_component_difference_odd (G : SimpleGraph V) (M : G.Subgraph)
    (hM : M.IsMatching) (C : G.ConnectedComponent) :
    Odd (C.supp \ M.verts).ncard ↔ Odd C.supp.ncard := by
  have heven : Even (C.supp ∩ M.verts).ncard := by
    simpa only [Set.inter_comm] using matching_component_inter_even G M hM C
  have hcard := Set.ncard_inter_add_ncard_diff_eq_ncard C.supp M.verts
  rw [Nat.even_iff] at heven
  simp only [Nat.odd_iff]
  omega

/-- With connectivity retained, deleting an actual matching preserves the
number of odd components. The component equivalence and support sizes
are constructed from the two reachability hypotheses. -/
theorem oddComponents_after_matching_deletion (G : SimpleGraph V)
    (M : G.Subgraph) (hM : M.IsMatching)
    (hreflect : ∀ u v : ↥(M.vertsᶜ : Set V),
      G.Reachable u v → (G.induce M.vertsᶜ).Reachable u v)
    (hsurvive : ∀ v : V, ∃ w : ↥(M.vertsᶜ : Set V), G.Reachable v w) :
    (G.induce M.vertsᶜ).oddComponents.ncard = G.oddComponents.ncard := by
  let e := survivingComponentEquiv G M.vertsᶜ hreflect hsurvive
  have hcard (C : (G.induce M.vertsᶜ).ConnectedComponent) :
      C.supp.ncard = ((e C).supp \ M.verts).ncard := by
    have himage := survivingComponentEquiv_support G M.vertsᶜ hreflect hsurvive C
    have hh := Set.ncard_image_of_injective C.supp Subtype.val_injective
    rw [himage] at hh
    exact hh.symm
  let f : (G.induce M.vertsᶜ).oddComponents ≃ G.oddComponents :=
    Equiv.subtypeEquiv e (fun C => by
      change Odd C.supp.ncard ↔ Odd (e C).supp.ncard
      rw [hcard C]
      exact matching_component_difference_odd G M hM (e C))
  simpa only [Nat.card_coe_set_eq] using Nat.card_congr f

/-- Apply matching-deletion parity after deleting an ambient vertex set
disjoint from the matching. -/
theorem oddComponents_after_disjoint_deletion (G : SimpleGraph V)
    (M : G.Subgraph) (hM : M.IsMatching) (X : Set V) (hMX : Disjoint M.verts X)
    (hreflect : ∀ u v : ↥((restrictTo G M Xᶜ).vertsᶜ),
      (G.induce Xᶜ).Reachable u v →
        ((G.induce Xᶜ).induce (restrictTo G M Xᶜ).vertsᶜ).Reachable u v)
    (hsurvive : ∀ v : ↥(Xᶜ : Set V),
      ∃ w : ↥((restrictTo G M Xᶜ).vertsᶜ), (G.induce Xᶜ).Reachable v w) :
    ((G.induce M.vertsᶜ).induce (Subtype.val ⁻¹' X)ᶜ).oddComponents.ncard =
      (G.induce Xᶜ).oddComponents.ncard := by
  have hMr : (restrictTo G M Xᶜ).IsMatching :=
    restrictTo_isMatching G M hM Xᶜ (by
      intro v _ w hvw hwX
      exact Set.disjoint_left.mp hMX (M.edge_vert (M.symm hvw)) hwX)
  calc
    _ = ((G.induce Xᶜ).induce (restrictTo G M Xᶜ).vertsᶜ).oddComponents.ncard :=
      TutteBerge.oddComponents_ncard_iso (induceSwapIso G M.vertsᶜ Xᶜ)
    _ = _ := oddComponents_after_matching_deletion (G.induce Xᶜ)
      (restrictTo G M Xᶜ) hMr hreflect hsurvive

/-- Tutte's theorem with odd components expressed using actual induced
complements, rather than the subgraph vertex-deletion convention. -/
theorem perfectMatching_of_induced_odd_bounds (G : SimpleGraph V)
    (hbound : ∀ X : Set V, (G.induce Xᶜ).oddComponents.ncard ≤ X.ncard) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  apply SimpleGraph.tutte.mpr
  intro X
  apply not_lt_of_ge
  change ((⊤ : G.Subgraph).deleteVerts X).coe.oddComponents.ncard ≤ X.ncard
  rw [← TutteBerge.oddComponents_ncard_iso (inducedComplementIso G X)]
  exact hbound X

/-- The exact Tutte bounds for the actual remaining graph complete the
prescribed matching in the ambient graph. -/
theorem complete_of_induced_odd_bounds (G : SimpleGraph V)
    (M : G.Subgraph) (hM : M.IsMatching)
    (hbound : ∀ Y : Set ↥(M.vertsᶜ : Set V),
      ((G.induce M.vertsᶜ).induce Yᶜ).oddComponents.ncard ≤ Y.ncard) :
    ∃ K : G.Subgraph, K.IsPerfectMatching ∧ M ≤ K := by
  classical
  obtain ⟨N, hN⟩ := perfectMatching_of_induced_odd_bounds (G.induce M.vertsᶜ) hbound
  exact complete_from_induced_complement G M hM N hN

/-- A flat complement-of-union interface to the matching-parity transfer. -/
theorem oddComponents_after_disjoint_deletion_flat (G : SimpleGraph V)
    (M : G.Subgraph) (hM : M.IsMatching) (X : Set V) (hMX : Disjoint M.verts X)
    (hreflect : ∀ u v : ↥((M.verts ∪ X)ᶜ),
      (G.induce Xᶜ).Reachable (unionComplementInclusion M.verts X u)
        (unionComplementInclusion M.verts X v) →
          (G.induce (M.verts ∪ X)ᶜ).Reachable u v)
    (hsurvive : ∀ C : (G.induce Xᶜ).ConnectedComponent,
      ∃ v ∈ C.supp, v.val ∉ M.verts) :
    ((G.induce M.vertsᶜ).induce (Subtype.val ⁻¹' X)ᶜ).oddComponents.ncard =
      (G.induce Xᶜ).oddComponents.ncard := by
  apply oddComponents_after_disjoint_deletion G M hM X hMX
  · intro u v huv
    let e := inducedUnionComplementIso G M.verts X
    exact (hreflect (e u) (e v) huv).map e.symm.toHom
  · intro v
    obtain ⟨w, hw, hwM⟩ := hsurvive ((G.induce Xᶜ).connectedComponentMk v)
    exact ⟨⟨w, hwM⟩, ConnectedComponent.exact hw.symm⟩

/-- Delete a set of vertices of the actual remaining graph. Its ambient
image is automatically disjoint from the prescribed matching. -/
theorem oddComponents_after_remaining_deletion (G : SimpleGraph V)
    (M : G.Subgraph) (hM : M.IsMatching) (Y : Set ↥(M.vertsᶜ : Set V))
    (hreflect : let X : Set V := Subtype.val '' Y
      ∀ u v : ↥((M.verts ∪ X)ᶜ),
        (G.induce Xᶜ).Reachable (unionComplementInclusion M.verts X u)
          (unionComplementInclusion M.verts X v) →
            (G.induce (M.verts ∪ X)ᶜ).Reachable u v)
    (hsurvive : let X : Set V := Subtype.val '' Y
      ∀ C : (G.induce Xᶜ).ConnectedComponent, ∃ v ∈ C.supp, v.val ∉ M.verts) :
    ((G.induce M.vertsᶜ).induce Yᶜ).oddComponents.ncard =
      (G.induce (Subtype.val '' Y)ᶜ).oddComponents.ncard := by
  have hMX : Disjoint M.verts (Subtype.val '' Y) := by
    apply Set.disjoint_left.mpr
    rintro v hv ⟨w, _, rfl⟩
    exact w.property hv
  have hpre : (Subtype.val ⁻¹' (Subtype.val '' Y) : Set ↥(M.vertsᶜ : Set V)) = Y :=
    Set.preimage_image_eq _ Subtype.val_injective
  have hh := oddComponents_after_disjoint_deletion_flat G M hM
    (Subtype.val '' Y) hMX hreflect hsurvive
  rw [hpre] at hh
  exact hh

theorem induced_odd_bound_of_perfectMatching (G : SimpleGraph V)
    (K : G.Subgraph) (hK : K.IsPerfectMatching) (X : Set V) :
    (G.induce Xᶜ).oddComponents.ncard ≤ X.ncard := by
  have hh := SimpleGraph.tutte.mp ⟨K, hK⟩ X
  change ¬ X.ncard < ((⊤ : G.Subgraph).deleteVerts X).coe.oddComponents.ncard at hh
  rw [TutteBerge.oddComponents_ncard_iso (inducedComplementIso G X)]
  exact not_lt.mp hh

/-- The small-deletion Tutte inequality after removing a prescribed
matching follows from the original perfect matching and the retained
component connectivity. -/
theorem remaining_odd_bound (G : SimpleGraph V) (K : G.Subgraph)
    (hK : K.IsPerfectMatching) (M : G.Subgraph) (hM : M.IsMatching)
    (Y : Set ↥(M.vertsᶜ : Set V))
    (hreflect : let X : Set V := Subtype.val '' Y
      ∀ u v : ↥((M.verts ∪ X)ᶜ),
        (G.induce Xᶜ).Reachable (unionComplementInclusion M.verts X u)
          (unionComplementInclusion M.verts X v) →
            (G.induce (M.verts ∪ X)ᶜ).Reachable u v)
    (hsurvive : let X : Set V := Subtype.val '' Y
      ∀ C : (G.induce Xᶜ).ConnectedComponent, ∃ v ∈ C.supp, v.val ∉ M.verts) :
    ((G.induce M.vertsᶜ).induce Yᶜ).oddComponents.ncard ≤ Y.ncard := by
  rw [oddComponents_after_remaining_deletion G M hM Y hreflect hsurvive]
  calc
    _ ≤ (Subtype.val '' Y).ncard := induced_odd_bound_of_perfectMatching G K hK _
    _ = _ := Set.ncard_image_of_injective Y Subtype.val_injective

omit [Fintype V] in
theorem remainingDeletion_oddComponents (G : SimpleGraph V) (D : Set V)
    (Y : Set ↥(Dᶜ : Set V)) :
    ((G.induce Dᶜ).induce Yᶜ).oddComponents.ncard =
      (G.induce (D ∪ Subtype.val '' Y)ᶜ).oddComponents.ncard :=
  TutteBerge.oddComponents_ncard_iso (remainingDeletionIso G D Y)

end Overfull.PrescribedMatching
