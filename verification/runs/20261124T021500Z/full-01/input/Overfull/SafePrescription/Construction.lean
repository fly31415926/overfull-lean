import Overfull.PrescribedMatching
import Overfull.Compression.Matching
import Overfull.TutteBerge.Matching

namespace Overfull.SafePrescription

open Finset Classical SimpleGraph
open PrescribedMatching Compression

variable {V W I C : Type*}

/-- Change only the ambient host, preserving every actual vertex and edge. -/
def rehost (G H : SimpleGraph V) (M : G.Subgraph)
    (h : ∀ u v, M.Adj u v → H.Adj u v) : H.Subgraph where
  verts := M.verts
  Adj := M.Adj
  adj_sub := h _ _
  edge_vert := M.edge_vert
  symm := M.symm

theorem rehost_isMatching (G H : SimpleGraph V) (M : G.Subgraph)
    (h : ∀ u v, M.Adj u v → H.Adj u v) (hM : M.IsMatching) :
    (rehost G H M h).IsMatching := hM

theorem rehost_isPerfectMatching (G H : SimpleGraph V) (M : G.Subgraph)
    (h : ∀ u v, M.Adj u v → H.Adj u v) (hM : M.IsPerfectMatching) :
    (rehost G H M h).IsPerfectMatching := hM

/-- Embed a matching from a surviving vertex set after verifying that
its retained edges are edges of the original graph. -/
def embed (G : SimpleGraph V) (S : Set V) (H : SimpleGraph S) (M : H.Subgraph)
    (h : ∀ u v, M.Adj u v → G.Adj u.val v.val) : G.Subgraph :=
  (rehost H (G.induce S) M h).map (Hom.comap Subtype.val G)

theorem embed_isMatching (G : SimpleGraph V) (S : Set V) (H : SimpleGraph S)
    (M : H.Subgraph) (h : ∀ u v, M.Adj u v → G.Adj u.val v.val)
    (hM : M.IsMatching) : (embed G S H M h).IsMatching :=
  hM.map _ Subtype.val_injective

theorem embed_verts (G : SimpleGraph V) (S : Set V) (H : SimpleGraph S)
    (M : H.Subgraph) (h : ∀ u v, M.Adj u v → G.Adj u.val v.val) :
    (embed G S H M h).verts = Subtype.val '' M.verts := rfl

theorem embed_verts_subset (G : SimpleGraph V) (S : Set V) (H : SimpleGraph S)
    (M : H.Subgraph) (h : ∀ u v, M.Adj u v → G.Adj u.val v.val) :
    (embed G S H M h).verts ⊆ S := by
  rintro v ⟨w, _, rfl⟩
  exact w.property

theorem embed_adj (G : SimpleGraph V) (S : Set V) (H : SimpleGraph S)
    (M : H.Subgraph) (h : ∀ u v, M.Adj u v → G.Adj u.val v.val) (u v : S) :
    (embed G S H M h).Adj u.val v.val ↔ M.Adj u v := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    cases Subtype.ext ha
    cases Subtype.ext hb
    exact hab
  · intro huv
    exact ⟨u, v, huv, rfl, rfl⟩

theorem embed_edgeSet (G : SimpleGraph V) (S : Set V) (H : SimpleGraph S)
    (M : H.Subgraph) (h : ∀ u v, M.Adj u v → G.Adj u.val v.val) :
    (embed G S H M h).edgeSet = Sym2.map Subtype.val '' M.edgeSet := by
  rw [embed, Subgraph.edgeSet_map]
  rfl

theorem embed_edgeSet_card (G : SimpleGraph V) (S : Set V) (H : SimpleGraph S)
    (M : H.Subgraph) (h : ∀ u v, M.Adj u v → G.Adj u.val v.val) :
    (embed G S H M h).edgeSet.ncard = M.edgeSet.ncard := by
  rw [embed_edgeSet, Set.ncard_image_of_injective _
    (Sym2.map.injective Subtype.val_injective)]

/-- Keep the original same-cluster edges and add only internal core edges. -/
def cliqueAux (G : SimpleGraph V) (U : I → Finset V) (c : V → C) (S : Set V) :
    SimpleGraph S where
  Adj u v := (G.Adj u.val v.val ∧ c u.val = c v.val) ∨
    (u ≠ v ∧ ∃ i, u.val ∈ U i ∧ v.val ∈ U i)
  symm := by
    intro u v huv
    rcases huv with ⟨huv, hc⟩ | ⟨hne, i, hu, hv⟩
    · exact Or.inl ⟨huv.symm, hc.symm⟩
    · exact Or.inr ⟨hne.symm, i, hv, hu⟩
  loopless := by
    intro v hv
    rcases hv with ⟨hv, _⟩ | ⟨hv, _⟩
    · exact G.loopless v hv
    · exact hv rfl

theorem embed_restrict_eq (G : SimpleGraph V) (M : G.Subgraph) (S : Set V)
    (hverts : M.verts ⊆ S) :
    embed G S (G.induce S) (restrictTo G M S) (fun _ _ h => M.adj_sub h) = M := by
  apply Subgraph.ext
  · ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hv
      exact ⟨⟨v, hverts hv⟩, hv, rfl⟩
  · funext u v
    apply propext
    constructor
    · rintro ⟨a, b, hab, rfl, rfl⟩
      exact hab
    · intro huv
      exact ⟨⟨u, hverts (M.edge_vert huv)⟩, ⟨v, hverts (M.edge_vert (M.symm huv))⟩,
        huv, rfl, rfl⟩

variable [Fintype V]

/-- The surviving portion of a finite vertex set. -/
noncomputable def surviving (S : Set V) (A : Finset V) : Finset S :=
  (Subtype.val ⁻¹' (A : Set V)).toFinset

@[simp] theorem mem_surviving (S : Set V) (A : Finset V) (v : S) :
    v ∈ surviving S A ↔ v.val ∈ A := by
  simp [surviving]

theorem surviving_card (S : Set V) (A : Finset V) :
    (surviving S A).card = ((A : Set V) ∩ S).ncard := by
  unfold surviving
  rw [← Set.ncard_eq_toFinset_card']
  exact Set.ncard_subtype (fun v => v ∈ S) (A : Set V)

theorem surviving_card_le (S : Set V) (A : Finset V) :
    (surviving S A).card ≤ A.card := by
  rw [surviving_card, ← Set.ncard_coe_finset A]
  exact Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _)

theorem cliqueAux_isClique (G : SimpleGraph V) (U : I → Finset V)
    (c : V → C) (S : Set V) (i : I) :
    (cliqueAux G U c S).IsClique (surviving S (U i) : Set S) := by
  intro u hu v hv hne
  exact Or.inr ⟨hne, i, (mem_surviving S (U i) u).mp hu,
    (mem_surviving S (U i) v).mp hv⟩

omit [Fintype V] in
theorem cliqueAux_cluster (G : SimpleGraph V) (U : I → Finset V)
    (c : V → C) (S : Set V)
    (hcore : ∀ i u v, u ∈ U i → v ∈ U i → c u = c v)
    {u v : S} (h : (cliqueAux G U c S).Adj u v) : c u.val = c v.val := by
  rcases h with h | ⟨_, i, hu, hv⟩
  · exact h.2
  · exact hcore i u v hu hv

theorem cliqueAux_original_edge (G : SimpleGraph V) (U : I → Finset V)
    (c : V → C) (S : Set V) (M : (cliqueAux G U c S).Subgraph)
    (hno : ∀ i u v, u ∈ surviving S (U i) → v ∈ surviving S (U i) → ¬ M.Adj u v)
    {u v : S} (h : M.Adj u v) : G.Adj u.val v.val := by
  rcases M.adj_sub h with ha | ⟨_, i, hu, hv⟩
  · exact ha.1
  · exact (hno i u v ((mem_surviving _ _ _).mpr hu)
      ((mem_surviving _ _ _).mpr hv) h).elim

/-- Original neighbors in the cores of the same cluster. -/
def clusterCoreNeighbors (G : SimpleGraph V) (Z : Finset V) (c : V → C) (v : V) : Set V :=
  {w | G.Adj v w ∧ w ∉ Z ∧ c v = c w}

omit [Fintype V] in
theorem marked_subset_boundary (G : SimpleGraph V) (Z₀ : Finset V) (c : V → C)
    (K B : G.Subgraph) (hK : K.IsPerfectMatching)
    (hboundary : ∀ u v, B.Adj u v ↔ K.Adj u v ∧
      (u ∈ Z₀ ∨ v ∈ Z₀ ∨ c u ≠ c v)) : (Z₀ : Set V) ⊆ B.verts := by
  intro v hv
  obtain ⟨w, hvw, _⟩ := hK.1 (hK.2 v)
  exact B.edge_vert ((hboundary v w).mpr ⟨hvw, Or.inl hv⟩)

omit [Fintype V] in
/-- After fixing the boundary matching, the sampled matching is still
perfect in the clique-completed graph without intercluster edges. -/
theorem cliqueAux_has_perfect_matching (G : SimpleGraph V) (U : I → Finset V)
    (Z₀ : Finset V) (c : V → C) (K B : G.Subgraph)
    (hK : K.IsPerfectMatching) (hB : B.IsMatching) (hBK : B ≤ K)
    (hboundary : ∀ u v, B.Adj u v ↔ K.Adj u v ∧
      (u ∈ Z₀ ∨ v ∈ Z₀ ∨ c u ≠ c v)) :
    ∃ L : (cliqueAux G U c B.vertsᶜ).Subgraph, L.IsPerfectMatching := by
  let R := restrictTo G K B.vertsᶜ
  have hR : R.IsPerfectMatching := restrict_complement_of_submatching G K B hK hB hBK
  have hactual : ∀ u v, R.Adj u v → (cliqueAux G U c B.vertsᶜ).Adj u v := by
    intro u v huv
    refine Or.inl ⟨K.adj_sub huv, ?_⟩
    by_contra hne
    have hb := (hboundary u v).mpr ⟨huv, Or.inr (Or.inr hne)⟩
    exact u.property (B.edge_vert hb)
  exact ⟨rehost _ _ R hactual, rehost_isPerfectMatching _ _ R hactual hR⟩

theorem surviving_disjoint (S : Set V) (A B : Finset V) (h : Disjoint A B) :
    Disjoint (surviving S A) (surviving S B) := by
  apply Finset.disjoint_left.mpr
  intro v ha hb
  exact Finset.disjoint_left.mp h ((mem_surviving _ _ _).mp ha) ((mem_surviving _ _ _).mp hb)

theorem surviving_cover (U : I → Finset V) (Z : Finset V) (S : Set V)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) :
    ∀ v : S, v ∈ surviving S Z ∨ ∃ i, v ∈ surviving S (U i) := by
  intro v
  simpa only [mem_surviving] using hcover v.val

theorem surviving_core_large (U : I → Finset V) (Z : Finset V) (D : Set V)
    (q : ℕ) (hD : D.ncard ≤ 2*q)
    (horder : ∀ i, 2*Z.card+4+2*q < (U i).card) (i : I) :
    2*(surviving Dᶜ Z).card+4 < (surviving Dᶜ (U i)).card := by
  have hZ := surviving_card_le Dᶜ Z
  have hdelete := Set.ncard_le_ncard_diff_add_ncard (U i : Set V) D
  have hcore := surviving_card Dᶜ (U i)
  have hdiff : ((U i : Set V) ∩ Dᶜ) = (U i : Set V) \ D := rfl
  rw [hdiff] at hcore
  rw [Set.ncard_coe_finset] at hdelete
  have hi := horder i
  omega

theorem cliqueAux_neighbors_large (G : SimpleGraph V) (U : I → Finset V)
    (Z Z₀ : Finset V) (c : V → C) (D : Set V) (q : ℕ)
    (hD : D.ncard ≤ 2*q) (hZ₀ : (Z₀ : Set V) ⊆ D)
    (hneighbors : ∀ v ∈ Z, v ∉ Z₀ →
      2*Z.card+4+2*q < (clusterCoreNeighbors G Z c v).ncard) :
    ∀ v ∈ surviving Dᶜ Z,
      2*(surviving Dᶜ Z).card+4 <
        ((cliqueAux G U c Dᶜ).neighborSet v \ (surviving Dᶜ Z : Set ↥(Dᶜ : Set V))).ncard := by
  intro v hv
  have hvZ : v.val ∈ Z := (mem_surviving _ _ _).mp hv
  have hvZ₀ : v.val ∉ Z₀ := fun h => v.property (hZ₀ h)
  have hlarge := hneighbors v hvZ hvZ₀
  have hdelete := Set.ncard_le_ncard_diff_add_ncard (clusterCoreNeighbors G Z c v) D
  have hZ := surviving_card_le Dᶜ Z
  let A := (cliqueAux G U c Dᶜ).neighborSet v \ (surviving Dᶜ Z : Set ↥(Dᶜ : Set V))
  have hsub : clusterCoreNeighbors G Z c v \ D ⊆ Subtype.val '' A := by
    intro w hw
    refine ⟨⟨w, hw.2⟩, ?_, rfl⟩
    exact ⟨Or.inl ⟨hw.1.1, hw.1.2.2⟩,
      fun h => hw.1.2.1 ((mem_surviving _ _ _).mp h)⟩
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_image_of_injective _ Subtype.val_injective] at hle
  change 2*(surviving Dᶜ Z).card+4 < A.ncard
  omega

theorem surviving_uncovered_image (D : Set V) (A : Finset V) (L : Set ↥(Dᶜ : Set V)) :
    Subtype.val '' ((surviving Dᶜ A : Set ↥(Dᶜ : Set V)) \ L) =
      (A : Set V) \ (D ∪ Subtype.val '' L) := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨(mem_surviving _ _ _).mp hw.1, ?_⟩
    rintro (hwD | ⟨u, huL, hu⟩)
    · exact w.property hwD
    · exact hw.2 (Subtype.ext hu ▸ huL)
  · rintro ⟨hvA, hv⟩
    have hvD : v ∉ D := fun h => hv (Or.inl h)
    refine ⟨⟨v, hvD⟩, ⟨(mem_surviving _ _ _).mpr hvA, ?_⟩, rfl⟩
    intro hvL
    exact hv (Or.inr ⟨⟨v, hvD⟩, hvL, rfl⟩)

theorem uncovered_embed_union_card (G : SimpleGraph V) (B : G.Subgraph)
    (H : SimpleGraph ↥(B.vertsᶜ : Set V)) (L : H.Subgraph)
    (hactual : ∀ u v, L.Adj u v → G.Adj u.val v.val) (A : Finset V) :
    ((A : Set V) \ (B ⊔ embed G B.vertsᶜ H L hactual).verts).ncard =
      ((surviving B.vertsᶜ A : Set ↥(B.vertsᶜ : Set V)) \ L.verts).ncard := by
  change ((A : Set V) \ (B.verts ∪ Subtype.val '' L.verts)).ncard = _
  rw [← surviving_uncovered_image, Set.ncard_image_of_injective _ Subtype.val_injective]

variable [Fintype I]

/-- Retain a prescribed matching after fixing the sampled boundary.
One application of the prescribed-edge theorem to all surviving cores
loses at most 135720 additional edges. All retained edges belong to the
original graph, and the result is ready for any internal core completion. -/
theorem exists_retained_partial_matching
    (G : SimpleGraph V) (U : I → Finset V) (Z Z₀ : Finset V) (c : V → C)
    (hI : Fintype.card I ≤ 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z) (hZ₀Z : Z₀ ⊆ Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hcore : ∀ i u v, u ∈ U i → v ∈ U i → c u = c v)
    (K B M : G.Subgraph) (hK : K.IsPerfectMatching)
    (hB : B.IsMatching) (hBK : B ≤ K)
    (hboundary : ∀ u v, B.Adj u v ↔ K.Adj u v ∧
      (u ∈ Z₀ ∨ v ∈ Z₀ ∨ c u ≠ c v))
    (q : ℕ) (hBedges : B.edgeSet.ncard ≤ q) (hBverts : B.verts.ncard ≤ 2*q)
    (hM : M.IsMatching)
    (hMZ : ∀ u v, M.Adj u v → u ∈ Z ∨ v ∈ Z)
    (hMc : ∀ u v, M.Adj u v → c u = c v)
    (horder : ∀ i, 2*Z.card+4+2*q < (U i).card)
    (hneighbors : ∀ v ∈ Z, v ∉ Z₀ →
      2*Z.card+4+2*q < (clusterCoreNeighbors G Z c v).ncard) :
    ∃ F : G.Subgraph, F.IsMatching ∧ B ≤ F ∧ (Z : Set V) ⊆ F.verts ∧
      (M.edgeSet \ F.edgeSet).ncard ≤ 2*q+135720 ∧
      F.edgeSet.ncard ≤ q+Z.card+3 ∧
      F.verts.ncard ≤ 2*(q+Z.card+3) ∧
      (∀ i, (F.verts ∩ (U i : Set V)).ncard ≤ 2*(q+Z.card+3)) ∧
      (∀ i, Even (((U i : Set V) \ F.verts).ncard)) ∧
      (∀ i u v, u ∈ U i → v ∈ U i → ¬ F.Adj u v) ∧
      (∀ u v, F.Adj u v → B.Adj u v ∨
        (u ∉ Z₀ ∧ v ∉ Z₀ ∧ c u = c v)) := by
  classical
  let S : Set V := B.vertsᶜ
  let H := cliqueAux G U c S
  let U' (i : I) : Finset S := surviving S (U i)
  let Z' : Finset S := surviving S Z
  have hmarked : (Z₀ : Set V) ⊆ B.verts := marked_subset_boundary G Z₀ c K B hK hboundary
  have hUZ' (i : I) : Disjoint (U' i) Z' := surviving_disjoint S (U i) Z (hUZ i)
  have hcover' : ∀ v : S, v ∈ Z' ∨ ∃ i, v ∈ U' i := surviving_cover U Z S hcover
  have hclique (i : I) : H.IsClique (U' i : Set S) := cliqueAux_isClique G U c S i
  have horder' (i : I) : 2*Z'.card+4 < (U' i).card :=
    surviving_core_large U Z B.verts q hBverts horder i
  have hneighbors' : ∀ v ∈ Z', 2*Z'.card+4 < (H.neighborSet v \ (Z' : Set S)).ncard :=
    cliqueAux_neighbors_large G U Z Z₀ c B.verts q hBverts hmarked hneighbors
  have hperfect : ∃ L : H.Subgraph, L.IsPerfectMatching :=
    cliqueAux_has_perfect_matching G U Z₀ c K B hK hB hBK hboundary
  let R := avoidVertices G M B.verts.toFinset
  have hR : R.IsMatching := avoidVertices_isMatching G M hM B.verts.toFinset
  have hRM : R ≤ M := avoidVertices_le G M B.verts.toFinset
  have hRS : R.verts ⊆ S := by
    rintro v ⟨w, _, hv, _⟩
    exact fun h => hv (Set.mem_toFinset.mpr h)
  have hRloss : (M.edgeSet \ R.edgeSet).ncard ≤ 2*q := by
    have hh := avoidVertices_omitted_edges_le G M hM B.verts.toFinset
    rw [← Set.ncard_eq_toFinset_card'] at hh
    exact hh.trans hBverts
  let R' := restrictTo G R S
  have hR' : R'.IsMatching := restrictTo_isMatching G R hR S
    (fun _ _ _ h => hRS (R.edge_vert (R.symm h)))
  have hR'H : ∀ u v, R'.Adj u v → H.Adj u v := by
    intro u v huv
    exact Or.inl ⟨R.adj_sub huv, hMc u v (hRM.2 huv)⟩
  let P : H.Subgraph := rehost (G.induce S) H R' hR'H
  have hP : P.IsMatching := hR'
  have hPZ : ∀ u v, P.Adj u v → u ∈ Z' ∨ v ∈ Z' := by
    intro u v huv
    simpa only [Z', mem_surviving] using hMZ u v (hRM.2 huv)
  have hPactual : ∀ u v, P.Adj u v → G.Adj u.val v.val := fun _ _ h => R.adj_sub h
  have hPembed : embed G S H P hPactual = R := by
    change embed G S (G.induce S) (restrictTo G R S) (fun _ _ h => R.adj_sub h) = R
    exact embed_restrict_eq G R S hRS
  obtain ⟨N, hN, hPN⟩ := Overfull.prescribed_exceptional_core_matching H
    (fun i => (U' i : Set S)) Z' hI hclique
    (fun i => Finset.disjoint_coe.mpr (hUZ' i)) hcover'
    (by intro i; simpa only [Set.ncard_coe_finset] using horder' i)
    hneighbors' hperfect P hP hPZ
  have hdisjoint' : ∀ i j, i ≠ j → Disjoint (U' i) (U' j) := by
    intro i j hij
    exact surviving_disjoint S (U i) (U j) (hdisjoint i j hij)
  obtain ⟨L, hL, _hLN, hretain, hZL, hLedge, _hLvert, _hLcore, heven, hno, _hforest⟩ :=
    Compression.exists_compressed_matching H U' Z' hI hdisjoint' hUZ' hcover' N hN
  have hPL : (P.edgeSet \ L.edgeSet).ncard ≤ 135720 := by
    apply (Set.ncard_le_ncard (t := P.edgeSet \ N.edgeSet) ?_ (Set.toFinite _)).trans hPN
    rintro e ⟨heP, heL⟩
    refine ⟨heP, ?_⟩
    intro heN
    induction e using Sym2.ind with
    | h u v => exact heL (hretain u v heN (hPZ u v heP))
  have hLactual : ∀ u v, L.Adj u v → G.Adj u.val v.val := by
    intro u v huv
    exact cliqueAux_original_edge G U c S L hno huv
  let Q := embed G S H L hLactual
  have hQ : Q.IsMatching := embed_isMatching G S H L hLactual hL
  have hQS : Q.verts ⊆ S := embed_verts_subset G S H L hLactual
  have hQedge : Q.edgeSet.ncard ≤ Z.card+3 := by
    rw [embed_edgeSet_card]
    exact hLedge.trans (Nat.add_le_add_right (show Z'.card ≤ Z.card from surviving_card_le S Z) 3)
  have hdisjointBQ : Disjoint B.verts Q.verts := by
    apply Set.disjoint_left.mpr
    intro v hvB hvQ
    exact hQS hvQ hvB
  let F := B ⊔ Q
  have hF : F.IsMatching := hB.sup hQ
    (hdisjointBQ.mono B.support_subset_verts Q.support_subset_verts)
  have hBF : B ≤ F := le_sup_left
  have hQF : Q ≤ F := le_sup_right
  have hZF : (Z : Set V) ⊆ F.verts := by
    intro v hvZ
    by_cases hvB : v ∈ B.verts
    · exact Or.inl hvB
    · exact Or.inr ⟨⟨v, hvB⟩, hZL ((mem_surviving _ _ _).mpr hvZ), rfl⟩
  have hRimage : R.edgeSet = Sym2.map Subtype.val '' P.edgeSet := by
    rw [← hPembed, embed_edgeSet]
  have hRloss' : (R.edgeSet \ Q.edgeSet).ncard ≤ 135720 := by
    rw [hRimage, embed_edgeSet, ← Set.image_diff (Sym2.map.injective Subtype.val_injective),
      Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]
    exact hPL
  have hloss : (M.edgeSet \ F.edgeSet).ncard ≤ 2*q+135720 := by
    have hsub : M.edgeSet \ F.edgeSet ⊆
        (M.edgeSet \ R.edgeSet) ∪ (R.edgeSet \ Q.edgeSet) := by
      rintro e ⟨heM, heF⟩
      by_cases heR : e ∈ R.edgeSet
      · exact Or.inr ⟨heR, fun heQ => heF (Subgraph.edgeSet_mono hQF heQ)⟩
      · exact Or.inl ⟨heM, heR⟩
    have hle := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
      (Set.ncard_union_le (M.edgeSet \ R.edgeSet) (R.edgeSet \ Q.edgeSet))
    omega
  have hedge : F.edgeSet.ncard ≤ q+Z.card+3 := by
    have hle := Set.ncard_union_le B.edgeSet Q.edgeSet
    change (B ⊔ Q).edgeSet.ncard ≤ _
    rw [Subgraph.edgeSet_sup]
    omega
  have hverts : F.verts.ncard ≤ 2*(q+Z.card+3) := by
    have heq := TutteBerge.matching_vertices_card G F hF
    have hcount : F.spanningCoe.edgeFinset.card = F.edgeSet.ncard := by
      rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
      exact Nat.card_coe_set_eq _
    rw [hcount] at heq
    omega
  have hfootprint (i : I) : (F.verts ∩ (U i : Set V)).ncard ≤ 2*(q+Z.card+3) :=
    (Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _)).trans hverts
  have hevenF (i : I) : Even (((U i : Set V) \ F.verts).ncard) := by
    rw [uncovered_embed_union_card]
    exact heven i
  have hnoF : ∀ i u v, u ∈ U i → v ∈ U i → ¬ F.Adj u v := by
    intro i u v hu hv huv
    rcases huv with huv | huv
    · rcases ((hboundary u v).mp huv).2 with hz | hz | hc
      · exact Finset.disjoint_left.mp (hUZ i) hu (hZ₀Z hz)
      · exact Finset.disjoint_left.mp (hUZ i) hv (hZ₀Z hz)
      · exact hc (hcore i u v hu hv)
    · obtain ⟨a, b, hab, rfl, rfl⟩ := huv
      exact hno i a b ((mem_surviving _ _ _).mpr hu) ((mem_surviving _ _ _).mpr hv) hab
  have hloc : ∀ u v, F.Adj u v → B.Adj u v ∨ (u ∉ Z₀ ∧ v ∉ Z₀ ∧ c u = c v) := by
    intro u v huv
    rcases huv with huv | huv
    · exact Or.inl huv
    · obtain ⟨a, b, hab, rfl, rfl⟩ := huv
      exact Or.inr ⟨fun hz => a.property (hmarked hz),
        fun hz => b.property (hmarked hz), cliqueAux_cluster G U c S hcore (L.adj_sub hab)⟩
  exact ⟨F, hF, hBF, hZF, hloss, hedge, hverts, hfootprint, hevenF, hnoF, hloc⟩

end Overfull.SafePrescription
