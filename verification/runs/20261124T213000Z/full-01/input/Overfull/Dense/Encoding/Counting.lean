import Overfull.Dense.Encoding.Coloring

/-!
# Degree and color-class identities in the tripartite encoding
-/

namespace Overfull.Dense.Encoding.SimplePart

open Finset Classical
open TripartiteGraph

variable {A B E : Type*} [Fintype A] [Fintype B]
variable {G : Multigraph (A ⊕ B) E} (H : SimplePart G) {k : ℕ}

theorem selected_left_card (a : A) :
    (H.edges.filter (fun e => Sum.inl a ∈ G.edge e)).card =
      (univ.filter (H.adj a)).card := by
  symm
  refine Finset.card_bij
    (fun b hb => H.edgeMap ⟨(a,b),(Finset.mem_filter.mp hb).2⟩) ?_ ?_ ?_
  · intro b hb
    exact Finset.mem_filter.mpr ⟨H.edgeMap_mem_edges _, (H.map_mem_left _ _).mpr rfl⟩
  · intro b hb b' hb' h
    exact congrArg (fun e : H.Edge => e.val.2) (H.edgeMap.injective h)
  · intro e he
    obtain ⟨heH,hea⟩ := Finset.mem_filter.mp he
    let x := H.edgeOfMem e heH
    have hxmap : H.edgeMap x = e := H.edgeMap_edgeOfMem e heH
    have hxa : x.val.1 = a := (H.map_mem_left x a).mp (by rw [hxmap]; exact hea)
    have hxb : x.val.2 ∈ univ.filter (H.adj a) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hxa ▸ x.property
    refine ⟨x.val.2,hxb,?_⟩
    rw [← hxmap]
    apply congrArg H.edgeMap
    exact Subtype.ext (Prod.ext hxa.symm rfl)

theorem selected_right_card (b : B) :
    (H.edges.filter (fun e => Sum.inr b ∈ G.edge e)).card =
      (univ.filter (fun a => H.adj a b)).card := by
  symm
  refine Finset.card_bij
    (fun a ha => H.edgeMap ⟨(a,b),(Finset.mem_filter.mp ha).2⟩) ?_ ?_ ?_
  · intro a ha
    exact Finset.mem_filter.mpr ⟨H.edgeMap_mem_edges _, (H.map_mem_right _ _).mpr rfl⟩
  · intro a ha a' ha' h
    exact congrArg (fun e : H.Edge => e.val.1) (H.edgeMap.injective h)
  · intro e he
    obtain ⟨heH,heb⟩ := Finset.mem_filter.mp he
    let x := H.edgeOfMem e heH
    have hxmap : H.edgeMap x = e := H.edgeMap_edgeOfMem e heH
    have hxb : x.val.2 = b := (H.map_mem_right x b).mp (by rw [hxmap]; exact heb)
    have hxa : x.val.1 ∈ univ.filter (fun a => H.adj a b) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hxb ▸ x.property
    refine ⟨x.val.1,hxa,?_⟩
    rw [← hxmap]
    apply congrArg H.edgeMap
    exact Subtype.ext (Prod.ext rfl hxb.symm)

variable [Fintype E] (c₀ : H.remainder.EdgeColoring k)

theorem neighborsWA_card_add_remainder_degree (a : A) :
    ((H.encoded c₀).neighborsWA a).card + H.remainder.degree (.inl a) = k :=
  c₀.availableColors_card_add_degree (.inl a)

theorem neighborsWB_card_add_remainder_degree (b : B) :
    ((H.encoded c₀).neighborsWB b).card + H.remainder.degree (.inr b) = k :=
  c₀.availableColors_card_add_degree (.inr b)

theorem neighborsB_card_add_remainder_degree (a : A) :
    ((H.encoded c₀).neighborsB a).card + H.remainder.degree (.inl a) =
      G.degree (.inl a) := by
  have h := MultigraphMatchingProbability.remaining_degree_add_selected (G := G) H.edges
    (.inl a)
  have hs : (H.edges.filter (fun e => Sum.inl a ∈ G.edge e)).card =
      ((H.encoded c₀).neighborsB a).card := H.selected_left_card a
  have h' : H.remainder.degree (.inl a) +
      (H.edges.filter (fun e => Sum.inl a ∈ G.edge e)).card = G.degree (.inl a) := by
    convert h using 1
    congr 3
  omega

theorem neighborsA_card_add_remainder_degree (b : B) :
    ((H.encoded c₀).neighborsA b).card + H.remainder.degree (.inr b) =
      G.degree (.inr b) := by
  have h := MultigraphMatchingProbability.remaining_degree_add_selected (G := G) H.edges
    (.inr b)
  have hs : (H.edges.filter (fun e => Sum.inr b ∈ G.edge e)).card =
      ((H.encoded c₀).neighborsA b).card := H.selected_right_card b
  have h' : H.remainder.degree (.inr b) +
      (H.edges.filter (fun e => Sum.inr b ∈ G.edge e)).card = G.degree (.inr b) := by
    convert h using 1
    congr 3
  omega

/-- The color class consists of actual complementary edge copies. -/
noncomputable def colorClass (w : Fin k) : Finset {e : E // e ∉ H.edges} :=
  univ.filter (fun e => c₀.color e = w)

theorem colorClass_left_injective (P : Bipartition G) (w : Fin k) :
    Set.InjOn (fun e : {e : E // e ∉ H.edges} => P.left e.val) (H.colorClass c₀ w) := by
  intro e he f hf hef
  have hcolor : c₀.color e = c₀.color f :=
    (Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm
  apply c₀.proper hcolor (v := .inl (P.left e.val))
  · exact (P.mem_left e.val _).mpr rfl
  · exact (P.mem_left f.val _).mpr hef.symm

theorem colorClass_right_injective (P : Bipartition G) (w : Fin k) :
    Set.InjOn (fun e : {e : E // e ∉ H.edges} => P.right e.val) (H.colorClass c₀ w) := by
  intro e he f hf hef
  have hcolor : c₀.color e = c₀.color f :=
    (Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm
  apply c₀.proper hcolor (v := .inr (P.right e.val))
  · exact (P.mem_right e.val _).mpr rfl
  · exact (P.mem_right f.val _).mpr hef.symm

theorem used_left_eq_colorClass_image (P : Bipartition G) (w : Fin k) :
    univ.filter (fun a => ¬ c₀.Available (.inl a) w) =
      (H.colorClass c₀ w).image (fun e => P.left e.val) := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Multigraph.EdgeColoring.Available, not_not, Finset.mem_image, colorClass]
  constructor
  · rintro ⟨e,he,hcolor⟩
    exact ⟨e,hcolor,(P.mem_left e.val a).mp he⟩
  · rintro ⟨e,hcolor,he⟩
    exact ⟨e,(P.mem_left e.val a).mpr he,hcolor⟩

theorem used_right_eq_colorClass_image (P : Bipartition G) (w : Fin k) :
    univ.filter (fun b => ¬ c₀.Available (.inr b) w) =
      (H.colorClass c₀ w).image (fun e => P.right e.val) := by
  ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Multigraph.EdgeColoring.Available, not_not, Finset.mem_image, colorClass]
  constructor
  · rintro ⟨e,he,hcolor⟩
    exact ⟨e,hcolor,(P.mem_right e.val b).mp he⟩
  · rintro ⟨e,hcolor,he⟩
    exact ⟨e,(P.mem_right e.val b).mpr he,hcolor⟩

theorem linkA_card_add_colorClass (P : Bipartition G) (w : Fin k) :
    ((H.encoded c₀).linkA w).card + (H.colorClass c₀ w).card = Fintype.card A := by
  have h := Finset.filter_card_add_filter_neg_card_eq_card (s := (univ : Finset A))
    (fun a => c₀.Available (.inl a) w)
  rw [H.used_left_eq_colorClass_image c₀ P w,
    Finset.card_image_iff.mpr (H.colorClass_left_injective c₀ P w)] at h
  simpa only [Finset.card_univ] using h

theorem linkB_card_add_colorClass (P : Bipartition G) (w : Fin k) :
    ((H.encoded c₀).linkB w).card + (H.colorClass c₀ w).card = Fintype.card B := by
  have h := Finset.filter_card_add_filter_neg_card_eq_card (s := (univ : Finset B))
    (fun b => c₀.Available (.inr b) w)
  rw [H.used_right_eq_colorClass_image c₀ P w,
    Finset.card_image_iff.mpr (H.colorClass_right_injective c₀ P w)] at h
  simpa only [Finset.card_univ] using h

theorem encoded_locallyBalanced (P : Bipartition G)
    (hregular : ∀ v, G.degree v = k) (hbalance : Fintype.card A = Fintype.card B) :
    (H.encoded c₀).IsLocallyBalanced := by
  refine ⟨?_,?_,?_⟩
  · intro a
    have h₁ := H.neighborsWA_card_add_remainder_degree c₀ a
    have h₂ := H.neighborsB_card_add_remainder_degree c₀ a
    rw [hregular] at h₂
    omega
  · intro b
    have h₁ := H.neighborsWB_card_add_remainder_degree c₀ b
    have h₂ := H.neighborsA_card_add_remainder_degree c₀ b
    rw [hregular] at h₂
    omega
  · intro w
    have h₁ := H.linkA_card_add_colorClass c₀ P w
    have h₂ := H.linkB_card_add_colorClass c₀ P w
    omega

end Overfull.Dense.Encoding.SimplePart
