import Overfull.OrdinaryFactorization.FirstHalfData
import Overfull.BipartiteFactorization.Preferred
import Overfull.BipartiteFactorization.Palettes

/-!
# Selecting first-half labels without exhausting an apex shore

Two disjoint sets of incident colors can contribute prescribed numbers of
labels. Properness then gives exact counts of the original surviving edge
copies. This is a finite selection argument, with no random palette input.
-/

noncomputable section

namespace Overfull.OrdinaryFactorization

open Finset Classical SmallCuts BipartiteFactorization

variable {k h : ℕ}

/-- An embedding whose finite range is the specified palette. -/
theorem exists_labels_with_range (I : Finset (Fin k)) (hI : I.card = h) :
    ∃ l : Fin h ↪ Fin k, (univ : Finset (Fin h)).map l = I := by
  let e : I ≃ Fin h := I.equivFinOfCardEq hI
  let l : Fin h ↪ Fin k := e.symm.toEmbedding.trans
    (Function.Embedding.subtype (fun i => i ∈ I))
  refine ⟨l, ?_⟩
  ext i
  constructor
  · rintro hi
    obtain ⟨j, _, rfl⟩ := mem_map.mp hi
    exact (e.symm j).property
  · intro hi
    refine mem_map.mpr ⟨e ⟨i, hi⟩, mem_univ _, ?_⟩
    exact congrArg Subtype.val (e.symm_apply_apply ⟨i, hi⟩)

/-- Choose half of the labels from each of two disjoint available rows. -/
theorem exists_two_row_labels (A B : Finset (Fin k)) (hAB : Disjoint A B)
    (hA : h / 2 ≤ A.card) (hB : h - h / 2 ≤ B.card) :
    ∃ l : Fin h ↪ Fin k,
      (A.filter (fun i => i ∈ Set.range l)).card = h / 2 ∧
      (B.filter (fun i => i ∈ Set.range l)).card = h - h / 2 := by
  obtain ⟨S, hSA, hS⟩ := exists_subset_card_eq hA
  obtain ⟨T, hTB, hT⟩ := exists_subset_card_eq hB
  have hST : Disjoint S T := hAB.mono hSA hTB
  have hcard : (S ∪ T).card = h := by
    rw [card_union_of_disjoint hST, hS, hT]
    omega
  obtain ⟨l, hl⟩ := exists_labels_with_range (S ∪ T) hcard
  have hrange (i : Fin k) : i ∈ Set.range l ↔ i ∈ S ∪ T := by
    rw [← hl]
    simp only [mem_map, mem_univ, true_and, Set.mem_range]
  have hleft : A.filter (fun i => i ∈ Set.range l) = S := by
    ext i
    rw [mem_filter, hrange, mem_union]
    constructor
    · rintro ⟨hiA, hiS | hiT⟩
      · exact hiS
      · exact False.elim (disjoint_left.mp hAB hiA (hTB hiT))
    · intro hiS
      exact ⟨hSA hiS, Or.inl hiS⟩
  have hright : B.filter (fun i => i ∈ Set.range l) = T := by
    ext i
    rw [mem_filter, hrange, mem_union]
    constructor
    · rintro ⟨hiB, hiS | hiT⟩
      · exact False.elim (disjoint_left.mp hAB (hSA hiS) hiB)
      · exact hiT
    · intro hiT
      exact ⟨hTB hiT, Or.inr hiT⟩
  exact ⟨l, hleft ▸ hS, hright ▸ hT⟩

variable {V E : Type*} [Fintype E] {G : Multigraph V E}

/-- Incident copies on disjoint vertex rows have disjoint proper colors. -/
theorem colorsOn_rows_disjoint (c : G.EdgeColoring k) (x : V)
    (A B : Finset V) (hAB : Disjoint A B) :
    Disjoint (colorsOn c (G.edgesTo x A)) (colorsOn c (G.edgesTo x B)) := by
  apply disjoint_left.mpr
  intro i hiA hiB
  obtain ⟨e, he, hei⟩ := mem_image.mp hiA
  obtain ⟨f, hf, hfi⟩ := mem_image.mp hiB
  have hef : e = f := c.proper (hei.trans hfi.symm)
    ((G.mem_edgesTo x A e).mp he).1 ((G.mem_edgesTo x B f).mp hf).1
  subst f
  exact disjoint_left.mp hAB ((G.mem_edgesTo x A e).mp he).2
    ((G.mem_edgesTo x B e).mp hf).2

/-- Properness identifies a selected set of incident copies with its colors. -/
theorem row_selected_colors_card (c : G.EdgeColoring k) (x : V)
    (A : Finset V) (l : Fin h ↪ Fin k) :
    ((G.edgesTo x A).filter (fun e => c.color e ∈ Set.range l)).card =
      ((colorsOn c (G.edgesTo x A)).filter (fun i => i ∈ Set.range l)).card := by
  have hset : ((G.edgesTo x A).filter (fun e => c.color e ∈ Set.range l)).image c.color =
      (colorsOn c (G.edgesTo x A)).filter (fun i => i ∈ Set.range l) := by
    ext i
    simp only [colorsOn, mem_image, mem_filter]
    constructor
    · rintro ⟨e, ⟨he, hsel⟩, rfl⟩
      exact ⟨⟨e, he, rfl⟩, hsel⟩
    · rintro ⟨⟨e, he, rfl⟩, hsel⟩
      exact ⟨e, ⟨he, hsel⟩, rfl⟩
  rw [← hset]
  symm
  apply card_image_of_injOn
  intro e he f hf hef
  exact c.proper hef ((G.mem_edgesTo x A e).mp (mem_filter.mp he).1).1
    ((G.mem_edgesTo x A f).mp (mem_filter.mp hf).1).1

/-- The first-half palette can leave the exact complementary number of
incident copies on each shore of a chosen exterior vertex. -/
theorem exists_labels_preserving_rows (c : G.EdgeColoring k) (x : V)
    (A B : Finset V) (hAB : Disjoint A B)
    (hA : h / 2 ≤ (G.edgesTo x A).card)
    (hB : h - h / 2 ≤ (G.edgesTo x B).card) :
    ∃ l : Fin h ↪ Fin k,
      ((G.edgesTo x A).filter (fun e => c.color e ∉ Set.range l)).card =
        (G.edgesTo x A).card - h / 2 ∧
      ((G.edgesTo x B).filter (fun e => c.color e ∉ Set.range l)).card =
        (G.edgesTo x B).card - (h - h / 2) := by
  obtain ⟨l, hlA, hlB⟩ := exists_two_row_labels
    (colorsOn c (G.edgesTo x A)) (colorsOn c (G.edgesTo x B))
    (colorsOn_rows_disjoint c x A B hAB)
    (by simpa only [core_colors_card] using hA)
    (by simpa only [core_colors_card] using hB)
  have hleft := filter_card_add_filter_neg_card_eq_card
    (s := G.edgesTo x A) (fun e => c.color e ∈ Set.range l)
  have hright := filter_card_add_filter_neg_card_eq_card
    (s := G.edgesTo x B) (fun e => c.color e ∈ Set.range l)
  rw [row_selected_colors_card, hlA] at hleft
  rw [row_selected_colors_card, hlB] at hright
  exact ⟨l, by omega, by omega⟩

variable {U : Finset V}

/-- Every incidence at an exterior vertex belongs to the actual core
complement, so restricting to that complement preserves each shore count. -/
theorem complement_apex_row_card (C : Core G U) (x : V) (hx : x ∉ U)
    (A : Finset V) :
    ((G.restrictEdges (OneCore.coreEdges C)ᶜ).edgesTo x A).card =
      (G.edgesTo x A).card := by
  rw [G.restrictEdges_edgesTo_card]
  apply congrArg Finset.card
  apply inter_eq_right.mpr
  intro e he
  apply mem_compl.mpr
  intro heC
  exact hx (OneCore.coreEdges_endpoint C heC ((G.mem_edgesTo x A e).mp he).1)

/-- Repairing core matchings does not change which original apex incidences
survive: only the selected exterior labels determine that count. -/
theorem residualGraph_apex_row_card (C : Core G U)
    (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k)
    (l : Fin h ↪ Fin k) (N : Fin h → C.graph.Subgraph)
    (x : V) (hx : x ∉ U) (A : Finset V) :
    ((residualGraph C c l N).edgesTo x A).card =
      (((G.restrictEdges (OneCore.coreEdges C)ᶜ).edgesTo x A).filter
        (fun e => c.color e ∉ Set.range l)).card := by
  rw [residualGraph, G.restrictEdges_edgesTo_card]
  have hcomp (e : E) (he : e ∈ G.edgesTo x A) : e ∈ (OneCore.coreEdges C)ᶜ := by
    apply mem_compl.mpr
    intro heC
    exact hx (OneCore.coreEdges_endpoint C heC ((G.mem_edgesTo x A e).mp he).1)
  apply card_bij (fun e he =>
    (⟨e, hcomp e (mem_inter.mp he).2⟩ : ↥((OneCore.coreEdges C)ᶜ)))
  · intro e he
    obtain ⟨heD, heA⟩ := mem_inter.mp he
    apply mem_filter.mpr
    constructor
    · exact ((G.restrictEdges (OneCore.coreEdges C)ᶜ).mem_edgesTo x A _).mpr
        ((G.mem_edgesTo x A e).mp heA)
    · exact (complement_survives_iff C c l N ⟨e, hcomp e heA⟩).mp heD
  · intro e _ f _ hef
    exact congrArg Subtype.val hef
  · intro e he
    obtain ⟨heA, hsel⟩ := mem_filter.mp he
    have heA' : e.val ∈ G.edgesTo x A :=
      (G.mem_edgesTo x A e.val).mpr
        (((G.restrictEdges (OneCore.coreEdges C)ᶜ).mem_edgesTo x A e).mp heA)
    exact ⟨e.val, mem_inter.mpr
      ⟨(complement_survives_iff C c l N e).mpr hsel, heA'⟩, Subtype.ext rfl⟩

end Overfull.OrdinaryFactorization
