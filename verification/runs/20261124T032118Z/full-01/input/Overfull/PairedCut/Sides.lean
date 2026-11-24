import Overfull.PairedCut.Labels
import Overfull.BipartiteMatching

/-!
# The crossing graph with its sides as vertex types

The explicit graph isomorphism preserves every original crossing edge.
This permits the paired-cut theorem to feed the bipartite matching lemmas.
-/

namespace Overfull.PairedCut

open Finset Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def cutSidesGraph (G : SimpleGraph V) (A B : Finset V) :
    SimpleGraph (A ⊕ B) :=
  (crossingGraph G A).comap (Sum.elim Subtype.val Subtype.val)

noncomputable def cutSidesEquiv (A B : Finset V) (hdisjoint : Disjoint A B)
    (hunion : A ∪ B = univ) : A ⊕ B ≃ V :=
  Equiv.ofBijective (Sum.elim Subtype.val Subtype.val) ⟨by
    intro x y hxy
    rcases x with x | x <;> rcases y with y | y
    · exact congrArg Sum.inl (Subtype.ext hxy)
    · change x.val = y.val at hxy
      exact False.elim (Finset.disjoint_left.mp hdisjoint x.property
        (hxy.symm ▸ y.property))
    · change x.val = y.val at hxy
      exact False.elim (Finset.disjoint_left.mp hdisjoint y.property
        (hxy ▸ x.property))
    · exact congrArg Sum.inr (Subtype.ext hxy), by
    intro v
    have hv : v ∈ A ∪ B := by rw [hunion]; simp
    rcases Finset.mem_union.mp hv with hA | hB
    · exact ⟨.inl ⟨v,hA⟩,rfl⟩
    · exact ⟨.inr ⟨v,hB⟩,rfl⟩⟩

@[simp] theorem cutSidesEquiv_inl (A B : Finset V) (hd : Disjoint A B)
    (hu : A ∪ B = univ) (a : A) : cutSidesEquiv A B hd hu (.inl a) = a.val := rfl

@[simp] theorem cutSidesEquiv_inr (A B : Finset V) (hd : Disjoint A B)
    (hu : A ∪ B = univ) (b : B) : cutSidesEquiv A B hd hu (.inr b) = b.val := rfl

noncomputable def cutSidesIso (G : SimpleGraph V) (A B : Finset V)
    (hd : Disjoint A B) (hu : A ∪ B = univ) :
    cutSidesGraph G A B ≃g crossingGraph G A :=
  { cutSidesEquiv A B hd hu with map_rel_iff' := Iff.rfl }

omit [Fintype V] [DecidableEq V] in
theorem cutSidesGraph_cross_adj (G : SimpleGraph V) (A B : Finset V)
    (hd : Disjoint A B) (a : A) (b : B) :
    (cutSidesGraph G A B).Adj (.inl a) (.inr b) ↔ G.Adj a.val b.val := by
  have hb : b.val ∉ A := fun h => Finset.disjoint_left.mp hd h b.property
  simp [cutSidesGraph,crossingGraph,a.property,hb]

theorem cutSidesGraph_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hd : Disjoint A B) (hu : A ∪ B = univ) (v : A ⊕ B) :
    (cutSidesGraph G A B).degree v =
      (crossingGraph G A).degree (Sum.elim Subtype.val Subtype.val v) :=
  Overfull.iso_degree_eq (cutSidesIso G A B hd hu) v

theorem cutSides_neighbors_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hd : Disjoint A B) (S : Finset A) (b : B) :
    (S ∩ leftNeighbors (cutSidesGraph G A B) b).card =
      (G.neighborFinset b.val ∩ S.image Subtype.val).card := by
  have heq : (S ∩ leftNeighbors (cutSidesGraph G A B) b).image Subtype.val =
      G.neighborFinset b.val ∩ S.image Subtype.val := by
    ext v
    constructor
    · rintro hv
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨haS,haL⟩ := Finset.mem_inter.mp ha
      have hadj : G.Adj b.val a.val := by
        simpa [leftNeighbors,cutSidesGraph_cross_adj G A B hd,G.adj_comm] using haL
      exact Finset.mem_inter.mpr ⟨by simpa using hadj,Finset.mem_image.mpr ⟨a,haS,rfl⟩⟩
    · rintro hv
      obtain ⟨hvG,hvS⟩ := Finset.mem_inter.mp hv
      obtain ⟨a,haS,rfl⟩ := Finset.mem_image.mp hvS
      have hadj : G.Adj a.val b.val := by simpa [G.adj_comm] using hvG
      refine Finset.mem_image.mpr ⟨a,Finset.mem_inter.mpr ⟨haS,?_⟩,rfl⟩
      simpa [leftNeighbors,cutSidesGraph_cross_adj G A B hd] using hadj
  rw [← heq,Finset.card_image_of_injective _ Subtype.val_injective]

theorem cutSides_robustNeighbors_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hd : Disjoint A B)
    (hhalf : (Fintype.card V : ℝ) = 2 * Fintype.card A) (ν : ℝ) (S : Finset A) :
    (bipartiteRobustNeighbors (cutSidesGraph G A B) ν S).card =
      (B ∩ robustNeighbors G (ν / 2) (S.image Subtype.val)).card := by
  have hthreshold : ν * Fintype.card A = (ν / 2) * Fintype.card V := by rw [hhalf]; ring
  have heq : (bipartiteRobustNeighbors (cutSidesGraph G A B) ν S).image Subtype.val =
      B ∩ robustNeighbors G (ν / 2) (S.image Subtype.val) := by
    ext v
    constructor
    · intro hv
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
      refine Finset.mem_inter.mpr ⟨b.property,?_⟩
      rw [mem_robustNeighbors]
      have hb' : ν * Fintype.card A ≤
          ((S ∩ leftNeighbors (cutSidesGraph G A B) b).card : ℝ) := by
        simpa [bipartiteRobustNeighbors] using hb
      rw [cutSides_neighbors_card G A B hd S b,hthreshold] at hb'
      exact hb'
    · intro hv
      obtain ⟨hvB,hvR⟩ := Finset.mem_inter.mp hv
      let b : B := ⟨v,hvB⟩
      refine Finset.mem_image.mpr ⟨b,?_,rfl⟩
      have hv' := (mem_robustNeighbors G (ν / 2) (S.image Subtype.val) v).mp hvR
      have hb' : ν * Fintype.card A ≤
          ((S ∩ leftNeighbors (cutSidesGraph G A B) b).card : ℝ) := by
        rw [cutSides_neighbors_card G A B hd S b,hthreshold]
        exact hv'
      simpa [bipartiteRobustNeighbors] using hb'
  rw [← heq,Finset.card_image_of_injective _ Subtype.val_injective]

end Overfull.PairedCut
