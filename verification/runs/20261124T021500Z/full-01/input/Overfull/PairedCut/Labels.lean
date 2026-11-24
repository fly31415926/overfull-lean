import Overfull.PairedCut.Uniform
import Overfull.Relabeling

/-!
# Cuts splitting a prescribed pairing on arbitrary vertices

An equivalence `I × Bool ≃ V` specifies the prescribed pairs without
restricting the vertex labels. The cut below has equal sides, splits every
prescribed pair, preserves a third of the minimum-degree lower bound, and
balances every set in a fixed bounded family of linearly sized clusters.
The robust-expansion conclusion of the paired-cut lemma is a separate step.
-/

namespace Overfull.PairedCut

open Finset Classical

variable {U V I : Type*}

/-- Keep precisely the edges crossing from `A` to its complement. -/
noncomputable def crossingGraph (G : SimpleGraph V) (A : Finset V) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ (v ∈ A) ≠ (w ∈ A)
  symm := by intro v w h; exact ⟨h.1.symm,h.2.symm⟩
  loopless := by intro v h; exact h.2 rfl

theorem crossingGraph_le (G : SimpleGraph V) (A : Finset V) : crossingGraph G A ≤ G :=
  fun _ _ h => h.1

theorem inverse_inter_card [DecidableEq U] [DecidableEq V]
    (e : U ≃ V) (S : Finset V) (A : Finset U) :
    ((S.map e.symm.toEmbedding) ∩ A).card = (S ∩ A.map e.toEmbedding).card := by
  have heq : ((S.map e.symm.toEmbedding) ∩ A).map e.toEmbedding =
      S ∩ A.map e.toEmbedding := by
    ext v
    simp only [Finset.mem_map_equiv,Finset.mem_inter,Equiv.symm_symm,
      Equiv.apply_symm_apply]
  rw [← heq,Finset.card_map]

noncomputable def pairCutIso [Fintype I] (G : SimpleGraph V)
    (e : I × Bool ≃ V) (ω : I → Bool) :
    cutGraph (G.comap e) ω ≃g crossingGraph G ((leftVertices ω).map e.toEmbedding) :=
  { e with
    map_rel_iff' := by
      intro v w
      change (G.Adj (e v) (e w) ∧
        (e v ∈ (leftVertices ω).map e.toEmbedding) ≠
          (e w ∈ (leftVertices ω).map e.toEmbedding)) ↔
        (G.Adj (e v) (e w) ∧ (v ∈ leftVertices ω) ≠ (w ∈ leftVertices ω))
      simp only [Finset.mem_map_equiv,Equiv.symm_apply_apply] }

/-- Simultaneously split any prescribed pairing, preserve minimum degree,
and balance a bounded family of fixed clusters. The threshold is uniform
over the graph, pairing, vertex labels and clusters. -/
theorem exists_prescribed_pair_cut (α ε β : ℝ) (K : ℕ)
    (hα : 0 < α) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hβ : 0 < β) :
    ∃ n₀ : ℕ, ∀ (V I J : Type*) [Fintype V] [Fintype I] [Fintype J]
      (G : SimpleGraph V) [DecidableRel G.Adj] (e : I × Bool ≃ V)
      (C : J → Finset V),
      Fintype.card J ≤ K → n₀ ≤ Fintype.card V →
      (∀ v, α * Fintype.card V ≤ (G.degree v : ℝ)) →
      (∀ j, β * Fintype.card V ≤ ((C j).card : ℝ)) →
      ∃ A B : Finset V,
        Disjoint A B ∧ A ∪ B = univ ∧
        A.card = Fintype.card I ∧ B.card = Fintype.card I ∧
        (∀ i, (e (i,false) ∈ A ∧ e (i,true) ∈ B) ∨
          (e (i,true) ∈ A ∧ e (i,false) ∈ B)) ∧
        (∀ v, α * Fintype.card V / 3 ≤ ((crossingGraph G A).degree v : ℝ)) ∧
        ∀ j,
          |(((C j) ∩ A).card : ℝ) - (C j).card / 2| < ε * (C j).card ∧
          |(((C j) ∩ B).card : ℝ) - (C j).card / 2| < ε * (C j).card := by
  obtain ⟨n₀,hn₀⟩ := exists_orientation α ε β K hα hε hε1 hβ
  refine ⟨n₀,?_⟩
  intro V I J _ _ _ G _ e C hK hn hdegree hsize
  let C' := fun j => (C j).map e.symm.toEmbedding
  have hcard : Fintype.card (I × Bool) = Fintype.card V := Fintype.card_congr e
  have hdegree' (v : I × Bool) :
      α * Fintype.card (I × Bool) ≤ ((G.comap e).degree v : ℝ) := by
    have hd := Overfull.iso_degree_eq (SimpleGraph.Iso.comap e G) v
    change (G.comap e).degree v = G.degree (e v) at hd
    rw [hcard,hd]
    exact hdegree (e v)
  have hsize' (j : J) : β * Fintype.card (I × Bool) ≤ ((C' j).card : ℝ) := by
    simpa only [C',Finset.card_map,hcard] using hsize j
  obtain ⟨ω,hcut,hbalance⟩ := hn₀ I J (G.comap e) C' hK (by simpa [hcard] using hn)
    hdegree' hsize'
  let A := (leftVertices ω).map e.toEmbedding
  let B := (rightVertices ω).map e.toEmbedding
  refine ⟨A,B,?_,?_,?_,?_,?_,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro v hvA hvB
    change v ∈ (leftVertices ω).map e.toEmbedding at hvA
    change v ∈ (rightVertices ω).map e.toEmbedding at hvB
    rw [Finset.mem_map_equiv] at hvA hvB
    exact Finset.disjoint_left.mp (sides_disjoint ω) hvA hvB
  · ext v
    change (v ∈ (leftVertices ω).map e.toEmbedding ∪
      (rightVertices ω).map e.toEmbedding) ↔ v ∈ univ
    simp only [Finset.mem_union,Finset.mem_map_equiv,Finset.mem_univ,iff_true]
    have h : e.symm v ∈ leftVertices ω ∪ rightVertices ω := by rw [sides_union]; simp
    exact Finset.mem_union.mp h
  · simp only [A,Finset.card_map,leftVertices_card]
  · simp only [B,Finset.card_map,rightVertices_card]
  · intro i
    cases hω : ω i <;>
      simp [A,B,Finset.mem_map_equiv,mem_leftVertices,mem_rightVertices,hω]
  · intro v
    obtain ⟨u,rfl⟩ := e.surjective v
    have h := hcut u
    rw [hcard,Overfull.iso_degree_eq (pairCutIso G e ω)] at h
    exact h
  · intro j
    have h := hbalance j
    dsimp only [C'] at h
    rw [inverse_inter_card e (C j) (leftVertices ω),
      inverse_inter_card e (C j) (rightVertices ω),Finset.card_map] at h
    exact h

end Overfull.PairedCut
