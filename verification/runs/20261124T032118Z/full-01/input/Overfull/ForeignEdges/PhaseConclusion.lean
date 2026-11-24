import Overfull.ForeignEdges.Phase
import Overfull.ForeignEdges.Assignment
import Overfull.ForeignEdges.Incidence

/-!
# Fresh phase data and the actual conclusion of a completed phase

The maximizing assignment and its matching classes are chosen before the
deletion sequence. Their surviving restrictions meet the exceptional and
same-cluster hypotheses of safe prescription. Once those classes have been
processed, the bound is on the actual foreign graph in the final residual.
This module does not assume that assignments agree between different phases.
-/

namespace Overfull.ForeignPhase

open Finset Classical SimpleGraph MatchingProbability Compression
open ForeignAssignment BipartitePackingAccounting

variable {V I C : Type*} [Fintype V]

omit [Fintype V] in
/-- Extend a finite indexed family by empty classes outside its range. -/
noncomputable def extendClasses {X : Type*} {d : ℕ}
    (B : Fin d → Finset X) (j : ℕ) : Finset X :=
  if hj : j < d then B ⟨j,hj⟩ else ∅

@[simp] theorem extendClasses_lt {X : Type*} {d : ℕ}
    (B : Fin d → Finset X) (j : ℕ) (hj : j < d) :
    extendClasses B j = B ⟨j,hj⟩ := by
  simp only [extendClasses,dif_pos hj]

theorem biUnion_extendClasses {X : Type*} [DecidableEq X] {d : ℕ} (B : Fin d → Finset X) :
    (range d).biUnion (extendClasses B) = univ.biUnion B := by
  ext e
  simp only [mem_biUnion,mem_range,mem_univ,true_and]
  constructor
  · rintro ⟨j,hj,he⟩
    exact ⟨⟨j,hj⟩,(extendClasses_lt B j hj) ▸ he⟩
  · rintro ⟨j,he⟩
    exact ⟨j.val,j.isLt,(extendClasses_lt B j.val j.isLt).symm ▸ he⟩

/-- Changing the ambient host does not change the number of surviving
foreign edges. This equality relates the two actual host-edge subtypes. -/
theorem foreignEdges_card_eq_surviving (G R : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel R.Adj] (hR : R ≤ G)
    (U : I → Finset V) (E : Finset V) (c : V → C) (p : I → C) (a : V → I) :
    (foreignEdges R U E c p a).card =
      (survivingEdges G R (foreignEdges G U E c p a)).card := by
  apply card_bij (fun e _ => (⟨e.val, SimpleGraph.edgeSet_mono hR e.property⟩ : G.edgeSet))
  · intro e he
    apply (mem_survivingEdges G R _ _).mpr
    refine ⟨?_,e.property⟩
    apply (mem_foreignEdges G U E c p a _).mpr
    exact SimpleGraph.edgeSet_mono
      (show foreignGraph R U E c p a ≤ foreignGraph G U E c p a from
        fun _ _ h => ⟨hR h.1,h.2⟩) ((mem_foreignEdges R U E c p a e).mp he)
  · intro e _ f _ heq
    exact Subtype.ext (congrArg (fun x : G.edgeSet => x.val) heq)
  · intro e he
    obtain ⟨heF,heR⟩ := (mem_survivingEdges G R _ e).mp he
    have hf : e.val ∈ (foreignGraph R U E c p a).edgeSet := by
      rw [foreignGraph_subgraph_eq G R hR,SimpleGraph.edgeSet_inf]
      exact ⟨heR,(mem_foreignEdges G U E c p a e).mp heF⟩
    refine ⟨⟨e.val, heR⟩, ?_, ?_⟩
    · exact (mem_foreignEdges R U E c p a _).mpr hf
    · exact Subtype.ext rfl

/-- Every current prescribed edge from a foreign class is incident with
an actual exceptional vertex, and both endpoints have the same cluster. -/
theorem currentClass_location (G R : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (E Z : Finset V) (c : V → C) (p : I → C) (a : V → I)
    (hEZ : E ⊆ Z) (hcolor : ∀ i v, v ∈ U i → c v = p i)
    (A : Finset G.edgeSet) (hA : A ⊆ foreignEdges G U E c p a) :
    (∀ u v, (currentClass G R A).Adj u v → u ∈ Z ∨ v ∈ Z) ∧
    (∀ u v, (currentClass G R A).Adj u v → c u = c v) := by
  have hforeign : ∀ u v, (currentClass G R A).Adj u v →
      (foreignGraph G U E c p a).Adj u v := by
    rintro u v ⟨huv, he⟩
    exact (mem_foreignEdges G U E c p a ⟨s(u,v),huv⟩).mp
      (hA ((mem_survivingEdges G R A _).mp he).1)
  constructor
  · intro u v huv
    rcases (hforeign u v huv).2 with ⟨hu, _⟩ | ⟨hv, _⟩
    · exact Or.inl (hEZ hu)
    · exact Or.inr (hEZ hv)
  · intro u v huv
    rcases (hforeign u v huv).2 with ⟨_, i, hv, hpi, _⟩ | ⟨_, i, hu, hpi, _⟩
    · exact hpi.symm.trans (hcolor i v hv).symm
    · exact (hcolor i u hu).trans hpi

/-- At the end of a completed fresh phase, the bound concerns the actual
foreign graph of the residual, not a proxy count in the initial host. -/
theorem complete_foreign_phase_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (E : Finset V) (c : V → C) (p : I → C) (a : V → I)
    (N : ℕ → G.Subgraph) (d c₁ : ℕ) (A : ℕ → Finset G.edgeSet)
    (hclasses : (range d).biUnion A = foreignEdges G U E c p a)
    (hused : ∀ j < d, (N j).spanningCoe ≤ afterDeletions G N j)
    (hloss : ∀ j < d,
      ((currentClass G (afterDeletions G N j) (A j)).edgeSet \
        (N j).edgeSet).ncard ≤ c₁) :
    (foreignEdges (afterDeletions G N d) U E c p a).card ≤ c₁*d := by
  rw [foreignEdges_card_eq_surviving G (afterDeletions G N d)
    (fun _ _ h => h.1) U E c p a]
  exact complete_phase_card_le_of_prescribed_loss G N d c₁ A _ hclasses hused hloss

variable [Fintype I] [Nonempty I]

/-- Construct fresh maximizing phase data, ready for every later
deletion sequence. The only process hypothesis in the last clause is the
actual bounded loss supplied by the safe-prescription construction. -/
theorem exists_fresh_phase_data (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (E Z : Finset V) (c : V → C) (p : I → C)
    (hEZ : E ⊆ Z) (hcolor : ∀ i v, v ∈ U i → c v = p i)
    (hdisjoint : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hUE : ∀ i, Disjoint (U i) E) (hcount : Fintype.card I ≤ 4)
    (hrepresented : ∀ v ∈ E, ∃ i, p i = c v)
    (H : ∀ i, SimpleGraph (U i)) (hH : ∀ i, H i ≤ G.induce (U i : Set V))
    (h : ℕ) (ε : ℝ) (hregular : ∀ v, G.degree v = h)
    (hcore : ∀ i v, (h : ℝ)-ε ≤ ((H i).degree v : ℝ))
    (hsmall : 4*ε ≤ 3*h) :
    ∃ a : V → I, ∃ A : ℕ → Finset G.edgeSet,
      (∀ v ∈ E, p (a v) = c v ∧
        ∀ i, p i = c v → (coreNeighbors G U v i).card ≤
          (coreNeighbors G U v (a v)).card) ∧
      (range (3*h/4)).biUnion A = foreignEdges G U E c p a ∧
      (∀ j < 3*h/4, ∀ R : SimpleGraph V,
        (currentClass G R (A j)).IsMatching ∧
        (∀ u v, (currentClass G R (A j)).Adj u v → u ∈ Z ∨ v ∈ Z) ∧
        (∀ u v, (currentClass G R (A j)).Adj u v → c u = c v)) ∧
      ∀ (N : ℕ → G.Subgraph) (c₁ : ℕ),
        (∀ j < 3*h/4, (N j).IsPerfectMatching) →
        (∀ j < 3*h/4, (N j).spanningCoe ≤ afterDeletions G N j) →
        (∀ j < 3*h/4,
          ((currentClass G (afterDeletions G N j) (A j)).edgeSet \
            (N j).edgeSet).ncard ≤ c₁) →
        (foreignEdges (afterDeletions G N (3*h/4)) U E c p a).card ≤ c₁*(3*h/4) ∧
        (∀ v, (afterDeletions G N (3*h/4)).degree v = h-3*h/4) ∧
        h ≤ 4*(h-3*h/4) := by
  obtain ⟨a, ha, M, hM, _hdisj, hunion, _hgraph⟩ :=
    exists_assignment_color_classes_of_cores G U E c p hdisjoint hUE hcount
      hrepresented H hH h ε hregular hcore hsmall
  let A : ℕ → Finset G.edgeSet := extendClasses (fun i => matchingEdges (M i))
  have hA (j : ℕ) (hj : j < 3*h/4) : A j = matchingEdges (M ⟨j,hj⟩) := by
    exact extendClasses_lt _ j hj
  have hunion' : (range (3*h/4)).biUnion A = foreignEdges G U E c p a :=
    (biUnion_extendClasses (fun i => matchingEdges (M i))).trans hunion
  have hsubset (j : ℕ) (hj : j < 3*h/4) : A j ⊆ foreignEdges G U E c p a := by
    intro e he
    rw [← hunion']
    exact mem_biUnion.mpr ⟨j,mem_range.mpr hj,he⟩
  refine ⟨a,A,ha,hunion',?_,?_⟩
  · intro j hj R
    refine ⟨?_,currentClass_location G R U E Z c p a hEZ hcolor (A j) (hsubset j hj)⟩
    apply SafePrescription.rehost_isMatching
    apply selectedMatching_isMatching G (M ⟨j,hj⟩) (hM ⟨j,hj⟩)
    rw [← hA j hj]
    exact filter_subset _ _
  · intro N c₁ hN hused hloss
    refine ⟨complete_foreign_phase_card_le G U E c p a N (3*h/4) c₁ A
      hunion' hused hloss, ?_, (phase_degree_reserve h (3*h/4) le_rfl).2⟩
    intro v
    have hid := ForeignIncidence.perfect_deletion_degree_identity G N (3*h/4) hN hused v
    have hreg := hregular v
    simp only [afterDeletions,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] at hid hreg ⊢
    omega

end Overfull.ForeignPhase
