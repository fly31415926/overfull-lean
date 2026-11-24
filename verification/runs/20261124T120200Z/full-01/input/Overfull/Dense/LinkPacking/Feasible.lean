import Overfull.Dense.LinkPacking.Candidates
import Overfull.Dense.LinkPacking.Parameters
import Overfull.Dense.LinkPacking.History

/-!
# Candidate feasibility from the actual local used-edge load

Only used edges into the current link count against its crossing degrees.
The used graph may have arbitrarily many edges elsewhere. The output is an
actual candidate family for the total history, with no candidate-existence
or probabilistic assumption.
-/

noncomputable section

namespace Overfull.Dense.LinkPacking

open Finset Classical SimpleGraph DenseLinkPacking

variable {V : Type*} [Fintype V]

/-- Deleting used edges removes at most the used neighbors inside the
specified opposite side. -/
theorem cross_degree_after_deletion_local (G U : SimpleGraph V)
    (B : Finset V) (v : V) :
    (G.neighborFinset v ∩ B).card ≤
      ((G \ U).neighborFinset v ∩ B).card + (U.neighborFinset v ∩ B).card := by
  have heq : (G.neighborFinset v ∩ B) \ (U.neighborFinset v ∩ B) =
      (G \ U).neighborFinset v ∩ B := by
    ext w
    simp only [Finset.mem_sdiff, Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      SimpleGraph.sdiff_adj]
    tauto
  have hpart := Finset.card_sdiff_add_card_inter
    (G.neighborFinset v ∩ B) (U.neighborFinset v ∩ B)
  rw [heq] at hpart
  have hcap : ((G.neighborFinset v ∩ B) ∩ (U.neighborFinset v ∩ B)).card ≤
      (U.neighborFinset v ∩ B).card :=
    Finset.card_le_card Finset.inter_subset_right
  omega

/-- A local load bound suffices to construct all actual matching candidates.
The two local sides may both be empty, and the used graph is unrestricted
outside their union. -/
theorem exists_candidateOK_of_local_load (G U : SimpleGraph V)
    (A B : Finset V) (hAB : Disjoint A B) (hbalance : A.card = B.card)
    (t : ℕ) (L : ℝ)
    (hleft : ∀ v ∈ A,
      (A.card : ℝ) / 2 + L + t ≤ (G.neighborFinset v ∩ B).card)
    (hright : ∀ v ∈ B,
      (A.card : ℝ) / 2 + L + t ≤ (G.neighborFinset v ∩ A).card)
    (hload : ∀ v ∈ A ∪ B,
      ((U.neighborFinset v ∩ (A ∪ B)).card : ℝ) ≤ L) :
    ∃ K : Fin t → G.Subgraph, CandidateOK G t (A ∪ B) U K := by
  obtain ⟨R, hR⟩ : ∃ R : SimpleGraph V, R = G \ U := ⟨_, rfl⟩
  have hneighbors (v : V) : (G \ U).neighborFinset v = R.neighborFinset v := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset]
    rw [hR]
  have hl : ∀ v ∈ A,
      (A.card : ℝ) / 2 + t ≤ (R.neighborFinset v ∩ B).card := by
    intro v hv
    have hdeg := cross_degree_after_deletion_local G U B v
    rw [hneighbors v] at hdeg
    have hcap : (U.neighborFinset v ∩ B).card ≤
        (U.neighborFinset v ∩ (A ∪ B)).card := by
      apply Finset.card_le_card
      intro w hw
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hw).1,
        Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mp hw).2)⟩
    have hdegR : ((G.neighborFinset v ∩ B).card : ℝ) ≤
        (R.neighborFinset v ∩ B).card + (U.neighborFinset v ∩ B).card := by
      exact_mod_cast hdeg
    have hcapR : ((U.neighborFinset v ∩ B).card : ℝ) ≤
        (U.neighborFinset v ∩ (A ∪ B)).card := by exact_mod_cast hcap
    have hlocal := hload v (Finset.mem_union.mpr (Or.inl hv))
    have hdense := hleft v hv
    linarith
  have hr : ∀ v ∈ B,
      (A.card : ℝ) / 2 + t ≤ (R.neighborFinset v ∩ A).card := by
    intro v hv
    have hdeg := cross_degree_after_deletion_local G U A v
    rw [hneighbors v] at hdeg
    have hcap : (U.neighborFinset v ∩ A).card ≤
        (U.neighborFinset v ∩ (A ∪ B)).card := by
      apply Finset.card_le_card
      intro w hw
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hw).1,
        Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mp hw).2)⟩
    have hdegR : ((G.neighborFinset v ∩ A).card : ℝ) ≤
        (R.neighborFinset v ∩ A).card + (U.neighborFinset v ∩ A).card := by
      exact_mod_cast hdeg
    have hcapR : ((U.neighborFinset v ∩ A).card : ℝ) ≤
        (U.neighborFinset v ∩ (A ∪ B)).card := by exact_mod_cast hcap
    have hlocal := hload v (Finset.mem_union.mpr (Or.inr hv))
    have hdense := hright v hv
    linarith
  obtain ⟨M, hM, hverts, hdisj⟩ :=
    exists_matching_candidates R A B hAB hbalance t hl hr
  have hRG : R ≤ G := by rw [hR]; exact sdiff_le
  let K : Fin t → G.Subgraph := fun i => liftOfLE hRG (M i)
  refine ⟨K, ?_, ?_⟩
  · intro i
    refine ⟨liftOfLE_isMatching hRG (M i) (hM i), ?_, ?_⟩
    · simpa only [K, liftOfLE_verts] using hverts i
    · apply disjoint_iff_inf_le.mpr
      intro v w h
      have hMadj : (M i).Adj v w := (liftOfLE_adj hRG (M i) v w).mp h.1
      have hres : (G \ U).Adj v w := by
        rw [← hR]
        exact (M i).adj_sub hMadj
      exact hres.2 h.2
  · intro i j hij
    apply disjoint_iff_inf_le.mpr
    intro v w h
    exact (hdisj hij).le_bot
      ⟨(liftOfLE_adj hRG (M i) v w).mp h.1,
        (liftOfLE_adj hRG (M j) v w).mp h.2⟩

/-- The manuscript's `81 b λ^(3/2) n` margin supplies the actual rounded
candidate family whenever the local used-edge load is at most the prescribed
load. The parameter assumptions are explicit and the empty-link case is
included. -/
theorem exists_candidateOK_of_degree_81 (G U : SimpleGraph V)
    (A B : Finset V) (hAB : Disjoint A B) (hbalance : A.card = B.card)
    (b lam : ℝ) (n : ℕ) (hb : 1 ≤ b) (hL : 8 ≤ Parameters.load lam n)
    (hleft : ∀ v ∈ A,
      (A.card : ℝ) / 2 + 81 * b * Parameters.load lam n ≤
        (G.neighborFinset v ∩ B).card)
    (hright : ∀ v ∈ B,
      (A.card : ℝ) / 2 + 81 * b * Parameters.load lam n ≤
        (G.neighborFinset v ∩ A).card)
    (hload : ∀ v ∈ A ∪ B,
      ((U.neighborFinset v ∩ (A ∪ B)).card : ℝ) ≤ Parameters.load lam n) :
    ∃ K : Fin (Parameters.choices b lam n) → G.Subgraph,
      CandidateOK G (Parameters.choices b lam n) (A ∪ B) U K := by
  apply exists_candidateOK_of_local_load G U A B hAB hbalance
    (Parameters.choices b lam n) (Parameters.load lam n) _ _ hload
  · intro v hv
    have hbudget := Parameters.load_add_choices_le b lam n hb hL
    have hdense := hleft v hv
    linarith
  · intro v hv
    have hbudget := Parameters.load_add_choices_le b lam n hb hL
    have hdense := hright v hv
    linarith

end Overfull.Dense.LinkPacking
