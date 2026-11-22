import Overfull.BipartitePackingHistory
import Overfull.BipartitePackingOnline

/-!
# A total finite choice history for link matchings

Each round chooses from a family of disjoint candidate matchings avoiding all
previously used edges. If no such family exists, every candidate is empty.
The experiment is therefore defined at every history. Matching and edge
disjointness hold throughout; graph degree bounds will prove completeness
on the good event.
-/

noncomputable section

namespace Overfull.Dense.LinkPacking

open Finset Classical SimpleGraph BipartitePackingAccounting

variable {V : Type*}

def used (G : SimpleGraph V) {s : ℕ} (H : Fin s → G.Subgraph) : SimpleGraph V :=
  edgeUnion (fun i => (H i).spanningCoe) univ

def CandidateOK (G : SimpleGraph V) (t : ℕ) (Y : Finset V) (U : SimpleGraph V)
    (K : Fin t → G.Subgraph) : Prop :=
  (∀ j, (K j).IsMatching ∧ (K j).verts = (↑Y : Set V) ∧
    Disjoint (K j).spanningCoe U) ∧
  Pairwise (fun i j => Disjoint (K i).spanningCoe (K j).spanningCoe)

def candidates (G : SimpleGraph V) (t : ℕ) (Y : Finset V) (U : SimpleGraph V) :
    Fin t → G.Subgraph :=
  if h : ∃ K, CandidateOK G t Y U K then Classical.choose h else fun _ => ⊥

theorem candidates_spec (G : SimpleGraph V) (t : ℕ) (Y : Finset V)
    (U : SimpleGraph V) (h : ∃ K, CandidateOK G t Y U K) :
    CandidateOK G t Y U (candidates G t Y U) := by
  unfold candidates
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem candidates_of_not_exists (G : SimpleGraph V) (t : ℕ) (Y : Finset V)
    (U : SimpleGraph V) (h : ¬ ∃ K, CandidateOK G t Y U K) :
    candidates G t Y U = fun _ => ⊥ := by
  simp only [candidates, dif_neg h]

theorem candidates_matching (G : SimpleGraph V) (t : ℕ) (Y : Finset V)
    (U : SimpleGraph V) (j : Fin t) : (candidates G t Y U j).IsMatching := by
  by_cases h : ∃ K, CandidateOK G t Y U K
  · exact (candidates_spec G t Y U h).1 j |>.1
  · rw [candidates_of_not_exists G t Y U h]
    intro v hv
    exact False.elim hv

theorem candidates_verts_subset (G : SimpleGraph V) (t : ℕ) (Y : Finset V)
    (U : SimpleGraph V) (j : Fin t) :
    (candidates G t Y U j).verts ⊆ (↑Y : Set V) := by
  by_cases h : ∃ K, CandidateOK G t Y U K
  · rw [(candidates_spec G t Y U h).1 j |>.2.1]
  · rw [candidates_of_not_exists G t Y U h]
    exact Set.empty_subset _

theorem candidates_avoid (G : SimpleGraph V) (t : ℕ) (Y : Finset V)
    (U : SimpleGraph V) (j : Fin t) :
    Disjoint (candidates G t Y U j).spanningCoe U := by
  by_cases h : ∃ K, CandidateOK G t Y U K
  · exact (candidates_spec G t Y U h).1 j |>.2.2
  · rw [candidates_of_not_exists G t Y U h]
    exact disjoint_bot_left

theorem candidates_disjoint (G : SimpleGraph V) (t : ℕ) (Y : Finset V)
    (U : SimpleGraph V) :
    Pairwise (fun i j => Disjoint (candidates G t Y U i).spanningCoe
      (candidates G t Y U j).spanningCoe) := by
  by_cases h : ∃ K, CandidateOK G t Y U K
  · exact (candidates_spec G t Y U h).2
  · rw [candidates_of_not_exists G t Y U h]
    intro i j _
    exact disjoint_bot_left

def history (G : SimpleGraph V) (t : ℕ) (Y : ℕ → Finset V) :
    (s : ℕ) → (Fin s → Fin t) → Fin s → G.Subgraph
  | 0, _ => Fin.elim0
  | s + 1, ω =>
      let H := history G t Y s (Fin.init ω)
      Fin.snoc H (candidates G t (Y s) (used G H) (ω (Fin.last s)))

@[simp] theorem history_snoc (G : SimpleGraph V) (t : ℕ) (Y : ℕ → Finset V)
    (s : ℕ) (ω : Fin s → Fin t) (j : Fin t) :
    history G t Y (s + 1) (Fin.snoc ω j) =
      Fin.snoc (history G t Y s ω)
        (candidates G t (Y s) (used G (history G t Y s ω)) j) := by
  simp only [history, Fin.init_snoc, Fin.snoc_last]

theorem history_matching (G : SimpleGraph V) (t : ℕ) (Y : ℕ → Finset V)
    (s : ℕ) (ω : Fin s → Fin t) : ∀ i, (history G t Y s ω i).IsMatching := by
  induction s with
  | zero => intro i; exact Fin.elim0 i
  | succ s ih =>
    exact BipartitePackingHistory.matching_snoc G
      (history G t Y s (Fin.init ω))
      (candidates G t (Y s) (used G (history G t Y s (Fin.init ω))) (ω (Fin.last s)))
      (ih _) (candidates_matching _ _ _ _ _)

theorem history_disjoint (G : SimpleGraph V) (t : ℕ) (Y : ℕ → Finset V)
    (s : ℕ) (ω : Fin s → Fin t) :
    Pairwise (fun i j => Disjoint (history G t Y s ω i).spanningCoe
      (history G t Y s ω j).spanningCoe) := by
  induction s with
  | zero => intro i; exact Fin.elim0 i
  | succ s ih =>
    exact BipartitePackingHistory.pairwise_disjoint_snoc G
      (history G t Y s (Fin.init ω))
      (candidates G t (Y s) (used G (history G t Y s (Fin.init ω))) (ω (Fin.last s)))
      (ih _) (candidates_avoid _ _ _ _ _)

end Overfull.Dense.LinkPacking
