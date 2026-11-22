import Overfull.FourOdd.Relabeling
import Overfull.FourOdd.OriginalGraph

/-!
# Relabeling actual quotient data

These identities transfer degrees, pair supplies and two-label cut bounds
under a permutation of the four labels. The underlying graph and every
original edge copy stay fixed.
-/

noncomputable section

namespace Overfull.FourOdd

open Finset Classical Compression CircuitPatterns

variable {V E : Type*}

def Decomposition.congrLabel {G : Multigraph V E} {L K : E → LabelPair}
    {C : Finset E} {h : ℕ} (P : Decomposition G L C h) (heq : ∀ e, L e = K e) :
    Decomposition G K C h := (funext heq) ▸ P

theorem relabel_join (G : Multigraph V E) (label : V → Fin 4)
    (hjoin : ∀ e, label (G.firstEnd e) ≠ label (G.secondEnd e))
    (σ : Equiv.Perm (Fin 4)) (e : E) :
    σ (label (G.firstEnd e)) ≠ σ (label (G.secondEnd e)) :=
  fun h => hjoin e (σ.injective h)

variable [Fintype E]

theorem relabel_quotient_degree (G : Multigraph V E) (label : V → Fin 4)
    (hjoin : ∀ e, label (G.firstEnd e) ≠ label (G.secondEnd e))
    (σ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    (G.labelQuotient (fun v => σ (label v)) (relabel_join G label hjoin σ)).degree i =
      (G.labelQuotient label hjoin).degree (σ.symm i) := by
  unfold Multigraph.degree Multigraph.incidenceEdges
  congr 1
  ext e
  simp only [mem_filter, mem_univ, true_and,
    Multigraph.labelQuotient_incident_iff, σ.apply_eq_iff_eq_symm_apply]

theorem relabel_quotient_pairPool (G : Multigraph V E) (label : V → Fin 4)
    (hjoin : ∀ e, label (G.firstEnd e) ≠ label (G.secondEnd e))
    (σ : Equiv.Perm (Fin 4)) (p : LabelPair) :
    pairPool (G.labelQuotient (fun v => σ (label v)) (relabel_join G label hjoin σ)) p =
      pairPool (G.labelQuotient label hjoin) (relabelPair σ.symm p) := by
  ext e
  simp only [mem_pairPool]
  rw [labelQuotient_edgeLabelPair_relabel G label σ hjoin (relabel_join G label hjoin σ)]
  exact (relabelPair σ).apply_eq_iff_eq_symm_apply

theorem relabel_quotient_cut_pair (G : Multigraph V E) (label : V → Fin 4)
    (hjoin : ∀ e, label (G.firstEnd e) ≠ label (G.secondEnd e))
    (σ : Equiv.Perm (Fin 4)) (i j : Fin 4) :
    (G.labelQuotient (fun v => σ (label v)) (relabel_join G label hjoin σ)).cutOn
        univ {i, j} =
      (G.labelQuotient label hjoin).cutOn univ {σ.symm i, σ.symm j} := by
  ext e
  simp only [labelQuotient_mem_cutOn_iff, mem_insert, mem_singleton,
    σ.apply_eq_iff_eq_symm_apply]

/-- Return a renamed quotient decomposition to the original part names. -/
def Decomposition.unrelabel (G : Multigraph V E) (label : V → Fin 4)
    (hjoin : ∀ e, label (G.firstEnd e) ≠ label (G.secondEnd e))
    (σ : Equiv.Perm (Fin 4)) {C : Finset E} {h : ℕ}
    (P : Decomposition G
      (G.labelQuotient (fun v => σ (label v)) (relabel_join G label hjoin σ)).edgeLabelPair
      C h) : Decomposition G (G.labelQuotient label hjoin).edgeLabelPair C h := by
  apply (P.relabel σ.symm).congrLabel
  intro e
  rw [labelQuotient_edgeLabelPair_relabel G label σ hjoin]
  exact (relabelPair σ).symm_apply_apply _

end Overfull.FourOdd
