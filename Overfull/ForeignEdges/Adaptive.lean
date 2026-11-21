import Overfull.ForeignEdges.Incidence
import Overfull.OrdinaryPackingStrategy

/-!
# Admissible core inputs from actual partial matchings

The incidence budget is established for the enlarged partial-matching
prefix before its last matching has been completed.  Its parity is the
parity of the actual uncovered core, and its size is the actual footprint.
-/

namespace Overfull.ForeignIncidence

open Finset Classical SimpleGraph ForceMatching
open BipartitePackingAccounting

variable {V : Type*} [Fintype V]

theorem coveredCore_parity (U : Finset V) (G : SimpleGraph V) (F : G.Subgraph)
    (heven : Even (((U : Set V) \ F.verts).ncard)) :
    (coveredCore U G F).card % 2 = U.card % 2 := by
  classical
  have hc := Finset.card_add_card_compl (coveredCore U G F)
  rw [Fintype.card_coe, uncoveredCore_card] at hc
  obtain ⟨r,hr⟩ := heven
  omega

/-- A local packing history records exactly the prescribed ambient
footprints, independently of which local matchings it records. -/
theorem history_incidence_eq_footprint (U : Finset V) (G : SimpleGraph V)
    (H : SimpleGraph U) (F : ℕ → G.Subgraph) (q : ℕ)
    (hist : Fin q → Finset U × H.Subgraph)
    (hinputs : ∀ j, (hist j).1 = coveredCore U G (F j.val)) (v : U) :
    (univ.filter (fun j : Fin q => v ∈ (hist j).1)).card =
      footprintCount U G F (range q) v := by
  unfold footprintCount
  refine Finset.card_bij (fun (j : Fin q) _ => j.val) ?_ ?_ ?_
  · intro j hj
    refine mem_filter.mpr ⟨mem_range.mpr j.isLt,?_⟩
    simpa only [hinputs j] using (mem_filter.mp hj).2
  · intro i _ j _ hij
    exact Fin.val_injective hij
  · intro j hj
    have hjq := mem_range.mp (mem_filter.mp hj).1
    refine ⟨⟨j,hjq⟩,mem_filter.mpr ⟨mem_univ _,?_⟩,rfl⟩
    simpa only [hinputs ⟨j,hjq⟩] using (mem_filter.mp hj).2

/-- The next input satisfies the precise `Allowed` predicate used by the
fixed adaptive core rule.  No completion of the current partial matching
is assumed: only earlier partial matchings have ambient completions. -/
theorem allowed_of_partial_prefix (U : Finset V) (G : SimpleGraph V)
    (H : SimpleGraph U) (hH : H ≤ G.induce (U : Set V))
    (F N : ℕ → G.Subgraph) (q k : ℕ) (ε : ℝ)
    (hist : Fin q → Finset U × H.Subgraph)
    (hinputs : ∀ j, (hist j).1 = coveredCore U G (F j.val))
    (hF : ∀ j ≤ q, (F j).IsMatching)
    (hFN : ∀ j < q, (F j).spanningCoe ≤ (N j).spanningCoe)
    (hpresent : ∀ j ≤ q, (F j).spanningCoe ≤
      G \ edgeUnion (fun i => (N i).spanningCoe) (range j))
    (hno : ∀ j ≤ q, ∀ u v, u ∈ U → v ∈ U → ¬ (F j).Adj u v)
    (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ v, (k : ℝ) - ε*U.card ≤ H.degree v)
    (heven : Even (((U : Set V) \ (F q).verts).ncard))
    (hsize : ((coveredCore U G (F q)).card : ℝ) ≤ ε*U.card) :
    OrdinaryPackingStrategy.Allowed H U.card ε q hist (coveredCore U G (F q)) := by
  refine ⟨coveredCore_parity U G (F q) heven,hsize,?_⟩
  intro v
  have hcount : (footprintCount U G F (range (q+1)) v : ℝ) ≤ ε*U.card := by
    apply footprintCount_le_real_error U G H hH F (range (q+1))
      (fun j hj => hF j (by simpa only [mem_range,Nat.lt_succ_iff] using hj))
      (partial_prefix_pairwise G F N q hFN hpresent)
      (fun j hj => hno j (by simpa only [mem_range,Nat.lt_succ_iff] using hj))
      k (ε*U.card) hregular hdegree
  have hmono : footprintCount U G F (range q) v ≤
      footprintCount U G F (range (q+1)) v := by
    apply Finset.card_le_card
    intro j hj
    obtain ⟨hjq,hjv⟩ := mem_filter.mp hj
    exact mem_filter.mpr
      ⟨mem_range.mpr ((mem_range.mp hjq).trans (Nat.lt_succ_self q)),hjv⟩
  have hhist := history_incidence_eq_footprint U G H F q hist hinputs v
  have hnat := hhist.le.trans hmono
  have hreal : ((univ.filter (fun j : Fin q => v ∈ (hist j).1)).card : ℝ) ≤
      footprintCount U G F (range (q+1)) v := by exact_mod_cast hnat
  convert hreal.trans hcount using 1
  congr 2
  ext j
  simp only [mem_filter,mem_univ]

end Overfull.ForeignIncidence
