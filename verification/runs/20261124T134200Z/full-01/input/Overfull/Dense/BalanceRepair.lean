import Overfull.Dense.BalanceRepair.Routing
import Overfull.Dense.BalanceRepair.Graph
import Overfull.Dense.BalanceRepair.Cancellation
import Overfull.Dense.BalanceRepairBounds

/-!
# Integer balance repair in a dense tripartite graph

For Lemma 5.11, actual short routes cancel the cyclic degree imbalance.
A finite maximum-state argument controls internal uses of every vertex.
The selected arcs form an actual deletion subgraph, and their complement
is locally balanced. All constants are chosen before the graph.
-/

namespace Overfull.Dense.BalanceRepair

open Finset Classical
open scoped BigOperators

theorem positive_balance_sum_le {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (V × V)) (n : ℕ) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (hcard : Fintype.card V ≤ 4*n)
    (hbalance : ∀ v, |(arcBalance E v : ℝ)| ≤ ξ*n) :
    (∑ v : V, ((arcBalance E v).toNat : ℝ)) ≤ 4*ξ*(n : ℝ)^2 := by
  have hpositive (v : V) : ((arcBalance E v).toNat : ℝ) ≤ ξ*n := by
    apply le_trans _ (hbalance v)
    by_cases h : 0 ≤ arcBalance E v
    · have heq : ((arcBalance E v).toNat : ℝ) = arcBalance E v := by
        exact_mod_cast Int.toNat_of_nonneg h
      rw [heq]
      exact le_abs_self _
    · have heq : (arcBalance E v).toNat = 0 := by omega
      rw [heq, Nat.cast_zero]
      exact abs_nonneg _
  calc
    _ ≤ ∑ _v : V, ξ*n := Finset.sum_le_sum (fun v _ => hpositive v)
    _ = (Fintype.card V : ℝ)*(ξ*n) := by simp
    _ ≤ (4*(n : ℝ))*(ξ*n) := mul_le_mul_of_nonneg_right
      (by exact_mod_cast hcard) (by positivity)
    _ = _ := by ring

end Overfull.Dense.BalanceRepair

namespace Overfull

open Finset Classical
open Dense.BalanceRepair
open scoped BigOperators

/-- Integer balance repair by deleting actual edges. The constants precede
the graph; after fixing the error parameter, one order threshold works for
all graphs satisfying the stated part-size and density conditions. -/
theorem dense_balance_repair (η : ℝ) (hη : 0 < η) :
    ∃ c₀ c₁ ξ₀ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ 0 < ξ₀ ∧
      ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ → ∃ n₀ : ℕ,
        ∀ (A B W : Type*) [Fintype A] [Fintype B] [Fintype W]
          [DecidableEq A] [DecidableEq B] [DecidableEq W]
          (G : TripartiteGraph A B W),
          n₀ ≤ Fintype.card A → Fintype.card A = Fintype.card B →
          (Fintype.card A : ℝ)/2 ≤ Fintype.card W →
          (Fintype.card W : ℝ) ≤ 2*Fintype.card A →
          (∀ a, (1/2+η)*Fintype.card A ≤ ((G.neighborsB a).card : ℝ)) →
          (∀ b, (1/2+η)*Fintype.card A ≤ ((G.neighborsA b).card : ℝ)) →
          (∀ a, (Fintype.card W : ℝ)-(G.neighborsWA a).card ≤ c₀*Fintype.card A) →
          (∀ b, (Fintype.card W : ℝ)-(G.neighborsWB b).card ≤ c₀*Fintype.card A) →
          (∀ w, (Fintype.card A : ℝ)-(G.linkA w).card ≤ c₀*Fintype.card A) →
          (∀ w, (Fintype.card B : ℝ)-(G.linkB w).card ≤ c₀*Fintype.card A) →
          (∀ v, |(arcBalance (arcSet G) v : ℝ)| ≤ ξ*Fintype.card A) →
          ∃ Hdel H : TripartiteGraph A B W,
            Hdel.toSimpleGraph ≤ G.toSimpleGraph ∧
            H.toSimpleGraph = G.toSimpleGraph \ Hdel.toSimpleGraph ∧
            H.IsLocallyBalanced ∧
            ∀ v, (Hdel.toSimpleGraph.degree v : ℝ) ≤ c₁*Real.sqrt ξ*Fintype.card A := by
  let c₀ := min η 1 / 1000
  let ξ₀ := (c₀/100)^2
  obtain ⟨hc₀,_hcη,hc₀small,hξ₀,hthreshold⟩ := Dense.BalanceRepairBounds.thresholds η hη
  refine ⟨c₀,5,ξ₀,hc₀,by norm_num,hξ₀,?_⟩
  intro ξ hξ hξsmall
  obtain ⟨n₀,hn₀⟩ := hthreshold ξ hξ hξsmall
  refine ⟨n₀,?_⟩
  intro A B W _ _ _ _ _ _ G horder hAB hWlower hWupper
    hdegreeA hdegreeB hmissingA hmissingB hmissingWA hmissingWB himbalance
  let n := Fintype.card A
  let E := arcSet G
  let L := Nat.ceil (Real.sqrt ξ*n)
  let s := Real.sqrt ξ*n
  let D := 5*s
  let k := 16*s
  obtain ⟨hn,hs,_hsqrt,hscaled,hL,_hLupper,_hendpoint,hsaturation,hdegree,
    _hsatSmall,_hdegreeSmall⟩ := hn₀ n horder
  have hD : 2*(L : ℝ)+ξ*n ≤ D := by
    simpa only [D,s,mul_assoc] using hdegree
  have hSat : 16*ξ*(n : ℝ)^2/L ≤ k := by
    simpa only [k,s,mul_assoc] using hsaturation
  have hBcard : Fintype.card B = n := hAB.symm
  have hWcard : Fintype.card W ≤ 2*n := by exact_mod_cast hWupper
  have hVcard : Fintype.card (Vertex A B W) ≤ 4*n := by
    rw [Fintype.card_sum,Fintype.card_sum,hBcard]
    change n+(n+Fintype.card W) ≤ 4*n
    omega
  have hMass : (positiveMass E : ℝ) ≤ 4*ξ*(n : ℝ)^2 := by
    simpa only [positiveMass,Nat.cast_sum] using
      positive_balance_sum_le E n ξ hξ.le hVcard himbalance
  have state_degree (F : Finset (Vertex A B W × Vertex A B W))
      (hF : CancellationState E L F) (v : Vertex A B W) :
      (arcOut F v : ℝ)+arcIn F v ≤ D := by
    have hh : (arcOut F v : ℝ)+arcIn F v ≤
        2*(L : ℝ)+(arcBalance E v).natAbs := by
      exact_mod_cast hF.deleted_degree_le v
    rw [Int.cast_natAbs, Int.cast_abs] at hh
    exact hh.trans ((add_le_add_left (himbalance v) _).trans hD)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnum := Dense.BalanceRepairBounds.routing_bounds (n : ℝ) c₀ s D η
    hnR hc₀small hs hscaled (by dsimp [D]; exact le_rfl) hη.le
  have hroute : ∀ F : Finset (Vertex A B W × Vertex A B W),
      CancellationState E L F → ∀ u v,
      arcBalance F u < arcBalance E u → arcBalance E v < arcBalance F v →
      ∃ P : RoutingPath (E \ F) u v, Disjoint P.internal (saturated F L) := by
    intro F hF u v hu hv
    have hne : u ≠ v := by intro h; subst v; omega
    have hforbidden : ((saturated F L).card : ℝ) ≤ k := by
      calc
        _ ≤ 4*(4*ξ*(n : ℝ)^2)/L := hF.saturated_card_bound hL _ hMass
        _ = 16*ξ*(n : ℝ)^2/L := by ring
        _ ≤ k := hSat
    have hconditions : RoutingConditions (eraseArcs G F) (c₀*n+D) k :=
      routingConditions_after_deletion G F hF.subset n η c₀ D k rfl hBcard hWlower
        (by dsimp [D,s]; positivity) (by dsimp [k]; linarith [hnum.1,hnR])
        hnum.2.1 hnum.2.2 hdegreeA hdegreeB hmissingA hmissingB hmissingWA hmissingWB
        (state_degree F hF)
    have hpath := exists_routing_path (eraseArcs G F) (c₀*n+D) k hconditions
      (saturated F L) hforbidden u v hne
    rw [arcSet_eraseArcs] at hpath
    exact hpath
  obtain ⟨F,hF,hbalanceF⟩ := exists_balanced_deletion E L hroute
  have hbalanced : (eraseArcs G F).IsLocallyBalanced := by
    apply (locallyBalanced_iff _).mpr
    intro v
    rw [arcSet_eraseArcs,arcBalance_sdiff (arcSet G) F hF.subset v,hbalanceF v,sub_self]
  refine ⟨selectArcs G F,eraseArcs G F,selectArcs_le G F,eraseArcs_eq_sdiff G F,
    hbalanced,?_⟩
  intro v
  rw [selectArcs_degree G F hF.subset v,Nat.cast_add]
  calc
    _ ≤ D := state_degree F hF v
    _ = 5*Real.sqrt ξ*Fintype.card A := by dsimp [D,s,n]; ring

end Overfull
