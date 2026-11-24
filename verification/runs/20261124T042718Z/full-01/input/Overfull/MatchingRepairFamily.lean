import Overfull.BipartitePackingAccounting

/-!
# Disjointness when a matching family is repaired

A new repair uses only its own original edges and reserve edges unused by
previous repairs. The actual repaired family therefore remains edge-disjoint.
-/

namespace Overfull.MatchingRepairFamily

open Finset Classical SimpleGraph
open BipartitePackingAccounting

variable {V I : Type*}

theorem fresh_disjoint_union (G R : SimpleGraph V) (M N : I → G.Subgraph)
    (T : Finset I) (i : I) (P : G.Subgraph) (hi : i ∉ T)
    (hMdisj : Pairwise (fun i j => Disjoint (M i).spanningCoe (M j).spanningCoe))
    (hMR : ∀ i, Disjoint (M i).spanningCoe R)
    (hNedges : ∀ j ∈ T, (N j).spanningCoe ≤ (M j).spanningCoe ⊔ R)
    (hP : P.spanningCoe ≤ (M i).spanningCoe ⊔
      (R \ edgeUnion (fun j => (N j).spanningCoe) T)) :
    Disjoint P.spanningCoe (edgeUnion (fun j => (N j).spanningCoe) T) := by
  apply disjoint_iff_inf_le.mpr
  intro x y hxy
  rcases hP hxy.1 with hMxy | hRxy
  · obtain ⟨j, hj, hNxy⟩ := hxy.2
    rcases hNedges j hj hNxy with hMjxy | hRxy
    · exact (hMdisj (by intro h; subst j; exact hi hj)).le_bot ⟨hMxy, hMjxy⟩
    · exact (hMR i).le_bot ⟨hMxy, hRxy⟩
  · exact hRxy.2 hxy.2

theorem update_pairwise_disjoint [DecidableEq I] (G R : SimpleGraph V) (M N : I → G.Subgraph)
    (T : Finset I) (i : I) (P : G.Subgraph) (hi : i ∉ T)
    (hMdisj : Pairwise (fun i j => Disjoint (M i).spanningCoe (M j).spanningCoe))
    (hMR : ∀ i, Disjoint (M i).spanningCoe R)
    (hNdisj : ∀ j ∈ T, ∀ k ∈ T, j ≠ k →
      Disjoint (N j).spanningCoe (N k).spanningCoe)
    (hNedges : ∀ j ∈ T, (N j).spanningCoe ≤ (M j).spanningCoe ⊔ R)
    (hP : P.spanningCoe ≤ (M i).spanningCoe ⊔
      (R \ edgeUnion (fun j => (N j).spanningCoe) T)) :
    ∀ j ∈ insert i T, ∀ k ∈ insert i T, j ≠ k →
      Disjoint (Function.update N i P j).spanningCoe
        (Function.update N i P k).spanningCoe := by
  have hPU := fresh_disjoint_union G R M N T i P hi hMdisj hMR hNedges hP
  have hPUj (j : I) (hj : j ∈ T) : Disjoint P.spanningCoe (N j).spanningCoe :=
    hPU.mono_right (by intro x y hxy; exact ⟨j, hj, hxy⟩)
  intro j hj k hk hjk
  by_cases hji : j = i
  · subst j
    have hki : k ≠ i := Ne.symm hjk
    have hkT : k ∈ T := (Finset.mem_insert.mp hk).resolve_left hki
    simpa only [Function.update_self, Function.update_of_ne hki] using hPUj k hkT
  · have hjT : j ∈ T := (Finset.mem_insert.mp hj).resolve_left hji
    by_cases hki : k = i
    · subst k
      simpa only [Function.update_self, Function.update_of_ne hji] using (hPUj j hjT).symm
    · have hkT : k ∈ T := (Finset.mem_insert.mp hk).resolve_left hki
      simpa only [Function.update_of_ne hji, Function.update_of_ne hki] using
        hNdisj j hjT k hkT hjk

end Overfull.MatchingRepairFamily
