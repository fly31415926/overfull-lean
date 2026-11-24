import Overfull.NativeReserve.Residual
import Overfull.BoundedExterior.ColorFactorization

/-!
# Reassembly on the original edge copies

A disjoint family of actual matchings and a coloring of its actual residual
give a coloring of the original multigraph. The first palette retains the
matching indices, and the residual labels are shifted by its length. In a
regular host, the resulting color classes form an exact one-factorization.
-/

noncomputable section

namespace Overfull.NativeTerminal

open Finset Classical NativeReserve

variable {V E : Type*} {q k : ℕ}

/-- The label of a prefix matching in the joined palette. -/
def prefixLabel (k : ℕ) (i : Fin q) : Fin (q + k) := i.castAdd k

/-- A residual label shifted beyond every prefix label. -/
def residualLabel (q : ℕ) (j : Fin k) : Fin (q + k) := Fin.natAdd q j

theorem prefixLabel_injective (k : ℕ) : Function.Injective (@prefixLabel q k) := by
  intro i j h
  have hv := congrArg Fin.val h
  exact Fin.ext hv

theorem residualLabel_injective (q : ℕ) : Function.Injective (@residualLabel k q) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change q + i.val = q + j.val at hv
  omega

theorem prefixLabel_ne_residualLabel (i : Fin q) (j : Fin k) :
    prefixLabel k i ≠ residualLabel q j := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = q + j.val at hv
  have hi := i.isLt
  omega

/-- Select the index of an actually removed original copy. -/
def prefixIndex (M : Fin q → Finset E) (e : removedCopies M univ) : Fin q :=
  Classical.choose ((mem_removedCopies M univ e.val).mp e.property)

theorem prefixIndex_mem (M : Fin q → Finset E) (e : removedCopies M univ) :
    e.val ∈ M (prefixIndex M e) :=
  (Classical.choose_spec ((mem_removedCopies M univ e.val).mp e.property)).2

theorem prefixIndex_eq (M : Fin q → Finset E)
    (hdisj : Pairwise (fun i j => Disjoint (M i) (M j)))
    (e : removedCopies M univ) (i : Fin q) (he : e.val ∈ M i) :
    prefixIndex M e = i := by
  by_contra hne
  exact disjoint_left.mp (hdisj hne) (prefixIndex_mem M e) he

/-- Reassemble a coloring without changing or identifying original copies. -/
def reassembledColoring (G : Multigraph V E) (M : Fin q → Finset E)
    (hmatch : ∀ i, G.IsMatching (M i))
    (c : (residualGraph G M univ).EdgeColoring k) : G.EdgeColoring (q + k) where
  color e := if he : e ∈ removedCopies M univ then
    prefixLabel k (prefixIndex M ⟨e, he⟩)
    else residualLabel q (c.color ⟨e, he⟩)
  proper := by
    intro e f v hef hev hfv
    by_cases he : e ∈ removedCopies M univ
    · by_cases hf : f ∈ removedCopies M univ
      · have hi : prefixIndex M ⟨e, he⟩ = prefixIndex M ⟨f, hf⟩ := by
          apply prefixLabel_injective k
          simpa only [dif_pos he, dif_pos hf] using hef
        have hfm : f ∈ M (prefixIndex M ⟨e, he⟩) := by
          rw [hi]
          exact prefixIndex_mem M ⟨f, hf⟩
        exact hmatch _ e (prefixIndex_mem M ⟨e, he⟩) f hfm v hev hfv
      · have hp : prefixLabel k (prefixIndex M ⟨e, he⟩) =
            residualLabel q (c.color ⟨f, hf⟩) := by
          simpa only [dif_pos he, dif_neg hf] using hef
        exact (prefixLabel_ne_residualLabel _ _ hp).elim
    · by_cases hf : f ∈ removedCopies M univ
      · have hp : prefixLabel k (prefixIndex M ⟨f, hf⟩) =
            residualLabel q (c.color ⟨e, he⟩) := by
          simpa only [dif_neg he, dif_pos hf] using hef.symm
        exact (prefixLabel_ne_residualLabel _ _ hp).elim
      · have hc : c.color ⟨e, he⟩ = c.color ⟨f, hf⟩ := by
          apply residualLabel_injective q
          simpa only [dif_neg he, dif_neg hf] using hef
        exact congrArg Subtype.val (c.proper hc hev hfv)

theorem reassembledColoring_prefix (G : Multigraph V E) (M : Fin q → Finset E)
    (hmatch : ∀ i, G.IsMatching (M i))
    (hdisj : Pairwise (fun i j => Disjoint (M i) (M j)))
    (c : (residualGraph G M univ).EdgeColoring k)
    (i : Fin q) (e : E) (he : e ∈ M i) :
    (reassembledColoring G M hmatch c).color e = prefixLabel k i := by
  have heM : e ∈ removedCopies M univ :=
    (mem_removedCopies M univ e).mpr ⟨i, mem_univ _, he⟩
  simp only [reassembledColoring, dif_pos heM]
  exact congrArg (prefixLabel k) (prefixIndex_eq M hdisj ⟨e, heM⟩ i he)

theorem reassembledColoring_residual (G : Multigraph V E) (M : Fin q → Finset E)
    (hmatch : ∀ i, G.IsMatching (M i))
    (c : (residualGraph G M univ).EdgeColoring k)
    (e : {e : E // e ∉ removedCopies M univ}) :
    (reassembledColoring G M hmatch c).color e.val = residualLabel q (c.color e) := by
  simp only [reassembledColoring, dif_neg e.property]

variable [Fintype E]

/-- Every original prefix matching is exactly its reassembled color class. -/
theorem reassembledColorClass_prefix (G : Multigraph V E) (M : Fin q → Finset E)
    (hmatch : ∀ i, G.IsMatching (M i))
    (hdisj : Pairwise (fun i j => Disjoint (M i) (M j)))
    (c : (residualGraph G M univ).EdgeColoring k) (i : Fin q) :
    (reassembledColoring G M hmatch c).colorClass (prefixLabel k i) = M i := by
  ext e
  simp only [Multigraph.EdgeColoring.colorClass, mem_filter, mem_univ, true_and]
  constructor
  · intro hc
    by_cases he : e ∈ removedCopies M univ
    · have hi : prefixIndex M ⟨e, he⟩ = i := by
        apply prefixLabel_injective k
        simpa only [reassembledColoring, dif_pos he] using hc
      rw [← hi]
      exact prefixIndex_mem M ⟨e, he⟩
    · have hbad : prefixLabel k i = residualLabel q (c.color ⟨e, he⟩) := by
        simpa only [reassembledColoring, dif_neg he] using hc.symm
      exact (prefixLabel_ne_residualLabel _ _ hbad).elim
  · exact reassembledColoring_prefix G M hmatch hdisj c i e

/-- Each remaining factor contains exactly the same surviving original copies. -/
theorem reassembledColorClass_residual (G : Multigraph V E) (M : Fin q → Finset E)
    (hmatch : ∀ i, G.IsMatching (M i))
    (c : (residualGraph G M univ).EdgeColoring k) (j : Fin k) :
    (reassembledColoring G M hmatch c).colorClass (residualLabel q j) =
      (c.colorClass j).image Subtype.val := by
  ext e
  simp only [Multigraph.EdgeColoring.colorClass, mem_filter, mem_univ, true_and,
    mem_image]
  constructor
  · intro hc
    by_cases he : e ∈ removedCopies M univ
    · have hbad : prefixLabel k (prefixIndex M ⟨e, he⟩) = residualLabel q j := by
        simpa only [reassembledColoring, dif_pos he] using hc
      exact (prefixLabel_ne_residualLabel _ _ hbad).elim
    · refine ⟨⟨e, he⟩, ?_, rfl⟩
      apply residualLabel_injective q
      simpa only [reassembledColoring, dif_neg he] using hc
  · rintro ⟨f, hf, rfl⟩
    rw [reassembledColoring_residual, hf]

/-- A supplied residual coloring constructs the full host coloring, retaining
both the exact prefix indices and the shifted residual labels. -/
theorem exists_reassembled_coloring (G : Multigraph V E) (M : Fin q → Finset E)
    (hmatch : ∀ i, G.IsMatching (M i))
    (hdisj : Pairwise (fun i j => Disjoint (M i) (M j)))
    (c : (residualGraph G M univ).EdgeColoring k) :
    ∃ d : G.EdgeColoring (q + k),
      (∀ i e, e ∈ M i → d.color e = prefixLabel k i) ∧
      (∀ e : {e : E // e ∉ removedCopies M univ},
        d.color e.val = residualLabel q (c.color e)) ∧
      (∀ i, d.colorClass (prefixLabel k i) = M i) ∧
      (∀ j, d.colorClass (residualLabel q j) = (c.colorClass j).image Subtype.val) := by
  refine ⟨reassembledColoring G M hmatch c, ?_, ?_, ?_, ?_⟩
  · exact reassembledColoring_prefix G M hmatch hdisj c
  · exact reassembledColoring_residual G M hmatch c
  · exact reassembledColorClass_prefix G M hmatch hdisj c
  · exact reassembledColorClass_residual G M hmatch c

/-- Regularity turns the reassembled coloring into an exact factorization of
the original copies; the prescribed prefix factors are preserved verbatim. -/
theorem exists_reassembled_one_factorization (G : Multigraph V E)
    (M : Fin q → Finset E) (hmatch : ∀ i, G.IsMatching (M i))
    (hdisj : Pairwise (fun i j => Disjoint (M i) (M j)))
    (c : (residualGraph G M univ).EdgeColoring k)
    (hregular : ∀ v, G.degree v = q + k) :
    ∃ F : Fin (q + k) → Finset E,
      (∀ i, G.IsPerfectMatching (F i)) ∧
      Pairwise (fun i j => Disjoint (F i) (F j)) ∧
      univ.biUnion F = univ ∧
      (∀ i, F (prefixLabel k i) = M i) ∧
      (∀ j, F (residualLabel q j) = (c.colorClass j).image Subtype.val) := by
  let d := reassembledColoring G M hmatch c
  refine ⟨d.colorClass, BoundedExterior.colorClass_isPerfectMatching d hregular,
    BoundedExterior.colorClasses_pairwise_disjoint d, BoundedExterior.colorClasses_union d,
    ?_, ?_⟩
  · exact reassembledColorClass_prefix G M hmatch hdisj c
  · exact reassembledColorClass_residual G M hmatch c

end Overfull.NativeTerminal
