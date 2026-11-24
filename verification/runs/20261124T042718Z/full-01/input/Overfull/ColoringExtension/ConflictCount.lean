import Overfull.ColoringExtension.Permutation
import Overfull.Konig
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic

/-!
# A color relabeling with sparse forbidden conflicts

The original coloring makes the source labels of any collection of edges
at a vertex distinct. Counting permutations on each selected collection,
then counting the collections and vertices, gives a relabeling with few
conflicting actual edge copies at every vertex.
-/

namespace Overfull.ColoringExtension

open Finset Classical
open scoped BigOperators

variable {V E : Type*} [Fintype E]
variable (G : Multigraph V E) {r h : ℕ} (c : G.EdgeColoring r)
  (f : Fin r ↪ Fin h) (B : E → Finset (Fin h))

/-- The actual conflicting edge copies incident with a vertex. -/
noncomputable def conflictIncidences (σ : Equiv.Perm (Fin h)) (v : V) : Finset E :=
  (G.incidenceEdges v).filter (fun e => σ (f (c.color e)) ∈ B e)

@[simp] theorem mem_conflictIncidences (σ : Equiv.Perm (Fin h)) (v : V) (e : E) :
    e ∈ conflictIncidences G c f B σ v ↔
      v ∈ G.edge e ∧ σ (f (c.color e)) ∈ B e := by
  simp [conflictIncidences]

/-- Properness supplies an injection of any selected incident edges into the
source palette, including when the original host has parallel copies. -/
def incidentSource (v : V) (S : Finset E) (hS : S ⊆ G.incidenceEdges v) : S ↪ Fin h where
  toFun e := f (c.color e.val)
  inj' := by
    intro e e' he
    apply Subtype.ext
    exact c.proper (f.injective he)
      ((G.mem_incidenceEdges v e.val).mp (hS e.property))
      ((G.mem_incidenceEdges v e'.val).mp (hS e'.property))

/-- Permutations for which every edge of a specified collection conflicts. -/
noncomputable def selectedConflicts (S : Finset E) : Finset (Equiv.Perm (Fin h)) :=
  permutationsMem (fun e : S => f (c.color e.val)) (fun e => B e.val)

omit [Fintype E] in
@[simp] theorem mem_selectedConflicts (S : Finset E) (σ : Equiv.Perm (Fin h)) :
    σ ∈ selectedConflicts G c f B S ↔ ∀ e ∈ S, σ (f (c.color e)) ∈ B e := by
  simp only [selectedConflicts, mem_permutationsMem]
  exact Subtype.forall

/-- A fixed collection of distinct incident copies has at most the factorial
fiber count times the number of possible forbidden target tuples. -/
theorem selectedConflicts_card_le (v : V) (S : Finset E)
    (hS : S ⊆ G.incidenceEdges v) (b : ℕ) (hB : ∀ e, (B e).card ≤ b) :
    (selectedConflicts G c f B S).card ≤ (h - S.card).factorial * b ^ S.card := by
  have hc := permutations_mem_card_le_pow (incidentSource G c f v S hS)
    (fun e : S => B e.val) b (fun e => hB e.val)
  simpa only [Fintype.card_fin, Fintype.card_coe] using hc

/-- A bad permutation at a vertex has at least `t` conflicting incidences. -/
noncomputable def vertexBadPermutations (t : ℕ) (v : V) : Finset (Equiv.Perm (Fin h)) :=
  univ.filter (fun σ => t ≤ (conflictIncidences G c f B σ v).card)

@[simp] theorem mem_vertexBadPermutations (t : ℕ) (v : V) (σ : Equiv.Perm (Fin h)) :
    σ ∈ vertexBadPermutations G c f B t v ↔
      t ≤ (conflictIncidences G c f B σ v).card := by
  simp [vertexBadPermutations]

/-- The union is over actual `t`-element collections of incident edge copies. -/
theorem vertexBadPermutations_eq_union (t : ℕ) (v : V) :
    vertexBadPermutations G c f B t v =
      ((G.incidenceEdges v).powersetCard t).biUnion (selectedConflicts G c f B) := by
  ext σ
  rw [mem_vertexBadPermutations, Finset.mem_biUnion]
  constructor
  · intro hσ
    obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq hσ
    have hinc : S ⊆ G.incidenceEdges v :=
      hS.trans (Finset.filter_subset _ _)
    refine ⟨S, Finset.mem_powersetCard.mpr ⟨hinc, hcard⟩, ?_⟩
    apply (mem_selectedConflicts G c f B S σ).mpr
    intro e he
    exact (Finset.mem_filter.mp (hS he)).2
  · rintro ⟨S, hS, hσ⟩
    obtain ⟨hinc, hcard⟩ := Finset.mem_powersetCard.mp hS
    have hsub : S ⊆ conflictIncidences G c f B σ v := by
      intro e he
      exact Finset.mem_filter.mpr ⟨hinc he,
        (mem_selectedConflicts G c f B S σ).mp hσ e he⟩
    rw [← hcard]
    exact Finset.card_le_card hsub

/-- Count the collections at one vertex before replacing its degree by the
larger palette bound. -/
theorem vertexBadPermutations_card_le_degree (t : ℕ) (v : V) (b : ℕ)
    (hB : ∀ e, (B e).card ≤ b) :
    (vertexBadPermutations G c f B t v).card ≤
      (G.degree v).choose t * ((h - t).factorial * b ^ t) := by
  rw [vertexBadPermutations_eq_union]
  apply Finset.card_biUnion_le.trans
  calc
    (∑ S ∈ (G.incidenceEdges v).powersetCard t, (selectedConflicts G c f B S).card) ≤
        ∑ _S ∈ (G.incidenceEdges v).powersetCard t, (h - t).factorial * b ^ t := by
      apply Finset.sum_le_sum
      intro S hS
      obtain ⟨hinc, hcard⟩ := Finset.mem_powersetCard.mp hS
      simpa only [hcard] using selectedConflicts_card_le G c f B v S hinc b hB
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul, Nat.cast_id,
        Multigraph.degree]

include c f in
/-- The target palette bounds every vertex degree, through the given proper
coloring and palette embedding. -/
theorem degree_le_target (v : V) : G.degree v ≤ h := by
  have hf : r ≤ h := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_embedding f
  exact (c.degree_le v).trans hf

theorem vertexBadPermutations_card_le (t : ℕ) (v : V) (b : ℕ)
    (hB : ∀ e, (B e).card ≤ b) :
    (vertexBadPermutations G c f B t v).card ≤
      h.choose t * ((h - t).factorial * b ^ t) := by
  apply (vertexBadPermutations_card_le_degree G c f B t v b hB).trans
  exact Nat.mul_le_mul_right _ (Nat.choose_le_choose t (degree_le_target G c f v))

variable [Fintype V]

/-- The permutations having a conflict-degree failure at some actual vertex. -/
noncomputable def badPermutations (t : ℕ) : Finset (Equiv.Perm (Fin h)) :=
  univ.biUnion (vertexBadPermutations G c f B t)

@[simp] theorem mem_badPermutations (t : ℕ) (σ : Equiv.Perm (Fin h)) :
    σ ∈ badPermutations G c f B t ↔ ∃ v, t ≤ (conflictIncidences G c f B σ v).card := by
  simp [badPermutations]

/-- An exact finite union bound; each factor counts vertices, subsets, target
tuples, or complement permutations. -/
theorem badPermutations_card_le (t b : ℕ) (hB : ∀ e, (B e).card ≤ b) :
    (badPermutations G c f B t).card ≤
      Fintype.card V * (h.choose t * ((h - t).factorial * b ^ t)) := by
  unfold badPermutations
  apply Finset.card_biUnion_le.trans
  calc
    (∑ v : V, (vertexBadPermutations G c f B t v).card) ≤
        ∑ _v : V, h.choose t * ((h - t).factorial * b ^ t) :=
      Finset.sum_le_sum (fun v _ => vertexBadPermutations_card_le G c f B t v b hB)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]

/-- Factorial cancellation proves the existence of a good permutation without
introducing a probability space or dividing a natural-number count. -/
theorem exists_sparse_conflicts_of_le (b t : ℕ) (ht : t ≤ h)
    (hB : ∀ e, (B e).card ≤ b)
    (htail : Fintype.card V * b ^ t < t.factorial) :
    ∃ σ : Equiv.Perm (Fin h), ∀ v, (conflictIncidences G c f B σ v).card < t := by
  have hcount := badPermutations_card_le G c f B t b hB
  have hscaled : t.factorial * (badPermutations G c f B t).card ≤
      (Fintype.card V * b ^ t) * h.factorial := by
    calc
      _ ≤ t.factorial * (Fintype.card V * (h.choose t * ((h - t).factorial * b ^ t))) :=
        Nat.mul_le_mul_left _ hcount
      _ = (Fintype.card V * b ^ t) *
          (h.choose t * t.factorial * (h - t).factorial) := by ring
      _ = _ := by rw [Nat.choose_mul_factorial_mul_factorial ht]
  have hstrict : t.factorial * (badPermutations G c f B t).card <
      t.factorial * h.factorial :=
    hscaled.trans_lt (Nat.mul_lt_mul_of_pos_right htail (Nat.factorial_pos h))
  have hlt : (badPermutations G c f B t).card < h.factorial :=
    (Nat.mul_lt_mul_left (Nat.factorial_pos t)).mp hstrict
  have htotal : (badPermutations G c f B t).card <
      (univ : Finset (Equiv.Perm (Fin h))).card := by
    simpa only [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] using hlt
  obtain ⟨σ, _hσuniv, hσ⟩ := Finset.exists_mem_notMem_of_card_lt_card htotal
  refine ⟨σ, ?_⟩
  intro v
  apply Nat.lt_of_not_ge
  intro hv
  exact hσ ((mem_badPermutations G c f B t σ).mpr ⟨v, hv⟩)

/-- Relabel the given proper coloring so that fewer than `t` actual incident
edge copies hit their forbidden sets at every vertex. No upper bound on `t`
is needed: the larger-than-palette case is immediate from properness. -/
theorem exists_sparse_conflicts (b t : ℕ) (_ht : 1 ≤ t)
    (hB : ∀ e, (B e).card ≤ b)
    (htail : Fintype.card V * b ^ t < t.factorial) :
    ∃ σ : Equiv.Perm (Fin h), ∀ v,
      ((G.incidenceEdges v).filter (fun e => σ (f (c.color e)) ∈ B e)).card < t := by
  by_cases hle : t ≤ h
  · exact exists_sparse_conflicts_of_le G c f B b t hle hB htail
  · refine ⟨1, ?_⟩
    intro v
    have hsub : ((G.incidenceEdges v).filter
        (fun e => (1 : Equiv.Perm (Fin h)) (f (c.color e)) ∈ B e)).card ≤ G.degree v :=
      Finset.card_le_card (Finset.filter_subset _ _)
    exact (hsub.trans (degree_le_target G c f v)).trans_lt (Nat.lt_of_not_ge hle)

end Overfull.ColoringExtension
