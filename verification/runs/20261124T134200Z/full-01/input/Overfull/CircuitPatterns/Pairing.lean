import Overfull.MatchingPolytope
import Overfull.CompatibleCircuits.Basic
import Mathlib.Combinatorics.Hall.Finite

/-!
# Pairing small supports without endpoint conflicts

A support of size at most `b` meets at most `b * a` members of a
family in which every vertex occurs at most `a` times. For two equally
large families, Hall's theorem therefore pairs disjoint supports whenever
the common family size is greater than `2 * b * a`.

The multigraph corollary uses actual edge copies: the union of each paired
pair is an actual matching. This is the Hall pairing component of the
four-odd-parts argument, not the circuit-decomposition theorem.
-/

noncomputable section

namespace Overfull.CircuitPatterns

open Finset Classical
open scoped BigOperators

variable {V I J : Type*}

/-- The number of family members meeting a finite support is bounded by
the sum of the vertex loads on that support. -/
theorem support_conflicts_card_le [Fintype J]
    (A : Finset V) (B : J → Finset V) (a : ℕ)
    (hload : ∀ v ∈ A, (univ.filter (fun j => v ∈ B j)).card ≤ a) :
    (univ.filter (fun j => ¬ Disjoint A (B j))).card ≤ A.card * a := by
  have hsub : (univ.filter (fun j => ¬ Disjoint A (B j))) ⊆
      A.biUnion (fun v => univ.filter (fun j => v ∈ B j)) := by
    intro j hj
    obtain ⟨v, hvA, hvB⟩ := Finset.not_disjoint_iff.mp (mem_filter.mp hj).2
    exact mem_biUnion.mpr ⟨v, hvA, mem_filter.mpr ⟨mem_univ _, hvB⟩⟩
  calc
    _ ≤ (A.biUnion (fun v => univ.filter (fun j => v ∈ B j))).card :=
      card_le_card hsub
    _ ≤ ∑ v ∈ A, (univ.filter (fun j => v ∈ B j)).card := card_biUnion_le
    _ ≤ ∑ _v ∈ A, a := sum_le_sum hload
    _ = A.card * a := by simp

/-- A balanced finite relation has a bijective choice if every element on
either side has at most `c` forbidden partners and the common order exceeds
`2 * c`. This proves Hall's condition from the two conflict bounds. -/
theorem exists_equiv_of_few_conflicts [Fintype I] [Fintype J]
    (R : I → J → Prop) (c : ℕ)
    (hcard : Fintype.card I = Fintype.card J)
    (hleft : ∀ i, (univ.filter (fun j => ¬ R i j)).card ≤ c)
    (hright : ∀ j, (univ.filter (fun i => ¬ R i j)).card ≤ c)
    (hsize : 2 * c < Fintype.card I) :
    ∃ f : I ≃ J, ∀ i, R i (f i) := by
  let T : I → Finset J := fun i => univ.filter (R i)
  have hT (i : I) : Fintype.card J ≤ (T i).card + c := by
    have hpartition := filter_card_add_filter_neg_card_eq_card (s := (univ : Finset J)) (R i)
    have hbound := hleft i
    simp only [card_univ] at hpartition
    dsimp only [T]
    omega
  have hHall : ∀ S : Finset I, S.card ≤ (S.biUnion T).card := by
    intro S
    by_cases hS : S.Nonempty
    · by_cases hsmall : S.card ≤ c
      · obtain ⟨i, hi⟩ := hS
        have hsubset := card_le_card (subset_biUnion_of_mem T hi)
        have hdegree := hT i
        omega
      · have hfull : S.biUnion T = univ := by
          apply eq_univ_iff_forall.mpr
          intro j
          by_contra hj
          have hsub : S ⊆ univ.filter (fun i => ¬ R i j) := by
            intro i hi
            refine mem_filter.mpr ⟨mem_univ _, ?_⟩
            intro hij
            exact hj (mem_biUnion.mpr ⟨i, hi, mem_filter.mpr ⟨mem_univ _, hij⟩⟩)
          exact hsmall ((card_le_card hsub).trans (hright j))
        rw [hfull, card_univ, ← hcard]
        exact card_le_univ S
    · simp [not_nonempty_iff_eq_empty.mp hS]
  obtain ⟨f, hinj, hmem⟩ :=
    (all_card_le_biUnion_card_iff_existsInjective' T).mp hHall
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩
  exact ⟨Equiv.ofBijective f hbij, fun i => (mem_filter.mp (hmem i)).2⟩

/-- Two equally large families of small finite supports can be paired by
a bijection so that each paired pair is disjoint. No graph assumptions or
pairwise disjointness within either family are required. -/
theorem exists_disjoint_support_equiv [Fintype I] [Fintype J]
    (A : I → Finset V) (B : J → Finset V) (b a : ℕ)
    (hcard : Fintype.card I = Fintype.card J)
    (hA : ∀ i, (A i).card ≤ b) (hB : ∀ j, (B j).card ≤ b)
    (hloadA : ∀ v, (univ.filter (fun i => v ∈ A i)).card ≤ a)
    (hloadB : ∀ v, (univ.filter (fun j => v ∈ B j)).card ≤ a)
    (hsize : 2 * b * a < Fintype.card I) :
    ∃ f : I ≃ J, ∀ i, Disjoint (A i) (B (f i)) := by
  apply exists_equiv_of_few_conflicts (fun i j => Disjoint (A i) (B j)) (b * a) hcard
  · intro i
    convert (support_conflicts_card_le (A i) B a (fun v _ => hloadB v)).trans
      (Nat.mul_le_mul_right a (hA i)) using 1
    congr 1
    ext j
    simp only [mem_filter]
  · intro j
    have hh := (support_conflicts_card_le (B j) A a (fun v _ => hloadA v)).trans
      (Nat.mul_le_mul_right a (hB j))
    convert hh using 1
    congr 1
    ext i
    simp only [mem_filter, disjoint_comm]
  · simpa only [Nat.mul_assoc] using hsize

variable {E : Type*}

/-- Disjoint endpoint supports make the union of two actual edge-copy
matchings an actual matching. Parallel copies retain their identities. -/
theorem isMatching_union_of_disjoint_support (G : Multigraph V E)
    (M N : Finset E) (hM : G.IsMatching M) (hN : G.IsMatching N)
    (hdisjoint : Disjoint (G.edgeSupport M) (G.edgeSupport N)) :
    G.IsMatching (M ∪ N) := by
  intro e he f hf v hev hfv
  rcases mem_union.mp he with he | he <;> rcases mem_union.mp hf with hf | hf
  · exact hM e he f hf v hev hfv
  · exact (Finset.disjoint_left.mp hdisjoint
      ((G.mem_edgeSupport M v).mpr ⟨e, he, hev⟩)
      ((G.mem_edgeSupport N v).mpr ⟨f, hf, hfv⟩)).elim
  · exact (Finset.disjoint_left.mp hdisjoint
      ((G.mem_edgeSupport M v).mpr ⟨f, hf, hfv⟩)
      ((G.mem_edgeSupport N v).mpr ⟨e, he, hev⟩)).elim
  · exact hN e he f hf v hev hfv

/-- Hall pairing for two equally large families of actual edge-copy
matchings. Both the endpoint disjointness and matching unions are outputs. -/
theorem exists_matching_pairing [Fintype I] [Fintype J]
    (G : Multigraph V E) (M : I → Finset E) (N : J → Finset E) (b a : ℕ)
    (hcard : Fintype.card I = Fintype.card J)
    (hM : ∀ i, G.IsMatching (M i)) (hN : ∀ j, G.IsMatching (N j))
    (hsizeM : ∀ i, (G.edgeSupport (M i)).card ≤ b)
    (hsizeN : ∀ j, (G.edgeSupport (N j)).card ≤ b)
    (hloadM : ∀ v, (univ.filter (fun i => v ∈ G.edgeSupport (M i))).card ≤ a)
    (hloadN : ∀ v, (univ.filter (fun j => v ∈ G.edgeSupport (N j))).card ≤ a)
    (hsize : 2 * b * a < Fintype.card I) :
    ∃ f : I ≃ J,
      (∀ i, Disjoint (G.edgeSupport (M i)) (G.edgeSupport (N (f i)))) ∧
      ∀ i, G.IsMatching (M i ∪ N (f i)) := by
  obtain ⟨f, hf⟩ := exists_disjoint_support_equiv
    (fun i => G.edgeSupport (M i)) (fun j => G.edgeSupport (N j)) b a
    hcard hsizeM hsizeN hloadM hloadN hsize
  exact ⟨f, hf, fun i => isMatching_union_of_disjoint_support G (M i) (N (f i))
    (hM i) (hN (f i)) (hf i)⟩

/-- The six-endpoint specialization used for the two path families in
Lemma 4.15. The strict hypothesis is the manuscript's `12 * a < u`. -/
theorem exists_six_endpoint_pairing (G : Multigraph V E) (u a : ℕ)
    (M N : Fin u → Finset E)
    (hM : ∀ i, G.IsMatching (M i)) (hN : ∀ i, G.IsMatching (N i))
    (hsizeM : ∀ i, (G.edgeSupport (M i)).card ≤ 6)
    (hsizeN : ∀ i, (G.edgeSupport (N i)).card ≤ 6)
    (hloadM : ∀ v, (univ.filter (fun i => v ∈ G.edgeSupport (M i))).card ≤ a)
    (hloadN : ∀ v, (univ.filter (fun i => v ∈ G.edgeSupport (N i))).card ≤ a)
    (hsize : 12 * a < u) :
    ∃ f : Equiv.Perm (Fin u),
      (∀ i, Disjoint (G.edgeSupport (M i)) (G.edgeSupport (N (f i)))) ∧
      ∀ i, G.IsMatching (M i ∪ N (f i)) := by
  exact exists_matching_pairing G M N 6 a rfl hM hN hsizeM hsizeN hloadM hloadN
    (by simpa only [Fintype.card_fin, Nat.reduceMul] using hsize)

end Overfull.CircuitPatterns
