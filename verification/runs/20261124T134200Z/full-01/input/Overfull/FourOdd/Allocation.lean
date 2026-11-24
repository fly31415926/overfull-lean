import Overfull.CircuitPatterns.IncidenceLoad

/-!
# Injective allocation with bounded endpoint conflicts

When a finite receiving pool has enough room for every requested piece and
all of one piece's forbidden endpoints, Hall's theorem allocates distinct
receivers.  The statement applies to actual endpoint supports without any
assumed matching or decomposition.
-/

noncomputable section

namespace Overfull.FourOdd

open Finset Classical CircuitPatterns

variable {V I J : Type*}

/-- A one-sided conflict bound gives a simultaneous injective choice. -/
theorem exists_injective_of_few_conflicts [Fintype I] [Fintype J]
    (R : I → J → Prop) (c : ℕ)
    (hbad : ∀ i, (univ.filter (fun j => ¬ R i j)).card ≤ c)
    (hsize : Fintype.card I + c ≤ Fintype.card J) :
    ∃ f : I ↪ J, ∀ i, R i (f i) := by
  let T : I → Finset J := fun i => univ.filter (R i)
  have hT (i : I) : Fintype.card I ≤ (T i).card := by
    have hp := filter_card_add_filter_neg_card_eq_card
      (s := (univ : Finset J)) (R i)
    have hb := hbad i
    simp only [card_univ] at hp
    dsimp only [T]
    omega
  have hHall : ∀ S : Finset I, S.card ≤ (S.biUnion T).card := by
    intro S
    by_cases hs : S.Nonempty
    · obtain ⟨i, hi⟩ := hs
      exact (card_le_univ S).trans ((hT i).trans
        (card_le_card (subset_biUnion_of_mem T hi)))
    · simp [not_nonempty_iff_eq_empty.mp hs]
  obtain ⟨f, hinj, hmem⟩ :=
    (all_card_le_biUnion_card_iff_existsInjective' T).mp hHall
  exact ⟨⟨f, hinj⟩, fun i => (mem_filter.mp (hmem i)).2⟩

/-- Allocate distinct members of a receiving family, each with endpoint
support disjoint from the corresponding requested support. -/
theorem exists_injective_disjoint_support [Fintype I] [Fintype J]
    (A : I → Finset V) (B : J → Finset V) (b D : ℕ)
    (hA : ∀ i, (A i).card ≤ b)
    (hload : ∀ v, (univ.filter (fun j => v ∈ B j)).card ≤ D)
    (hsize : Fintype.card I + b * D ≤ Fintype.card J) :
    ∃ f : I ↪ J, ∀ i, Disjoint (A i) (B (f i)) := by
  apply exists_injective_of_few_conflicts
    (fun i j => Disjoint (A i) (B j)) (b * D) _ hsize
  intro i
  convert (support_conflicts_card_le (A i) B D (fun v _ => hload v)).trans
    (Nat.mul_le_mul_right D (hA i)) using 1
  congr 1
  ext j
  simp only [mem_filter]

/-- Allocate distinct original singleton copies which extend prescribed
two-copy matchings without introducing endpoint conflicts. -/
theorem exists_matching_singleton_injection {E : Type*} [Fintype I] [Fintype E]
    (G : Multigraph V E) (M : I → Finset E) (S : Finset E) (D : ℕ)
    (hM : ∀ i, G.IsMatching (M i)) (hcard : ∀ i, (M i).card ≤ 2)
    (hdegree : ∀ v, G.degree v ≤ D)
    (hsize : Fintype.card I + 4 * D ≤ S.card) :
    ∃ f : I ↪ S, ∀ i, G.IsMatching (M i ∪ {(f i).val}) := by
  let N : S → Finset E := fun e => {e.val}
  have hdisj : Pairwise (fun e f : S => Disjoint (N e) (N f)) := by
    intro e f hne
    simpa only [N, disjoint_singleton] using
      (show e.val ≠ f.val from fun h => hne (Subtype.ext h))
  have hload (v : V) :
      (univ.filter (fun e : S => v ∈ G.edgeSupport (N e))).card ≤ D := by
    have ht := G.family_support_load_le_degreeOn N univ hdisj
      (fun _ => subset_univ _) v
    exact ht.trans (hdegree v)
  obtain ⟨f, hf⟩ := exists_injective_disjoint_support
    (fun i => G.edgeSupport (M i)) (fun e => G.edgeSupport (N e)) 4 D
    (fun i => (G.edgeSupport_card_le (M i)).trans
      (Nat.mul_le_mul_left 2 (hcard i))) hload (by simpa using hsize)
  refine ⟨f, fun i => ?_⟩
  apply isMatching_union_of_disjoint_support G (M i) (N (f i)) (hM i) _ (hf i)
  intro e he e' he' _ _ _
  exact (mem_singleton.mp he).trans (mem_singleton.mp he').symm

end Overfull.FourOdd
