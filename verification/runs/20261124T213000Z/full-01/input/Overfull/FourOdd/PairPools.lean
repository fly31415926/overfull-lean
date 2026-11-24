import Overfull.ColoringExtension.Balance
import Overfull.SparseColoring

/-!
# Actual singleton copies and pairs in a bipartite pool

König coloring followed by equitable balancing divides a finite bipartite
edge-copy pool into any feasible prescribed number of singleton copies and
actual two-edge matchings.  The paired copies can later be viewed as parallel
circuits in a label quotient; this file does not assume such a decomposition.
-/

noncomputable section

namespace Overfull.FourOdd

open Finset Classical
open scoped BigOperators

variable {V E F : Type*}

/-- An exact partition into actual two-edge matchings. -/
structure MatchingPairPartition (G : Multigraph V E) (S : Finset E) where
  parts : Finset (Finset E)
  matching : ∀ C ∈ parts, G.IsMatching C
  card_two : ∀ C ∈ parts, C.card = 2
  disjoint : ∀ C ∈ parts, ∀ D ∈ parts, C ≠ D → Disjoint C D
  cover : parts.biUnion id = S

namespace MatchingPairPartition

variable {G : Multigraph V E} {S T : Finset E}

theorem part_subset (P : MatchingPairPartition G S) {C : Finset E}
    (hC : C ∈ P.parts) : C ⊆ S := by
  intro e he
  rw [← P.cover]
  exact mem_biUnion.mpr ⟨C, hC, he⟩

/-- The empty pool has its empty actual partition. -/
def empty (G : Multigraph V E) : MatchingPairPartition G ∅ where
  parts := ∅
  matching := by simp
  card_two := by simp
  disjoint := by simp
  cover := by simp

/-- Transport the actual copy sets through an injective endpoint-preserving map. -/
def map (P : MatchingPairPartition G S) (H : Multigraph V F)
    (f : E → F) (hinj : Function.Injective f)
    (hedge : ∀ e, H.edge (f e) = G.edge e) :
    MatchingPairPartition H (S.image f) where
  parts := P.parts.image (fun C => C.image f)
  matching := by
    intro D hD
    obtain ⟨C, hC, rfl⟩ := mem_image.mp hD
    intro x hx y hy v hxv hyv
    obtain ⟨e, he, rfl⟩ := mem_image.mp hx
    obtain ⟨e', he', rfl⟩ := mem_image.mp hy
    rw [hedge] at hxv hyv
    exact congrArg f (P.matching C hC e he e' he' v hxv hyv)
  card_two := by
    intro D hD
    obtain ⟨C, hC, rfl⟩ := mem_image.mp hD
    rw [card_image_of_injective _ hinj]
    exact P.card_two C hC
  disjoint := by
    intro C hC D hD hne
    obtain ⟨A, hA, rfl⟩ := mem_image.mp hC
    obtain ⟨B, hB, rfl⟩ := mem_image.mp hD
    have hAB : A ≠ B := by intro h; subst B; exact hne rfl
    apply disjoint_left.mpr
    intro x hxA hxB
    obtain ⟨a, ha, hax⟩ := mem_image.mp hxA
    obtain ⟨b, hb, hbx⟩ := mem_image.mp hxB
    have hab : a = b := hinj (hax.trans hbx.symm)
    subst b
    exact disjoint_left.mp (P.disjoint A hA B hB hAB) ha hb
  cover := by
    ext x
    constructor
    · intro hx
      obtain ⟨D, hD, hxD⟩ := mem_biUnion.mp hx
      obtain ⟨C, hC, rfl⟩ := mem_image.mp hD
      obtain ⟨e, he, rfl⟩ := mem_image.mp hxD
      exact mem_image.mpr ⟨e, P.part_subset hC he, rfl⟩
    · intro hx
      obtain ⟨e, he, rfl⟩ := mem_image.mp hx
      rw [← P.cover] at he
      obtain ⟨C, hC, heC⟩ := mem_biUnion.mp he
      exact mem_biUnion.mpr
        ⟨C.image f, mem_image.mpr ⟨C, hC, rfl⟩, mem_image.mpr ⟨e, heC, rfl⟩⟩

/-- Combine partitions of disjoint original copy sets. -/
def union (P : MatchingPairPartition G S) (Q : MatchingPairPartition G T)
    (hST : Disjoint S T) : MatchingPairPartition G (S ∪ T) where
  parts := P.parts ∪ Q.parts
  matching := by
    intro C hC
    rcases mem_union.mp hC with hC | hC
    · exact P.matching C hC
    · exact Q.matching C hC
  card_two := by
    intro C hC
    rcases mem_union.mp hC with hC | hC
    · exact P.card_two C hC
    · exact Q.card_two C hC
  disjoint := by
    intro C hC D hD hne
    rcases mem_union.mp hC with hC | hC <;>
      rcases mem_union.mp hD with hD | hD
    · exact P.disjoint C hC D hD hne
    · exact hST.mono (P.part_subset hC) (Q.part_subset hD)
    · exact hST.symm.mono (Q.part_subset hC) (P.part_subset hD)
    · exact Q.disjoint C hC D hD hne
  cover := by
    calc
      (P.parts ∪ Q.parts).biUnion id = P.parts.biUnion id ∪ Q.parts.biUnion id := by
        ext e
        simp only [mem_biUnion, mem_union, or_and_right, exists_or]
      _ = S ∪ T := by rw [P.cover, Q.cover]

end MatchingPairPartition

variable [Fintype V] [Fintype E]
variable {G : Multigraph V E} {k : ℕ}

omit [Fintype V] in
private theorem colorClass_disjoint (c : G.EdgeColoring k) {i j : Fin k}
    (hij : i ≠ j) : Disjoint (c.colorClass i) (c.colorClass j) := by
  apply disjoint_left.mpr
  intro e hei hej
  exact hij ((mem_filter.mp hei).2.symm.trans (mem_filter.mp hej).2)

omit [Fintype V] in
private theorem sum_colorClass_card (c : G.EdgeColoring k) :
    (∑ i : Fin k, (c.colorClass i).card) = Fintype.card E := by
  symm
  simpa only [Multigraph.EdgeColoring.colorClass, card_univ] using
    (card_eq_sum_card_fiberwise
      (s := (univ : Finset E)) (t := (univ : Finset (Fin k)))
      (fun e _ => mem_univ (c.color e)))

omit [Fintype V] in
/-- An equitable coloring whose average class size is between one and two
has only singleton and two-edge classes.  Empty palettes are permitted. -/
theorem equitable_colorClass_card_one_or_two (c : G.EdgeColoring k)
    (hlo : k ≤ Fintype.card E) (hhi : Fintype.card E ≤ 2 * k)
    (hspread : ∀ i j, |((c.colorClass i).card : ℤ) -
      ((c.colorClass j).card : ℤ)| ≤ 1) :
    ∀ i, (c.colorClass i).card = 1 ∨ (c.colorClass i).card = 2 := by
  intro i
  have hsum := sum_colorClass_card c
  have hpos : 1 ≤ (c.colorClass i).card := by
    by_contra hn
    have hi : (c.colorClass i).card = 0 := by omega
    have hall (j : Fin k) : (c.colorClass j).card ≤ 1 := by
      have hh := (abs_le.mp (hspread j i)).2
      omega
    have hlt : (∑ j : Fin k, (c.colorClass j).card) < ∑ _j : Fin k, 1 :=
      sum_lt_sum (fun j _ => hall j) ⟨i, mem_univ _, by omega⟩
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hlt
    omega
  have hle : (c.colorClass i).card ≤ 2 := by
    by_contra hn
    have hall (j : Fin k) : 2 ≤ (c.colorClass j).card := by
      have hh := (abs_le.mp (hspread i j)).2
      omega
    have hlt : (∑ _j : Fin k, 2) < ∑ j : Fin k, (c.colorClass j).card :=
      sum_lt_sum (fun j _ => hall j) ⟨i, mem_univ _, by omega⟩
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hlt
    omega
  omega

omit [Fintype V] in
/-- An equitable coloring with average class size exactly two consists
entirely of actual two-edge matching classes. -/
theorem equitable_colorClass_card_two (c : G.EdgeColoring k)
    (hcard : Fintype.card E = 2 * k)
    (hspread : ∀ i j, |((c.colorClass i).card : ℤ) -
      ((c.colorClass j).card : ℤ)| ≤ 1) :
    ∀ i, (c.colorClass i).card = 2 := by
  have h12 := equitable_colorClass_card_one_or_two c (by omega) (by omega) hspread
  intro i
  by_contra hn
  have hi : (c.colorClass i).card = 1 := (h12 i).resolve_right hn
  have hlt : (∑ j : Fin k, (c.colorClass j).card) < ∑ _j : Fin k, 2 :=
    sum_lt_sum (fun j _ => by rcases h12 j with h | h <;> omega)
      ⟨i, mem_univ _, by omega⟩
  rw [sum_colorClass_card c] at hlt
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hlt
  omega

/-- Select exactly the prescribed number of singleton copies.  Every
remaining actual copy is partitioned into two-edge matchings. -/
theorem exists_singletons_and_pairs (G : Multigraph V E) (hG : G.IsBipartite)
    (q : ℕ) (hq : q ≤ Fintype.card E)
    (hpar : Fintype.card E % 2 = q % 2)
    (hdegree : ∀ v, G.degree v ≤ (Fintype.card E + q) / 2) :
    ∃ S : Finset E, S.card = q ∧ Nonempty (MatchingPairPartition G Sᶜ) := by
  let k := (Fintype.card E + q) / 2
  have h2k : 2 * k = Fintype.card E + q := by dsimp [k]; omega
  obtain ⟨c₀⟩ := G.exists_edgeColoring_of_bipartite hG k hdegree
  obtain ⟨c, hspread⟩ := c₀.exists_equitable
  have h12 := equitable_colorClass_card_one_or_two c (by omega) (by omega) hspread
  let U : Finset (Fin k) := univ.filter (fun i => (c.colorClass i).card = 1)
  let T : Finset (Fin k) := univ.filter (fun i => (c.colorClass i).card = 2)
  let S := U.biUnion c.colorClass
  have hU (i : Fin k) : i ∈ U ↔ (c.colorClass i).card = 1 := by simp [U]
  have hT (i : Fin k) : i ∈ T ↔ (c.colorClass i).card = 2 := by simp [T]
  have hUdisj : U.toSet.PairwiseDisjoint c.colorClass := by
    intro i _ j _ hij
    exact colorClass_disjoint c hij
  have hScard : S.card = U.card := by
    dsimp [S]
    rw [card_biUnion hUdisj]
    calc
      (∑ i ∈ U, (c.colorClass i).card) = ∑ _i ∈ U, 1 :=
        sum_congr rfl (fun i hi => (hU i).mp hi)
      _ = U.card := by simp
  have hsumone : (∑ i : Fin k, if (c.colorClass i).card = 1 then 1 else 0) = U.card := by
    simp [U]
  have hpoint (i : Fin k) : (c.colorClass i).card +
      (if (c.colorClass i).card = 1 then 1 else 0) = 2 := by
    rcases h12 i with hi | hi <;> simp [hi]
  have hUcount : Fintype.card E + U.card = 2 * k := by
    calc
      Fintype.card E + U.card = (∑ i : Fin k, (c.colorClass i).card) +
          ∑ i : Fin k, (if (c.colorClass i).card = 1 then 1 else 0) := by
        rw [sum_colorClass_card c, hsumone]
      _ = ∑ i : Fin k, ((c.colorClass i).card +
          (if (c.colorClass i).card = 1 then 1 else 0)) := sum_add_distrib.symm
      _ = ∑ _i : Fin k, 2 := sum_congr rfl (fun i _ => hpoint i)
      _ = 2 * k := by simp [Nat.mul_comm]
  refine ⟨S, by omega, ⟨?_⟩⟩
  refine {
    parts := T.image c.colorClass
    matching := ?_
    card_two := ?_
    disjoint := ?_
    cover := ?_ }
  · intro C hC
    obtain ⟨i, _, rfl⟩ := mem_image.mp hC
    exact c.colorClass_isMatching i
  · intro C hC
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hC
    exact (hT i).mp hi
  · intro C hC D hD hne
    obtain ⟨i, _, rfl⟩ := mem_image.mp hC
    obtain ⟨j, _, rfl⟩ := mem_image.mp hD
    exact colorClass_disjoint c (by intro h; subst j; exact hne rfl)
  · ext e
    constructor
    · intro he
      obtain ⟨C, hC, heC⟩ := mem_biUnion.mp he
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hC
      apply mem_compl.mpr
      intro heS
      obtain ⟨j, hj, hej⟩ := mem_biUnion.mp heS
      have hij : i = j := (mem_filter.mp heC).2.symm.trans (mem_filter.mp hej).2
      have hi2 := (hT i).mp hi
      have hj1 := (hU j).mp hj
      subst j
      omega
    · intro he
      have hen : e ∉ S := mem_compl.mp he
      have hei : e ∈ c.colorClass (c.color e) := by
        simp [Multigraph.EdgeColoring.colorClass]
      have hi2 : (c.colorClass (c.color e)).card = 2 := by
        rcases h12 (c.color e) with hi1 | hi2
        · exact False.elim (hen (mem_biUnion.mpr ⟨c.color e, (hU _).mpr hi1, hei⟩))
        · exact hi2
      exact mem_biUnion.mpr ⟨c.colorClass (c.color e),
        mem_image.mpr ⟨c.color e, (hT _).mpr hi2, rfl⟩, hei⟩

/-- Safely cap a bipartite pool at `B` or `B+1`, retaining its parity.
If any copies are discarded, at least `B` actual copies remain, and the
discarded copies have a genuine partition into two-edge matchings. -/
theorem exists_capped_singletons_and_pairs (G : Multigraph V E)
    (hG : G.IsBipartite) (B : ℕ) (hdegree : ∀ v, G.degree v ≤ B) :
    ∃ S : Finset E, S.card ≤ B + 1 ∧ (S = univ ∨ B ≤ S.card) ∧
      Fintype.card E % 2 = S.card % 2 ∧ Nonempty (MatchingPairPartition G Sᶜ) := by
  let n := Fintype.card E
  let q := if n ≤ B + 1 then n else B + (n + B) % 2
  have hq : q ≤ n := by dsimp [q]; split_ifs <;> omega
  have hqcap : q ≤ B + 1 := by dsimp [q]; split_ifs <;> omega
  have hpar : n % 2 = q % 2 := by dsimp [q]; split_ifs <;> omega
  have hdegcard (v : V) : G.degree v ≤ n := by
    change (univ.filter (fun e => v ∈ G.edge e)).card ≤ Fintype.card E
    simpa only [card_univ] using
      card_le_card (filter_subset (fun e => v ∈ G.edge e) (univ : Finset E))
  have hdeg (v : V) : G.degree v ≤ (n + q) / 2 := by
    have h₁ := hdegree v
    have h₂ := hdegcard v
    dsimp [q]
    split_ifs <;> omega
  obtain ⟨S, hS, hP⟩ := exists_singletons_and_pairs G hG q hq hpar hdeg
  refine ⟨S, by omega, ?_, by simpa only [hS] using hpar, hP⟩
  by_cases hn : n ≤ B + 1
  · left
    have hqn : q = n := by simp [q, hn]
    apply eq_of_subset_of_card_le (subset_univ S)
    simpa only [card_univ, hS, hqn] using (le_refl n)
  · right
    have hBq : B ≤ q := by simp [q, hn]
    omega

omit [Fintype V] [Fintype E] in
private theorem image_subtype_compl (P : Finset E) [Fintype P] (S : Finset P) :
    Sᶜ.image Subtype.val = P \ S.image Subtype.val := by
  ext e
  constructor
  · intro he
    obtain ⟨x, hx, rfl⟩ := mem_image.mp he
    refine mem_sdiff.mpr ⟨x.property, ?_⟩
    intro hm
    obtain ⟨y, hy, hyx⟩ := mem_image.mp hm
    have hyx' : y = x := Subtype.val_injective hyx
    subst y
    exact (mem_compl.mp hx) hy
  · intro he
    obtain ⟨heP, heS⟩ := mem_sdiff.mp he
    refine mem_image.mpr ⟨⟨e, heP⟩, mem_compl.mpr ?_, rfl⟩
    intro he'
    exact heS (mem_image.mpr ⟨⟨e, heP⟩, he', rfl⟩)

omit [Fintype E] in
/-- The singleton/pair construction on a finite pool inside an ambient
graph, with every returned set expressed in the original edge-copy type. -/
theorem exists_singletons_and_pairs_on (G : Multigraph V E) (P : Finset E)
    (hP : (G.restrictEdges P).IsBipartite) (q : ℕ) (hq : q ≤ P.card)
    (hpar : P.card % 2 = q % 2)
    (hdegree : ∀ v, (G.restrictEdges P).degree v ≤ (P.card + q) / 2) :
    ∃ S : Finset E, S ⊆ P ∧ S.card = q ∧
      Nonempty (MatchingPairPartition G (P \ S)) := by
  letI : DecidableEq P := Classical.decEq _
  obtain ⟨S, hS, ⟨R⟩⟩ := exists_singletons_and_pairs (G.restrictEdges P) hP q
    (by simpa using hq) (by simpa using hpar) (by simpa using hdegree)
  refine ⟨S.image Subtype.val, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨x, _, rfl⟩ := mem_image.mp he
    exact x.property
  · rw [card_image_of_injective _ Subtype.val_injective, hS]
  · have R' := R.map G Subtype.val Subtype.val_injective (fun _ => rfl)
    refine ⟨{ R' with cover := ?_ }⟩
    rw [R'.cover]
    ext e
    constructor
    · intro he
      obtain ⟨x, hx, rfl⟩ := mem_image.mp he
      refine mem_sdiff.mpr ⟨x.property, ?_⟩
      intro hm
      obtain ⟨y, hy, hyx⟩ := mem_image.mp hm
      have hyx' : y = x := Subtype.val_injective hyx
      subst y
      exact (mem_compl.mp hx) hy
    · intro he
      obtain ⟨heP, heS⟩ := mem_sdiff.mp he
      refine mem_image.mpr ⟨⟨e, heP⟩, mem_compl.mpr ?_, rfl⟩
      intro he'
      exact heS (mem_image.mpr ⟨⟨e, heP⟩, he', rfl⟩)

omit [Fintype E] in
/-- Safe cap truncation on an ambient finite pool, retaining all original
copy identities and an actual matching-pair partition of what was removed. -/
theorem exists_capped_singletons_and_pairs_on (G : Multigraph V E) (P : Finset E)
    (hP : (G.restrictEdges P).IsBipartite) (B : ℕ)
    (hdegree : ∀ v, (G.restrictEdges P).degree v ≤ B) :
    ∃ S : Finset E, S ⊆ P ∧ S.card ≤ B + 1 ∧ (S = P ∨ B ≤ S.card) ∧
      P.card % 2 = S.card % 2 ∧ Nonempty (MatchingPairPartition G (P \ S)) := by
  letI : DecidableEq P := Classical.decEq _
  obtain ⟨S, hcap, hall, hpar, ⟨R⟩⟩ :=
    exists_capped_singletons_and_pairs (G.restrictEdges P) hP B hdegree
  have hcard : (S.image Subtype.val).card = S.card :=
    card_image_of_injective _ Subtype.val_injective
  have hsub : S.image Subtype.val ⊆ P := by
    intro e he
    obtain ⟨x, _, rfl⟩ := mem_image.mp he
    exact x.property
  refine ⟨S.image Subtype.val, hsub, by omega, ?_, ?_, ?_⟩
  · rcases hall with hall | hall
    · left
      subst S
      apply eq_of_subset_of_card_le hsub
      simp only [hcard, card_univ, Fintype.card_coe, le_refl]
    · right
      omega
  · simpa only [Fintype.card_coe, hcard] using hpar
  · have R' := R.map G Subtype.val Subtype.val_injective (fun _ => rfl)
    refine ⟨{ R' with cover := ?_ }⟩
    rw [R'.cover]
    ext e
    constructor
    · intro he
      obtain ⟨x, hx, rfl⟩ := mem_image.mp he
      refine mem_sdiff.mpr ⟨x.property, ?_⟩
      intro hm
      obtain ⟨y, hy, hyx⟩ := mem_image.mp hm
      have hyx' : y = x := Subtype.val_injective hyx
      subst y
      exact (mem_compl.mp hx) hy
    · intro he
      obtain ⟨heP, heS⟩ := mem_sdiff.mp he
      refine mem_image.mpr ⟨⟨e, heP⟩, mem_compl.mpr ?_, rfl⟩
      intro he'
      exact heS (mem_image.mpr ⟨⟨e, heP⟩, he', rfl⟩)

end Overfull.FourOdd
