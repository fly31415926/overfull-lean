import Overfull.CompatibleCircuits.TwoOddDecomposition
import Overfull.CircuitPatterns.IncidenceLoad
import Mathlib.Data.Fintype.EquivFin

/-!
# Bounded palette grouping of joining pieces

A finite greedy construction extends a proper prescribed palette assignment
while bounding the number of pieces in every group. The cardinality margin
is explicit; small individual pieces alone do not bound a whole palette class.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical
open scoped BigOperators

variable {J : Type*}

/-- A palette unavailable because it already contains `L` pieces. -/
def fullPalettes {h : ℕ} (A : Finset J) (c : J → Fin h) (L : ℕ) : Finset (Fin h) :=
  univ.filter (fun i => L ≤ (A.filter (fun x => c x = i)).card)

/-- Full palettes consume their full capacity in distinct color fibers. -/
theorem fullPalettes_mul_le {h L : ℕ} (A : Finset J) (c : J → Fin h) :
    (fullPalettes A c L).card * L ≤ A.card := by
  calc
    (fullPalettes A c L).card * L = ∑ _i ∈ fullPalettes A c L, L := by simp
    _ ≤ ∑ i ∈ fullPalettes A c L, (A.filter (fun x => c x = i)).card := by
      apply sum_le_sum
      intro i hi
      exact (mem_filter.mp hi).2
    _ = (A.filter (fun x => c x ∈ fullPalettes A c L)).card :=
      sum_card_fiberwise_eq_card_filter A _ c
    _ ≤ A.card := card_filter_le _ _

/-- With room for one more item, some palette avoids all conflicts and is
strictly below the prescribed capacity. -/
theorem exists_available_palette {h B L : ℕ} (A : Finset J) (c : J → Fin h)
    (F : Finset (Fin h)) (hF : F.card ≤ B) (hBh : B < h)
    (hA : A.card < L * (h-B)) :
    ∃ i : Fin h, i ∉ F ∧ (A.filter (fun x => c x = i)).card < L := by
  have hfull : (fullPalettes A c L).card < h-B := by
    by_contra hn
    have hm := Nat.mul_le_mul_right L (Nat.le_of_not_gt hn)
    have hb := fullPalettes_mul_le (L := L) A c
    nlinarith
  have hcard : (F ∪ fullPalettes A c L).card < h := by
    have hu := card_union_le F (fullPalettes A c L)
    omega
  have hex : ∃ i : Fin h, i ∉ F ∪ fullPalettes A c L := by
    by_contra hn
    push_neg at hn
    have heq : F ∪ fullPalettes A c L = univ := eq_univ_of_forall hn
    rw [heq, card_univ, Fintype.card_fin] at hcard
    omega
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, (notMem_union.mp hi).1, ?_⟩
  have hn := (notMem_union.mp hi).2
  simpa only [fullPalettes, mem_filter, mem_univ, true_and, not_le] using hn

/-- A proper precoloring extends to all pieces while respecting a uniform
class capacity, provided the conflict and total-size budgets have room. -/
theorem exists_bounded_palette_extension
    (R : J → J → Prop) (hsymm : Symmetric R) (hirrefl : Irreflexive R)
    (T P : Finset J) (hPT : P ⊆ T) {h B L : ℕ} (c₀ : J → Fin h)
    (hproper : ∀ x ∈ P, ∀ y ∈ P, R x y → c₀ x ≠ c₀ y)
    (hload : ∀ i, (P.filter (fun x => c₀ x = i)).card ≤ L)
    (hdegree : ∀ x ∈ T \ P, (T.filter (R x)).card ≤ B)
    (hBh : B < h) (hsize : T.card ≤ L * (h-B)) :
    ∃ c : J → Fin h,
      (∀ x ∈ P, c x = c₀ x) ∧
      (∀ x ∈ T, ∀ y ∈ T, R x y → c x ≠ c y) ∧
      (∀ i, (T.filter (fun x => c x = i)).card ≤ L) := by
  have hstep : ∀ U : Finset J, U ⊆ T \ P →
      ∃ c : J → Fin h,
        (∀ x ∈ P, c x = c₀ x) ∧
        (∀ x ∈ P ∪ U, ∀ y ∈ P ∪ U, R x y → c x ≠ c y) ∧
        (∀ i, ((P ∪ U).filter (fun x => c x = i)).card ≤ L) := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨c₀, fun _ _ => rfl, by simpa using hproper, by simpa using hload⟩
    | @insert x U hxU ih =>
      intro hUT
      have hxTP := hUT (mem_insert_self x U)
      have hxP : x ∉ P := (mem_sdiff.mp hxTP).2
      have hUT' : U ⊆ T \ P := (subset_insert _ _).trans hUT
      obtain ⟨c, hcP, hcproper, hcload⟩ := ih hUT'
      let A := P ∪ U
      have hAT : A ⊆ T := union_subset hPT (hUT'.trans sdiff_subset)
      have hxA : x ∉ A := by simp [A, hxP, hxU]
      have hcardA : A.card < L * (h-B) := by
        have hsub : insert x A ⊆ T := insert_subset (mem_sdiff.mp hxTP).1 hAT
        have hc := card_le_card hsub
        rw [card_insert_of_notMem hxA] at hc
        omega
      let F : Finset (Fin h) := (A.filter (R x)).image c
      have hF : F.card ≤ B :=
        (card_image_le).trans ((card_le_card (filter_subset_filter _ hAT)).trans
          (hdegree x hxTP))
      obtain ⟨i, hiF, hiL⟩ := exists_available_palette A c F hF hBh hcardA
      let d := Function.update c x i
      have hdx : d x = i := Function.update_self ..
      have hd (y : J) (hy : y ∈ A) : d y = c y := by
        apply Function.update_of_ne
        intro heq
        exact hxA (heq ▸ hy)
      have hfree (y : J) (hy : y ∈ A) (hxy : R x y) : i ≠ c y := by
        intro heq
        exact hiF (heq ▸ mem_image_of_mem c (mem_filter.mpr ⟨hy, hxy⟩))
      have hdomain : P ∪ insert x U = insert x A := by
        ext y
        simp only [A, mem_union, mem_insert]
        tauto
      refine ⟨d, ?_, ?_, ?_⟩
      · intro y hy
        rw [hd y (mem_union_left _ hy)]
        exact hcP y hy
      · rw [hdomain]
        intro y hy z hz hyz
        rcases mem_insert.mp hy with hyx | hyA
        · subst y
          rcases mem_insert.mp hz with hzx | hzA
          · subst z
            exact (hirrefl _ hyz).elim
          · rw [hdx, hd z hzA]
            exact hfree z hzA hyz
        · rcases mem_insert.mp hz with hzx | hzA
          · subst z
            rw [hd y hyA, hdx]
            exact (hfree y hyA (hsymm hyz)).symm
          · rw [hd y hyA, hd z hzA]
            exact hcproper y hyA z hzA hyz
      · rw [hdomain]
        intro j
        have hfilter : (A.filter (fun y => d y = j)) =
            A.filter (fun y => c y = j) := by
          apply filter_congr
          intro y hy
          rw [hd y hy]
        rw [filter_insert, hdx, hfilter]
        split_ifs with hij
        · subst j
          rw [card_insert_of_notMem (fun hh => hxA (mem_filter.mp hh).1)]
          omega
        · exact hcload j
  obtain ⟨c, hcP, hcproper, hcload⟩ := hstep (T \ P) (by rfl)
  rw [union_sdiff_of_subset hPT] at hcproper hcload
  exact ⟨c, hcP, hcproper, hcload⟩

variable {V E I : Type*} [Fintype I]

/-- Two distinct piece indices conflict when their actual endpoints meet. -/
def pieceConflict (G : Multigraph V E) (M : I → Finset E) (i j : I) : Prop :=
  i ≠ j ∧ ¬ Disjoint (G.edgeSupport (M i)) (G.edgeSupport (M j))

/-- Three-copy pieces have at most `6D` endpoint-conflicting indices when
all their copies belong to an edge set of maximum incidence `D`. -/
theorem pieceConflict_card_le (G : Multigraph V E) (M : I → Finset E)
    (S : Finset E) (D : ℕ) (hsize : ∀ i, (M i).card ≤ 3)
    (hdisjoint : Pairwise (fun i j => Disjoint (M i) (M j)))
    (hsubset : ∀ i, M i ⊆ S) (hdegree : ∀ v, G.degreeOn S v ≤ D) (i : I) :
    (univ.filter (pieceConflict G M i)).card ≤ 6*D := by
  have hsub : univ.filter (pieceConflict G M i) ⊆
      univ.filter (fun j => ¬ Disjoint (G.edgeSupport (M i)) (G.edgeSupport (M j))) := by
    intro j hj
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hj).2.2⟩
  exact (card_le_card hsub).trans
    ((CircuitPatterns.support_conflicts_card_le (G.edgeSupport (M i))
      (fun j => G.edgeSupport (M j)) D (fun v _ =>
        (G.family_support_load_le_degreeOn M S hdisjoint hsubset v).trans (hdegree v))).trans
          (Nat.mul_le_mul_right D (G.edgeSupport_card_le_six (hsize i))))

/-- The actual copy union assigned one palette label. -/
def groupedCopies {h : ℕ} (M : I → Finset E) (c : I → Fin h) (i : Fin h) : Finset E :=
  (univ.filter (fun j => c j = i)).biUnion M

@[simp] theorem mem_groupedCopies {h : ℕ} (M : I → Finset E)
    (c : I → Fin h) (i : Fin h) (e : E) :
    e ∈ groupedCopies M c i ↔ ∃ j, c j = i ∧ e ∈ M j := by
  simp only [groupedCopies, mem_biUnion, mem_filter, mem_univ, true_and]

/-- Proper colors for endpoint conflicts give actual matching group unions. -/
theorem groupedCopies_isMatching {h : ℕ} (G : Multigraph V E)
    (M : I → Finset E) (c : I → Fin h)
    (hM : ∀ i, G.IsMatching (M i))
    (hproper : ∀ i j, pieceConflict G M i j → c i ≠ c j) (i : Fin h) :
    G.IsMatching (groupedCopies M c i) := by
  intro e he f hf v hev hfv
  obtain ⟨j, hj, he⟩ := (mem_groupedCopies M c i e).mp he
  obtain ⟨k, hk, hf⟩ := (mem_groupedCopies M c i f).mp hf
  have hjk : j = k := by
    by_contra hne
    apply hproper j k ⟨hne, ?_⟩ (hj.trans hk.symm)
    intro hd
    exact disjoint_left.mp hd ((G.mem_edgeSupport _ _).mpr ⟨e, he, hev⟩)
      ((G.mem_edgeSupport _ _).mpr ⟨f, hf, hfv⟩)
  subst k
  exact hM j e he f hf v hev hfv

/-- Grouping keeps distinct palette classes edge-disjoint. -/
theorem groupedCopies_disjoint {h : ℕ} (M : I → Finset E) (c : I → Fin h)
    (hdisjoint : Pairwise (fun i j => Disjoint (M i) (M j))) :
    Pairwise (fun i j => Disjoint (groupedCopies M c i) (groupedCopies M c j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro e he hf
  obtain ⟨a, ha, he⟩ := (mem_groupedCopies M c i e).mp he
  obtain ⟨b, hb, hf⟩ := (mem_groupedCopies M c j e).mp hf
  have hab : a ≠ b := by
    intro heq
    subst b
    exact hij (ha.symm.trans hb)
  exact disjoint_left.mp (hdisjoint hab) he hf

/-- Every original piece and every original copy survives the grouping. -/
theorem groupedCopies_cover {h : ℕ} (M : I → Finset E) (c : I → Fin h) :
    univ.biUnion (groupedCopies M c) = univ.biUnion M := by
  ext e
  simp only [mem_biUnion, mem_univ, true_and, mem_groupedCopies]
  exact ⟨fun ⟨_, j, _, he⟩ => ⟨j, he⟩, fun ⟨j, he⟩ => ⟨c j, j, rfl, he⟩⟩

/-- Bounding the number of pieces gives the needed bound on the whole
palette group, rather than just on its individual pieces. -/
theorem groupedCopies_card_le {h L : ℕ} (M : I → Finset E) (c : I → Fin h)
    (hsize : ∀ i, (M i).card ≤ 3)
    (hload : ∀ i, (univ.filter (fun j => c j = i)).card ≤ L) (i : Fin h) :
    (groupedCopies M c i).card ≤ 3*L := by
  calc
    _ ≤ ∑ j ∈ univ.filter (fun j => c j = i), (M j).card := card_biUnion_le
    _ ≤ ∑ _j ∈ univ.filter (fun j => c j = i), 3 := sum_le_sum (fun j _ => hsize j)
    _ = 3*(univ.filter (fun j => c j = i)).card := by simp [Nat.mul_comm]
    _ ≤ 3*L := Nat.mul_le_mul_left 3 (hload i)

/-- The whole palette class has at most six vertices per allowed piece. -/
theorem groupedCopies_support_card_le {h L : ℕ} (G : Multigraph V E)
    (M : I → Finset E) (c : I → Fin h) (hsize : ∀ i, (M i).card ≤ 3)
    (hload : ∀ i, (univ.filter (fun j => c j = i)).card ≤ L) (i : Fin h) :
    (G.edgeSupport (groupedCopies M c i)).card ≤ 6*L := by
  have hh := (G.edgeSupport_card_le _).trans
    (Nat.mul_le_mul_left 2 (groupedCopies_card_le M c hsize hload i))
  simpa only [← Nat.mul_assoc] using hh

/-- Construct an endpoint-compatible bounded grouping, retaining any
injectively prescribed primary labels. All objects use original edge copies. -/
theorem exists_bounded_matching_grouping {h D L : ℕ}
    (G : Multigraph V E) (M : I → Finset E) (S : Finset E)
    (P : Finset I) (c₀ : I → Fin h)
    (hprimary : Set.InjOn c₀ P)
    (hM : ∀ i, G.IsMatching (M i)) (hsize : ∀ i, (M i).card ≤ 3)
    (hdisjoint : Pairwise (fun i j => Disjoint (M i) (M j)))
    (hsubset : ∀ i, M i ⊆ S) (hdegree : ∀ v, G.degreeOn S v ≤ D)
    (hL : 0 < L) (hDh : 6*D < h) (hbudget : Fintype.card I ≤ L*(h-6*D)) :
    ∃ c : I → Fin h,
      (∀ i ∈ P, c i = c₀ i) ∧
      (∀ i, (univ.filter (fun j => c j = i)).card ≤ L) ∧
      (∀ i, G.IsMatching (groupedCopies M c i)) ∧
      Pairwise (fun i j => Disjoint (groupedCopies M c i) (groupedCopies M c j)) ∧
      univ.biUnion (groupedCopies M c) = univ.biUnion M ∧
      (∀ i, (groupedCopies M c i).card ≤ 3*L) ∧
      (∀ i, (G.edgeSupport (groupedCopies M c i)).card ≤ 6*L) := by
  have hsymm : Symmetric (pieceConflict G M) := by
    intro i j hij
    exact ⟨hij.1.symm, fun hh => hij.2 hh.symm⟩
  have hirrefl : Irreflexive (pieceConflict G M) := fun _ hh => hh.1 rfl
  have hp : ∀ i ∈ P, ∀ j ∈ P, pieceConflict G M i j → c₀ i ≠ c₀ j := by
    intro i hi j hj hij hc
    exact hij.1 (hprimary hi hj hc)
  have hl : ∀ i, (P.filter (fun j => c₀ j = i)).card ≤ L := by
    intro i
    have hh : (P.filter (fun j => c₀ j = i)).card ≤ 1 := by
      apply card_le_one.mpr
      intro j hj k hk
      exact hprimary (mem_filter.mp hj).1 (mem_filter.mp hk).1
        ((mem_filter.mp hj).2.trans (mem_filter.mp hk).2.symm)
    omega
  obtain ⟨c, hcP, hcproper, hcload⟩ := exists_bounded_palette_extension
    (pieceConflict G M) hsymm hirrefl univ P (subset_univ _) c₀ hp hl
    (fun i _ => pieceConflict_card_le G M S D hsize hdisjoint hsubset hdegree i)
    hDh (by simpa only [card_univ] using hbudget)
  refine ⟨c, hcP, hcload, ?_, groupedCopies_disjoint M c hdisjoint,
    groupedCopies_cover M c, groupedCopies_card_le M c hsize hcload,
    groupedCopies_support_card_le G M c hsize hcload⟩
  exact groupedCopies_isMatching G M c hM (fun i j => hcproper i (mem_univ _) j (mem_univ _))

/-- Disjoint nonempty pieces are no more numerous than their actual copies. -/
theorem piece_count_le_copy_count (M : I → Finset E)
    (hne : ∀ i, (M i).Nonempty)
    (hdisjoint : Pairwise (fun i j => Disjoint (M i) (M j))) :
    Fintype.card I ≤ (univ.biUnion M).card := by
  calc
    _ = ∑ _i : I, 1 := by simp
    _ ≤ ∑ i : I, (M i).card := sum_le_sum (fun i _ => (hne i).card_pos)
    _ = (univ.biUnion M).card := (card_biUnion (fun i _ j _ hij => hdisjoint hij)).symm

/-- The global joining-incidence budget bounds the number of nonempty pieces
and can therefore discharge the total-size condition in the greedy theorem. -/
theorem twice_piece_count_le_order_mul_degree [Fintype V]
    (G : Multigraph V E) (M : I → Finset E) (S : Finset E) (D : ℕ)
    (hne : ∀ i, (M i).Nonempty)
    (hdisjoint : Pairwise (fun i j => Disjoint (M i) (M j)))
    (hsubset : ∀ i, M i ⊆ S) (hdegree : ∀ v, G.degreeOn S v ≤ D) :
    2*Fintype.card I ≤ Fintype.card V*D := by
  have hparts : univ.biUnion M ⊆ S := biUnion_subset.mpr (fun i _ => hsubset i)
  have hcount := (piece_count_le_copy_count M hne hdisjoint).trans (card_le_card hparts)
  have hsum := G.degreeOn_sum S
  have hs : (∑ v ∈ G.edgeSupport S, G.degreeOn S v) ≤ Fintype.card V*D := by
    calc
      _ ≤ ∑ _v ∈ G.edgeSupport S, D := sum_le_sum (fun v _ => hdegree v)
      _ = (G.edgeSupport S).card*D := by simp
      _ ≤ Fintype.card V*D := Nat.mul_le_mul_right D (card_le_univ _)
  omega

/-- Assign the prescribed `h` primary indices bijectively to the `h` labels,
using an arbitrary default only away from those primary indices. -/
def primarySeed {h : ℕ} (P : Finset I) (hP : P.card = h) (hpos : 0 < h) :
    I → Fin h :=
  fun j => if hj : j ∈ P then P.equivFinOfCardEq hP ⟨j, hj⟩ else ⟨0, hpos⟩

omit [Fintype I] in
/-- The initial primary labels are all distinct. -/
theorem primarySeed_injective {h : ℕ} (P : Finset I) (hP : P.card = h)
    (hpos : 0 < h) : Set.InjOn (primarySeed P hP hpos) P := by
  intro i hi j hj hij
  change i ∈ P at hi
  change j ∈ P at hj
  simp only [primarySeed, dif_pos hi, dif_pos hj] at hij
  exact congrArg Subtype.val ((P.equivFinOfCardEq hP).injective hij)

omit [Fintype I] in
/-- An extension of the primary seed retains exactly one primary piece
in every palette class, with no unused primary label. -/
theorem primarySeed_extension_unique {h : ℕ} (P : Finset I) (hP : P.card = h)
    (hpos : 0 < h) (c : I → Fin h)
    (hc : ∀ j ∈ P, c j = primarySeed P hP hpos j) (i : Fin h) :
    ∃! j : P, c j.val = i := by
  let j := (P.equivFinOfCardEq hP).symm i
  refine ⟨j, ?_, ?_⟩
  · change c j.val = i
    rw [hc j.val j.property]
    simp only [primarySeed, dif_pos j.property]
    exact (P.equivFinOfCardEq hP).apply_symm_apply i
  · intro k hk
    apply (P.equivFinOfCardEq hP).injective
    have hck := hc k.val k.property
    simp only [primarySeed, dif_pos k.property] at hck
    rw [← hck, hk]
    exact ((P.equivFinOfCardEq hP).apply_symm_apply i).symm

/-- The vertex-incidence estimate discharges the total palette capacity
condition using an explicit arithmetic budget in the host order. -/
theorem palette_capacity_of_incidence_budget [Fintype V]
    {h D L : ℕ} (G : Multigraph V E) (M : I → Finset E) (S : Finset E)
    (hne : ∀ i, (M i).Nonempty)
    (hdisjoint : Pairwise (fun i j => Disjoint (M i) (M j)))
    (hsubset : ∀ i, M i ⊆ S) (hdegree : ∀ v, G.degreeOn S v ≤ D)
    (hbudget : Fintype.card V*D ≤ 2*L*(h-6*D)) :
    Fintype.card I ≤ L*(h-6*D) := by
  have hh := twice_piece_count_le_order_mul_degree G M S D hne hdisjoint hsubset hdegree
  nlinarith

/-- Automatic quantitative grouping of the whole family. The explicit
capacity is one more than the average over the conflict-free palette margin. -/
theorem exists_matching_grouping_with_primary {h D : ℕ}
    (G : Multigraph V E) (M : I → Finset E) (S : Finset E)
    (P : Finset I) (hP : P.card = h)
    (hM : ∀ i, G.IsMatching (M i)) (hsize : ∀ i, (M i).card ≤ 3)
    (hdisjoint : Pairwise (fun i j => Disjoint (M i) (M j)))
    (hsubset : ∀ i, M i ⊆ S) (hdegree : ∀ v, G.degreeOn S v ≤ D)
    (hDh : 6*D < h) :
    ∃ c : I → Fin h,
      (∀ i, ∃! j : P, c j.val = i) ∧
      (∀ i, (univ.filter (fun j => c j = i)).card ≤ Fintype.card I/(h-6*D)+1) ∧
      (∀ i, G.IsMatching (groupedCopies M c i)) ∧
      Pairwise (fun i j => Disjoint (groupedCopies M c i) (groupedCopies M c j)) ∧
      univ.biUnion (groupedCopies M c) = univ.biUnion M ∧
      (∀ i, (groupedCopies M c i).card ≤ 3*(Fintype.card I/(h-6*D)+1)) ∧
      (∀ i, (G.edgeSupport (groupedCopies M c i)).card ≤
        6*(Fintype.card I/(h-6*D)+1)) := by
  have hpos : 0 < h := lt_of_le_of_lt (Nat.zero_le _) hDh
  have hmargin : 0 < h-6*D := Nat.sub_pos_of_lt hDh
  have hbudget : Fintype.card I ≤ (Fintype.card I/(h-6*D)+1)*(h-6*D) := by
    have hh := Nat.lt_mul_div_succ (Fintype.card I) hmargin
    nlinarith
  obtain ⟨c, hcP, hcload, hmatching, hdis, hcover, hcard, hsupport⟩ :=
    exists_bounded_matching_grouping G M S P (primarySeed P hP hpos)
      (primarySeed_injective P hP hpos) hM hsize hdisjoint hsubset hdegree
      (Nat.succ_pos _) hDh hbudget
  exact ⟨c, primarySeed_extension_unique P hP hpos c hcP, hcload,
    hmatching, hdis, hcover, hcard, hsupport⟩

/-- Every class remains in the original containing copy set. -/
theorem groupedCopies_subset {h : ℕ} (M : I → Finset E)
    (c : I → Fin h) (S : Finset E) (hsubset : ∀ i, M i ⊆ S) (i : Fin h) :
    groupedCopies M c i ⊆ S := by
  intro e he
  obtain ⟨j, _, he⟩ := (mem_groupedCopies M c i e).mp he
  exact hsubset j he

/-- Grouping cannot increase the load at any original vertex beyond its
original containing-set incidence. This bound is for whole palette classes. -/
theorem groupedCopies_support_load_le {h D : ℕ} (G : Multigraph V E)
    (M : I → Finset E) (c : I → Fin h) (S : Finset E)
    (hdisjoint : Pairwise (fun i j => Disjoint (M i) (M j)))
    (hsubset : ∀ i, M i ⊆ S) (hdegree : ∀ v, G.degreeOn S v ≤ D) (v : V) :
    (univ.filter (fun i => v ∈ G.edgeSupport (groupedCopies M c i))).card ≤ D :=
  (G.family_support_load_le_degreeOn (groupedCopies M c) S
    (groupedCopies_disjoint M c hdisjoint) (groupedCopies_subset M c S hsubset) v).trans
      (hdegree v)

/-- Automatic grouping when no primary palette labels are prescribed,
as in the all-even joining-circuit case. -/
theorem exists_matching_grouping {h D : ℕ}
    (G : Multigraph V E) (M : I → Finset E) (S : Finset E)
    (hM : ∀ i, G.IsMatching (M i)) (hsize : ∀ i, (M i).card ≤ 3)
    (hdisjoint : Pairwise (fun i j => Disjoint (M i) (M j)))
    (hsubset : ∀ i, M i ⊆ S) (hdegree : ∀ v, G.degreeOn S v ≤ D)
    (hDh : 6*D < h) :
    ∃ c : I → Fin h,
      (∀ i, (univ.filter (fun j => c j = i)).card ≤ Fintype.card I/(h-6*D)+1) ∧
      (∀ i, G.IsMatching (groupedCopies M c i)) ∧
      Pairwise (fun i j => Disjoint (groupedCopies M c i) (groupedCopies M c j)) ∧
      univ.biUnion (groupedCopies M c) = univ.biUnion M ∧
      (∀ i, (groupedCopies M c i).card ≤ 3*(Fintype.card I/(h-6*D)+1)) ∧
      (∀ i, (G.edgeSupport (groupedCopies M c i)).card ≤
        6*(Fintype.card I/(h-6*D)+1)) := by
  have hpos : 0 < h := lt_of_le_of_lt (Nat.zero_le _) hDh
  have hmargin : 0 < h-6*D := Nat.sub_pos_of_lt hDh
  have hbudget : Fintype.card I ≤ (Fintype.card I/(h-6*D)+1)*(h-6*D) := by
    have hh := Nat.lt_mul_div_succ (Fintype.card I) hmargin
    nlinarith
  obtain ⟨c, _, hcload, hmatching, hdis, hcover, hcard, hsupport⟩ :=
    exists_bounded_matching_grouping G M S ∅ (fun _ => ⟨0, hpos⟩)
      (by simp) hM hsize hdisjoint hsubset hdegree (Nat.succ_pos _) hDh hbudget
  exact ⟨c, hcload, hmatching, hdis, hcover, hcard, hsupport⟩

end Overfull.NativeReserve
