import Overfull.BipartiteFactorization.BlockSelectionBudget
import Overfull.Probability.PartitionPermutation

/-!
# Simultaneous actual blocks from shared part permutations

One permutation in each vertex part is shared by every block label. Each
label has the required independent fixed-size marginal law, while inclusions,
disjointness, and exact unions of position sets persist deterministically.
The labels may overlap, so a family can contain both fine blocks and their
coarse unions. Graph-derived marginal budgets give all block inequalities
simultaneously without assuming independence between the labels.
-/

noncomputable section

namespace Overfull.BipartiteFactorization.SimultaneousBlocks

open Finset Classical FiniteProbability BlockProductSampling BlockSelectionBudget

variable {V ι γ : Type*} [Fintype ι]

/-- In disjoint parts, intersecting an actual block with one part recovers
exactly the image of its coordinate sample. -/
theorem sampledBlock_inter_part (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (τ : ∀ i, Finset (D i)) (i : ι) :
    sampledBlock D τ ∩ D i = (τ i).image Subtype.val := by
  ext v
  constructor
  · intro hv
    obtain ⟨hτ, hD⟩ := Finset.mem_inter.mp hv
    exact Finset.mem_image.mpr ⟨⟨v, hD⟩,
      (sampledBlock_mem_part D hdisj τ i ⟨v, hD⟩).mp hτ, rfl⟩
  · intro hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_inter.mpr
      ⟨(sampledBlock_mem_part D hdisj τ i x).mpr hx, x.property⟩

theorem sampledBlock_inter_part_card (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (τ : ∀ i, Finset (D i)) (i : ι) :
    (sampledBlock D τ ∩ D i).card = (τ i).card := by
  rw [sampledBlock_inter_part D hdisj τ i]
  exact Finset.card_image_of_injective _ Subtype.val_injective

/-- Coordinatewise containment gives containment of the actual vertex blocks. -/
theorem sampledBlock_mono (D : ι → Finset V) {τ υ : ∀ i, Finset (D i)}
    (h : ∀ i, τ i ⊆ υ i) : sampledBlock D τ ⊆ sampledBlock D υ := by
  intro v hv
  obtain ⟨i, x, hx, hxv⟩ := (mem_sampledBlock D τ v).mp hv
  exact (mem_sampledBlock D υ v).mpr ⟨i, x, h i hx, hxv⟩

/-- Disjoint coordinate samples produce disjoint actual blocks in disjoint parts. -/
theorem sampledBlock_disjoint (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (τ υ : ∀ i, Finset (D i)) (h : ∀ i, Disjoint (τ i) (υ i)) :
    Disjoint (sampledBlock D τ) (sampledBlock D υ) := by
  apply Finset.disjoint_left.mpr
  intro v hv hυ
  obtain ⟨i, x, hx, rfl⟩ := (mem_sampledBlock D τ v).mp hv
  exact Finset.disjoint_left.mp (h i) hx
    ((sampledBlock_mem_part D hdisj υ i x).mp hυ)

/-- Taking vertex unions commutes with any finite union of coordinate samples. -/
theorem sampledBlock_biUnion (D : ι → Finset V) (J : Finset γ)
    (S : γ → ∀ i, Finset (D i)) :
    sampledBlock D (fun i => J.biUnion (fun j => S j i)) =
      J.biUnion (fun j => sampledBlock D (S j)) := by
  ext v
  constructor
  · intro hv
    obtain ⟨i, x, hx, hxv⟩ := (mem_sampledBlock D _ v).mp hv
    obtain ⟨j, hj, hx⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨j, hj,
      (mem_sampledBlock D (S j) v).mpr ⟨i, x, hx, hxv⟩⟩
  · intro hv
    obtain ⟨j, hj, hv⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨i, x, hx, hxv⟩ := (mem_sampledBlock D (S j) v).mp hv
    exact (mem_sampledBlock D _ v).mpr
      ⟨i, x, Finset.mem_biUnion.mpr ⟨j, hj, hx⟩, hxv⟩

theorem sampledBlock_univ (D : ι → Finset V) :
    sampledBlock D (fun _ => univ) = univ.biUnion D := by
  ext v
  constructor
  · intro hv
    obtain ⟨i, x, _, rfl⟩ := (mem_sampledBlock D _ v).mp hv
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, x.property⟩
  · intro hv
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hv
    exact (mem_sampledBlock D _ v).mpr ⟨i, ⟨v, hi⟩, Finset.mem_univ _, rfl⟩

/-- The actual vertex block obtained from shared permutations of its position sets. -/
def permutedBlock (D : ι → Finset V) (S : ∀ i, Finset (D i))
    (σ : ∀ i, Equiv.Perm (D i)) : Finset V :=
  sampledBlock D (PartitionPermutation.sample S σ)

theorem permutedBlock_subset (D : ι → Finset V) (B : Finset V)
    (hcover : univ.biUnion D = B) (S : ∀ i, Finset (D i))
    (σ : ∀ i, Equiv.Perm (D i)) : permutedBlock D S σ ⊆ B := by
  apply sampledBlock_subset
  intro i v hv
  rw [← hcover]
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hv⟩

theorem permutedBlock_inter_part_card (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (S : ∀ i, Finset (D i)) (σ : ∀ i, Equiv.Perm (D i)) (i : ι) :
    (permutedBlock D S σ ∩ D i).card = (S i).card := by
  exact (sampledBlock_inter_part_card D hdisj _ i).trans
    (PartitionPermutation.sample_card S σ i)

theorem permutedBlock_mono (D : ι → Finset V) {S T : ∀ i, Finset (D i)}
    (h : ∀ i, S i ⊆ T i) (σ : ∀ i, Equiv.Perm (D i)) :
    permutedBlock D S σ ⊆ permutedBlock D T σ := by
  exact sampledBlock_mono D (PartitionPermutation.sample_mono h σ)

theorem permutedBlock_disjoint (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (S T : ∀ i, Finset (D i)) (σ : ∀ i, Equiv.Perm (D i))
    (h : ∀ i, Disjoint (S i) (T i)) :
    Disjoint (permutedBlock D S σ) (permutedBlock D T σ) := by
  exact sampledBlock_disjoint D hdisj _ _ (PartitionPermutation.sample_disjoint S T σ h)

theorem permutedBlock_biUnion (D : ι → Finset V) (J : Finset γ)
    (S : γ → ∀ i, Finset (D i)) (σ : ∀ i, Equiv.Perm (D i)) :
    permutedBlock D (fun i => J.biUnion (fun j => S j i)) σ =
      J.biUnion (fun j => permutedBlock D (S j) σ) := by
  ext v
  constructor
  · intro hv
    obtain ⟨i, x, hx, hxv⟩ := (mem_sampledBlock D _ v).mp hv
    obtain ⟨j, hj, hx⟩ := Finset.mem_biUnion.mp
      ((PartitionPermutation.mem_sample _ σ i x).mp hx)
    exact Finset.mem_biUnion.mpr ⟨j, hj, (mem_sampledBlock D _ v).mpr
      ⟨i, x, (PartitionPermutation.mem_sample (S j) σ i x).mpr hx, hxv⟩⟩
  · intro hv
    obtain ⟨j, hj, hv⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨i, x, hx, hxv⟩ := (mem_sampledBlock D _ v).mp hv
    exact (mem_sampledBlock D _ v).mpr ⟨i, x,
      (PartitionPermutation.mem_sample _ σ i x).mpr (Finset.mem_biUnion.mpr
        ⟨j, hj, (PartitionPermutation.mem_sample (S j) σ i x).mp hx⟩), hxv⟩

theorem permutedBlock_univ (D : ι → Finset V) (σ : ∀ i, Equiv.Perm (D i)) :
    permutedBlock D (fun _ => univ) σ = univ.biUnion D := by
  unfold permutedBlock
  rw [PartitionPermutation.sample_univ, sampledBlock_univ]

/-- A concrete vertex family preserves the sizes and all supplied position
relations, including coarse unions and partitions of the whole sampled side. -/
structure RealizesPositions (D : ι → Finset V) (B : Finset V)
    (S : γ → ∀ i, Finset (D i)) (T : γ → Finset V) : Prop where
  subset : ∀ j, T j ⊆ B
  component_card : ∀ j i, (T j ∩ D i).card = (S j i).card
  mono : ∀ j l, (∀ i, S j i ⊆ S l i) → T j ⊆ T l
  disjoint : ∀ j l, (∀ i, Disjoint (S j i) (S l i)) → Disjoint (T j) (T l)
  biUnion : ∀ j (J : Finset γ),
    (∀ i, S j i = J.biUnion (fun l => S l i)) → T j = J.biUnion T
  cover : ∀ J : Finset γ,
    (∀ i, J.biUnion (fun j => S j i) = univ) → J.biUnion T = B

/-- Every tuple of shared permutations deterministically realizes all these
relations. No disjointness assumption between arbitrary labels is needed. -/
theorem permutedBlocks_realize (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (B : Finset V) (hcover : univ.biUnion D = B)
    (S : γ → ∀ i, Finset (D i)) (σ : ∀ i, Equiv.Perm (D i)) :
    RealizesPositions D B S (fun j => permutedBlock D (S j) σ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun j => permutedBlock_subset D B hcover (S j) σ
  · exact fun j i => permutedBlock_inter_part_card D hdisj (S j) σ i
  · exact fun _ _ h => permutedBlock_mono D h σ
  · exact fun j l h => permutedBlock_disjoint D hdisj (S j) (S l) σ h
  · intro j J h
    have heq : S j = fun i => J.biUnion (fun l => S l i) := funext h
    rw [heq, permutedBlock_biUnion]
  · intro J h
    rw [← permutedBlock_biUnion]
    have heq : (fun i => J.biUnion (fun j => S j i)) = fun _ => univ := funext h
    rw [heq, permutedBlock_univ, hcover]

variable {E : Type*} [Fintype E] [Fintype γ]

/-- A numerical sum of graph-derived failure budgets produces one shared
tuple of part permutations making every block good. Fractions, palette
fractions, and row caps may all vary between labels. -/
theorem exists_good_permutations (G : Multigraph V E)
    (D : ι → Finset V) (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (B U Wo Ws Zcorr : Finset V) (hcover : univ.biUnion D = B)
    (hBZ : Disjoint B Zcorr) (S : γ → ∀ i, Finset (D i))
    (F : V → Finset E) (β a : ℝ) (p₀ lam : γ → ℝ)
    (hp₀ : ∀ j, 0 < p₀ j) (hp₀1 : ∀ j, p₀ j ≤ 1)
    (hlam : ∀ j, 0 < lam j) (ha : 0 ≤ a)
    (hfraction : ∀ j i, ((S j i).card : ℝ) = p₀ j * (D i).card)
    (hselect : ∀ j i, (D i).Nonempty → 2 ≤ (S j i).card)
    (hdegree : ∀ v ∈ B, (G.degree v : ℝ) ≤ a)
    (hF : ∀ x ∈ Wo, F x ⊆ G.edgesTo x B)
    (hinj : ∀ x ∈ Wo, Set.InjOn (G.otherEnd x) (F x))
    (hFsize : ∀ x ∈ Wo, β * (G.edgesTo x U).card / 4 ≤ (F x).card)
    (hspecial_c : ∀ x ∈ Ws, 0 < ((G.edgesTo x U).card : ℝ))
    (hspecial_side : ∀ x ∈ Ws,
      ((G.edgesTo x U).card : ℝ) / 2 ≤ (G.edgesTo x B).card)
    (ell : γ → V → ℝ)
    (hc : ∀ x ∈ Zcorr, 0 < ((G.edgesTo x U).card : ℝ))
    (hdc : ∀ x ∈ Zcorr,
      ((G.edgesTo x B).card : ℝ) ≤ (G.edgesTo x U).card / 2)
    (hell_lower : ∀ j x, x ∈ Zcorr →
      (59 / 64 : ℝ) * lam j * (G.edgesTo x U).card ≤ ell j x)
    (hell_upper : ∀ j x, x ∈ Zcorr →
      ell j x ≤ (15 / 16 : ℝ) * lam j * (G.edgesTo x U).card)
    (ha_upper : ∀ j x, x ∈ Zcorr → a ≤ p₀ j * (G.edgesTo x U).card / 4096)
    (hM : 0 < (correctionPool G B Zcorr).card)
    (hbudget : (∑ j, failureBudget G B U Wo Ws Zcorr β (p₀ j) a) < 1) :
    ∃ σ : ∀ i, Equiv.Perm (D i), ∀ j,
      GoodBlock G B U Wo Ws Zcorr F β (p₀ j) (lam j) (ell j)
        (permutedBlock D (S j) σ) := by
  have hbad (j : γ) : MatchingProbability.probability
      (piWeight (fun i => Hypergeometric.weight (E := ↥(D i)) (S j i).card))
      (fun τ => bad G B U Wo Ws Zcorr F β (p₀ j) (lam j) (ell j)
        (sampledBlock D τ)) ≤ failureBudget G B U Wo Ws Zcorr β (p₀ j) a := by
    exact probability_bad_le G D hdisj B U Wo Ws Zcorr hcover hBZ
      (fun i => (S j i).card)
      (fun i => by simpa only [Fintype.card_coe] using Finset.card_le_univ (S j i))
      F β (p₀ j) (lam j) a (hp₀ j) (hp₀1 j) (hlam j) ha (hfraction j)
      (hselect j) hdegree hF hinj hFsize hspecial_c hspecial_side (ell j)
      hc hdc (hell_lower j) (hell_upper j) (ha_upper j) hM
  obtain ⟨σ, hσ⟩ := PartitionPermutation.exists_good_images S
    (fun j τ => bad G B U Wo Ws Zcorr F β (p₀ j) (lam j) (ell j)
      (sampledBlock D τ))
    (fun j => failureBudget G B U Wo Ws Zcorr β (p₀ j) a) hbad hbudget
  exact ⟨σ, fun j =>
    (not_bad_iff_goodBlock G B U Wo Ws Zcorr F β (p₀ j) (lam j) (ell j)
      (permutedBlock D (S j) σ)).mp (hσ j)⟩

/-- The resulting actual vertex blocks retain every supplied size, inclusion,
disjointness, and coarse-union relation while satisfying all three graph
inequalities. The assumptions are graph data and one explicit scalar budget. -/
theorem exists_good_blocks (G : Multigraph V E)
    (D : ι → Finset V) (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (B U Wo Ws Zcorr : Finset V) (hcover : univ.biUnion D = B)
    (hBZ : Disjoint B Zcorr) (S : γ → ∀ i, Finset (D i))
    (F : V → Finset E) (β a : ℝ) (p₀ lam : γ → ℝ)
    (hp₀ : ∀ j, 0 < p₀ j) (hp₀1 : ∀ j, p₀ j ≤ 1)
    (hlam : ∀ j, 0 < lam j) (ha : 0 ≤ a)
    (hfraction : ∀ j i, ((S j i).card : ℝ) = p₀ j * (D i).card)
    (hselect : ∀ j i, (D i).Nonempty → 2 ≤ (S j i).card)
    (hdegree : ∀ v ∈ B, (G.degree v : ℝ) ≤ a)
    (hF : ∀ x ∈ Wo, F x ⊆ G.edgesTo x B)
    (hinj : ∀ x ∈ Wo, Set.InjOn (G.otherEnd x) (F x))
    (hFsize : ∀ x ∈ Wo, β * (G.edgesTo x U).card / 4 ≤ (F x).card)
    (hspecial_c : ∀ x ∈ Ws, 0 < ((G.edgesTo x U).card : ℝ))
    (hspecial_side : ∀ x ∈ Ws,
      ((G.edgesTo x U).card : ℝ) / 2 ≤ (G.edgesTo x B).card)
    (ell : γ → V → ℝ)
    (hc : ∀ x ∈ Zcorr, 0 < ((G.edgesTo x U).card : ℝ))
    (hdc : ∀ x ∈ Zcorr,
      ((G.edgesTo x B).card : ℝ) ≤ (G.edgesTo x U).card / 2)
    (hell_lower : ∀ j x, x ∈ Zcorr →
      (59 / 64 : ℝ) * lam j * (G.edgesTo x U).card ≤ ell j x)
    (hell_upper : ∀ j x, x ∈ Zcorr →
      ell j x ≤ (15 / 16 : ℝ) * lam j * (G.edgesTo x U).card)
    (ha_upper : ∀ j x, x ∈ Zcorr → a ≤ p₀ j * (G.edgesTo x U).card / 4096)
    (hM : 0 < (correctionPool G B Zcorr).card)
    (hbudget : (∑ j, failureBudget G B U Wo Ws Zcorr β (p₀ j) a) < 1) :
    ∃ T : γ → Finset V, RealizesPositions D B S T ∧
      ∀ j, GoodBlock G B U Wo Ws Zcorr F β (p₀ j) (lam j) (ell j) (T j) := by
  obtain ⟨σ, hσ⟩ := exists_good_permutations G D hdisj B U Wo Ws Zcorr
    hcover hBZ S F β a p₀ lam hp₀ hp₀1 hlam ha hfraction hselect hdegree
    hF hinj hFsize hspecial_c hspecial_side ell hc hdc
    hell_lower hell_upper ha_upper hM hbudget
  exact ⟨fun j => permutedBlock D (S j) σ,
    permutedBlocks_realize D hdisj B hcover S σ, hσ⟩

end Overfull.BipartiteFactorization.SimultaneousBlocks
