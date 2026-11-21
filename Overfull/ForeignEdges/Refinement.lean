import Overfull.ForeignEdges.Minority
import Overfull.SafePrescription.Boundary
import Overfull.SafePrescription.Counting

/-!
# Refining the core groups and counting recorded cuts

Refinement uses the actual shore of a cut.  The new labels remember both
an old group and the new shore.  A split of a core group strictly increases
the number of groups.  The edge accounting retains the graphs in which the
cuts were recorded, so subsequent edge deletions cannot enlarge their cost.
-/

namespace Overfull.ForeignRefinement

open Finset Classical SimpleGraph SafePrescription MatchingProbability FractionalMatching
open scoped BigOperators

variable {V I C D : Type*}

/-- Refine a vertex label by its membership in the new shore. -/
noncomputable def refineVertex (c : V → C) (X : Finset V) (v : V) : C × Bool :=
  (c v, decide (v ∈ X))

/-- Refine a core label by the majority shore of the core. -/
noncomputable def refineCore (p : I → C) (U : I → Finset V) (X : Finset V)
    (i : I) : C × Bool :=
  (p i, decide (coreMajority U X i))

@[simp] theorem refineVertex_eq_iff (c : V → C) (X : Finset V) (u v : V) :
    refineVertex c X u = refineVertex c X v ↔
      c u = c v ∧ (u ∈ X ↔ v ∈ X) := by
  simp [refineVertex]

/-- The already constructed minority deletion makes the surviving core
homogeneous for the refined vertex labels. -/
theorem surviving_core_refined_label [Fintype I]
    (p : I → C) (c : V → C) (U : I → Finset V) (X : Finset V)
    (hlabel : ∀ i v, v ∈ U i → c v = p i)
    (i : I) (v : V) (hv : v ∈ U i \ minorityVertices U X) :
    refineVertex c X v = refineCore p U X i := by
  have hm := surviving_core_membership U X i v hv
  simp only [refineVertex, refineCore, Prod.mk.injEq]
  exact ⟨hlabel i v (mem_sdiff.mp hv).1, decide_eq_decide.mpr hm⟩

/-- Adding a shore bit never decreases the number of occupied core groups. -/
theorem image_card_le_refinement [Fintype I] [DecidableEq C] [DecidableEq D] (p : I → C) (b : I → D) :
    (univ.image p).card ≤ (univ.image (fun i => (p i, b i))).card := by
  classical
  have himage : (univ.image (fun i => (p i,b i))).image Prod.fst = univ.image p := by
    simp [image_image, Function.comp_def]
  rw [← himage]
  exact card_image_le

/-- Separating two cores of one old group strictly increases the number
of occupied groups.  This statement counts the actual image of the labels. -/
theorem image_card_lt_refinement [Fintype I] [DecidableEq C] [DecidableEq D] (p : I → C) (b : I → D)
    (i j : I) (hp : p i = p j) (hb : b i ≠ b j) :
    (univ.image p).card < (univ.image (fun i => (p i,b i))).card := by
  classical
  let S := univ.image (fun i => (p i,b i))
  have himage : S.image Prod.fst = univ.image p := by
    simp [S,image_image, Function.comp_def]
  have hle := image_card_le_refinement p b
  by_contra hn
  have hcard : (S.image Prod.fst).card = S.card := by
    rw [himage]
    change (univ.image p).card = (univ.image (fun i => (p i,b i))).card
    omega
  have hinj := (card_image_iff.mp hcard)
  have hpair : (p i,b i) = (p j,b j) := hinj
    (by exact mem_image.mpr ⟨i,mem_univ _,rfl⟩)
    (by exact mem_image.mpr ⟨j,mem_univ _,rfl⟩) hp
  exact hb (congrArg Prod.snd hpair)

/-- Strict refinement increases the number of occupied labels, even after
an injective re-encoding of those labels. -/
theorem image_card_lt_of_refinement [Fintype I] [DecidableEq C] [DecidableEq D] (p : I → C) (q : I → D)
    (hrefines : ∀ i j, q i = q j → p i = p j)
    (i j : I) (hp : p i = p j) (hq : q i ≠ q j) :
    (univ.image p).card < (univ.image q).card := by
  classical
  let S := univ.image (fun i => (p i,q i))
  have hstrict := image_card_lt_refinement p q i j hp hq
  have hinj : Set.InjOn (Prod.snd : C × D → D) (S : Set (C × D)) := by
    rintro x hx y hy hxy
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    obtain ⟨j,_,rfl⟩ := mem_image.mp hy
    exact Prod.ext (hrefines i j hxy) hxy
  have himage : S.image Prod.snd = univ.image q := by
    simp [S,image_image,Function.comp_def]
  have hcard := card_image_of_injOn hinj
  rw [himage] at hcard
  exact hstrict.trans_eq hcard.symm

/-- The trigger used in the manuscript really splits one occupied group. -/
theorem core_groups_increase [Fintype I] [DecidableEq C] (p : I → C)
    (U : I → Finset V) (X : Finset V) (i j : I)
    (hp : p i = p j)
    (hmajority : ¬ (coreMajority U X i ↔ coreMajority U X j)) :
    (univ.image p).card < (univ.image (refineCore p U X)).card := by
  classical
  have hb : decide (coreMajority U X i) ≠ decide (coreMajority U X j) := by
    intro hb
    exact hmajority (decide_eq_decide.mp hb)
  simpa only [refineCore] using
    image_card_lt_refinement p (fun a => decide (coreMajority U X a)) i j hp hb

/-- With at most four cores, any strict chain of occupied groups starting
with a nonempty group has at most three refinements. -/
theorem at_most_three_refinements (r : ℕ) (groups : ℕ → ℕ)
    (hstart : 1 ≤ groups 0) (hstep : ∀ j < r, groups j < groups (j+1))
    (hfinal : groups r ≤ 4) : r ≤ 3 := by
  have hbound : ∀ j ≤ r, j+1 ≤ groups j := by
    intro j hj
    induction j with
    | zero => simpa using hstart
    | succ j ih =>
      have hprev := ih (by omega)
      have hinc := hstep j (by omega)
      omega
  have hr := hbound r le_rfl
  omega

/-- For an actual sequence of core label maps, no merging and one strict
split at each transition imply at most three transitions. -/
theorem core_refinement_chain_length [Fintype I] [Nonempty I] [DecidableEq C]
    (p : ℕ → I → C) (r : ℕ) (hI : Fintype.card I ≤ 4)
    (hrefines : ∀ a < r, ∀ i j, p (a+1) i = p (a+1) j → p a i = p a j)
    (hsplit : ∀ a < r, ∃ i j, p a i = p a j ∧ p (a+1) i ≠ p (a+1) j) :
    r ≤ 3 := by
  classical
  apply at_most_three_refinements r (fun a => (univ.image (p a)).card)
  · exact card_pos.mpr (univ_nonempty.image _)
  · intro a ha
    obtain ⟨i,j,hp,hq⟩ := hsplit a ha
    exact image_card_lt_of_refinement (p a) (p (a+1)) (hrefines a ha) i j hp hq
  · exact card_image_le.trans (by simpa using hI)

/-- The complete list of recorded shore memberships is a canonical
cluster label. -/
noncomputable def historyLabel {J : Type*} (shores : J → Finset V) (v : V) : J → Bool :=
  fun j => decide (v ∈ shores j)

/-- Distinct history labels are separated by an actual recorded shore. -/
theorem historyLabel_separates {J : Type*} (shores : J → Finset V)
    (u v : V) (hlabels : historyLabel shores u ≠ historyLabel shores v) :
    ∃ j, (u ∈ shores j) ≠ (v ∈ shores j) := by
  by_contra hn
  apply hlabels
  funext j
  apply decide_eq_decide.mpr
  have heq : (u ∈ shores j) = (v ∈ shores j) := by
    by_contra h
    exact hn ⟨j,h⟩
  exact Iff.of_eq heq

/-- Re-encode the represented groups by `Fin 4` without identifying any
occupied core groups or any distinct unmarked vertex labels. -/
theorem encode_labels_fin_four [Fintype I] [DecidableEq C]
    (p : I → C) (c : V → C) (Z₀ : Finset V)
    (hI : Fintype.card I ≤ 4)
    (hrepresented : ∀ v, v ∉ Z₀ → ∃ i, c v = p i) :
    ∃ (p' : I → Fin 4) (c' : V → Fin 4),
      (∀ i j, p' i = p' j ↔ p i = p j) ∧
      (∀ v i, c v = p i → c' v = p' i) ∧
      (∀ u v, u ∉ Z₀ → v ∉ Z₀ → (c' u = c' v ↔ c u = c v)) ∧
      (univ.image p').card = (univ.image p).card := by
  classical
  let S := univ.image p
  have hS : Fintype.card S ≤ Fintype.card (Fin 4) := by
    simp only [Fintype.card_coe,Fintype.card_fin]
    exact card_image_le.trans (by simpa using hI)
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hS
  let p' : I → Fin 4 := fun i => e ⟨p i,mem_image.mpr ⟨i,mem_univ _,rfl⟩⟩
  let c' : V → Fin 4 := fun v => if h : c v ∈ S then e ⟨c v,h⟩ else 0
  have hp' (i j : I) : p' i = p' j ↔ p i = p j := by
    change e _ = e _ ↔ _
    rw [e.injective.eq_iff,Subtype.mk.injEq]
  have hc' (v : V) (i : I) (hvi : c v = p i) : c' v = p' i := by
    have hvS : c v ∈ S := mem_image.mpr ⟨i,mem_univ _,hvi.symm⟩
    simp only [c',dif_pos hvS,p']
    exact congrArg e (Subtype.ext hvi)
  refine ⟨p',c',hp',hc',?_,?_⟩
  · intro u v hu hv
    obtain ⟨i,hi⟩ := hrepresented u hu
    obtain ⟨j,hj⟩ := hrepresented v hv
    rw [hc' u i hi,hc' v j hj,hp',hi,hj]
  · let f : C → Fin 4 := fun x => if h : x ∈ S then e ⟨x,h⟩ else 0
    have hf : Set.InjOn f S := by
      intro x hx y hy hxy
      change x ∈ S at hx
      change y ∈ S at hy
      dsimp only [f] at hxy
      rw [dif_pos hx,dif_pos hy] at hxy
      exact congrArg Subtype.val (e.injective hxy)
    have himage : univ.image p' = S.image f := by
      ext z
      simp only [S,mem_image,mem_univ,true_and]
      constructor
      · rintro ⟨i,rfl⟩
        refine ⟨p i,⟨i,rfl⟩,?_⟩
        simp [f,p',S]
      · rintro ⟨x,⟨i,rfl⟩,rfl⟩
        exact ⟨i,by simp [f,p',S]⟩
    rw [himage,card_image_of_injOn hf]

section Counting

variable [Fintype V]

/-- The simple graph cut has exactly the edge-copy cut cardinality. -/
theorem cutGraph_card (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) :
    (cutGraph G X).edgeSet.ncard = cutCount (univ : Finset G.edgeSet) X := by
  classical
  let A := cutEdges (univ : Finset G.edgeSet) X
  have himage : A.image Subtype.val = (cutGraph G X).edgeFinset := by
    ext e
    constructor
    · intro he
      obtain ⟨f,hf,rfl⟩ := mem_image.mp he
      rw [SimpleGraph.mem_edgeFinset, ← edge_eq f]
      change G.Adj (firstEnd f) (secondEnd f) ∧ _
      exact ⟨endpoint_adj f, by simpa [A,cutEdges,Lovasz.BMatch.cut] using hf⟩
    · intro he
      have hecut : e ∈ (cutGraph G X).edgeSet := by simpa using he
      have heG : e ∈ G.edgeSet := edgeSet_mono (show cutGraph G X ≤ G from fun _ _ h => h.1) hecut
      refine mem_image.mpr ⟨⟨e,heG⟩,?_,rfl⟩
      have hcut : ((firstEnd (⟨e,heG⟩ : G.edgeSet) ∈ X) ≠
          (secondEnd (⟨e,heG⟩ : G.edgeSet) ∈ X)) := by
        have heq : s(firstEnd (⟨e,heG⟩ : G.edgeSet), secondEnd (⟨e,heG⟩ : G.edgeSet)) = e := edge_eq _
        rw [← heq] at hecut
        exact hecut.2
      simpa [A,cutEdges,Lovasz.BMatch.cut] using hcut
  rw [Set.ncard_eq_toFinset_card' (cutGraph G X).edgeSet]
  change (cutGraph G X).edgeFinset.card = A.card
  rw [← himage,card_image_of_injective A Subtype.val_injective]

/-- An edge deletion cannot increase the cardinality of a recorded cut. -/
theorem cutCount_mono_graph (G R : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel R.Adj]
    (hGR : G ≤ R) (X : Finset V) :
    cutCount (univ : Finset G.edgeSet) X ≤
      cutCount (univ : Finset R.edgeSet) X := by
  rw [← cutGraph_card,← cutGraph_card]
  exact Set.ncard_le_ncard (edgeSet_mono (fun _ _ h => ⟨hGR h.1,h.2⟩))

omit [Fintype V] in
/-- The separation invariant is maintained by an actual shore refinement. -/
theorem refinement_history_separation {J : Type*} (c : V → C)
    (Z₀ X : Finset V) (shores : J → Finset V)
    (hseparate : ∀ u v, u ∉ Z₀ → v ∉ Z₀ → c u ≠ c v →
      ∃ j, (u ∈ shores j) ≠ (v ∈ shores j)) :
    ∀ u v, u ∉ Z₀ → v ∉ Z₀ → refineVertex c X u ≠ refineVertex c X v →
      (∃ j, (u ∈ shores j) ≠ (v ∈ shores j)) ∨ ((u ∈ X) ≠ (v ∈ X)) := by
  intro u v hu hv hne
  by_cases hc : c u = c v
  · right
    intro hX
    apply hne
    exact (refineVertex_eq_iff c X u v).mpr ⟨hc,Iff.of_eq hX⟩
  · exact Or.inl (hseparate u v hu hv hc)

/-- Every current crossing edge is charged to an actual recorded cut.
The current graph may have lost edges since each cut was recorded. -/
theorem clusterCrossingEdges_card_le_history {J : Type*} [Fintype J]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → C) (Z₀ : Finset V)
    (recorded : J → SimpleGraph V) [∀ j, DecidableRel (recorded j).Adj]
    (shores : J → Finset V) (hle : ∀ j, G ≤ recorded j)
    (hseparate : ∀ u v, u ∉ Z₀ → v ∉ Z₀ → c u ≠ c v →
      ∃ j, (u ∈ shores j) ≠ (v ∈ shores j)) :
    (clusterCrossingEdges G c Z₀).card ≤
      ∑ j, cutCount (univ : Finset (recorded j).edgeSet) (shores j) := by
  classical
  have hsub : clusterCrossingEdges G c Z₀ ⊆
      univ.biUnion (fun j => cutEdges (univ : Finset G.edgeSet) (shores j)) := by
    intro e he
    obtain ⟨_,hu,hv,hc⟩ := mem_filter.mp he
    obtain ⟨j,hj⟩ := hseparate (firstEnd e) (secondEnd e) hu hv hc
    refine mem_biUnion.mpr ⟨j,mem_univ _,?_⟩
    simpa [cutEdges,Lovasz.BMatch.cut] using hj
  calc
    _ ≤ (univ.biUnion (fun j => cutEdges (univ : Finset G.edgeSet) (shores j))).card := card_le_card hsub
    _ ≤ ∑ j, cutCount (univ : Finset G.edgeSet) (shores j) := card_biUnion_le
    _ ≤ _ := sum_le_sum (fun j _ => cutCount_mono_graph G (recorded j) (hle j) (shores j))

/-- At most three recorded cuts, each of size at most `2*k₀`, charge at
most `6*k₀` actual current intercluster edges. -/
theorem clusterCrossingEdges_card_le_six {J : Type*} [Fintype J]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → C) (Z₀ : Finset V)
    (recorded : J → SimpleGraph V) [∀ j, DecidableRel (recorded j).Adj]
    (shores : J → Finset V) (k₀ : ℕ) (hJ : Fintype.card J ≤ 3)
    (hle : ∀ j, G ≤ recorded j)
    (hcut : ∀ j, cutCount (univ : Finset (recorded j).edgeSet) (shores j) ≤ 2*k₀)
    (hseparate : ∀ u v, u ∉ Z₀ → v ∉ Z₀ → c u ≠ c v →
      ∃ j, (u ∈ shores j) ≠ (v ∈ shores j)) :
    (clusterCrossingEdges G c Z₀).card ≤ 6*k₀ := by
  have hcount := clusterCrossingEdges_card_le_history G c Z₀ recorded shores hle hseparate
  have hsum : (∑ j, cutCount (univ : Finset (recorded j).edgeSet) (shores j)) ≤
      Fintype.card J * (2*k₀) := by
    simpa using sum_le_sum (s := univ) (fun j _ => hcut j)
  have hmul := Nat.mul_le_mul_right (2*k₀) hJ
  omega


/-- The canonical shore-history labels satisfy the complete six-cut
edge bound without an assumed separation invariant. -/
theorem history_crossing_edges_le_six {J : Type*} [Fintype J]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Z₀ : Finset V)
    (recorded : J → SimpleGraph V) [∀ j, DecidableRel (recorded j).Adj]
    (shores : J → Finset V) (k₀ : ℕ) (hJ : Fintype.card J ≤ 3)
    (hle : ∀ j, G ≤ recorded j)
    (hcut : ∀ j, cutCount (univ : Finset (recorded j).edgeSet) (shores j) ≤ 2*k₀) :
    (clusterCrossingEdges G (historyLabel shores) Z₀).card ≤ 6*k₀ := by
  apply clusterCrossingEdges_card_le_six G (historyLabel shores) Z₀ recorded shores k₀ hJ hle hcut
  intro u v _ _ hlabels
  exact historyLabel_separates shores u v hlabels

/-- The actual graph of edges between distinct unmarked clusters. -/
def clusterCrossingGraph (G : SimpleGraph V) (c : V → C) (Z₀ : Finset V) :
    SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∉ Z₀ ∧ v ∉ Z₀ ∧ c u ≠ c v
  symm := by
    rintro u v ⟨hG,hu,hv,hc⟩
    exact ⟨hG.symm,hv,hu,Ne.symm hc⟩
  loopless := by intro v h; exact h.2.2.2 rfl

/-- The intercluster degree at an unmarked vertex is counted by the
actual selected host edges, independently of their endpoint orientation. -/
theorem clusterCrossing_incident_eq_neighbors (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : V → C) (Z₀ : Finset V) (v : V) (hv : v ∉ Z₀) :
    incidentCount (clusterCrossingEdges G c Z₀) v =
      ((G.neighborFinset v).filter (fun w => w ∉ Z₀ ∧ c w ≠ c v)).card := by
  classical
  let R := clusterCrossingGraph G c Z₀
  have hRG : R ≤ G := fun _ _ h => h.1
  have hsets : (univ : Finset G.edgeSet).filter (fun e => e.val ∈ R.edgeSet) =
      clusterCrossingEdges G c Z₀ := by
    ext e
    simp only [clusterCrossingEdges,mem_filter,mem_univ,true_and]
    rw [← edge_eq e]
    change (G.Adj (firstEnd e) (secondEnd e) ∧ _) ↔ _
    exact and_iff_right (endpoint_adj e)
  rw [← hsets,incidentCount_subgraph_edges G R hRG,← card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp [R,clusterCrossingGraph,hv,ne_comm]

/-- Mark exactly those unmarked exceptional vertices exceeding the
prescribed threshold of intercluster degree. -/
noncomputable def heavyVertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → C) (Z Z₀ : Finset V) (T : ℝ) : Finset V :=
  (Z \ Z₀).filter (fun v => T <
    (((G.neighborFinset v).filter (fun w => w ∉ Z₀ ∧ c w ≠ c v)).card : ℝ))

theorem heavyVertices_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → C) (Z Z₀ : Finset V) (T : ℝ) :
    heavyVertices G c Z Z₀ T ⊆ Z \ Z₀ := filter_subset _ _

/-- Handshaking bounds the actual heavy set.  This includes the case
where it is empty and does not assume a bound on its cardinality. -/
theorem heavyVertices_card_mul_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → C) (Z Z₀ : Finset V) (T : ℝ) :
    (heavyVertices G c Z Z₀ T).card * T ≤
      2 * ((clusterCrossingEdges G c Z₀).card : ℝ) := by
  classical
  let A := clusterCrossingEdges G c Z₀
  let W := heavyVertices G c Z Z₀ T
  have hpoint (v : V) (hv : v ∈ W) : T ≤ (incidentCount A v : ℝ) := by
    have hv' := mem_filter.mp hv
    have hvZ₀ := (mem_sdiff.mp hv'.1).2
    rw [clusterCrossing_incident_eq_neighbors G c Z₀ v hvZ₀]
    exact hv'.2.le
  calc
    (W.card : ℝ) * T = ∑ v ∈ W, T := by simp
    _ ≤ ∑ v ∈ W, (incidentCount A v : ℝ) := sum_le_sum hpoint
    _ ≤ ∑ v : V, (incidentCount A v : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ W) (fun _ _ _ => Nat.cast_nonneg _)
    _ = 2 * (A.card : ℝ) := by exact_mod_cast total_incidence A

/-- The six-cut budget gives at most `12/θ` new heavy marks. -/
theorem heavyVertices_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → C) (Z Z₀ : Finset V) (θ : ℝ) (k₀ : ℕ)
    (hθ : 0 < θ) (hk : 0 < k₀)
    (hcross : (clusterCrossingEdges G c Z₀).card ≤ 6*k₀) :
    ((heavyVertices G c Z Z₀ (θ*k₀)).card : ℝ) ≤ 12/θ := by
  have hbound := heavyVertices_card_mul_le G c Z Z₀ (θ*k₀)
  have hcrossR : ((clusterCrossingEdges G c Z₀).card : ℝ) ≤ 6*k₀ := by exact_mod_cast hcross
  have hkR : (0 : ℝ) < k₀ := by exact_mod_cast hk
  apply (le_div_iff₀ hθ).mpr
  nlinarith

/-- After marking the actual heavy vertices, every unmarked exceptional
vertex has the required intercluster degree bound in the new clusters. -/
theorem after_marking_cross_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → C) (Z Z₀ : Finset V) (T : ℝ) (v : V)
    (hvZ : v ∈ Z) (hv : v ∉ Z₀ ∪ heavyVertices G c Z Z₀ T) :
    (((G.neighborFinset v).filter
      (fun w => w ∉ Z₀ ∪ heavyVertices G c Z Z₀ T ∧ c w ≠ c v)).card : ℝ) ≤ T := by
  classical
  have hv₀ : v ∉ Z₀ := fun h => hv (mem_union_left _ h)
  have hvW : v ∉ heavyVertices G c Z Z₀ T := fun h => hv (mem_union_right _ h)
  have hT : (((G.neighborFinset v).filter
      (fun w => w ∉ Z₀ ∧ c w ≠ c v)).card : ℝ) ≤ T := by
    by_contra h
    apply hvW
    exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨hvZ,hv₀⟩,lt_of_not_ge h⟩
  have hsub : (G.neighborFinset v).filter
      (fun w => w ∉ Z₀ ∪ heavyVertices G c Z Z₀ T ∧ c w ≠ c v) ⊆
      (G.neighborFinset v).filter (fun w => w ∉ Z₀ ∧ c w ≠ c v) := by
    intro w hw
    obtain ⟨hwG,hwZ,hwc⟩ := mem_filter.mp hw
    exact mem_filter.mpr ⟨hwG,(fun h => hwZ (mem_union_left _ h)),hwc⟩
  exact (Nat.cast_le.mpr (card_le_card hsub)).trans hT

/-- A regular vertex with fewer than its degree in exceptional and
intercluster neighbors has a neighbor in an actual core of its own group. -/
theorem exists_same_cluster_core (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z Z₀ : Finset V) (hZ₀ : Z₀ ⊆ Z)
    (c : V → C) (p : I → C)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hlabel : ∀ i v, v ∈ U i → c v = p i)
    (v : V) (hdegree : Z.card +
      ((G.neighborFinset v).filter (fun w => w ∉ Z₀ ∧ c w ≠ c v)).card < G.degree v) :
    ∃ i w, w ∈ U i ∧ G.Adj v w ∧ p i = c v := by
  classical
  have hcount := same_cluster_core_neighbors_lower G U Z Z₀ hZ₀ hcover c v
  have hpositive : 0 < ((G.neighborFinset v).filter
      (fun w => (∃ i, w ∈ U i) ∧ c w = c v)).card := by omega
  obtain ⟨w,hw⟩ := card_pos.mp hpositive
  obtain ⟨hwG,⟨i,hwi⟩,hc⟩ := mem_filter.mp hw
  exact ⟨i,w,hwi,(mem_neighborFinset G v w).mp hwG,(hlabel i w hwi).symm.trans hc⟩


/-- Enlarging the marked set removes intercluster edges. -/
theorem clusterCrossingEdges_marking_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → C) (Z₀ Z₁ : Finset V) (hZ : Z₀ ⊆ Z₁) :
    clusterCrossingEdges G c Z₁ ⊆ clusterCrossingEdges G c Z₀ := by
  intro e he
  obtain ⟨heG,hu,hv,hc⟩ := mem_filter.mp he
  exact mem_filter.mpr ⟨heG,(fun h => hu (hZ h)),(fun h => hv (hZ h)),hc⟩

/-- An injective re-encoding on the unmarked labels leaves the actual
intercluster edge set unchanged. -/
theorem clusterCrossingEdges_relabel {D : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → C) (d : V → D)
    (Z₀ : Finset V)
    (heq : ∀ u v, u ∉ Z₀ → v ∉ Z₀ → (c u = c v ↔ d u = d v)) :
    clusterCrossingEdges G c Z₀ = clusterCrossingEdges G d Z₀ := by
  ext e
  simp only [clusterCrossingEdges,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨hu,hv,hne⟩
    exact ⟨hu,hv,fun h => hne ((heq _ _ hu hv).mpr h)⟩
  · rintro ⟨hu,hv,hne⟩
    exact ⟨hu,hv,fun h => hne ((heq _ _ hu hv).mp h)⟩

/-- Actual marking eliminates core-free clusters whenever the degree
reserve exceeds the exceptional order and the allowed crossing degree. -/
theorem marking_leaves_represented_labels
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : I → Finset V)
    (Z Z₀ : Finset V) (hZ₀ : Z₀ ⊆ Z) (c : V → C) (p : I → C)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hlabel : ∀ i v, v ∈ U i → c v = p i)
    (T : ℝ) (h : ℕ) (hregular : ∀ v, G.degree v = h)
    (hreserve : (Z.card : ℝ) + T < h) :
    ∀ v, v ∉ Z₀ ∪ heavyVertices G c Z Z₀ T → ∃ i, c v = p i := by
  classical
  let Z₁ := Z₀ ∪ heavyVertices G c Z Z₀ T
  have hZ₁ : Z₁ ⊆ Z := by
    intro v hv
    rcases mem_union.mp hv with hv | hv
    · exact hZ₀ hv
    · exact (mem_sdiff.mp (heavyVertices_subset G c Z Z₀ T hv)).1
  intro v hv
  rcases hcover v with hvZ | ⟨i,hi⟩
  · have hcross := after_marking_cross_degree G c Z Z₀ T v hvZ hv
    have hdegree : Z.card +
        ((G.neighborFinset v).filter (fun w => w ∉ Z₁ ∧ c w ≠ c v)).card < G.degree v := by
      rw [hregular]
      have hreal : (Z.card : ℝ) +
          (((G.neighborFinset v).filter (fun w => w ∉ Z₁ ∧ c w ≠ c v)).card : ℝ) < h := by
        exact lt_of_le_of_lt (add_le_add_left hcross _) hreserve
      exact_mod_cast hreal
    obtain ⟨i,w,_,_,hi⟩ := exists_same_cluster_core G U Z Z₁ hZ₁ c p hcover hlabel v hdegree
    exact ⟨i,hi.symm⟩
  · exact ⟨i,hlabel i v hi⟩

/-- The actual marked set remains exceptional and its growth is bounded
by the cut history through the heavy-vertex estimate. -/
theorem marked_set_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → C) (Z Z₀ : Finset V) (hZ₀ : Z₀ ⊆ Z)
    (θ : ℝ) (k₀ : ℕ) (hθ : 0 < θ) (hk : 0 < k₀)
    (hcross : (clusterCrossingEdges G c Z₀).card ≤ 6*k₀) :
    Z₀ ∪ heavyVertices G c Z Z₀ (θ*k₀) ⊆ Z ∧
      ((Z₀ ∪ heavyVertices G c Z Z₀ (θ*k₀)).card : ℝ) ≤ Z₀.card + 12/θ := by
  constructor
  · intro v hv
    rcases mem_union.mp hv with hv | hv
    · exact hZ₀ hv
    · exact (mem_sdiff.mp (heavyVertices_subset G c Z Z₀ (θ*k₀) hv)).1
  · have hheavy := heavyVertices_card_le G c Z Z₀ θ k₀ hθ hk hcross
    have hcard : ((Z₀ ∪ heavyVertices G c Z Z₀ (θ*k₀)).card : ℝ) ≤
        Z₀.card + (heavyVertices G c Z Z₀ (θ*k₀)).card := by
      exact_mod_cast card_union_le Z₀ (heavyVertices G c Z Z₀ (θ*k₀))
    linarith

end Counting

end Overfull.ForeignRefinement
