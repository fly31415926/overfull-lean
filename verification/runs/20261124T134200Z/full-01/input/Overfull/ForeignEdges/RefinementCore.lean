import Overfull.ForeignEdges.Refinement
import Overfull.OrdinaryRobustStability
import Overfull.RobustRealization.Relabeling

/-!
# The actual core after a minority-vertex move

The surviving graph has vertex set `U \\ W`, with every edge inherited from
the original core.  The degree loss and robust parameters are proved for
this actual graph, so the result applies at each refinement restart.
-/

namespace Overfull.ForeignRefinement

open Finset Classical SimpleGraph SafePrescription
open scoped BigOperators

variable {V : Type*}

/-- The inclusion of the surviving core vertices into the old core. -/
def survivingInclusion (U W : Finset V) : ↥(U \ W) ↪ U where
  toFun v := ⟨v.val,(mem_sdiff.mp v.property).1⟩
  inj' := by intro v w h; exact Subtype.ext (congrArg (fun x : U => x.val) h)

/-- Restrict the old core to its surviving actual vertices. -/
def survivingCore (U W : Finset V) (H : SimpleGraph U) : SimpleGraph ↥(U \ W) :=
  H.comap (survivingInclusion U W)

instance (U W : Finset V) (H : SimpleGraph U) [DecidableRel H.Adj] :
    DecidableRel (survivingCore U W H).Adj :=
  inferInstanceAs (DecidableRel (H.comap (survivingInclusion U W)).Adj)

/-- The same surviving vertices, viewed inside the old core type. -/
noncomputable def keptCoreVertices (U W : Finset V) : Finset U :=
  univ.filter (fun v => v.val ∉ W)

@[simp] theorem mem_keptCoreVertices (U W : Finset V) (v : U) :
    v ∈ keptCoreVertices U W ↔ v.val ∉ W := by simp [keptCoreVertices]

/-- The two descriptions of the surviving vertex set carry the same
original vertex labels. -/
noncomputable def survivingEquiv (U W : Finset V) :
    ↥(U \ W) ≃ ↥(keptCoreVertices U W) where
  toFun v := ⟨survivingInclusion U W v,
    (mem_keptCoreVertices U W _).mpr (mem_sdiff.mp v.property).2⟩
  invFun v := ⟨v.val.val,mem_sdiff.mpr
    ⟨v.val.property,(mem_keptCoreVertices U W v.val).mp v.property⟩⟩
  left_inv := by intro v; rfl
  right_inv := by intro v; rfl

theorem keptCoreVertices_card (U W : Finset V) :
    (keptCoreVertices U W).card = (U \ W).card := by
  simpa only [Fintype.card_coe] using
    (Fintype.card_congr (survivingEquiv U W)).symm

/-- The restriction is exactly the induced graph, transported along the
identity on original vertex labels. -/
theorem survivingCore_eq_comap (U W : Finset V) (H : SimpleGraph U) :
    survivingCore U W H =
      (H.induce (keptCoreVertices U W : Set U)).comap (survivingEquiv U W) := by
  rfl

/-- The new core remains an actual subgraph of the same ambient graph. -/
theorem survivingCore_le_ambient (G : SimpleGraph V) (U W : Finset V)
    (H : SimpleGraph U) (hH : H ≤ G.induce (U : Set V)) :
    survivingCore U W H ≤ G.induce ((U \ W : Finset V) : Set V) := by
  intro u v huv
  exact hH huv

/-- On the ambient vertex type, the surviving core is contained in the
original lifted core. -/
theorem survivingCore_lift_le (U W : Finset V) (H : SimpleGraph U) :
    Replacement.lift (U \ W) (survivingCore U W H) ≤ Replacement.lift U H := by
  rintro u v ⟨x,y,hxy,rfl,rfl⟩
  exact ⟨survivingInclusion U W x,survivingInclusion U W y,hxy,rfl,rfl⟩

/-- A surviving vertex loses at most the number of deleted vertices.
Both degrees are those of the actual core graphs. -/
theorem survivingCore_degree_bounds (U W : Finset V) (H : SimpleGraph U)
    [DecidableRel H.Adj] (v : ↥(U \ W)) :
    (survivingCore U W H).degree v ≤ H.degree (survivingInclusion U W v) ∧
      H.degree (survivingInclusion U W v) ≤ (survivingCore U W H).degree v + W.card := by
  classical
  let K := H.induce (keptCoreVertices U W : Set U)
  have heq : (survivingCore U W H).degree v = K.degree (survivingEquiv U W v) := by
    exact RobustRealization.comap_equiv_degree K (survivingEquiv U W) v
  have hbounds := OrdinaryRobustStability.induced_degree_bounds H
    (keptCoreVertices U W) (survivingEquiv U W v)
  have hcard : U.card ≤ (U \ W).card + W.card := card_le_card_sdiff_add_card
  rw [keptCoreVertices_card,Fintype.card_coe] at hbounds
  change K.degree (survivingEquiv U W v) ≤ H.degree (survivingInclusion U W v) ∧
      H.degree (survivingInclusion U W v) + (U \ W).card ≤
        K.degree (survivingEquiv U W v) + U.card at hbounds
  rw [heq]
  exact ⟨hbounds.1,by omega⟩

/-- An at-most-one-vertex move increases the core error by at most one. -/
theorem survivingCore_degree_error (U W : Finset V) (H : SimpleGraph U)
    [DecidableRel H.Adj] (hW : W.card ≤ 1) (h a : ℝ)
    (hdegree : ∀ v, h-a ≤ (H.degree v : ℝ) ∧ (H.degree v : ℝ) ≤ h) :
    ∀ v, h-(a+1) ≤ ((survivingCore U W H).degree v : ℝ) ∧
      ((survivingCore U W H).degree v : ℝ) ≤ h := by
  intro v
  have hb := survivingCore_degree_bounds U W H v
  have hupper : ((survivingCore U W H).degree v : ℝ) ≤ H.degree (survivingInclusion U W v) := by
    exact_mod_cast hb.1
  have hlower : (H.degree (survivingInclusion U W v) : ℝ) ≤
      (survivingCore U W H).degree v + 1 := by
    exact_mod_cast (hb.2.trans (Nat.add_le_add_left hW _))
  have hd := hdegree (survivingInclusion U W v)
  constructor <;> linarith

/-- The explicit deletion allowance gives fixed robust parameters for the
actual surviving core. -/
theorem survivingCore_robust (U W : Finset V) (H : SimpleGraph U)
    [DecidableRel H.Adj] (ν τ : ℝ)
    (hrobust : IsRobustExpander H ν τ) (hν : 0 ≤ ν) (hνone : ν ≤ 1)
    (hτ : 0 ≤ τ) (hτquarter : τ < 1/4)
    (hdelete : (W.card : ℝ) ≤ ν*U.card/2) :
    IsRobustExpander (survivingCore U W H) (ν/2) (2*τ) := by
  classical
  have hcard : U.card ≤ (U \ W).card + W.card := card_le_card_sdiff_add_card
  have hloss : (Fintype.card U : ℝ) - (keptCoreVertices U W).card ≤ ν*Fintype.card U/2 := by
    rw [keptCoreVertices_card,Fintype.card_coe]
    have hcardR : (U.card : ℝ) ≤ (U \ W).card + W.card := by exact_mod_cast hcard
    linarith
  have hR := IsRobustExpander.after_vertex_deletion H hrobust hν hνone hτ hτquarter
    (keptCoreVertices U W) hloss
  convert RobustRealization.robust_comap_equiv
    (H.induce (keptCoreVertices U W : Set U)) (survivingEquiv U W) (ν/2) (2*τ) hR using 1

/-- One vertex can be moved whenever `2 ≤ ν*|U|`.  This bound is imposed
once at a refinement restart, not once per matching deletion. -/
theorem survivingCore_robust_one (U W : Finset V) (H : SimpleGraph U)
    [DecidableRel H.Adj] (ν τ : ℝ)
    (hrobust : IsRobustExpander H ν τ) (hν : 0 ≤ ν) (hνone : ν ≤ 1)
    (hτ : 0 ≤ τ) (hτquarter : τ < 1/4)
    (hW : W.card ≤ 1) (hlarge : 2 ≤ ν*U.card) :
    IsRobustExpander (survivingCore U W H) (ν/2) (2*τ) := by
  apply survivingCore_robust U W H ν τ hrobust hν hνone hτ hτquarter
  have hWR : (W.card : ℝ) ≤ 1 := by exact_mod_cast hW
  linarith


/-- A packing output at half the desired range can be restarted after a
minority move at the fixed range `τ`.  Its next neighborhood parameter is
chosen uniformly from the preceding output parameter and that fixed range. -/
theorem survivingCore_restart (U W : Finset V) (H : SimpleGraph U)
    [DecidableRel H.Adj] (ν τ : ℝ)
    (hrobust : IsRobustExpander H ν (τ/2))
    (hν : 0 < ν) (hνone : ν ≤ 1) (hτ : 0 < τ) (hτhalf : τ < 1/2)
    (hW : W.card ≤ 1) (hlarge : 2 ≤ ν*U.card) :
    0 < min ν (τ/2)/2 ∧
      IsRobustExpander (survivingCore U W H) (min ν (τ/2)/2) τ := by
  classical
  have hR := survivingCore_robust_one U W H ν (τ/2) hrobust hν.le hνone
    (by linarith) (by linarith) hW hlarge
  have hR' : IsRobustExpander (survivingCore U W H) (ν/2) τ := by
    convert hR using 1
    ring
  constructor
  · exact div_pos (lt_min hν (by linarith)) (by norm_num)
  · apply IsRobustExpander.mono_parameter _ hR'
    have hmin := min_le_left ν (τ/2)
    linarith

section RefinementStep

variable {I : Type*} [Fintype V] [Fintype I]

/-- The concrete output of one triggered refinement.  The only moved
vertices are the supplied minority deletion; all additional marked vertices
are the actual heavy exceptional vertices. -/
structure RefinementStep (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (H : ∀ i, SimpleGraph (U i)) [∀ i, DecidableRel (H i).Adj]
    (Z Z₀ : Finset V) (c : V → Fin 4) (p : I → Fin 4) (X : Finset V)
    (h : ℕ) (a ν τ T : ℝ) where
  moved : Finset V
  marked : Finset V
  vertexLabel : V → Fin 4
  coreLabel : I → Fin 4
  moved_card : moved.card ≤ 1
  moved_subset : moved ⊆ univ.biUnion U
  moved_disjoint : Disjoint moved Z
  exceptional_card : (Z ∪ moved).card ≤ Z.card + 1
  marked_old : Z₀ ∪ moved ⊆ marked
  marked_exceptional : marked ⊆ Z ∪ moved
  marked_eq : marked = (Z₀ ∪ moved) ∪
    heavyVertices G (refineVertex c X) (Z ∪ moved) (Z₀ ∪ moved) T
  core_disjoint : Pairwise (fun i j => Disjoint (U i \ moved) (U j \ moved))
  core_exceptional_disjoint : ∀ i, Disjoint (U i \ moved) (Z ∪ moved)
  cover : ∀ v, v ∈ Z ∪ moved ∨ ∃ i, v ∈ U i \ moved
  core_order : ∀ i, 2 ≤ (U i \ moved).card
  core_order_loss : ∀ i, (U i).card ≤ (U i \ moved).card + 1
  core_shore : ∀ i v, v ∈ U i \ moved → (v ∈ X ↔ coreMajority U X i)
  homogeneous : ∀ i v, v ∈ U i \ moved → vertexLabel v = coreLabel i
  represented : ∀ v, v ∉ marked → ∃ i, vertexLabel v = coreLabel i
  label_eq : ∀ u v, u ∉ marked → v ∉ marked →
    (vertexLabel u = vertexLabel v ↔ refineVertex c X u = refineVertex c X v)
  core_label_eq : ∀ i j, coreLabel i = coreLabel j ↔ refineCore p U X i = refineCore p U X j
  refines_old_groups : ∀ i j, coreLabel i = coreLabel j → p i = p j
  groups_increase : (univ.image p).card < (univ.image coreLabel).card
  core_ambient : ∀ i, survivingCore (U i) moved (H i) ≤ G.induce ((U i \ moved : Finset V) : Set V)
  core_degree : ∀ i v, (h : ℝ)-(a+1) ≤ ((survivingCore (U i) moved (H i)).degree v : ℝ) ∧
    ((survivingCore (U i) moved (H i)).degree v : ℝ) ≤ h
  core_robust : ∀ i, IsRobustExpander (survivingCore (U i) moved (H i)) (ν/2) (2*τ)
  cross_degree : ∀ v ∈ Z ∪ moved, v ∉ marked →
    (((G.neighborFinset v).filter (fun w => w ∉ marked ∧ vertexLabel w ≠ vertexLabel v)).card : ℝ) ≤ T

/-- A triggered cut produces one full refinement, including actual
surviving robust cores and Fin-4 labels after the heavy vertices are marked.
The numerical reserve is used to prove that no core-free group retains an
unmarked vertex. -/
theorem exists_refinement_step (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (H : ∀ i, SimpleGraph (U i)) [∀ i, DecidableRel (H i).Adj]
    (Z Z₀ : Finset V) (c : V → Fin 4) (p : I → Fin 4) (X : Finset V)
    (h : ℕ) (a ν τ T : ℝ)
    (hI : Fintype.card I ≤ 4)
    (hdisjoint : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hUZ : ∀ i, Disjoint (U i) Z) (hZ₀ : Z₀ ⊆ Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hlabel : ∀ i v, v ∈ U i → c v = p i)
    (horder : ∀ i, 3 ≤ (U i).card)
    (hminority : (∑ i, min (X ∩ U i).card (U i \ X).card) ≤ 1)
    (htrigger : ∃ i j, p i = p j ∧ ¬ (coreMajority U X i ↔ coreMajority U X j))
    (hregular : ∀ v, G.degree v = h)
    (hreserve : (Z.card : ℝ)+1+T < h)
    (hembed : ∀ i, H i ≤ G.induce (U i : Set V))
    (hdegree : ∀ i v, (h : ℝ)-a ≤ ((H i).degree v : ℝ) ∧ ((H i).degree v : ℝ) ≤ h)
    (hrobust : ∀ i, IsRobustExpander (H i) ν τ)
    (hν : 0 ≤ ν) (hνone : ν ≤ 1) (hτ : 0 ≤ τ) (hτquarter : τ < 1/4)
    (hlarge : ∀ i, 2 ≤ ν*(U i).card) :
    Nonempty (RefinementStep G U H Z Z₀ c p X h a ν τ T) := by
  classical
  obtain ⟨W,hWsubset,hW,hWZold,hZcard,hWloss,hWtwo,_,hWdisj,hWZ,hWcover,hWshore⟩ :=
    minority_shore_deletion U Z X hdisjoint hUZ hcover horder hminority
  let d := refineVertex c X
  let q := refineCore p U X
  let Zpre := Z₀ ∪ W
  let Znew := Z ∪ W
  let Z₁ := Zpre ∪ heavyVertices G d Znew Zpre T
  have hpre : Zpre ⊆ Znew := union_subset_union hZ₀ subset_rfl
  have hmark : Z₁ ⊆ Znew := by
    intro v hv
    rcases mem_union.mp hv with hv | hv
    · exact hpre hv
    · exact (mem_sdiff.mp (heavyVertices_subset G d Znew Zpre T hv)).1
  have hnewlabel (i : I) (v : V) (hv : v ∈ U i \ W) : d v = q i := by
    have hc := hlabel i v (mem_sdiff.mp hv).1
    have hs := hWshore i v hv
    exact Prod.ext hc (decide_eq_decide.mpr hs)
  have hnewreserve : (Znew.card : ℝ)+T < h := by
    have hcard : (Znew.card : ℝ) ≤ Z.card+1 := by exact_mod_cast hZcard
    linarith
  have hrepresented : ∀ v, v ∉ Z₁ → ∃ i, d v = q i :=
    marking_leaves_represented_labels G (fun i => U i \ W) Znew Zpre hpre d q
      hWcover hnewlabel T h hregular hnewreserve
  obtain ⟨p',c',hpeq,hencode,hceq,hp'card⟩ := encode_labels_fin_four q d Z₁ hI hrepresented
  have hcross (v : V) (hvZ : v ∈ Znew) (hv : v ∉ Z₁) :
      (((G.neighborFinset v).filter (fun w => w ∉ Z₁ ∧ c' w ≠ c' v)).card : ℝ) ≤ T := by
    have hbound := after_marking_cross_degree G d Znew Zpre T v hvZ hv
    have heq : (G.neighborFinset v).filter (fun w => w ∉ Z₁ ∧ c' w ≠ c' v) =
        (G.neighborFinset v).filter (fun w => w ∉ Z₁ ∧ d w ≠ d v) := by
      ext w
      simp only [mem_filter]
      constructor
      · rintro ⟨hwG,hw,hne⟩
        exact ⟨hwG,hw,fun hh => hne ((hceq w v hw hv).mpr hh)⟩
      · rintro ⟨hwG,hw,hne⟩
        exact ⟨hwG,hw,fun hh => hne ((hceq w v hw hv).mp hh)⟩
    rw [heq]
    convert hbound using 1
    congr 2
    ext w
    simp only [mem_filter]
    rfl
  have hincrease : (univ.image p).card < (univ.image p').card := by
    rw [hp'card]
    obtain ⟨i,j,hp,hmajority⟩ := htrigger
    exact core_groups_increase p U X i j hp hmajority
  refine ⟨{
    moved := W
    marked := Z₁
    vertexLabel := c'
    coreLabel := p'
    moved_card := hW
    moved_subset := hWsubset
    moved_disjoint := hWZold
    exceptional_card := hZcard
    marked_old := subset_union_left
    marked_exceptional := hmark
    marked_eq := rfl
    core_disjoint := hWdisj
    core_exceptional_disjoint := hWZ
    cover := hWcover
    core_order := hWtwo
    core_order_loss := hWloss
    core_shore := hWshore
    homogeneous := fun i v hv => hencode v i (hnewlabel i v hv)
    represented := ?_
    label_eq := hceq
    core_label_eq := hpeq
    refines_old_groups := fun i j hij => congrArg Prod.fst ((hpeq i j).mp hij)
    groups_increase := hincrease
    core_ambient := fun i => survivingCore_le_ambient G (U i) W (H i) (hembed i)
    core_degree := fun i => survivingCore_degree_error (U i) W (H i) hW h a (hdegree i)
    core_robust := fun i => survivingCore_robust_one (U i) W (H i) ν τ (hrobust i)
      hν hνone hτ hτquarter hW (hlarge i)
    cross_degree := hcross
  }⟩
  intro v hv
  obtain ⟨i,hi⟩ := hrepresented v hv
  exact ⟨i,hencode v i hi⟩

/-- The marks constructed by one refinement grow by at most one moved
core vertex and `12/θ` genuinely heavy exceptional vertices. -/
theorem RefinementStep.marked_card_growth
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (H : ∀ i, SimpleGraph (U i)) [∀ i, DecidableRel (H i).Adj]
    (Z Z₀ : Finset V) (c : V → Fin 4) (p : I → Fin 4) (X : Finset V)
    (h k₀ : ℕ) (a ν τ θ : ℝ)
    (R : RefinementStep G U H Z Z₀ c p X h a ν τ (θ*k₀))
    (hZ₀ : Z₀ ⊆ Z) (hθ : 0 < θ) (hk : 0 < k₀)
    (hcross : (clusterCrossingEdges G (refineVertex c X) (Z₀ ∪ R.moved)).card ≤ 6*k₀) :
    (R.marked.card : ℝ) ≤ Z₀.card + 1 + 12/θ := by
  have hpre : Z₀ ∪ R.moved ⊆ Z ∪ R.moved := union_subset_union hZ₀ subset_rfl
  have hbound := (marked_set_bound G (refineVertex c X) (Z ∪ R.moved)
    (Z₀ ∪ R.moved) hpre θ k₀ hθ hk hcross).2
  have hcard : ((Z₀ ∪ R.moved).card : ℝ) ≤ Z₀.card + 1 := by
    have hn := (card_union_le Z₀ R.moved).trans (Nat.add_le_add_left R.moved_card Z₀.card)
    exact_mod_cast hn
  rw [R.marked_eq]
  exact hbound.trans (by linarith)

/-- Re-encoding and marking preserve the edge budget inherited from the
actual recorded shore history. -/
theorem RefinementStep.crossing_edges_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (H : ∀ i, SimpleGraph (U i)) [∀ i, DecidableRel (H i).Adj]
    (Z Z₀ : Finset V) (c : V → Fin 4) (p : I → Fin 4) (X : Finset V)
    (h B : ℕ) (a ν τ T : ℝ)
    (R : RefinementStep G U H Z Z₀ c p X h a ν τ T)
    (hcross : (clusterCrossingEdges G (refineVertex c X) (Z₀ ∪ R.moved)).card ≤ B) :
    (clusterCrossingEdges G R.vertexLabel R.marked).card ≤ B := by
  rw [clusterCrossingEdges_relabel G R.vertexLabel (refineVertex c X) R.marked R.label_eq]
  exact (card_le_card (clusterCrossingEdges_marking_mono G (refineVertex c X)
    (Z₀ ∪ R.moved) R.marked R.marked_old)).trans hcross

end RefinementStep

end Overfull.ForeignRefinement
