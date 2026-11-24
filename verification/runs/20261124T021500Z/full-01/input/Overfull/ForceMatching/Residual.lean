import Overfull.ForceMatching.Family
import Overfull.ForceMatching.Cuts

namespace Overfull.ForceMatching

open Finset Classical MatchingProbability

variable {V I : Type*} [Fintype V]

omit [Fintype V] in
theorem starHit_mono {G : SimpleGraph V} (M N : G.Subgraph) (hMN : M ≤ N)
    (S : Finset G.edgeSet) (h : StarHit M S) : StarHit N S := by
  obtain ⟨e,heS,heM⟩ := h
  exact ⟨e,heS,SimpleGraph.Subgraph.edgeSet_mono hMN heM⟩

omit [Fintype V] in
/-- Retaining the sampled matching edges meeting the exceptional set
retains its selected edge in every exceptional-centered star. -/
theorem starHit_of_exceptional_retention {G : SimpleGraph V} (M Q : G.Subgraph)
    (Z : Finset V)
    (hretain : ∀ u v, M.Adj u v → u ∈ Z ∨ v ∈ Z → Q.Adj u v)
    (S : Finset G.edgeSet) (v : V) (hvZ : v ∈ Z)
    (hstar : ∀ e ∈ S, v ∈ e.val) (h : StarHit M S) : StarHit Q S := by
  obtain ⟨e,heS,heM⟩ := h
  have hadj : M.Adj (FractionalMatching.firstEnd e) (FractionalMatching.secondEnd e) := by
    change s(FractionalMatching.firstEnd e,FractionalMatching.secondEnd e) ∈ M.edgeSet
    rw [FractionalMatching.edge_eq e]
    exact heM
  have heZ : FractionalMatching.firstEnd e ∈ Z ∨ FractionalMatching.secondEnd e ∈ Z := by
    rcases (FractionalMatching.incident_iff e v).mp (hstar e heS) with he | he
    · exact Or.inl (by simpa only [he] using hvZ)
    · exact Or.inr (by simpa only [he] using hvZ)
  refine ⟨e,heS,?_⟩
  rw [← FractionalMatching.edge_eq e]
  exact hretain _ _ hadj heZ

/-- Embed an actual simple graph on a core into its ambient host. -/
noncomputable def embeddedCore (G : SimpleGraph V) (U : Finset V)
    (H : SimpleGraph U) (hH : H ≤ G.induce (U : Set V)) :
    SmallCuts.Core (Multigraph.ofSimpleGraph G) U := by
  let f : H →g G := ⟨Subtype.val,fun h => hH h⟩
  exact { graph := H
          edgeMap := ⟨f.mapEdgeSet,SimpleGraph.Hom.mapEdgeSet.injective f Subtype.val_injective⟩
          map_edge := fun _ => rfl }

theorem graphCutCount_eq_cutSize (G : SimpleGraph V) (X : Finset V) :
    graphCutCount G X = (Multigraph.ofSimpleGraph G).cutSize X := by
  have himage : ((Multigraph.ofSimpleGraph G).cutEdges X).image Subtype.val = graphCutEdges G X := by
    ext e
    constructor
    · intro he
      obtain ⟨a,ha,rfl⟩ := mem_image.mp he
      apply mem_filter.mpr
      exact ⟨SimpleGraph.mem_edgeFinset.mpr a.property,
        (Multigraph.mem_cutEdges_iff (Multigraph.ofSimpleGraph G) X a).mp ha⟩
    · intro he
      obtain ⟨heG,heX⟩ := mem_filter.mp he
      let a : G.edgeSet := ⟨e,SimpleGraph.mem_edgeFinset.mp heG⟩
      exact mem_image.mpr ⟨a,(Multigraph.mem_cutEdges_iff (Multigraph.ofSimpleGraph G) X a).mpr heX,rfl⟩
  rw [graphCutCount,← himage,card_image_of_injective _ Subtype.val_injective]
  rfl

/-- The actual residual is overfull on an odd shore exactly when its
cut is too small. -/
theorem regular_overfull_cut (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hregular : ∀ v, G.degree v = k) (X : Finset V) (hodd : X.card % 2 = 1)
    (hOver : IsOverfull G k X) : (Multigraph.ofSimpleGraph G).cutSize X < k := by
  classical
  have h := (overfull_iff_odd_deficiency G X k (fun v => (hregular v).le) hodd).mp hOver
  simp only [hregular,Nat.sub_self,sum_const_zero,zero_add] at h
  simpa only [SmallCuts.simple_cut_boundary] using h

variable [Fintype I]

/-- The small-cut lemma closes the full residual no-overfull conclusion
from the finite tested family. The residual cores are actual embedded
subgraphs; no classification of small cuts is assumed. -/
theorem residual_no_overfull (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z : Finset V)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hZ : ∀ i, Disjoint (U i) Z) (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (k : ℕ) (hregular : ∀ v, G.degree v = k)
    (N : G.Subgraph) (hN : N.IsPerfectMatching)
    (hsafe : ¬ FamilyFailure N k (wholeUnions U Z))
    (H : ∀ i, SimpleGraph (U i))
    (hH : ∀ i, H i ≤ (G \ N.spanningCoe).induce (U i : Set V))
    (α c ν τ a : ℝ) (hα : 0 < α) (hc : 0 < c) (hν : 0 < ν) (hτ : 0 ≤ τ)
    (hτα : τ ≤ α/10)
    (hklo : α*Fintype.card V ≤ (k-1 : ℕ)) (hkhi : ((k-1 : ℕ) : ℝ) ≤ 2*Fintype.card V)
    (ha : a ≤ α*Fintype.card V/10)
    (hlarge : 3 < ν^2*c^2*(Fintype.card V : ℝ))
    (hsize : ∀ i, c*Fintype.card V ≤ ((U i).card : ℝ))
    (hrobust : ∀ i, IsRobustExpander (H i) ν τ)
    (hdegree : ∀ i v, ((k-1 : ℕ) : ℝ)-a ≤ ((H i).degree v : ℝ)) :
    ∀ X : Finset V, ¬ IsOverfull (G \ N.spanningCoe) (k-1) X := by
  classical
  let R := G \ N.spanningCoe
  have hregularR : ∀ v, R.degree v = k-1 := remaining_regular hregular N hN
  let C : ∀ i, SmallCuts.Core (Multigraph.ofSimpleGraph R) (U i) :=
    fun i => embeddedCore R (U i) (H i) (hH i)
  intro X hOver
  have hodd : X.card % 2 = 1 := by
    by_contra h
    exact not_overfull_of_even_card R X (k-1) (fun v => (hregularR v).le) (by omega) hOver
  have hcut := regular_overfull_cut R (k-1) hregularR X hodd hOver
  have hcutR : ((Multigraph.ofSimpleGraph R).cutSize X : ℝ) ≤ ((k-1 : ℕ) : ℝ)+0 := by
    have hinst : G.fintypeEdgeSetSdiff N.spanningCoe = R.fintypeEdgeSet := Subsingleton.elim _ _
    simp only [hinst,add_zero]
    exact_mod_cast hcut.le
  have hb : (0 : ℝ) ≤ α*Fintype.card V/10 := by positivity
  have hminority := SmallCuts.minority_sum_le_one (Multigraph.ofSimpleGraph R) U C hdisj
    α c ν τ a 0 ((k-1 : ℕ) : ℝ) hα hc hν hτ hτα hklo hkhi ha hb hlarge
    hsize hrobust hdegree X hcutR
  have hclass := classified_of_minority U Z X hZ hcover hminority
  have hsafecut := safe_cut_of_classified N k (wholeUnions U Z) hsafe X hodd hclass
  apply hsafecut
  rw [cutFailure_iff_actual_cut,graphCutCount_eq_cutSize]
  convert hcut using 1
  congr 1
  exact Subsingleton.elim _ _

end Overfull.ForceMatching
