import Overfull.CriticalMultigraph
import Overfull.TwoColorEndpoints

/-!
# The two-edge fan argument

The elementary fan property is proved by actual recolorings and the bound
of two endpoints in a two-color component. No fan assertion is assumed.
-/

namespace Overfull.Multigraph

open Finset Classical

variable {V E : Type*} [Fintype E] {G : Multigraph V E} {k : ℕ}

namespace EdgeColoring

omit [Fintype E] in
/-- Shift the color of `xw` to the deleted edge `xv`, then color `xw`
with a color missing at both its ends. -/
theorem extend_two_edge_fan (e f : E) (hfe : f ≠ e) (x v w : V)
    (he : G.edge e = s(x,v)) (hf : G.edge f = s(x,w))
    (c : (G.deleteEdge e).EdgeColoring k) (i j : Fin k)
    (hfj : c.color ⟨f,hfe⟩ = j) (hjv : ¬ c.Covers j v)
    (hix : ¬ c.Covers i x) (hiw : ¬ c.Covers i w) :
    Nonempty (G.EdgeColoring k) := by
  have hx : x ∈ G.edge f := by simp [hf]
  have hji : j ≠ i := by
    intro h
    exact hix ⟨⟨f,hfe⟩, hfj.trans h, hx⟩
  have avoid_e (a : {a : E // a ≠ e}) (haf : a.val ≠ f)
      (z : V) (hze : z ∈ G.edge e) (hza : z ∈ G.edge a.val) : c.color a ≠ j := by
    intro haj
    have hz : z = x ∨ z = v := by simpa only [he, Sym2.mem_iff] using hze
    rcases hz with rfl | rfl
    · have hh := c.proper (haj.trans hfj.symm) hza hx
      exact haf (congrArg Subtype.val hh)
    · exact hjv ⟨a, haj, hza⟩
  have avoid_f (a : {a : E // a ≠ e})
      (z : V) (hzf : z ∈ G.edge f) (hza : z ∈ G.edge a.val) : c.color a ≠ i := by
    intro hai
    have hz : z = x ∨ z = w := by simpa only [hf, Sym2.mem_iff] using hzf
    rcases hz with rfl | rfl
    · exact hix ⟨a, hai, hza⟩
    · exact hiw ⟨a, hai, hza⟩
  let color : E → Fin k := fun a =>
    if ha : a = e then j else if a = f then i else c.color ⟨a,ha⟩
  refine ⟨⟨color, ?_⟩⟩
  intro a b z hab hza hzb
  by_cases hae : a = e
  · subst a
    by_cases hbe : b = e
    · exact hbe.symm
    · by_cases hbf : b = f
      · subst b
        exact (hji (by simpa [color, hfe] using hab)).elim
      · exact (avoid_e ⟨b,hbe⟩ hbf z hza hzb
          (by simpa [color, hbe, hbf] using hab.symm)).elim
  · by_cases haf : a = f
    · subst a
      by_cases hbe : b = e
      · subst b
        exact (hji (by simpa [color, hfe] using hab.symm)).elim
      · by_cases hbf : b = f
        · exact hbf.symm
        · exact (avoid_f ⟨b,hbe⟩ z hza hzb
            (by simpa [color, hfe, hbe, hbf] using hab.symm)).elim
    · by_cases hbe : b = e
      · subst b
        exact (avoid_e ⟨a,hae⟩ haf z hzb hza
          (by simpa [color, hae, haf] using hab)).elim
      · by_cases hbf : b = f
        · subst b
          exact (avoid_f ⟨a,hae⟩ z hzb hza
            (by simpa [color, hfe, hae, haf] using hab)).elim
        · exact congrArg Subtype.val (c.proper
            (by simpa [color, hae, haf, hbe, hbf] using hab) hza hzb)

end EdgeColoring

namespace IsKMinimal

variable [Fintype V] (hG : G.IsKMinimal k)

include hG

/-- The three vertices of a two-edge fan have pairwise disjoint missing
color sets. This is proved from the actual two-color component switch. -/
theorem two_edge_fan_elementary (e f : E) (hfe : f ≠ e) (x v w : V)
    (he : G.edge e = s(x,v)) (hf : G.edge f = s(x,w)) (hvw : v ≠ w)
    (c : (G.deleteEdge e).EdgeColoring k)
    (hfv : ¬ c.Covers (c.color ⟨f,hfe⟩) v) :
    Disjoint (c.missingColors x) (c.missingColors v) ∧
    Disjoint (c.missingColors x) (c.missingColors w) ∧
    Disjoint (c.missingColors v) (c.missingColors w) := by
  have hxv := hG.missing_disjoint e x v he c
  have hxw : Disjoint (c.missingColors x) (c.missingColors w) := by
    apply Finset.disjoint_left.mpr
    intro i hix hiw
    exact hG.2.1 (c.extend_two_edge_fan e f hfe x v w he hf i
      (c.color ⟨f,hfe⟩) rfl hfv
      ((c.mem_missingColors x i).mp hix) ((c.mem_missingColors w i).mp hiw))
  refine ⟨hxv,hxw,?_⟩
  apply Finset.disjoint_left.mpr
  intro β hβv hβw
  have hβv' := (c.mem_missingColors v β).mp hβv
  have hβw' := (c.mem_missingColors w β).mp hβw
  have hxinc : x ∈ G.edge e := by simp [he]
  obtain ⟨α,hαx⟩ := hG.missing_at_endpoint e x hxinc c
  have hαv : c.Covers α v := by
    by_contra hn
    exact Finset.disjoint_left.mp hxv
      ((c.mem_missingColors x α).mpr hαx) ((c.mem_missingColors v α).mpr hn)
  have hαw : c.Covers α w := by
    by_contra hn
    exact Finset.disjoint_left.mp hxw
      ((c.mem_missingColors x α).mpr hαx) ((c.mem_missingColors w α).mpr hn)
  have hβx : c.Covers β x := by
    by_contra hn
    exact Finset.disjoint_left.mp hxv ((c.mem_missingColors x β).mpr hn) hβv
  have hαβ : α ≠ β := by intro hh; exact hαx (hh ▸ hβx)
  have hcolorα : c.color ⟨f,hfe⟩ ≠ α := by intro hh; exact hfv (hh ▸ hαv)
  have hcolorβ : c.color ⟨f,hfe⟩ ≠ β := by
    intro hh
    exact hβw' ⟨⟨f,hfe⟩,hh,by simp [deleteEdge,hf]⟩
  let C := (c.twoColorGraph α β).connectedComponentMk x
  let X := c.componentVertices α β C
  have hxX : x ∈ X := by
    simp only [X, EdgeColoring.mem_componentVertices,
      SimpleGraph.ConnectedComponent.mem_supp_iff, C]
  let d := c.swapOn α β X (c.component_closed α β C)
  have hdβx : ¬ d.Covers β x := by
    rw [EdgeColoring.swapOn_covers]
    simpa only [if_pos hxX, Equiv.swap_apply_right] using hαx
  by_cases hvX : v ∈ X
  · have hxne : x ≠ v := by
      intro hh
      exact G.loopless e (by rw [he,hh]; simp)
    have hxwne : x ≠ w := by
      intro hh
      exact G.loopless f (by rw [hf,hh]; simp)
    have hwX : w ∉ X := by
      intro hwX
      have hsubset : ({x,v,w} : Finset V) ⊆ c.componentEndpoints α β C := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact Finset.mem_filter.mpr ⟨hxX,Or.inr ⟨hβx,hαx⟩⟩
        · exact Finset.mem_filter.mpr ⟨hvX,Or.inl ⟨hαv,hβv'⟩⟩
        · exact Finset.mem_filter.mpr ⟨hwX,Or.inl ⟨hαw,hβw'⟩⟩
      have hcard := Finset.card_le_card hsubset
      have hbound := c.componentEndpoints_card_le_two α β hαβ C
      have hthree : ({x,v,w} : Finset V).card = 3 := by simp [hxne,hxwne,hvw]
      omega
    have hdβw : ¬ d.Covers β w := by
      rw [EdgeColoring.swapOn_covers]
      simpa only [if_neg hwX] using hβw'
    have hdfv : ¬ d.Covers (c.color ⟨f,hfe⟩) v := by
      rw [EdgeColoring.swapOn_covers]
      simpa only [Equiv.swap_apply_of_ne_of_ne hcolorα hcolorβ, ite_self] using hfv
    have hdf : d.color ⟨f,hfe⟩ = c.color ⟨f,hfe⟩ := by
      rw [EdgeColoring.swapOn_color_at_vertex _ _ _ _ _ (v := x)
        (by simp [deleteEdge,hf])]
      simp only [if_pos hxX, Equiv.swap_apply_of_ne_of_ne hcolorα hcolorβ]
    exact hG.2.1 (d.extend_two_edge_fan e f hfe x v w he hf β
      (c.color ⟨f,hfe⟩) hdf hdfv hdβx hdβw)
  · have hdβv : ¬ d.Covers β v := by
      rw [EdgeColoring.swapOn_covers]
      simpa only [if_neg hvX] using hβv'
    exact hG.2.1 ⟨d.restoreMissing e x v he β hdβx hdβv⟩

/-- The low-degree-neighbor consequence of the fan argument. The budget is
given pointwise, which also covers the empty set without extra notation. -/
theorem no_edgesTo_low_set (x : V) (X : Finset V) (s : ℕ)
    (hdegree : ∀ v ∈ X, G.degree v ≤ s) (hs : 2 * s ≤ k)
    (hbudget : ∀ v ∈ X,
      (G.edgesTo x Xᶜ).card + (G.parallelEdges x v).card ≤ k - s + 1) :
    G.edgesTo x X = ∅ := by
  by_contra hne
  obtain ⟨e,heX⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨hxe,hvX⟩ := (G.mem_edgesTo x X e).mp heX
  let v := G.otherEnd x e
  have he : G.edge e = s(x,v) := G.edge_eq_otherEnd x e hxe
  obtain ⟨c⟩ := hG.2.2 e
  let F : Finset {a : E // a ≠ e} :=
    univ.filter (fun a => c.color a ∈ c.missingColors v ∧ x ∈ G.edge a.val)
  let A : Finset E := F.image Subtype.val
  have hcolorImage : F.image c.color = c.missingColors v := by
    ext i
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact (Finset.mem_filter.mp ha).2.1
    · intro hi
      have hcix : c.Covers i x := by
        by_contra hn
        exact Finset.disjoint_left.mp (hG.missing_disjoint e x v he c)
          ((c.mem_missingColors x i).mpr hn) hi
      obtain ⟨a,hai,hxa⟩ := hcix
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [hai] using hi, hxa⟩, hai⟩
  have hcolorInj : Set.InjOn c.color F := by
    intro a ha b hb hab
    exact c.proper hab (Finset.mem_filter.mp ha).2.2 (Finset.mem_filter.mp hb).2.2
  have hAcard : A.card = (c.missingColors v).card := by
    rw [Finset.card_image_of_injective F Subtype.val_injective]
    rw [← hcolorImage, Finset.card_image_of_injOn hcolorInj]
  have hmissingv : k - s + 1 ≤ (c.missingColors v).card := by
    have hd := G.deleteEdge_degree_add e v
    have hv : v ∈ G.edge e := by simp [he]
    rw [if_pos hv] at hd
    have hc := c.missingColors_card_add_degree v
    have hdv := hdegree v hvX
    omega
  have hepar : e ∈ G.parallelEdges x v := (G.mem_parallelEdges x v e).mpr ⟨hxe,rfl⟩
  let B := G.edgesTo x Xᶜ ∪ (G.parallelEdges x v).erase e
  have hBcard : B.card < A.card := by
    have hb := Finset.card_union_le (G.edgesTo x Xᶜ) ((G.parallelEdges x v).erase e)
    have hp := Finset.card_erase_add_one hepar
    have hbud := hbudget v hvX
    change B.card ≤ _ at hb
    omega
  obtain ⟨f,hfA,hfB⟩ := Finset.exists_mem_notMem_of_card_lt_card hBcard
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hfA
  have hxa : x ∈ G.edge a.val := (Finset.mem_filter.mp ha).2.2
  have hcolorv : ¬ c.Covers (c.color a) v :=
    (c.mem_missingColors v (c.color a)).mp (Finset.mem_filter.mp ha).2.1
  let w := G.otherEnd x a.val
  have hwX : w ∈ X := by
    by_contra hw
    exact hfB (Finset.mem_union.mpr (Or.inl
      ((G.mem_edgesTo x Xᶜ a.val).mpr ⟨hxa,Finset.mem_compl.mpr hw⟩)))
  have hvw : v ≠ w := by
    intro hvw
    exact hfB (Finset.mem_union.mpr (Or.inr (Finset.mem_erase.mpr
      ⟨a.property, (G.mem_parallelEdges x v a.val).mpr ⟨hxa,hvw.symm⟩⟩)))
  have hdisj := (hG.two_edge_fan_elementary e a.val a.property x v w he
    (G.edge_eq_otherEnd x a.val hxa) hvw c hcolorv).2.2
  have hmissingw : k - s ≤ (c.missingColors w).card := by
    have hd := G.deleteEdge_degree_add e w
    have hc := c.missingColors_card_add_degree w
    have hdw := hdegree w hwX
    omega
  have hcard := Finset.card_le_univ (c.missingColors v ∪ c.missingColors w)
  rw [Finset.card_union_of_disjoint hdisj, Fintype.card_fin] at hcard
  omega

/-- Lemma 2.6(2), with the maximum multiplicity written as a finite supremum. -/
theorem fan_low_degree_set (x : V) (X : Finset V) (s : ℕ)
    (hdegree : ∀ v ∈ X, G.degree v ≤ s) (hs : 2 * s ≤ k)
    (hbudget : (G.edgesTo x Xᶜ).card + X.sup (fun v => (G.parallelEdges x v).card)
      ≤ k - s + 1) :
    G.edgesTo x X = ∅ := by
  apply hG.no_edgesTo_low_set x X s hdegree hs
  intro v hv
  exact (Nat.add_le_add_left (Finset.le_sup (f := fun v => (G.parallelEdges x v).card) hv)
    (G.edgesTo x Xᶜ).card).trans hbudget

/-- The same fan consequence with an arbitrary real degree bound. -/
theorem fan_low_degree_set_real (x : V) (X : Finset V) (hX : X.Nonempty) (s : ℝ)
    (hdegree : ∀ v ∈ X, (G.degree v : ℝ) ≤ s) (hs : 2 * s ≤ k)
    (hbudget : ((G.edgesTo x Xᶜ).card : ℝ) +
      ((X.sup (fun v => (G.parallelEdges x v).card) : ℕ) : ℝ) ≤ (k : ℝ) - s + 1) :
    G.edgesTo x X = ∅ := by
  obtain ⟨v,hv⟩ := hX
  have hs0 : 0 ≤ s := (Nat.cast_nonneg (G.degree v)).trans (hdegree v hv)
  have hfloor := Nat.floor_le hs0
  have htk : Nat.floor s ≤ k := by
    have h : (Nat.floor s : ℝ) ≤ k := by linarith
    exact_mod_cast h
  apply hG.fan_low_degree_set x X (Nat.floor s)
    (fun v hv => Nat.le_floor (hdegree v hv))
  · have h : 2 * (Nat.floor s : ℝ) ≤ k := by linarith
    exact_mod_cast h
  · have h : (((G.edgesTo x Xᶜ).card +
        X.sup (fun v => (G.parallelEdges x v).card) : ℕ) : ℝ) ≤
        ((k - Nat.floor s + 1 : ℕ) : ℝ) := by
      simp only [Nat.cast_add, Nat.cast_sub htk, Nat.cast_one]
      linarith
    exact_mod_cast h

end IsKMinimal

end Overfull.Multigraph
