import Overfull.ForeignEdges.GlobalParameters
import Overfull.ForeignEdges.RefinementHistory
import Overfull.ForeignEdges.Concatenation

/-!
# Actual entry states for the four foreign-edge epochs

An entry state carries the changed core vertex sets, the actual recorded
cut history, and a perfect-matching prefix in the original graph.  Its
initial constructor uses the original partition and an empty prefix.
The refinement update consumes an actual interrupted matching prefix and
the concrete refinement of its current core graphs.
-/

namespace Overfull.ForeignProcess

open Finset Classical SimpleGraph ForceMatching SafePrescription MatchingProbability
open ForeignEpochParameters ForeignRefinement ForeignPhase ForeignConcatenation

variable {V I : Type*} [Fintype V] [Fintype I]
variable {α τ ν₀ : ℝ}

/-- Complete graph-level data at the beginning of epoch `j`.  The error
increases only when a refinement moves a core vertex. -/
structure Entry (G₀ : SimpleGraph V) (U₀ : I → Finset V) (Zinit : Finset V)
    (k₀ : ℕ) (a₀ : ℝ) (P : RestartParameters α τ ν₀) (j : Fin 4) where
  G : SimpleGraph V
  h : ℕ
  U : I → Finset V
  H : ∀ i, SimpleGraph (U i)
  Z : Finset V
  marked : Finset V
  c : V → Fin 4
  p : I → Fin 4
  history : RefinementHistory k₀ markingThreshold ∅ G marked c p
  history_length : history.length = j.val
  regular : ∀ v, G.degree v = h
  no_overfull : ∀ X : Finset V, ¬ IsOverfull G h X
  degree_le : h ≤ k₀
  retained_degree : k₀ ≤ 4^j.val*h
  core_subset : ∀ i, U i ⊆ U₀ i
  core_order_loss : ∀ i, (U₀ i).card ≤ (U i).card+j.val
  exceptional_subset : Zinit ⊆ Z
  exceptional_card : Z.card ≤ Zinit.card+j.val
  marked_subset : marked ⊆ Z
  core_disjoint : Pairwise (fun i l => Disjoint (U i) (U l))
  core_exceptional_disjoint : ∀ i, Disjoint (U i) Z
  cover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i
  homogeneous : ∀ i v, v ∈ U i → c v = p i
  core_embed : ∀ i, H i ≤ G.induce (U i : Set V)
  core_degree : ∀ i v, (h : ℝ)-(a₀+(j.val : ℝ)) ≤ ((H i).degree v : ℝ)
  core_robust : ∀ i, IsRobustExpander (H i) (P.input j) τ
  represented : ∀ v, v ∉ marked → ∃ i, c v = p i
  cross_degree : ∀ v ∈ Z, v ∉ marked →
    (((G.neighborFinset v).filter (fun w => w ∉ marked ∧ c w ≠ c v)).card : ℝ) ≤
      markingThreshold*k₀
  N : ℕ → G₀.Subgraph
  rounds : ℕ
  graph_eq : G = afterDeletions G₀ N rounds
  perfect : ∀ s < rounds, (N s).IsPerfectMatching
  present : ∀ s < rounds, (N s).spanningCoe ≤ afterDeletions G₀ N s

namespace Entry

variable {G₀ : SimpleGraph V} {U₀ : I → Finset V} {Zinit : Finset V}
variable {k₀ : ℕ} {a₀ : ℝ} {P : RestartParameters α τ ν₀} {j : Fin 4}

/-- The original partition gives an actual initial state.  Labels are
constant, the marked set and recorded history are empty, and no matching
has yet been deleted. -/
noncomputable def initial [Nonempty I]
    (G₀ : SimpleGraph V) (U₀ : I → Finset V) (H₀ : ∀ i, SimpleGraph (U₀ i))
    (Zinit : Finset V) (k₀ : ℕ) (a₀ : ℝ) (P : RestartParameters α τ ν₀)
    (hregular : ∀ v, G₀.degree v = k₀)
    (hsafe : ∀ X : Finset V, ¬ IsOverfull G₀ k₀ X)
    (hdisjoint : Pairwise (fun i l => Disjoint (U₀ i) (U₀ l)))
    (hUZ : ∀ i, Disjoint (U₀ i) Zinit)
    (hcover : ∀ v, v ∈ Zinit ∨ ∃ i, v ∈ U₀ i)
    (hembed : ∀ i, H₀ i ≤ G₀.induce (U₀ i : Set V))
    (hdegree : ∀ i v, (k₀ : ℝ)-a₀ ≤ ((H₀ i).degree v : ℝ))
    (hrobust : ∀ i, IsRobustExpander (H₀ i) ν₀ τ) :
    Entry G₀ U₀ Zinit k₀ a₀ P 0 := by
  classical
  refine {
    G := G₀
    h := k₀
    U := U₀
    H := H₀
    Z := Zinit
    marked := ∅
    c := fun _ => 0
    p := fun _ => 0
    history := RefinementHistory.initial k₀ markingThreshold ∅ G₀ 0
    history_length := rfl
    regular := hregular
    no_overfull := hsafe
    degree_le := le_rfl
    retained_degree := by simp
    core_subset := fun _ => subset_rfl
    core_order_loss := by intro i; simp
    exceptional_subset := subset_rfl
    exceptional_card := by simp
    marked_subset := empty_subset _
    core_disjoint := hdisjoint
    core_exceptional_disjoint := hUZ
    cover := hcover
    homogeneous := fun _ _ _ => rfl
    core_embed := hembed
    core_degree := by simpa using hdegree
    core_robust := by
      intro i
      rw [P.initial]
      exact hrobust i
    represented := fun _ _ => ⟨Classical.ofNonempty,rfl⟩
    cross_degree := ?_
    N := fun _ => ⊥
    rounds := 0
    graph_eq := by simp only [afterDeletions_zero]
    perfect := by intro s hs; omega
    present := by intro s hs; omega
  }
  intro v _ _
  simp only [ne_eq,not_true_eq_false,and_false,filter_false,card_empty,Nat.cast_zero]
  exact mul_nonneg markingThreshold_pos.le (Nat.cast_nonneg _)

/-- The current ambient graph is the actual original-host residual. -/
theorem graph_le_original (E : Entry G₀ U₀ Zinit k₀ a₀ P j) : E.G ≤ G₀ := by
  rw [E.graph_eq]
  exact sdiff_le

/-- The current marked-set bound is derived from its constructed history. -/
theorem marked_card_le (E : Entry G₀ U₀ Zinit k₀ a₀ P j)
    (hI : Fintype.card I ≤ 4) : E.marked.card ≤ markedLimit :=
  E.history.marked_card_le_nat hI markingThreshold_pos markedLimit markedLimit_eq.ge

/-- The current crossing-edge bound is derived from the actual recorded
hosts and shores, including any intervening matching deletions. -/
theorem crossing_card_le (E : Entry G₀ U₀ Zinit k₀ a₀ P j)
    (hI : Fintype.card I ≤ 4) :
    (clusterCrossingEdges E.G E.c E.marked).card ≤ 6*k₀ :=
  E.history.crossing_card_le_six hI

/-- Actual set containment gives the upper core-order bound. -/
theorem core_card_le (E : Entry G₀ U₀ Zinit k₀ a₀ P j) (i : I) :
    (E.U i).card ≤ (U₀ i).card := card_le_card (E.core_subset i)

/-- The core-loss field gives the lower bound in subtraction form. -/
theorem core_card_lower (E : Entry G₀ U₀ Zinit k₀ a₀ P j) (i : I) :
    (U₀ i).card-j.val ≤ (E.U i).card := by
  have hh := E.core_order_loss i
  omega

/-- At the last possible epoch every occupied core label is distinct.
This is forced by the accumulated actual strict refinements. -/
theorem labels_injective_at_three (E : Entry G₀ U₀ Zinit k₀ a₀ P j)
    (hI : Fintype.card I ≤ 4) (hj : j.val = 3) : Function.Injective E.p := by
  have hgroups := E.history.groups
  rw [E.history_length,hj] at hgroups
  have hcard : (univ.image E.p).card = (univ : Finset I).card := by
    have hupper := card_image_le (f := E.p) (s := (univ : Finset I))
    have hI' : (univ : Finset I).card ≤ 4 := by simpa using hI
    omega
  have hinj := card_image_iff.mp hcard
  intro i l hil
  exact hinj (mem_univ i) (mem_univ l) hil

/-- The final epoch has no triggering shore at all.  No small-cut
existence assumption or further robust restart is used here. -/
theorem no_trigger_at_three (E : Entry G₀ U₀ Zinit k₀ a₀ P j)
    (hI : Fintype.card I ≤ 4) (hj : j.val = 3) (X : Finset V)
    (i l : I) (hil : E.p i = E.p l) :
    coreMajority E.U X i ↔ coreMajority E.U X l := by
  have heq := E.labels_injective_at_three hI hj hil
  subst l
  rfl

/-- An actual interrupted epoch followed by its concrete refinement gives
the next entry.  The local matching sequence is appended to the original
host sequence, and the changed core vertex types are the actual survivors.
The input does not assert existence of a next state or a future process. -/
noncomputable def advance (r : Fin 3)
    (E : Entry G₀ U₀ Zinit k₀ a₀ P ⟨r.val,by omega⟩)
    (N : ℕ → E.G.Subgraph) (s : ℕ)
    (hperfect : ∀ m < s, (N m).IsPerfectMatching)
    (hpresent : ∀ m < s, (N m).spanningCoe ≤ afterDeletions E.G N m)
    (hs : s ≤ 3*E.h/4)
    (hsafe : ∀ X : Finset V, ¬ IsOverfull (afterDeletions E.G N s) (E.h-s) X)
    (K : ∀ i, SimpleGraph (E.U i)) (X : Finset V)
    (S : RefinementStep (afterDeletions E.G N s) E.U K E.Z E.marked E.c E.p X
      (E.h-s) (a₀+(r.val : ℝ)) (P.output ⟨r.val,by omega⟩) (τ/2)
      (markingThreshold*k₀))
    (hI : Fintype.card I ≤ 4) (hk₀ : 0 < k₀)
    (hcut : cutCount (univ : Finset (afterDeletions E.G N s).edgeSet) X ≤ 2*k₀) :
    Entry G₀ U₀ Zinit k₀ a₀ P ⟨r.val+1,by omega⟩ := by
  classical
  let R := afterDeletions E.G N s
  have hRG : R ≤ E.G := sdiff_le
  let hist := (E.history.mono_graph hRG).append E.U K E.Z X (E.h-s)
    (a₀+(r.val : ℝ)) (P.output ⟨r.val,by omega⟩) (τ/2) S
    hI E.marked_subset markingThreshold_pos hk₀ hcut
  let Q := appendEpoch G₀ E.G E.graph_le_original E.N E.rounds N
  have hregular (v : V) : R.degree v = E.h-s :=
    (actual_prefix_degree_reserve E.G N k₀ E.h r.val s E.regular
      hperfect hpresent E.retained_degree hs v).1
  refine {
    G := R
    h := E.h-s
    U := fun i => E.U i \ S.moved
    H := fun i => survivingCore (E.U i) S.moved (K i)
    Z := E.Z ∪ S.moved
    marked := S.marked
    c := S.vertexLabel
    p := S.coreLabel
    history := hist
    history_length := ?_
    regular := hregular
    no_overfull := hsafe
    degree_le := (Nat.sub_le _ _).trans E.degree_le
    retained_degree := within_epoch_degree_reserve k₀ E.h r.val s E.retained_degree hs
    core_subset := fun i => sdiff_subset.trans (E.core_subset i)
    core_order_loss := ?_
    exceptional_subset := E.exceptional_subset.trans subset_union_left
    exceptional_card := ?_
    marked_subset := S.marked_exceptional
    core_disjoint := S.core_disjoint
    core_exceptional_disjoint := S.core_exceptional_disjoint
    cover := S.cover
    homogeneous := S.homogeneous
    core_embed := S.core_ambient
    core_degree := ?_
    core_robust := ?_
    represented := S.represented
    cross_degree := S.cross_degree
    N := Q
    rounds := E.rounds+s
    graph_eq := (appendEpoch_suffix G₀ E.G E.graph_le_original E.N E.rounds N E.graph_eq s).symm
    perfect := appendEpoch_perfect G₀ E.G E.graph_le_original E.N E.rounds N s
      E.perfect hperfect
    present := appendEpoch_present G₀ E.G E.graph_le_original E.N E.rounds N s
      E.graph_eq E.present hpresent
  }
  · change E.history.length+1 = r.val+1
    rw [E.history_length]
  · intro i
    have hprior := E.core_order_loss i
    have hstep := S.core_order_loss i
    change (U₀ i).card ≤ (E.U i \ S.moved).card+(r.val+1)
    dsimp only at hprior
    omega
  · have hprior := E.exceptional_card
    have hstep := S.exceptional_card
    change (E.Z ∪ S.moved).card ≤ Zinit.card+(r.val+1)
    dsimp only at hprior
    omega
  · intro i v
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using (S.core_degree i v).1
  · intro i
    rw [P.next r]
    convert S.core_robust i using 1
    ring

end Entry

end Overfull.ForeignProcess
