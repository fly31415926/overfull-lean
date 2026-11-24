import Overfull.Compression.SelectedEdges
import Overfull.ForeignEdges.Incidence

/-!
# Greedy realization of finite boundary demands

Finite pools contain actual host edges.  The construction consumes a fresh
edge from the demanded pool and avoids the core endpoints already occupied
in the same round.  Exceptional endpoints are checked separately, since
those endpoints are prescribed by the demand rather than chosen greedily.
-/

namespace Overfull.PatternRealization

open Finset Classical SimpleGraph
open FractionalMatching MatchingProbability Compression
open scoped BigOperators

variable {V : Type*}

/-- Endpoint uniqueness proves that a finite collection of actual host
edges is a matching; no ambient matching is assumed. -/
theorem selectedMatching_isMatching_of_endpoints (G : SimpleGraph V)
    (A : Finset G.edgeSet)
    (hA : ∀ e ∈ A, ∀ f ∈ A, ∀ v : V, v ∈ e.val → v ∈ f.val → e = f) :
    (selectedMatching G A).IsMatching := by
  rintro v ⟨w,h,ha⟩
  refine ⟨w, ⟨h,ha⟩, ?_⟩
  rintro z ⟨hz,hza⟩
  have he := hA ⟨s(v,z),hz⟩ hza ⟨s(v,w),h⟩ ha v (by simp) (by simp)
  have he' : s(v,z) = s(v,w) := congrArg Subtype.val he
  rcases Sym2.eq_iff.mp he' with ⟨_,heq⟩ | ⟨h₁,h₂⟩
  · exact heq
  · exact h₂.trans h₁

section Pools

variable {S P R E W : Type*} [Fintype S] [DecidableEq P] [DecidableEq E] [DecidableEq W]

/-- Number of slots demanding one edge from a specified pool. -/
noncomputable def demandCount (kind : S → P) (p : P) : ℕ :=
  (univ.filter (fun s => kind s = p)).card

/-- A fresh candidate exists when used edges and forbidden endpoint
incidences occupy strictly less than the pool. -/
theorem exists_fresh_avoiding (pool used : Finset E) (support : E → Finset W)
    (B : Finset W) (d a : ℕ)
    (hused : (pool ∩ used).card ≤ d)
    (hinc : ∀ v ∈ B, (pool.filter (fun e => v ∈ support e)).card ≤ a)
    (hcap : d + B.card * a < pool.card) :
    ∃ e ∈ pool, e ∉ used ∧ Disjoint (support e) B := by
  classical
  let bad := (pool ∩ used) ∪ B.biUnion (fun v => pool.filter (fun e => v ∈ support e))
  have hbad : bad.card ≤ d + B.card * a := by
    calc
      _ ≤ (pool ∩ used).card +
          (B.biUnion (fun v => pool.filter (fun e => v ∈ support e))).card :=
        Finset.card_union_le _ _
      _ ≤ d + ∑ v ∈ B, (pool.filter (fun e => v ∈ support e)).card :=
        Nat.add_le_add hused (Finset.card_biUnion_le)
      _ ≤ d + ∑ _v ∈ B, a :=
        Nat.add_le_add_left (Finset.sum_le_sum hinc) d
      _ = d + B.card * a := by simp
  obtain ⟨e,he,hbadE⟩ := Finset.exists_mem_notMem_of_card_lt_card (hbad.trans_lt hcap)
  refine ⟨e,he,?_,Finset.disjoint_left.mpr ?_⟩
  · intro hu
    exact hbadE (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨he,hu⟩))
  · intro v hv hB
    exact hbadE (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨v,hB,Finset.mem_filter.mpr ⟨he,hv⟩⟩))

/-- Greedy choice from disjoint edge pools.  The support is the set of
core endpoints, so the per-round budget is the sum of the prescribed
core-endpoint arities. -/
theorem exists_pool_selection_of_nonempty [Nonempty E]
    (pool : P → Finset E) (kind : S → P) (round : S → R)
    (support : E → Finset W) (arity : P → ℕ) (a D : ℕ)
    (hpools : ∀ p q, p ≠ q → Disjoint (pool p) (pool q))
    (harity : ∀ p, ∀ e ∈ pool p, (support e).card ≤ arity p)
    (hinc : ∀ s v, ((pool (kind s)).filter (fun e => v ∈ support e)).card ≤ a)
    (hround : ∀ r, ∑ s ∈ univ.filter (fun s => round s = r), arity (kind s) ≤ D)
    (hcap : ∀ s, demandCount kind (kind s) + D * a < (pool (kind s)).card) :
    ∃ pick : S → E,
      (∀ s, pick s ∈ pool (kind s)) ∧ Function.Injective pick ∧
      (∀ i j, i ≠ j → round i = round j →
        Disjoint (support (pick i)) (support (pick j))) := by
  classical
  have hpartial : ∀ T : Finset S, ∃ pick : S → E,
      (∀ s ∈ T, pick s ∈ pool (kind s)) ∧ Set.InjOn pick T ∧
      (∀ i ∈ T, ∀ j ∈ T, i ≠ j → round i = round j →
        Disjoint (support (pick i)) (support (pick j))) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        exact ⟨fun _ => Classical.arbitrary E, by simp, by simp, by simp⟩
    | @insert s T hs ih =>
        obtain ⟨pick,hpick,hinj,hdisj⟩ := ih
        let B := (T.filter (fun j => round j = round s)).biUnion (fun j => support (pick j))
        have hB : B.card ≤ D := by
          calc
            _ ≤ ∑ j ∈ T.filter (fun j => round j = round s), (support (pick j)).card :=
              Finset.card_biUnion_le
            _ ≤ ∑ j ∈ T.filter (fun j => round j = round s), arity (kind j) := by
              apply Finset.sum_le_sum
              intro j hj
              exact harity (kind j) (pick j) (hpick j (Finset.mem_filter.mp hj).1)
            _ ≤ ∑ j ∈ univ.filter (fun j => round j = round s), arity (kind j) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro j hj
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,(Finset.mem_filter.mp hj).2⟩
              · intros; exact Nat.zero_le _
            _ ≤ D := hround (round s)
        have hused : ((pool (kind s)) ∩ T.image pick).card ≤ demandCount kind (kind s) := by
          have hsub : (pool (kind s)) ∩ T.image pick ⊆
              (T.filter (fun j => kind j = kind s)).image pick := by
            intro e he
            obtain ⟨hep,hej⟩ := Finset.mem_inter.mp he
            obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hej
            have hkind : kind j = kind s := by
              by_contra hn
              exact Finset.disjoint_left.mp (hpools _ _ hn) (hpick j hj) hep
            exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨hj,hkind⟩,rfl⟩
          calc
            _ ≤ ((T.filter (fun j => kind j = kind s)).image pick).card := Finset.card_le_card hsub
            _ ≤ (T.filter (fun j => kind j = kind s)).card := Finset.card_image_le
            _ ≤ demandCount kind (kind s) := by
              apply Finset.card_le_card
              intro j hj
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,(Finset.mem_filter.mp hj).2⟩
        obtain ⟨e,he,hfresh,havoid⟩ := exists_fresh_avoiding
          (pool (kind s)) (T.image pick) support B (demandCount kind (kind s)) a hused
          (fun v _ => hinc s v)
          ((Nat.add_le_add_left (Nat.mul_le_mul_right a hB) _).trans_lt (hcap s))
        have hne (j : S) (hj : j ∈ T) : e ≠ pick j := by
          intro hh
          exact hfresh (Finset.mem_image.mpr ⟨j,hj,hh.symm⟩)
        have havoidj (j : S) (hj : j ∈ T) (hr : round j = round s) :
            Disjoint (support e) (support (pick j)) := by
          apply havoid.mono_right
          intro v hv
          exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_filter.mpr ⟨hj,hr⟩,hv⟩
        refine ⟨Function.update pick s e, ?_, ?_, ?_⟩
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · simpa using he
          · rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hs)]
            exact hpick j hj
        · intro i hi j hj hij
          by_cases his : i = s
          · subst i
            by_cases hjs : j = s
            · exact hjs.symm
            · rw [Function.update_self, Function.update_of_ne hjs] at hij
              exact False.elim (hne j ((Finset.mem_insert.mp hj).resolve_left hjs) hij)
          · by_cases hjs : j = s
            · subst j
              rw [Function.update_self, Function.update_of_ne his] at hij
              exact False.elim (hne i ((Finset.mem_insert.mp hi).resolve_left his) hij.symm)
            · rw [Function.update_of_ne his, Function.update_of_ne hjs] at hij
              exact hinj ((Finset.mem_insert.mp hi).resolve_left his)
                ((Finset.mem_insert.mp hj).resolve_left hjs) hij
        · intro i hi j hj hij hr
          by_cases his : i = s
          · subst i
            have hjs : j ≠ s := Ne.symm hij
            rw [Function.update_self, Function.update_of_ne hjs]
            exact havoidj j ((Finset.mem_insert.mp hj).resolve_left hjs) hr.symm
          · by_cases hjs : j = s
            · subst j
              rw [Function.update_self, Function.update_of_ne his]
              exact (havoidj i ((Finset.mem_insert.mp hi).resolve_left his) hr).symm
            · rw [Function.update_of_ne his, Function.update_of_ne hjs]
              exact hdisj i ((Finset.mem_insert.mp hi).resolve_left his)
                j ((Finset.mem_insert.mp hj).resolve_left hjs) hij hr
  obtain ⟨pick,hpick,hinj,hdisj⟩ := hpartial univ
  exact ⟨pick,fun s => hpick s (Finset.mem_univ s),
    fun _ _ h => hinj (Finset.mem_univ _) (Finset.mem_univ _) h,
    fun i j hij hr => hdisj i (Finset.mem_univ i) j (Finset.mem_univ j) hij hr⟩

/-- The empty schedule is allowed even when the edge type is empty. -/
theorem exists_pool_selection
    (pool : P → Finset E) (kind : S → P) (round : S → R)
    (support : E → Finset W) (arity : P → ℕ) (a D : ℕ)
    (hpools : ∀ p q, p ≠ q → Disjoint (pool p) (pool q))
    (harity : ∀ p, ∀ e ∈ pool p, (support e).card ≤ arity p)
    (hinc : ∀ s v, ((pool (kind s)).filter (fun e => v ∈ support e)).card ≤ a)
    (hround : ∀ r, ∑ s ∈ univ.filter (fun s => round s = r), arity (kind s) ≤ D)
    (hcap : ∀ s, demandCount kind (kind s) + D * a < (pool (kind s)).card) :
    ∃ pick : S → E,
      (∀ s, pick s ∈ pool (kind s)) ∧ Function.Injective pick ∧
      (∀ i j, i ≠ j → round i = round j →
        Disjoint (support (pick i)) (support (pick j))) := by
  classical
  by_cases hS : Nonempty S
  · let s := Classical.choice hS
    have hn : (pool (kind s)).Nonempty :=
      Finset.card_pos.mp ((Nat.zero_le _).trans_lt (hcap s))
    letI : Nonempty E := ⟨hn.choose⟩
    exact exists_pool_selection_of_nonempty pool kind round support arity a D
      hpools harity hinc hround hcap
  · haveI : IsEmpty S := not_nonempty_iff.mp hS
    refine ⟨isEmptyElim,?_,?_,?_⟩
    · intro s; exact isEmptyElim s
    · intro s; exact isEmptyElim s
    · intro s; exact isEmptyElim s

omit [Fintype S] in
/-- Exact pool use, for every subset of the demand slots. -/
theorem chosen_pool_card (pool : P → Finset E) (kind : S → P)
    (pick : S → E) (hpick : ∀ s, pick s ∈ pool (kind s))
    (hinj : Function.Injective pick)
    (hpools : ∀ p q, p ≠ q → Disjoint (pool p) (pool q))
    (T : Finset S) (p : P) :
    ((T.image pick).filter (fun e => e ∈ pool p)).card =
      (T.filter (fun s => kind s = p)).card := by
  classical
  have heq : (T.image pick).filter (fun e => e ∈ pool p) =
      (T.filter (fun s => kind s = p)).image pick := by
    ext e
    simp only [Finset.mem_filter,Finset.mem_image]
    constructor
    · rintro ⟨⟨s,hs,rfl⟩,he⟩
      have hkind : kind s = p := by
        by_contra hn
        exact Finset.disjoint_left.mp (hpools _ _ hn) (hpick s) he
      exact ⟨s,⟨hs,hkind⟩,rfl⟩
    · rintro ⟨s,⟨hs,hk⟩,rfl⟩
      exact ⟨⟨s,hs,rfl⟩,hk ▸ hpick s⟩
  rw [heq,Finset.card_image_of_injective _ hinj]

omit [Fintype S] [DecidableEq E] [DecidableEq P] in
/-- Endpoint support of any chosen subset is bounded by its arity sum. -/
theorem chosen_support_card_le (pool : P → Finset E) (kind : S → P)
    (support : E → Finset W) (arity : P → ℕ)
    (harity : ∀ p, ∀ e ∈ pool p, (support e).card ≤ arity p)
    (pick : S → E) (hpick : ∀ s, pick s ∈ pool (kind s)) (T : Finset S) :
    (T.biUnion (fun s => support (pick s))).card ≤ ∑ s ∈ T, arity (kind s) := by
  classical
  exact Finset.card_biUnion_le.trans
    (Finset.sum_le_sum (fun s _ => harity _ _ (hpick s)))

/-- The slack used in the manuscript gives the strict natural-number
capacity bound, including a real rather than integral error parameter. -/
theorem capacity_of_real_slack (d m D : ℕ) (a η : ℝ)
    (ha : 0 < a) (huse : (m : ℝ) ≤ (1-η) * d)
    (hslack : ((D : ℝ) + 2) * a ≤ η * d) :
    m + D * ⌊a⌋₊ < d := by
  have hfloor : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le ha.le
  have hmul := mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg D : (0 : ℝ) ≤ D)
  have hstrict : (m : ℝ) + D * (⌊a⌋₊ : ℝ) < d := by nlinarith
  exact_mod_cast hstrict

end Pools

section Graph

variable {S P R V : Type*} [Fintype S] [DecidableEq V] (G : SimpleGraph V)

/-- The unordered endpoint set of an actual host edge. -/
noncomputable def edgeEnds (e : G.edgeSet) : Finset V :=
  {firstEnd e, secondEnd e}

@[simp] theorem mem_edgeEnds (e : G.edgeSet) (v : V) :
    v ∈ edgeEnds G e ↔ v ∈ e.val := by
  rw [incident_iff]
  simp [edgeEnds,eq_comm]

@[simp] theorem edgeEnds_card (e : G.edgeSet) : (edgeEnds G e).card = 2 := by
  simp [edgeEnds,endpoints_distinct e]

/-- Only endpoints outside the exceptional set are chosen greedily. -/
noncomputable def coreEnds (Z : Finset V) (e : G.edgeSet) : Finset V :=
  edgeEnds G e \ Z

@[simp] theorem mem_coreEnds (Z : Finset V) (e : G.edgeSet) (v : V) :
    v ∈ coreEnds G Z e ↔ v ∈ e.val ∧ v ∉ Z := by
  simp [coreEnds]

/-- Core endpoints and prescribed exceptional endpoints partition the two
endpoints of the host edge. -/
theorem coreEnds_card_add (Z : Finset V) (e : G.edgeSet) :
    (coreEnds G Z e).card + (edgeEnds G e ∩ Z).card = 2 := by
  rw [coreEnds,Finset.card_sdiff_add_card_inter,edgeEnds_card]

/-- The exact host edges selected in one round. -/
noncomputable def roundEdges (pick : S → G.edgeSet) (round : S → R) (r : R) :
    Finset G.edgeSet := (univ.filter (fun s => round s = r)).image pick

/-- The actual subgraph formed from the selected round edges. -/
noncomputable def roundMatching (pick : S → G.edgeSet) (round : S → R) (r : R) :
    G.Subgraph := selectedMatching G (roundEdges G pick round r)

@[simp] theorem roundMatching_edges [Fintype V] [DecidableRel G.Adj] (pick : S → G.edgeSet) (round : S → R) (r : R) :
    matchingEdges (roundMatching G pick round r) = roundEdges G pick round r :=
  selectedMatching_edges G _

theorem roundMatching_isMatching (Z : Finset V) (pool : P → Finset G.edgeSet)
    (special : P → Finset V) (kind : S → P) (round : S → R)
    (pick : S → G.edgeSet) (hpick : ∀ s, pick s ∈ pool (kind s))
    (hspecial : ∀ p, ∀ e ∈ pool p, edgeEnds G e ∩ Z = special p)
    (hspecialDisj : ∀ i j, i ≠ j → round i = round j →
      Disjoint (special (kind i)) (special (kind j)))
    (hcoreDisj : ∀ i j, i ≠ j → round i = round j →
      Disjoint (coreEnds G Z (pick i)) (coreEnds G Z (pick j))) (r : R) :
    (roundMatching G pick round r).IsMatching := by
  classical
  apply selectedMatching_isMatching_of_endpoints
  intro e he f hf v hve hvf
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hf
  by_cases hij : i = j
  · exact congrArg pick hij
  · have hr : round i = round j :=
      (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm
    by_cases hvZ : v ∈ Z
    · have hvi : v ∈ special (kind i) := by
        rw [← hspecial _ _ (hpick i)]
        exact Finset.mem_inter.mpr ⟨(mem_edgeEnds G _ _).mpr hve,hvZ⟩
      have hvj : v ∈ special (kind j) := by
        rw [← hspecial _ _ (hpick j)]
        exact Finset.mem_inter.mpr ⟨(mem_edgeEnds G _ _).mpr hvf,hvZ⟩
      exact False.elim (Finset.disjoint_left.mp (hspecialDisj i j hij hr) hvi hvj)
    · exact False.elim (Finset.disjoint_left.mp (hcoreDisj i j hij hr)
        ((mem_coreEnds G Z _ _).mpr ⟨hve,hvZ⟩)
        ((mem_coreEnds G Z _ _).mpr ⟨hvf,hvZ⟩))

/-- A globally injective edge choice gives edge-disjoint round matchings. -/
theorem roundMatching_disjoint (pick : S → G.edgeSet) (round : S → R)
    (hinj : Function.Injective pick) (r r' : R) (hne : r ≠ r') :
    Disjoint (roundMatching G pick round r).spanningCoe
      (roundMatching G pick round r').spanningCoe := by
  classical
  apply disjoint_iff_inf_le.mpr
  rintro v w ⟨hvw,hwv⟩
  obtain ⟨he,hee⟩ := hvw
  obtain ⟨he',hee'⟩ := hwv
  obtain ⟨s,hs,heq⟩ := Finset.mem_image.mp hee
  obtain ⟨s',hs',heq'⟩ := Finset.mem_image.mp hee'
  have hss : s = s' := hinj (heq.trans heq'.symm)
  exact hne ((Finset.mem_filter.mp hs).2.symm.trans
    (hss ▸ (Finset.mem_filter.mp hs').2))

/-- Every prescribed exceptional endpoint is covered by its round. -/
theorem roundMatching_covers (Z : Finset V) (pool : P → Finset G.edgeSet)
    (special : P → Finset V) (kind : S → P) (round : S → R)
    (pick : S → G.edgeSet) (hpick : ∀ s, pick s ∈ pool (kind s))
    (hspecial : ∀ p, ∀ e ∈ pool p, edgeEnds G e ∩ Z = special p)
    (r : R) (hcover : ∀ v ∈ Z, ∃ s, round s = r ∧ v ∈ special (kind s)) :
    (Z : Set V) ⊆ (roundMatching G pick round r).verts := by
  intro v hv
  obtain ⟨s,hs,hvs⟩ := hcover v hv
  rw [← hspecial _ _ (hpick s)] at hvs
  apply (selectedMatching_mem_verts G _ v).mpr
  exact ⟨pick s,Finset.mem_image.mpr ⟨s,Finset.mem_filter.mpr ⟨Finset.mem_univ s,hs⟩,rfl⟩,
    (mem_edgeEnds G _ _).mp (Finset.mem_inter.mp hvs).1⟩

/-- Properties of every candidate edge pass to the actual round graph. -/
theorem roundMatching_no_internal {I : Type*} (U : I → Finset V)
    (pool : P → Finset G.edgeSet) (kind : S → P) (round : S → R)
    (pick : S → G.edgeSet) (hpick : ∀ s, pick s ∈ pool (kind s))
    (hno : ∀ s, ∀ e ∈ pool (kind s), ∀ i u v, u ∈ U i → v ∈ U i →
      ¬ e.val = s(u,v)) (r : R) :
    ∀ i u v, u ∈ U i → v ∈ U i → ¬ (roundMatching G pick round r).Adj u v := by
  intro i u v hu hv hAdj
  obtain ⟨he,hee⟩ := hAdj
  obtain ⟨s,hs,hpicke⟩ := Finset.mem_image.mp hee
  exact hno s (pick s) (hpick s) i u v hu hv (congrArg Subtype.val hpicke)

/-- Construct actual pairwise edge-disjoint round matchings from the
numerical pool inequalities.  The support of exceptional vertices is
prescribed by each pool and occurs at most once within any round. -/
theorem exists_boundary_matchings [DecidableEq P] (Z : Finset V)
    (pool : P → Finset G.edgeSet) (special : P → Finset V)
    (kind : S → P) (round : S → R) (arity : P → ℕ) (a D : ℕ)
    (hpools : ∀ p q, p ≠ q → Disjoint (pool p) (pool q))
    (harity : ∀ p, ∀ e ∈ pool p, (coreEnds G Z e).card ≤ arity p)
    (hinc : ∀ s v, ((pool (kind s)).filter (fun e => v ∈ coreEnds G Z e)).card ≤ a)
    (hround : ∀ r, ∑ s ∈ univ.filter (fun s => round s = r), arity (kind s) ≤ D)
    (hcap : ∀ s, demandCount kind (kind s) + D*a < (pool (kind s)).card)
    (hspecial : ∀ p, ∀ e ∈ pool p, edgeEnds G e ∩ Z = special p)
    (hspecialDisj : ∀ i j, i ≠ j → round i = round j →
      Disjoint (special (kind i)) (special (kind j)))
    (hcover : ∀ r, ∀ v ∈ Z, ∃ s, round s = r ∧ v ∈ special (kind s)) :
    ∃ pick : S → G.edgeSet,
      (∀ s, pick s ∈ pool (kind s)) ∧ Function.Injective pick ∧
      (∀ r, (roundMatching G pick round r).IsMatching) ∧
      (∀ r r', r ≠ r' → Disjoint (roundMatching G pick round r).spanningCoe
        (roundMatching G pick round r').spanningCoe) ∧
      (∀ r, (Z : Set V) ⊆ (roundMatching G pick round r).verts) ∧
      (∀ T : Finset S, ∀ p,
        ((T.image pick).filter (fun e => e ∈ pool p)).card =
          (T.filter (fun s => kind s = p)).card) := by
  classical
  obtain ⟨pick,hpick,hinj,hcoreDisj⟩ := exists_pool_selection pool kind round
    (coreEnds G Z) arity a D hpools harity hinc hround hcap
  exact ⟨pick,hpick,hinj,
    roundMatching_isMatching G Z pool special kind round pick hpick hspecial hspecialDisj hcoreDisj,
    roundMatching_disjoint G pick round hinj,
    fun r => roundMatching_covers G Z pool special kind round pick hpick hspecial r (hcover r),
    fun T p => by simpa using chosen_pool_card pool kind pick hpick hinj hpools T p⟩

/-- Exact number of edges in a realized round. -/
theorem roundMatching_edge_card (pick : S → G.edgeSet) (round : S → R)
    (hinj : Function.Injective pick) (r : R) :
    (roundMatching G pick round r).edgeSet.ncard =
      (univ.filter (fun s => round s = r)).card := by
  rw [roundMatching,selectedMatching_edgeSet_card,roundEdges,
    Finset.card_image_of_injective _ hinj]

/-- Actual covered core vertices are exactly the union of chosen core
endpoint sets. -/
theorem roundMatching_core_verts [Fintype V]
    (Z : Finset V) (pick : S → G.edgeSet) (round : S → R) (r : R) :
    (roundMatching G pick round r).verts.toFinset \ Z =
      (univ.filter (fun s => round s = r)).biUnion (fun s => coreEnds G Z (pick s)) := by
  classical
  ext v
  simp only [Finset.mem_sdiff,Set.mem_toFinset,roundMatching,
    selectedMatching_mem_verts,roundEdges,Finset.mem_image,Finset.mem_filter,
    Finset.mem_univ,true_and,Finset.mem_biUnion,mem_coreEnds]
  constructor
  · rintro ⟨⟨e,⟨s,hs,rfl⟩,hv⟩,hvZ⟩
    exact ⟨s,hs,hv,hvZ⟩
  · rintro ⟨s,hs,hv,hvZ⟩
    exact ⟨⟨pick s,⟨s,hs,rfl⟩,hv⟩,hvZ⟩

/-- The core footprint bound refers to the actual matching vertices. -/
theorem roundMatching_core_card_le [Fintype V]
    (Z : Finset V) (pool : P → Finset G.edgeSet) (kind : S → P)
    (round : S → R) (arity : P → ℕ)
    (harity : ∀ p, ∀ e ∈ pool p, (coreEnds G Z e).card ≤ arity p)
    (pick : S → G.edgeSet) (hpick : ∀ s, pick s ∈ pool (kind s)) (r : R) :
    ((roundMatching G pick round r).verts.toFinset \ Z).card ≤
      ∑ s ∈ univ.filter (fun s => round s = r), arity (kind s) := by
  rw [roundMatching_core_verts]
  exact chosen_support_card_le pool kind (coreEnds G Z) arity harity pick hpick _

end Graph

end Overfull.PatternRealization
