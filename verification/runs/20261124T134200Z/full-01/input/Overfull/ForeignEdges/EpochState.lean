import Overfull.ForeignEdges.Adaptive
import Overfull.ForeignEdges.RuleCompletion
import Overfull.ForeignEdges.PhaseConclusion

/-!
# Actual matching transcripts in a foreign-edge epoch

Admissibility is not a field of the state. It is derived from the actual
partial matchings, their distinct exterior edges, and their footprint sizes
and parities. The current core is the whole unused initial core.
-/

namespace Overfull.ForeignEpoch

open Finset Classical SimpleGraph ForceMatching SafePrescription
open ForeignTranscript ForeignPhase ForeignIncidence ForeignRuleCompletion
open BipartitePackingAccounting

universe u v
variable {V : Type u} {I : Type v} [Fintype V]

structure Transcript (G : SimpleGraph V) (U : I → Finset V)
    (H₀ : ∀ i, SimpleGraph (U i)) where
  full : ℕ → G.Subgraph
  part : ℕ → G.Subgraph
  core : ∀ i, ℕ → Finset (U i) × (H₀ i).Subgraph

variable {G : SimpleGraph V} {U : I → Finset V} {H₀ : ∀ i, SimpleGraph (U i)}

def Transcript.graph (T : Transcript G U H₀) (s : ℕ) : SimpleGraph V :=
  afterDeletions G T.full s

def Transcript.currentCore (T : Transcript G U H₀) (s : ℕ) (i : I) :
    SimpleGraph (U i) := unusedGraph (H₀ i) (T.core i) s

structure Valid
    (rule : ∀ i, (s : ℕ) → (Fin s → Finset (U i) × (H₀ i).Subgraph) →
      Finset (U i) → (H₀ i).Subgraph)
    (h₀ loss : ℕ) (ε : ℝ) (A : ℕ → Finset G.edgeSet)
    (s : ℕ) (T : Transcript G U H₀) : Prop where
  perfect : ∀ j < s, (T.full j).IsPerfectMatching
  present : ∀ j < s, (T.full j).spanningCoe ≤ T.graph j
  partial_matching : ∀ j < s, (T.part j).IsMatching
  partial_le : ∀ j < s, (T.part j).spanningCoe ≤ (T.full j).spanningCoe
  no_internal : ∀ j < s, ∀ i u v, u ∈ U i → v ∈ U i → ¬ (T.part j).Adj u v
  even : ∀ j < s, ∀ i, Even (((U i : Set V) \ (T.part j).verts).ncard)
  footprint : ∀ j < s, ∀ i,
    ((coveredCore (U i) G (T.part j)).card : ℝ) ≤ ε*(U i).card
  inputs : ∀ j < s, ∀ i, (T.core i j).1 = coveredCore (U i) G (T.part j)
  consistent : ∀ j < s, ∀ i,
    (T.core i j).2 = rule i j (transcriptPrefix (T.core i) j) (T.core i j).1
  local_edges : ∀ j < s, ∀ i,
    (T.full j).spanningCoe.induce (U i : Set V) = (T.core i j).2.spanningCoe
  loss_bound : ∀ j < s,
    ((currentClass G (T.graph j) (A j)).edgeSet \ (T.full j).edgeSet).ncard ≤ loss
  safe : ∀ X : Finset V, ¬ IsOverfull (T.graph s) (h₀-s) X

def emptyTranscript : Transcript G U H₀ where
  full := fun _ => ⊥
  part := fun _ => ⊥
  core := fun _ _ => (∅,⊥)

noncomputable def Transcript.append (T : Transcript G U H₀)
    (rule : ∀ i, (s : ℕ) → (Fin s → Finset (U i) × (H₀ i).Subgraph) →
      Finset (U i) → (H₀ i).Subgraph)
    (s : ℕ) (F N : G.Subgraph) : Transcript G U H₀ where
  full := Function.update T.full s N
  part := Function.update T.part s F
  core := fun i => Function.update (T.core i) s
    (coveredCore (U i) G F,rule i s (transcriptPrefix (T.core i) s) (coveredCore (U i) G F))

omit [Fintype V] in
theorem afterDeletions_update_of_le (G : SimpleGraph V) (N : ℕ → G.Subgraph)
    (s : ℕ) (M : G.Subgraph) (j : ℕ) (hj : j ≤ s) :
    afterDeletions G (Function.update N s M) j = afterDeletions G N j := by
  unfold afterDeletions
  congr 1
  ext u v
  simp only [edgeUnion_adj,mem_range]
  apply exists_congr
  intro k
  apply and_congr_right
  intro hk
  rw [Function.update_of_ne (Nat.ne_of_lt (hk.trans_le hj))]

theorem Transcript.graph_append_of_le (T : Transcript G U H₀)
    (rule : ∀ i, (s : ℕ) → (Fin s → Finset (U i) × (H₀ i).Subgraph) →
      Finset (U i) → (H₀ i).Subgraph)
    (s : ℕ) (F N : G.Subgraph) (j : ℕ) (hj : j ≤ s) :
    (T.append rule s F N).graph j = T.graph j :=
  afterDeletions_update_of_le G T.full s N j hj

theorem Transcript.graph_append_succ (T : Transcript G U H₀)
    (rule : ∀ i, (s : ℕ) → (Fin s → Finset (U i) × (H₀ i).Subgraph) →
      Finset (U i) → (H₀ i).Subgraph)
    (s : ℕ) (F N : G.Subgraph) :
    (T.append rule s F N).graph (s+1) = T.graph s \ N.spanningCoe := by
  change afterDeletions G _ (s+1) = _
  rw [afterDeletions_succ]
  simp only [Transcript.append]
  rw [afterDeletions_update_of_le G T.full s N s le_rfl]
  simp only [Function.update_self,Transcript.graph]

theorem Transcript.prefix_append_of_le (T : Transcript G U H₀)
    (rule : ∀ i, (s : ℕ) → (Fin s → Finset (U i) × (H₀ i).Subgraph) →
      Finset (U i) → (H₀ i).Subgraph)
    (s : ℕ) (F N : G.Subgraph) (i : I) (j : ℕ) (hj : j ≤ s) :
    transcriptPrefix ((T.append rule s F N).core i) j = transcriptPrefix (T.core i) j :=
  prefix_update_of_le (T.core i) s _ j hj

theorem valid_zero
    (rule : ∀ i, (s : ℕ) → (Fin s → Finset (U i) × (H₀ i).Subgraph) →
      Finset (U i) → (H₀ i).Subgraph)
    (h₀ loss : ℕ) (ε : ℝ) (A : ℕ → Finset G.edgeSet)
    (hsafe : ∀ X : Finset V, ¬ IsOverfull G h₀ X) :
    Valid rule h₀ loss ε A 0 (emptyTranscript : Transcript G U H₀) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals try { intro j hj; omega }
  intro X
  simpa only [Transcript.graph,afterDeletions_zero,Nat.sub_zero] using hsafe X

omit [Fintype V] in
theorem prefix_edgeUnion_eq_range (H : SimpleGraph V)
    (T : ℕ → Finset V × H.Subgraph) (s : ℕ) :
    edgeUnion (fun i => (transcriptPrefix T s i).2.spanningCoe) univ =
      edgeUnion (fun j => (T j).2.spanningCoe) (range s) := by
  ext u v
  constructor
  · rintro ⟨j,_,hj⟩
    exact ⟨j.val,mem_range.mpr j.isLt,hj⟩
  · rintro ⟨j,hj,hjedge⟩
    exact ⟨⟨j,mem_range.mp hj⟩,mem_univ _,hjedge⟩

omit [Fintype V] in
theorem Transcript.currentCore_eq_remaining (T : Transcript G U H₀) (s : ℕ) (i : I) :
    T.currentCore s i =
      remainingCore (U i) (H₀ i) (fun j => (T.core i j).2) (range s) := by
  unfold Transcript.currentCore unusedGraph remainingCore
  rw [prefix_edgeUnion_eq_range]

namespace Valid

variable {rule : ∀ i, (s : ℕ) → (Fin s → Finset (U i) × (H₀ i).Subgraph) →
    Finset (U i) → (H₀ i).Subgraph}
variable {h₀ loss s : ℕ} {ε : ℝ} {A : ℕ → Finset G.edgeSet}
variable {T : Transcript G U H₀}

/-- Update the actual sequences and transcript entries using one actual
safe completion. No existence or admissibility hypothesis is hidden in
this deterministic state update. -/
theorem append (hT : Valid rule h₀ loss ε A s T) (F N : G.Subgraph)
    (hN : N.IsPerfectMatching) (hNpresent : N.spanningCoe ≤ T.graph s)
    (hF : F.IsMatching) (hFN : F.spanningCoe ≤ N.spanningCoe)
    (hno : ∀ i u v, u ∈ U i → v ∈ U i → ¬ F.Adj u v)
    (heven : ∀ i, Even (((U i : Set V) \ F.verts).ncard))
    (hfoot : ∀ i, ((coveredCore (U i) G F).card : ℝ) ≤ ε*(U i).card)
    (hlocal : ∀ i, N.spanningCoe.induce (U i : Set V) =
      (rule i s (transcriptPrefix (T.core i) s) (coveredCore (U i) G F)).spanningCoe)
    (hloss : ((currentClass G (T.graph s) (A s)).edgeSet \ N.edgeSet).ncard ≤ loss)
    (hsafe : ∀ X : Finset V, ¬ IsOverfull (T.graph s \ N.spanningCoe) (h₀-(s+1)) X) :
    Valid rule h₀ loss ε A (s+1) (T.append rule s F N) := by
  have hfull (j : ℕ) (hj : j < s) : (T.append rule s F N).full j = T.full j := by
    simp only [Transcript.append,Function.update_of_ne (Nat.ne_of_lt hj)]
  have hpart (j : ℕ) (hj : j < s) : (T.append rule s F N).part j = T.part j := by
    simp only [Transcript.append,Function.update_of_ne (Nat.ne_of_lt hj)]
  have hcore (i : I) (j : ℕ) (hj : j < s) :
      (T.append rule s F N).core i j = T.core i j :=
    Function.update_of_ne (Nat.ne_of_lt hj) _ (T.core i)
  have hfullLast : (T.append rule s F N).full s = N := Function.update_self _ _ _
  have hpartLast : (T.append rule s F N).part s = F := Function.update_self _ _ _
  have hcoreLast (i : I) : (T.append rule s F N).core i s =
      (coveredCore (U i) G F,
        rule i s (transcriptPrefix (T.core i) s) (coveredCore (U i) G F)) :=
    Function.update_self _ _ _
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j hj
    by_cases hjs : j = s
    · subst j; simpa only [hfullLast] using hN
    · simpa only [hfull j (by omega)] using hT.perfect j (by omega)
  · intro j hj
    by_cases hjs : j = s
    · subst j
      simpa only [hfullLast,T.graph_append_of_le rule s F N s le_rfl] using hNpresent
    · simpa only [hfull j (by omega),T.graph_append_of_le rule s F N j (by omega)]
        using hT.present j (by omega)
  · intro j hj
    by_cases hjs : j = s
    · subst j; simpa only [hpartLast] using hF
    · simpa only [hpart j (by omega)] using hT.partial_matching j (by omega)
  · intro j hj
    by_cases hjs : j = s
    · subst j; simpa only [hpartLast,hfullLast] using hFN
    · simpa only [hpart j (by omega),hfull j (by omega)] using hT.partial_le j (by omega)
  · intro j hj i
    by_cases hjs : j = s
    · subst j; simpa only [hpartLast] using hno i
    · simpa only [hpart j (by omega)] using hT.no_internal j (by omega) i
  · intro j hj i
    by_cases hjs : j = s
    · subst j; simpa only [hpartLast] using heven i
    · simpa only [hpart j (by omega)] using hT.even j (by omega) i
  · intro j hj i
    by_cases hjs : j = s
    · subst j; simpa only [hpartLast] using hfoot i
    · simpa only [hpart j (by omega)] using hT.footprint j (by omega) i
  · intro j hj i
    by_cases hjs : j = s
    · subst j; simp only [hcoreLast,hpartLast]
    · simpa only [hcore i j (by omega),hpart j (by omega)] using hT.inputs j (by omega) i
  · intro j hj i
    by_cases hjs : j = s
    · subst j
      simp only [hcoreLast,T.prefix_append_of_le rule s F N i s le_rfl]
    · simpa only [hcore i j (by omega),T.prefix_append_of_le rule s F N i j (by omega)]
        using hT.consistent j (by omega) i
  · intro j hj i
    by_cases hjs : j = s
    · subst j; simpa only [hfullLast,hcoreLast] using hlocal i
    · simpa only [hfull j (by omega),hcore i j (by omega)] using hT.local_edges j (by omega) i
  · intro j hj
    by_cases hjs : j = s
    · subst j
      rw [hfullLast]
      have heq := congrArg (fun R : SimpleGraph V =>
        ((currentClass G R (A s)).edgeSet \ N.edgeSet).ncard)
        (T.graph_append_of_le rule s F N s le_rfl)
      exact heq.le.trans hloss
    · rw [hfull j (by omega)]
      have heq := congrArg (fun R : SimpleGraph V =>
        ((currentClass G R (A j)).edgeSet \ (T.full j).edgeSet).ncard)
        (T.graph_append_of_le rule s F N j (by omega))
      exact heq.le.trans (hT.loss_bound j (by omega))
  · intro X
    simpa only [T.graph_append_succ rule s F N] using hsafe X

/-- Every earlier `Allowed` input is proved from the actual partial
matchings. In particular, the state does not assume an admissibility oracle. -/
theorem allowed (hT : Valid rule h₀ loss ε A s T)
    (hH : ∀ i, H₀ i ≤ G.induce (U i : Set V))
    (hregular : ∀ v, G.degree v = h₀)
    (hdegree : ∀ i v, (h₀ : ℝ)-ε*(U i).card ≤ (H₀ i).degree v)
    (i : I) (j : ℕ) (hj : j < s) :
    OrdinaryPackingStrategy.Allowed (H₀ i) (Fintype.card (U i)) ε j
      (transcriptPrefix (T.core i) j) (T.core i j).1 := by
  have hall := allowed_of_partial_prefix (U i) G (H₀ i) (hH i)
    T.part T.full j h₀ ε (transcriptPrefix (T.core i) j)
    (fun k => hT.inputs k.val (k.isLt.trans hj) i)
    (fun k hk => hT.partial_matching k (hk.trans_lt hj))
    (fun k hk => hT.partial_le k (hk.trans hj))
    (fun k hk => (hT.partial_le k (hk.trans_lt hj)).trans (hT.present k (hk.trans_lt hj)))
    (fun k hk => hT.no_internal k (hk.trans_lt hj) i)
    hregular (hdegree i) (hT.even j hj i) (hT.footprint j hj i)
  rw [hT.inputs j hj i]
  simpa only [Fintype.card_coe] using hall

/-- Admissibility of the currently prepared matching is established
before constructing its ambient completion. -/
theorem allowed_next (hT : Valid rule h₀ loss ε A s T)
    (hH : ∀ i, H₀ i ≤ G.induce (U i : Set V))
    (hregular : ∀ v, G.degree v = h₀)
    (hdegree : ∀ i v, (h₀ : ℝ)-ε*(U i).card ≤ (H₀ i).degree v)
    (F : G.Subgraph) (hF : F.IsMatching) (hpresent : F.spanningCoe ≤ T.graph s)
    (hno : ∀ i u v, u ∈ U i → v ∈ U i → ¬ F.Adj u v)
    (heven : ∀ i, Even (((U i : Set V) \ F.verts).ncard))
    (hfoot : ∀ i, ((coveredCore (U i) G F).card : ℝ) ≤ ε*(U i).card) (i : I) :
    OrdinaryPackingStrategy.Allowed (H₀ i) (Fintype.card (U i)) ε s
      (transcriptPrefix (T.core i) s) (coveredCore (U i) G F) := by
  let P := Function.update T.part s F
  have hprev (j : ℕ) (hj : j < s) : P j = T.part j :=
    Function.update_of_ne (Nat.ne_of_lt hj) F T.part
  have hlast : P s = F := Function.update_self _ _ _
  have hPmatch : ∀ j ≤ s, (P j).IsMatching := by
    intro j hj
    by_cases hjs : j = s
    · subst j; simpa only [hlast] using hF
    · simpa only [hprev j (by omega)] using hT.partial_matching j (by omega)
  have hPN : ∀ j < s, (P j).spanningCoe ≤ (T.full j).spanningCoe := by
    intro j hj
    simpa only [hprev j hj] using hT.partial_le j hj
  have hPpresent : ∀ j ≤ s, (P j).spanningCoe ≤ T.graph j := by
    intro j hj
    by_cases hjs : j = s
    · subst j; simpa only [hlast] using hpresent
    · simpa only [hprev j (by omega)] using
        (hT.partial_le j (by omega)).trans (hT.present j (by omega))
  have hPno : ∀ j ≤ s, ∀ u v, u ∈ U i → v ∈ U i → ¬ (P j).Adj u v := by
    intro j hj
    by_cases hjs : j = s
    · subst j; simpa only [hlast] using hno i
    · simpa only [hprev j (by omega)] using hT.no_internal j (by omega) i
  have hinputs : ∀ j : Fin s,
      (transcriptPrefix (T.core i) s j).1 = coveredCore (U i) G (P j.val) := by
    intro j
    simpa only [transcriptPrefix,hprev j.val j.isLt] using hT.inputs j.val j.isLt i
  have hall := allowed_of_partial_prefix (U i) G (H₀ i) (hH i) P T.full s h₀ ε
    (transcriptPrefix (T.core i) s) hinputs hPmatch hPN hPpresent hPno hregular
    (hdegree i) (by simpa only [hlast] using heven i)
    (by simpa only [hlast] using hfoot i)
  simpa only [Fintype.card_coe,hlast] using hall

theorem graph_degree (hT : Valid rule h₀ loss ε A s T)
    (hregular : ∀ v, G.degree v = h₀) (v : V) :
    (T.graph s).degree v = h₀-s := by
  have hh := (perfect_deletion_regular G T.full s h₀ hregular hT.perfect hT.present v).2
  simpa only [Transcript.graph,afterDeletions,← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] using hh

theorem core_embed (hT : Valid rule h₀ loss ε A s T)
    (hH : ∀ i, H₀ i ≤ G.induce (U i : Set V)) (i : I) :
    T.currentCore s i ≤ (T.graph s).induce (U i : Set V) := by
  rw [T.currentCore_eq_remaining s i]
  exact remainingCore_le_residual (U i) G (H₀ i) (hH i)
    (fun j => (T.core i j).2) T.full (range s)
    (fun j hj => hT.local_edges j (mem_range.mp hj) i)

theorem core_packing (hT : Valid rule h₀ loss ε A s T)
    (hH : ∀ i, H₀ i ≤ G.induce (U i : Set V))
    (hregular : ∀ v, G.degree v = h₀)
    (hdegree : ∀ i v, (h₀ : ℝ)-ε*(U i).card ≤ (H₀ i).degree v)
    (q : I → ℕ) (θ σ : ℝ)
    (hcertificate : ∀ i, RuleCertificate (H₀ i) (q i) ε θ σ (rule i))
    (hs : ∀ i, s ≤ q i) (i : I) :
    IsPackingHistory (H₀ i) s (transcriptPrefix (T.core i) s) ∧
      IsRobustExpander (T.currentCore s i) θ σ := by
  obtain ⟨hp,hr⟩ := hcertificate i (T.core i) s (hs i)
    (fun j hj => hT.consistent j hj i)
    (fun j hj => hT.allowed hH hregular hdegree i j hj)
  exact ⟨hp,by convert hr using 1⟩

/-- The real core error is retained throughout the whole epoch. -/
theorem core_degree (hT : Valid rule h₀ loss ε A s T)
    (hH : ∀ i, H₀ i ≤ G.induce (U i : Set V))
    (hregular : ∀ v, G.degree v = h₀)
    (a : ℝ) (hdegree : ∀ i v, (h₀ : ℝ)-a ≤ (H₀ i).degree v)
    (ha : ∀ i, a ≤ ε*(U i).card)
    (q : I → ℕ) (θ σ : ℝ)
    (hcertificate : ∀ i, RuleCertificate (H₀ i) (q i) ε θ σ (rule i))
    (hsq : ∀ i, s ≤ q i) (hsh : s ≤ h₀) (i : I) (v : U i) :
    ((h₀-s : ℕ) : ℝ)-a ≤ (T.currentCore s i).degree v ∧
      ((T.currentCore s i).degree v : ℝ) ≤ (h₀-s : ℕ) := by
  have hdegreeε : ∀ i v, (h₀ : ℝ)-ε*(U i).card ≤ (H₀ i).degree v := by
    intro i v
    have hd := hdegree i v
    have he := ha i
    linarith
  have hp := (hT.core_packing hH hregular hdegreeε q θ σ hcertificate hsq i).1
  have hfullDisj := deletion_sequence_pairwise G T.full s hT.present
  have hpartialDisj := deletion_sequence_partial_pairwise G T.part T.full s
    hT.partial_le hT.present
  have hlocalDisj := local_pairwise_of_ambient (U i) G (H₀ i)
    (fun j => (T.core i j).2) T.full (range s)
    (fun j hj => hT.local_edges j (mem_range.mp hj) i) hfullDisj
  have hlocalMatch (j : ℕ) (hj : j ∈ range s) : (T.core i j).2.IsMatching :=
    hp.1 ⟨j,mem_range.mp hj⟩
  have hlocalVerts (j : ℕ) (hj : j ∈ range s) :
      (T.core i j).2.verts = (coveredCore (U i) G (T.part j) : Set (U i))ᶜ := by
    have hv := hp.2.1 ⟨j,mem_range.mp hj⟩
    change (T.core i j).2.verts = ((T.core i j).1 : Set (U i))ᶜ at hv
    simpa only [hT.inputs j (mem_range.mp hj) i] using hv
  have hbounds := remainingCore_real_degree_bounds (U i) G (H₀ i) (hH i)
    T.part (fun j => (T.core i j).2) (range s)
    (fun j hj => hT.partial_matching j (mem_range.mp hj)) hpartialDisj
    (fun j hj => hT.no_internal j (mem_range.mp hj) i)
    hlocalMatch hlocalDisj hlocalVerts h₀ a hregular (hdegree i) v
  rw [T.currentCore_eq_remaining s i]
  simpa only [card_range,Nat.cast_sub hsh,← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] using hbounds

end Valid

end Overfull.ForeignEpoch
