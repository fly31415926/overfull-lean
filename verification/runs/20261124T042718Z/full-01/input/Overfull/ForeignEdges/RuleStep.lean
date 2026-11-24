import Overfull.ForeignEdges.PackingSchedule

/-!
# One actual step of a previously fixed packing rule

Updating the next transcript entry preserves every earlier prefix.  The
proved transcript certificate therefore applies at the next length and
constructs a matching in the actual unused graph.  The rule is fixed before
the transcript and before the next forbidden set.
-/

namespace Overfull.ForeignTranscript

open Classical

variable {Input Output : Type*}

/-- Updating the first unrecorded entry leaves every earlier prefix
unchanged. -/
theorem prefix_update_of_le (T : ℕ → Input × Output) (s : ℕ) (x : Input × Output)
    (j : ℕ) (hj : j ≤ s) :
    transcriptPrefix (Function.update T s x) j = transcriptPrefix T j := by
  funext i
  exact Function.update_of_ne (Nat.ne_of_lt (i.isLt.trans_le hj)) x T

theorem prefix_update_succ (T : ℕ → Input × Output) (s : ℕ) (x : Input × Output) :
    transcriptPrefix (Function.update T s x) (s+1) = Fin.snoc (transcriptPrefix T s) x := by
  rw [prefix_succ,prefix_update_of_le T s x s le_rfl,Function.update_self]

/-- The next entry obtained from the same rule extends consistency. -/
theorem consistent_update
    (rule : (s : ℕ) → (Fin s → Input × Output) → Input → Output)
    (T : ℕ → Input × Output) (s : ℕ) (x : Input)
    (hconsistent : ∀ j < s, (T j).2 = rule j (transcriptPrefix T j) (T j).1) :
    let T' := Function.update T s (x,rule s (transcriptPrefix T s) x)
    ∀ j < s+1, (T' j).2 = rule j (transcriptPrefix T' j) (T' j).1 := by
  dsimp only
  intro j hj
  by_cases hjs : j = s
  · subst j
    rw [prefix_update_of_le T s _ s le_rfl,Function.update_self]
  · have hjlt : j < s := by omega
    rw [prefix_update_of_le T s _ j hjlt.le,Function.update_of_ne hjs]
    exact hconsistent j hjlt

end Overfull.ForeignTranscript

namespace Overfull.ForeignRuleStep

open Finset Classical SimpleGraph ForeignTranscript
open BipartitePackingAccounting BipartitePackingHistory BipartitePackingOnline

universe u
variable {V : Type u} [Fintype V]

omit [Fintype V] in
/-- The edge union after a transcript update is precisely the old union
and the newly chosen matching. -/
theorem prefix_update_edgeUnion (G : SimpleGraph V)
    (T : ℕ → Finset V × G.Subgraph) (s : ℕ) (S : Finset V) (C : G.Subgraph) :
    edgeUnion (fun i => (transcriptPrefix (Function.update T s (S,C)) (s+1) i).2.spanningCoe) univ =
      edgeUnion (fun i => (transcriptPrefix T s i).2.spanningCoe) univ ⊔ C.spanningCoe := by
  rw [prefix_update_succ]
  ext u v
  simp only [edgeUnion_adj,mem_univ,true_and,SimpleGraph.sup_adj]
  constructor
  · rintro ⟨i,hi⟩
    induction i using Fin.lastCases with
    | last => exact Or.inr (by simpa using hi)
    | cast i => exact Or.inl ⟨i,by simpa using hi⟩
  · rintro (⟨i,hi⟩ | hi)
    · exact ⟨i.castSucc,by simpa using hi⟩
    · exact ⟨Fin.last s,by simpa using hi⟩

omit [Fintype V] in
theorem prefix_update_unused (G : SimpleGraph V)
    (T : ℕ → Finset V × G.Subgraph) (s : ℕ) (S : Finset V) (C : G.Subgraph) :
    G \ edgeUnion (fun i => (transcriptPrefix (Function.update T s (S,C)) (s+1) i).2.spanningCoe) univ =
      (G \ edgeUnion (fun i => (transcriptPrefix T s i).2.spanningCoe) univ) \ C.spanningCoe := by
  rw [prefix_update_edgeUnion]
  ext u v
  simp only [SimpleGraph.sdiff_adj,SimpleGraph.sup_adj]
  tauto

/-- All earlier admissibility hypotheses survive the transcript update,
and the supplied current input gives admissibility at the final index. -/
theorem allowed_update (G : SimpleGraph V) (ε : ℝ)
    (T : ℕ → Finset V × G.Subgraph) (s : ℕ) (S : Finset V) (C : G.Subgraph)
    (hallowed : ∀ j < s, OrdinaryPackingStrategy.Allowed G (Fintype.card V) ε j
      (transcriptPrefix T j) (T j).1)
    (hS : OrdinaryPackingStrategy.Allowed G (Fintype.card V) ε s (transcriptPrefix T s) S) :
    ∀ j < s+1, OrdinaryPackingStrategy.Allowed G (Fintype.card V) ε j
      (transcriptPrefix (Function.update T s (S,C)) j) ((Function.update T s (S,C)) j).1 := by
  intro j hj
  by_cases hjs : j = s
  · subst j
    rw [prefix_update_of_le T s _ s le_rfl,Function.update_self]
    exact hS
  · have hjlt : j < s := by omega
    rw [prefix_update_of_le T s _ j hjlt.le,Function.update_of_ne hjs]
    exact hallowed j hjlt

/-- Extract one matching and the exact next robust residual from a
certificate valid for all consistent admissible transcripts. -/
theorem step_of_certificate (G : SimpleGraph V) (q : ℕ) (ε θ σ : ℝ)
    (rule : (s : ℕ) → (Fin s → Finset V × G.Subgraph) → Finset V → G.Subgraph)
    (hcertificate : ∀ T : ℕ → Finset V × G.Subgraph, ∀ s ≤ q,
      (∀ j < s, (T j).2 = rule j (transcriptPrefix T j) (T j).1) →
      (∀ j < s, OrdinaryPackingStrategy.Allowed G (Fintype.card V) ε j
        (transcriptPrefix T j) (T j).1) →
      IsPackingHistory G s (transcriptPrefix T s) ∧
      IsRobustExpander
        (G \ edgeUnion (fun i => (transcriptPrefix T s i).2.spanningCoe) univ) θ σ)
    (T : ℕ → Finset V × G.Subgraph) (s : ℕ) (S : Finset V)
    (hs : s < q)
    (hconsistent : ∀ j < s, (T j).2 = rule j (transcriptPrefix T j) (T j).1)
    (hallowed : ∀ j < s, OrdinaryPackingStrategy.Allowed G (Fintype.card V) ε j
      (transcriptPrefix T j) (T j).1)
    (hS : OrdinaryPackingStrategy.Allowed G (Fintype.card V) ε s (transcriptPrefix T s) S) :
    let C := rule s (transcriptPrefix T s) S
    C.IsMatching ∧ C.verts = (S : Set V)ᶜ ∧
      Disjoint C.spanningCoe (edgeUnion (fun i => (transcriptPrefix T s i).2.spanningCoe) univ) ∧
      C.spanningCoe ≤ G \ edgeUnion (fun i => (transcriptPrefix T s i).2.spanningCoe) univ ∧
      IsPackingHistory G (s+1) (transcriptPrefix (Function.update T s (S,C)) (s+1)) ∧
      IsRobustExpander
        ((G \ edgeUnion (fun i => (transcriptPrefix T s i).2.spanningCoe) univ) \ C.spanningCoe) θ σ := by
  let C := rule s (transcriptPrefix T s) S
  let T' := Function.update T s (S,C)
  have hcons := consistent_update rule T s S hconsistent
  have hall := allowed_update G ε T s S C hallowed hS
  obtain ⟨hpacking,hrobust⟩ := hcertificate T' (s+1) (by omega) hcons hall
  have hlast : (transcriptPrefix T' (s+1) (Fin.last s)) = (S,C) := by
    simp [transcriptPrefix,T']
  have hold (i : Fin s) : transcriptPrefix T' (s+1) i.castSucc = transcriptPrefix T s i := by
    exact Function.update_of_ne (Nat.ne_of_lt i.isLt) (S,C) T
  have hC : C.IsMatching := by
    have hh := hpacking.1 (Fin.last s)
    simpa only [hlast] using hh
  have hverts : C.verts = (S : Set V)ᶜ := by
    have hh := hpacking.2.1 (Fin.last s)
    simpa only [hlast] using hh
  have hdisjoint : Disjoint C.spanningCoe
      (edgeUnion (fun i => (transcriptPrefix T s i).2.spanningCoe) univ) := by
    apply disjoint_iff_inf_le.mpr
    rintro u v ⟨hCuv,i,_,hIuv⟩
    have hindices : Fin.last s ≠ i.castSucc := by
      intro heq
      have hh := congrArg Fin.val heq
      exact (Nat.ne_of_gt i.isLt) hh
    have hh := hpacking.2.2 hindices
    dsimp only at hh
    rw [hlast,hold i] at hh
    exact (disjoint_iff_inf_le.mp hh) ⟨hCuv,hIuv⟩
  have hunused : C.spanningCoe ≤
      G \ edgeUnion (fun i => (transcriptPrefix T s i).2.spanningCoe) univ := by
    intro u v huv
    refine ⟨C.adj_sub huv,?_⟩
    exact fun hold => (disjoint_iff_inf_le.mp hdisjoint) ⟨huv,hold⟩
  refine ⟨hC,hverts,hdisjoint,hunused,hpacking,?_⟩
  change IsRobustExpander
    (G \ edgeUnion (fun i => (transcriptPrefix (Function.update T s (S,C)) (s+1) i).2.spanningCoe) univ) θ σ at hrobust
  exact hrobust.mono_graph _ _ (le_of_eq (prefix_update_unused G T s S C))

/-- The actual proved packing theorem chooses one rule before every
transcript and next input.  Its step properties are conclusions, with no
assumption of a separate local completion lemma. -/
theorem exists_step_rule (α γ ν τ ε θ : ℝ) (m₀ : ℕ)
    (hpacking : ForeignPackingSchedule.PackingRule.{u} α γ ν τ ε θ m₀)
    (G : SimpleGraph V) (Δ : ℝ)
    (hm : m₀ ≤ Fintype.card V) (hrobust : IsRobustExpander G ν τ)
    (hΔ : α*Fintype.card V ≤ Δ)
    (hdegree : ∀ v, |(G.degree v : ℝ)-Δ| ≤ ε*Fintype.card V) :
    ∃ rule : (s : ℕ) → (Fin s → Finset V × G.Subgraph) → Finset V → G.Subgraph,
      ∀ (T : ℕ → Finset V × G.Subgraph) (s : ℕ) (S : Finset V),
        s < Nat.floor (Δ-γ*Fintype.card V) →
        (∀ j < s, (T j).2 = rule j (transcriptPrefix T j) (T j).1) →
        (∀ j < s, OrdinaryPackingStrategy.Allowed G (Fintype.card V) ε j
          (transcriptPrefix T j) (T j).1) →
        OrdinaryPackingStrategy.Allowed G (Fintype.card V) ε s (transcriptPrefix T s) S →
        let C := rule s (transcriptPrefix T s) S
        C.IsMatching ∧ C.verts = (S : Set V)ᶜ ∧
          Disjoint C.spanningCoe (edgeUnion (fun i => (transcriptPrefix T s i).2.spanningCoe) univ) ∧
          C.spanningCoe ≤ G \ edgeUnion (fun i => (transcriptPrefix T s i).2.spanningCoe) univ ∧
          IsPackingHistory G (s+1) (transcriptPrefix (Function.update T s (S,C)) (s+1)) ∧
          IsRobustExpander
            ((G \ edgeUnion (fun i => (transcriptPrefix T s i).2.spanningCoe) univ) \ C.spanningCoe)
            θ (τ/2) := by
  obtain ⟨rule,hrule⟩ := hpacking V G Δ hm hrobust hΔ hdegree
  refine ⟨rule,?_⟩
  intro T s S hs hconsistent hallowed hS
  exact step_of_certificate G (Nat.floor (Δ-γ*Fintype.card V)) ε θ (τ/2)
    rule hrule T s S hs hconsistent hallowed hS

end Overfull.ForeignRuleStep
