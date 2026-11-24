import Overfull.ForeignEdges.Completion
import Overfull.ForeignEdges.RuleStep

/-!
# Ambient completions produced by fixed core packing rules

The matching in a current core is obtained from the certified rule on the
initial core. Rehosting preserves its actual edges and vertices. The exact
unused graph from the rule is therefore the exact residual core used in
the ambient completion.
-/

namespace Overfull.ForeignRuleCompletion

open Finset Classical SimpleGraph ForceMatching SafePrescription
open ForeignTranscript ForeignRuleStep ForeignCompletion
open BipartitePackingAccounting

universe u v
variable {V : Type u} [Fintype V]

omit [Fintype V] in
def unusedGraph (G : SimpleGraph V) (T : ℕ → Finset V × G.Subgraph)
    (s : ℕ) : SimpleGraph V :=
  G \ edgeUnion (fun i => (transcriptPrefix T s i).2.spanningCoe) univ

/-- The certificate supplied by the proved finite-prefix packing theorem. -/
def RuleCertificate (G : SimpleGraph V) (q : ℕ) (ε θ σ : ℝ)
    (rule : (s : ℕ) → (Fin s → Finset V × G.Subgraph) → Finset V → G.Subgraph) : Prop :=
  ∀ T : ℕ → Finset V × G.Subgraph, ∀ s ≤ q,
    (∀ j < s, (T j).2 = rule j (transcriptPrefix T j) (T j).1) →
    (∀ j < s, OrdinaryPackingStrategy.Allowed G (Fintype.card V) ε j
      (transcriptPrefix T j) (T j).1) →
    IsPackingHistory G s (transcriptPrefix T s) ∧
    IsRobustExpander (unusedGraph G T s) θ σ

/-- An actual next rule output is rehosted into the whole current unused
core, with exactly the same edges and the certified robust remainder. -/
theorem core_matching_from_certificate (G : SimpleGraph V) (q : ℕ) (ε θ σ : ℝ)
    (rule : (s : ℕ) → (Fin s → Finset V × G.Subgraph) → Finset V → G.Subgraph)
    (hcertificate : RuleCertificate G q ε θ σ rule)
    (T : ℕ → Finset V × G.Subgraph) (s : ℕ) (S : Finset V)
    (hs : s < q)
    (hconsistent : ∀ j < s, (T j).2 = rule j (transcriptPrefix T j) (T j).1)
    (hallowed : ∀ j < s, OrdinaryPackingStrategy.Allowed G (Fintype.card V) ε j
      (transcriptPrefix T j) (T j).1)
    (hS : OrdinaryPackingStrategy.Allowed G (Fintype.card V) ε s (transcriptPrefix T s) S) :
    ∃ C : (unusedGraph G T s).Subgraph,
      C.IsMatching ∧ C.verts = (S : Set V)ᶜ ∧
      C.spanningCoe = (rule s (transcriptPrefix T s) S).spanningCoe ∧
      IsRobustExpander ((unusedGraph G T s) \ C.spanningCoe) θ σ := by
  have hcert : ∀ T : ℕ → Finset V × G.Subgraph, ∀ s ≤ q,
      (∀ j < s, (T j).2 = rule j (transcriptPrefix T j) (T j).1) →
      (∀ j < s, OrdinaryPackingStrategy.Allowed G (Fintype.card V) ε j
        (transcriptPrefix T j) (T j).1) →
      IsPackingHistory G s (transcriptPrefix T s) ∧
      IsRobustExpander
        (G \ edgeUnion (fun i => (transcriptPrefix T s i).2.spanningCoe) univ) θ σ := by
    intro T s hs hc ha
    obtain ⟨hp,hr⟩ := hcertificate T s hs hc ha
    exact ⟨hp,by convert hr using 1⟩
  obtain ⟨hC,hverts,_hdisj,hunused,_hpacking,hrobust⟩ :=
    step_of_certificate G q ε θ σ rule hcert T s S hs hconsistent hallowed hS
  let C₀ := rule s (transcriptPrefix T s) S
  let C := rehost G (unusedGraph G T s) C₀ (fun _ _ h => hunused h)
  have hCspan : C.spanningCoe = C₀.spanningCoe := rfl
  refine ⟨C,rehost_isMatching G _ C₀ _ hC,hverts,hCspan,?_⟩
  exact hrobust.mono_graph _ _ (by rw [hCspan]; exact le_rfl)

omit [Fintype V] in
/-- One rule for each initial core is chosen before the transcripts and
before any ambient partial matching is presented. -/
theorem exists_certified_core_rules {I : Type v}
    (U : I → Finset V) (H₀ : ∀ i, SimpleGraph (U i))
    (α γ ν τ ε θ : ℝ) (m₀ : ℕ)
    (hpacking : ForeignPackingSchedule.PackingRule.{u} α γ ν τ ε θ m₀) (Δ : ℝ)
    (hm : ∀ i, m₀ ≤ (U i).card)
    (hrobust : ∀ i, IsRobustExpander (H₀ i) ν τ)
    (hΔ : ∀ i, α*(U i).card ≤ Δ)
    (hdegree : ∀ i v, |((H₀ i).degree v : ℝ)-Δ| ≤ ε*(U i).card) :
    ∃ rule : ∀ i, (s : ℕ) → (Fin s → Finset (U i) × (H₀ i).Subgraph) →
        Finset (U i) → (H₀ i).Subgraph,
      ∀ i, RuleCertificate (H₀ i) (Nat.floor (Δ-γ*(U i).card)) ε θ (τ/2) (rule i) := by
  have hex (i : I) : ∃ rule : (s : ℕ) →
      (Fin s → Finset (U i) × (H₀ i).Subgraph) → Finset (U i) → (H₀ i).Subgraph,
      RuleCertificate (H₀ i) (Nat.floor (Δ-γ*(U i).card)) ε θ (τ/2) rule := by
    obtain ⟨rule,hrule⟩ := hpacking (U i) (H₀ i) Δ
      (by simpa only [Fintype.card_coe] using hm i)
      (by convert hrobust i using 1) (by simpa only [Fintype.card_coe] using hΔ i)
      (by intro v; simpa only [Fintype.card_coe] using hdegree i v)
    refine ⟨rule,?_⟩
    intro T s hs hc ha
    obtain ⟨hp,hr⟩ := hrule T s (by simpa only [Fintype.card_coe] using hs) hc ha
    exact ⟨hp,by convert hr using 1⟩
  choose rule hrule using hex
  exact ⟨rule,hrule⟩

/-- Certified next outputs in all cores give an actual ambient perfect
matching. Robust completion is a conclusion derived from the certificates,
not an additional existence hypothesis. -/
theorem assemble_from_certificates {I : Type v}
    (G : SimpleGraph V) (U : I → Finset V) (Z : Finset V)
    (H₀ : ∀ i, SimpleGraph (U i))
    (rule : ∀ i, (s : ℕ) → (Fin s → Finset (U i) × (H₀ i).Subgraph) →
      Finset (U i) → (H₀ i).Subgraph)
    (q : I → ℕ) (ε θ σ : ℝ)
    (hcertificate : ∀ i, RuleCertificate (H₀ i) (q i) ε θ σ (rule i))
    (T : ∀ i, ℕ → Finset (U i) × (H₀ i).Subgraph) (s : ℕ)
    (F : G.Subgraph)
    (hH : ∀ i, unusedGraph (H₀ i) (T i) s ≤ G.induce (U i : Set V))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hF : F.IsMatching) (hZ : (Z : Set V) ⊆ F.verts)
    (hno : ∀ i u v, u ∈ U i → v ∈ U i → ¬ F.Adj u v)
    (hs : ∀ i, s < q i)
    (hconsistent : ∀ i j, j < s →
      (T i j).2 = rule i j (transcriptPrefix (T i) j) (T i j).1)
    (hallowed : ∀ i j, j < s →
      OrdinaryPackingStrategy.Allowed (H₀ i) (Fintype.card (U i)) ε j
        (transcriptPrefix (T i) j) (T i j).1)
    (hS : ∀ i, OrdinaryPackingStrategy.Allowed (H₀ i) (Fintype.card (U i)) ε s
      (transcriptPrefix (T i) s) (coveredCore (U i) G F)) :
    ∃ N : G.Subgraph, ∃ C : ∀ i, (unusedGraph (H₀ i) (T i) s).Subgraph,
      N.IsPerfectMatching ∧ F ≤ N ∧
      (∀ u v, N.Adj u v → F.Adj u v ∨ ∃ i, u ∈ U i ∧ v ∈ U i) ∧
      (∀ i, (C i).IsMatching) ∧
      (∀ i, (C i).verts = (coveredCore (U i) G F : Set (U i))ᶜ) ∧
      (∀ i, (C i).spanningCoe =
        (rule i s (transcriptPrefix (T i) s) (coveredCore (U i) G F)).spanningCoe) ∧
      (∀ i, N.spanningCoe.induce (U i : Set V) = (C i).spanningCoe) ∧
      (∀ i, (unusedGraph (H₀ i) (T i) s) \ (C i).spanningCoe ≤
        (G \ N.spanningCoe).induce (U i : Set V)) ∧
      (∀ i, IsRobustExpander
        ((unusedGraph (H₀ i) (T i) s) \ (C i).spanningCoe) θ σ) := by
  have hex (i : I) := core_matching_from_certificate (H₀ i) (q i) ε θ σ
    (rule i) (hcertificate i) (T i) s (coveredCore (U i) G F) (hs i)
    (hconsistent i) (hallowed i) (hS i)
  choose C hC hverts hCspan hrobust using hex
  obtain ⟨N,hN,hFN,hNedges,hNlocal,hRle⟩ :=
    assemble_core_completions G U Z (fun i => unusedGraph (H₀ i) (T i) s) hH F C
      hdisjoint hcover hF hZ hno hC hverts
  exact ⟨N,C,hN,hFN,hNedges,hC,hverts,hCspan,hNlocal,hRle,by
    intro i
    convert hrobust i using 1⟩

set_option maxHeartbeats 800000 in
/-- The safe-completion clause produced by `prepare_safe_prescription`
is now applied to completions constructed from the fixed rules. In
particular, robustness of a completion is derived from the certificates.
The returned induced matching edges equal the exact next rule outputs. -/
theorem safe_complete_from_certificates {I : Type v}
    (G : SimpleGraph V) (U : I → Finset V) (Z : Finset V)
    (H₀ : ∀ i, SimpleGraph (U i))
    (rule : ∀ i, (s : ℕ) → (Fin s → Finset (U i) × (H₀ i).Subgraph) →
      Finset (U i) → (H₀ i).Subgraph)
    (q : I → ℕ) (ε θ σ μ τ : ℝ)
    (hcertificate : ∀ i, RuleCertificate (H₀ i) (q i) ε θ σ (rule i))
    (T : ∀ i, ℕ → Finset (U i) × (H₀ i).Subgraph) (s h loss : ℕ) (a : ℝ)
    (F M : G.Subgraph)
    (hH : ∀ i, unusedGraph (H₀ i) (T i) s ≤ G.induce (U i : Set V))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hF : F.IsMatching) (hZ : (Z : Set V) ⊆ F.verts)
    (hno : ∀ i u v, u ∈ U i → v ∈ U i → ¬ F.Adj u v)
    (hs : ∀ i, s < q i)
    (hconsistent : ∀ i j, j < s →
      (T i j).2 = rule i j (transcriptPrefix (T i) j) (T i j).1)
    (hallowed : ∀ i j, j < s →
      OrdinaryPackingStrategy.Allowed (H₀ i) (Fintype.card (U i)) ε j
        (transcriptPrefix (T i) j) (T i j).1)
    (hS : ∀ i, OrdinaryPackingStrategy.Allowed (H₀ i) (Fintype.card (U i)) ε s
      (transcriptPrefix (T i) s) (coveredCore (U i) G F))
    (hh : 0 < h) (hμ : μ ≤ θ) (hστ : σ ≤ τ)
    (hdegree : ∀ i v, (h : ℝ)-a ≤ (unusedGraph (H₀ i) (T i) s).degree v)
    (hsafe : ∀ (N : G.Subgraph) (R : ∀ i, SimpleGraph (U i)),
      N.IsPerfectMatching → F ≤ N →
      (∀ u v, N.Adj u v → F.Adj u v ∨ ∃ i, u ∈ U i ∧ v ∈ U i) →
      (∀ i, R i ≤ (G \ N.spanningCoe).induce (U i : Set V)) →
      (∀ i, IsRobustExpander (R i) μ τ) →
      (∀ i v, ((h-1 : ℕ) : ℝ)-a ≤ (R i).degree v) →
      (M.edgeSet \ N.edgeSet).ncard ≤ loss ∧
      (∀ X : Finset V, ¬ IsOverfull (G \ N.spanningCoe) (h-1) X)) :
    ∃ N : G.Subgraph,
      N.IsPerfectMatching ∧ F ≤ N ∧
      (M.edgeSet \ N.edgeSet).ncard ≤ loss ∧
      (∀ X : Finset V, ¬ IsOverfull (G \ N.spanningCoe) (h-1) X) ∧
      (∀ i, N.spanningCoe.induce (U i : Set V) =
        (rule i s (transcriptPrefix (T i) s) (coveredCore (U i) G F)).spanningCoe) ∧
      (∀ i, IsRobustExpander
        ((unusedGraph (H₀ i) (T i) s) \
          (rule i s (transcriptPrefix (T i) s) (coveredCore (U i) G F)).spanningCoe) θ σ) ∧
      (∀ i, (unusedGraph (H₀ i) (T i) s) \
          (rule i s (transcriptPrefix (T i) s) (coveredCore (U i) G F)).spanningCoe ≤
        (G \ N.spanningCoe).induce (U i : Set V)) := by
  obtain ⟨N,C,hN,hFN,hNedges,hC,_hverts,hCspan,hNlocal,hRle,hrobust⟩ :=
    assemble_from_certificates G U Z H₀ rule q ε θ σ hcertificate T s F
      hH hdisjoint hcover hF hZ hno hs hconsistent hallowed hS
  have hRdegree : ∀ i v, ((h-1 : ℕ) : ℝ)-a ≤
      (((unusedGraph (H₀ i) (T i) s) \ (C i).spanningCoe).degree v : ℝ) := by
    intro i v
    have hl := core_remainder_degree_lower (unusedGraph (H₀ i) (T i) s)
      (C i) (hC i) (h : ℝ) a (hdegree i) v
    simpa only [Nat.cast_sub (by omega : 1 ≤ h),Nat.cast_one] using hl
  obtain ⟨hloss,hresidual⟩ := hsafe N
    (fun i => (unusedGraph (H₀ i) (T i) s) \ (C i).spanningCoe)
    hN hFN hNedges hRle (by
      intro i
      have hr := (hrobust i).mono_parameter _ hμ
      have hr' := hr.mono_range _ hστ
      convert hr' using 1) (by
      intro i v
      simpa only [← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hRdegree i v)
  refine ⟨N,hN,hFN,hloss,hresidual,?_,?_,?_⟩
  · intro i
    exact (hNlocal i).trans (hCspan i)
  · intro i
    exact (hrobust i).mono_graph _ _ (by rw [hCspan i])
  · intro i
    simpa only [hCspan i] using hRle i

end Overfull.ForeignRuleCompletion
