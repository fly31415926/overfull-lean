import Overfull.CompatibleCircuits.FourAdmissibleCoarsening
import Overfull.CompatibleCircuits.FourAdmissibleTransfer

/-! Four canonical four-regular graphs, including the disconnected case.
The three connected cases use the earlier checked small-kernel certificates. -/

namespace Overfull.CompatibleCircuits.FourRegular

open Finset Classical

def first : Fin 4 → Fin 8 → Fin 4 :=
  ![![0,0,0,0,2,2,2,2], SmallKernel.first 2, SmallKernel.first 3, SmallKernel.first 4]

def second : Fin 4 → Fin 8 → Fin 4 :=
  ![![1,1,1,1,3,3,3,3], SmallKernel.second 2, SmallKernel.second 3, SmallKernel.second 4]

theorem endpoints_ne : ∀ (t : Fin 4) (e : Fin 8), first t e ≠ second t e := by decide

def graph (t : Fin 4) : Multigraph (Fin 4) (Fin 8) where
  edge e := s(first t e,second t e)
  loopless e := by simpa using endpoints_ne t e

def rank : Fin 4 → Fin 4 → Fin 8 → ℕ :=
  ![(fun _ e => e.val % 4), SmallKernel.incidenceRank 2,
    SmallKernel.incidenceRank 3, SmallKernel.incidenceRank 4]

def classes (t : Fin 4) (choice : Fin 4 → Fin 3) (v : Fin 4) (e : Fin 8) : Bool :=
  SmallKernel.pairClass (choice v) (rank t v e)

def port : Fin 4 → Fin 4 → Fin 4 → Fin 8 :=
  ![![![0,1,2,3],![0,1,2,3],![4,5,6,7],![4,5,6,7]],
    ![![0,1,2,6],![0,1,2,7],![3,4,5,6],![3,4,5,7]],
    ![![0,1,4,5],![0,1,6,7],![2,3,4,5],![2,3,6,7]],
    ![![0,1,4,6],![0,1,5,7],![2,3,4,7],![2,3,5,6]]]

theorem port_injective : ∀ (t v : Fin 4), Function.Injective (port t v) := by decide

theorem port_incident : ∀ (t v : Fin 4) (i : Fin 4),
    v = first t (port t v i) ∨ v = second t (port t v i) := by decide

theorem port_surjective : ∀ (t v : Fin 4) (e : Fin 8),
    (v = first t e ∨ v = second t e) → ∃ i, port t v i = e := by decide

theorem rank_port : ∀ (t v i : Fin 4), rank t v (port t v i) = i.val := by decide

/-- The incidence ranking is an actual bijection at each vertex. -/
def portEquiv (t v : Fin 4) : Fin 4 ≃ {e : Fin 8 // v ∈ (graph t).edge e} :=
  Equiv.ofBijective (fun i => ⟨port t v i, by
    simpa only [graph,Sym2.mem_iff] using port_incident t v i⟩) ⟨by
      intro i j h
      exact port_injective t v (congrArg Subtype.val h), by
      intro e
      obtain ⟨i,hi⟩ := port_surjective t v e.val (by
        simpa only [graph,Sym2.mem_iff] using e.property)
      exact ⟨i,Subtype.ext hi⟩⟩

def different (a b : Fin 3) : Fin 3 :=
  if a ≠ 0 ∧ b ≠ 0 then 0 else if a ≠ 1 ∧ b ≠ 1 then 1 else 2

theorem different_left : ∀ a b, different a b ≠ a := by decide
theorem different_right : ∀ a b, different a b ≠ b := by decide

def pairIndex : Fin 3 → Fin 2 → Fin 2 → Fin 4 :=
  ![![![0,1],![2,3]],![![0,2],![1,3]],![![0,3],![1,2]]]

def pairEdge (b : Fin 2) (q : Fin 3) (j k : Fin 2) : Fin 8 :=
  ⟨4*b.val + (pairIndex q j k).val, by omega⟩

def pairPart (b : Fin 2) (q : Fin 3) (j : Fin 2) : Finset (Fin 8) :=
  {pairEdge b q j 0,pairEdge b q j 1}

theorem pairEdge_ne : ∀ b q j, pairEdge b q j 0 ≠ pairEdge b q j 1 := by decide

theorem pairEdge_parallel : ∀ b q j,
    (graph 0).edge (pairEdge b q j 0) = (graph 0).edge (pairEdge b q j 1) := by decide

theorem pairClass_ne : ∀ (q r : Fin 3) (b j : Fin 2), q ≠ r →
    SmallKernel.pairClass r (rank 0 0 (pairEdge b q j 0)) ≠
      SmallKernel.pairClass r (rank 0 0 (pairEdge b q j 1)) := by decide

def disconnectedPart (choice : Fin 4 → Fin 3) (i : Fin 2 × Fin 2) : Finset (Fin 8) :=
  pairPart i.1 (different (choice (if i.1 = 0 then 0 else 2))
    (choice (if i.1 = 0 then 1 else 3))) i.2

theorem disconnected_circuit (choice : Fin 4 → Fin 3) (i : Fin 2 × Fin 2) :
    (graph 0).IsCircuit (disconnectedPart choice i) :=
  (graph 0).isCircuit_parallel_pair (pairEdge_ne _ _ _) (pairEdge_parallel _ _ _)

theorem disconnected_compatible (choice : Fin 4 → Fin 3) (i : Fin 2 × Fin 2) :
    (graph 0).Compatible (classes 0 choice) (disconnectedPart choice i) := by
  rcases i with ⟨b,j⟩
  let q := different (choice (if b=0 then 0 else 2)) (choice (if b=0 then 1 else 3))
  have hq0 := different_left (choice (if b=0 then 0 else 2)) (choice (if b=0 then 1 else 3))
  have hq1 := different_right (choice (if b=0 then 0 else 2)) (choice (if b=0 then 1 else 3))
  have hinc : ∀ v k, v ∈ (graph 0).edge (pairEdge b q j k) →
      v = (if b=0 then 0 else 2) ∨ v = (if b=0 then 1 else 3) := by
    have h : ∀ (b : Fin 2) (q : Fin 3) (j k : Fin 2) (v : Fin 4),
        (v = first 0 (pairEdge b q j k) ∨ v = second 0 (pairEdge b q j k)) →
        v = (if b=0 then 0 else 2) ∨ v = (if b=0 then 1 else 3) := by decide
    intro v k hv
    exact h b q j k v (by simpa only [graph,Sym2.mem_iff] using hv)
  have hdiff (v : Fin 4) (hv : v ∈ (graph 0).edge (pairEdge b q j 0)) :
      classes 0 choice v (pairEdge b q j 0) ≠ classes 0 choice v (pairEdge b q j 1) := by
    have hq : q ≠ choice v := by
      rcases hinc v 0 hv with h | h
      · simpa only [h] using hq0
      · simpa only [h] using hq1
    exact pairClass_ne q (choice v) b j hq
  intro v e he hve f hf hvf hclasses
  change e ∈ pairPart b q j at he
  change f ∈ pairPart b q j at hf
  simp only [pairPart,mem_insert,mem_singleton] at he hf
  rcases he with rfl | rfl <;> rcases hf with rfl | rfl
  · rfl
  · exact False.elim (hdiff v hve hclasses)
  · exact False.elim (hdiff v hvf hclasses.symm)
  · rfl

theorem disconnected_disjoint : ∀ (q₀ q₁ : Fin 3) (b j b' j' : Fin 2),
    (b,j) ≠ (b',j') →
      Disjoint (pairPart b (if b=0 then q₀ else q₁) j)
        (pairPart b' (if b'=0 then q₀ else q₁) j') := by decide

theorem disconnected_cover : ∀ (q₀ q₁ : Fin 3),
    univ.biUnion (fun i : Fin 2 × Fin 2 => pairPart i.1 (if i.1=0 then q₀ else q₁) i.2) =
      univ := by decide

noncomputable def disconnectedPartition (choice : Fin 4 → Fin 3) :
    (graph 0).CompatibleCircuitPartition (classes 0 choice) univ where
  parts := univ.image (disconnectedPart choice)
  circuit := by
    intro D hD
    obtain ⟨i,_,rfl⟩ := mem_image.mp hD
    exact disconnected_circuit choice i
  compatible := by
    intro D hD
    obtain ⟨i,_,rfl⟩ := mem_image.mp hD
    exact disconnected_compatible choice i
  disjoint := by
    intro D hD D' hD' hne
    obtain ⟨⟨b,j⟩,_,rfl⟩ := mem_image.mp hD
    obtain ⟨⟨b',j'⟩,_,rfl⟩ := mem_image.mp hD'
    have hh := disconnected_disjoint (different (choice 0) (choice 1))
      (different (choice 2) (choice 3)) b j b' j' (by
        intro h; exact hne (congrArg (disconnectedPart choice) h))
    fin_cases b <;> fin_cases b' <;> simpa [disconnectedPart] using hh
  cover := by
    have hh := disconnected_cover (different (choice 0) (choice 1))
      (different (choice 2) (choice 3))
    have heq : disconnectedPart choice =
        fun i : Fin 2 × Fin 2 => pairPart i.1
          (if i.1=0 then different (choice 0) (choice 1)
           else different (choice 2) (choice 3)) i.2 := by
      funext i
      rcases i with ⟨b,j⟩
      fin_cases b <;> rfl
    rw [heq]
    simpa only [Finset.biUnion_image,id_comp] using hh

theorem exists_template_partition (t : Fin 4) (choice : Fin 4 → Fin 3) :
    Nonempty ((graph t).CompatibleCircuitPartition (classes t choice) univ) := by
  fin_cases t
  · exact ⟨disconnectedPartition choice⟩
  · simpa [graph,first,second,classes,rank,SmallKernel.graph,SmallKernel.classOf,
      SmallKernel.copies,SmallKernel.copyCount] using SmallKernel.exists_partition 2 choice
  · simpa [graph,first,second,classes,rank,SmallKernel.graph,SmallKernel.classOf,
      SmallKernel.copies,SmallKernel.copyCount] using SmallKernel.exists_partition 3 choice
  · simpa [graph,first,second,classes,rank,SmallKernel.graph,SmallKernel.classOf,
      SmallKernel.copies,SmallKernel.copyCount] using SmallKernel.exists_partition 4 choice

end Overfull.CompatibleCircuits.FourRegular
