import Overfull.ExceptionalPalette.ReserveCopies

/-!
# Inserting entire reserved boundaries into protected palette colors

A protected color has precisely the joining part of its prescribed boundary.
Replacing that color by the entire boundary inserts only internal copies.
The construction preserves all matching and disjointness certificates,
retains exact joining-copy coverage and cut parity, and records every added
copy. It applies to both singleton joining colors and protected empty colors.
-/

noncomputable section
namespace Overfull.NativeReserve
open Finset Classical FourOdd
open scoped BigOperators

variable {V E K I : Type*} [Fintype V] [Fintype E] [DecidableEq K]
    {G : Multigraph V E} {label : V → K} {h D L : ℕ} {p : K → ℕ}
    (C : JoiningPalette G label h D L p)

/-- Replace injectively indexed protected colors by their prescribed boundaries. -/
def reserveClasses (B : I → Finset E) (f : I → Fin h) : Fin h → Finset E :=
  Function.extend f B C.classes

@[simp] theorem reserveClasses_at (B : I → Finset E) (f : I → Fin h)
    (hf : Function.Injective f) (i : I) : reserveClasses C B f (f i) = B i :=
  hf.extend_apply B C.classes i

@[simp] theorem reserveClasses_other (B : I → Finset E) (f : I → Fin h)
    (j : Fin h) (hj : ¬∃ i, f i=j) : reserveClasses C B f j = C.classes j :=
  Function.extend_apply' B C.classes j hj

theorem joiningPalette_class_subset (j : Fin h) :
    C.classes j ⊆ joiningCopies G label := by
  intro e he
  rw [← C.cover]
  exact mem_biUnion.mpr ⟨j,mem_univ _,he⟩

theorem reserveClasses_matching (B : I → Finset E) (f : I → Fin h)
    (hf : Function.Injective f) (hB : ∀ i, G.IsMatching (B i)) (j : Fin h) :
    G.IsMatching (reserveClasses C B f j) := by
  by_cases hj : ∃ i, f i=j
  · obtain ⟨i,rfl⟩ := hj
    rw [reserveClasses_at C B f hf]
    exact hB i
  · rw [reserveClasses_other C B f j hj]
    exact C.matching j

/-- The replacement leaves the exact joining portion of every color unchanged. -/
theorem reserveClasses_joining (B : I → Finset E) (f : I → Fin h)
    (hf : Function.Injective f)
    (htrace : ∀ i, B i ∩ joiningCopies G label = C.classes (f i)) (j : Fin h) :
    reserveClasses C B f j ∩ joiningCopies G label = C.classes j := by
  by_cases hj : ∃ i, f i=j
  · obtain ⟨i,rfl⟩ := hj
    rw [reserveClasses_at C B f hf]
    exact htrace i
  · rw [reserveClasses_other C B f j hj]
    exact inter_eq_left.mpr (joiningPalette_class_subset C j)

/-- No original joining class loses any of its copies. -/
theorem reserveClasses_contains_original (B : I → Finset E) (f : I → Fin h)
    (hf : Function.Injective f)
    (htrace : ∀ i, B i ∩ joiningCopies G label = C.classes (f i)) (j : Fin h) :
    C.classes j ⊆ reserveClasses C B f j := by
  rw [← reserveClasses_joining C B f hf htrace j]
  exact inter_subset_left

/-- The original and inserted copies remain properly partitioned by colors. -/
theorem reserveClasses_disjoint (B : I → Finset E) (f : I → Fin h)
    (hf : Function.Injective f)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (htrace : ∀ i, B i ∩ joiningCopies G label = C.classes (f i)) :
    Pairwise (fun i j => Disjoint (reserveClasses C B f i) (reserveClasses C B f j)) := by
  intro j k hjk
  by_cases hj : ∃ i, f i=j
  · obtain ⟨a,rfl⟩ := hj
    rw [reserveClasses_at C B f hf]
    by_cases hk : ∃ i, f i=k
    · obtain ⟨b,rfl⟩ := hk
      rw [reserveClasses_at C B f hf]
      exact hB (fun hab => hjk (congrArg f hab))
    · rw [reserveClasses_other C B f k hk]
      apply disjoint_left.mpr
      intro e heB heC
      have he : e ∈ C.classes (f a) := by
        rw [← htrace a]
        exact mem_inter.mpr ⟨heB,joiningPalette_class_subset C k heC⟩
      exact disjoint_left.mp (C.disjoint hjk) he heC
  · rw [reserveClasses_other C B f j hj]
    by_cases hk : ∃ i, f i=k
    · obtain ⟨b,rfl⟩ := hk
      rw [reserveClasses_at C B f hf]
      apply disjoint_left.mpr
      intro e heC heB
      have he : e ∈ C.classes (f b) := by
        rw [← htrace b]
        exact mem_inter.mpr ⟨heB,joiningPalette_class_subset C j heC⟩
      exact disjoint_left.mp (C.disjoint hjk) heC he
    · rw [reserveClasses_other C B f k hk]
      exact C.disjoint hjk

/-- Only whole-class sizes matter; protected replacements have the original
reserve bound, independent of the number of protected colors. -/
theorem reserveClasses_card_le (B : I → Finset E) (f : I → Fin h)
    (hf : Function.Injective f) {b : ℕ} (hB : ∀ i, (B i).card ≤ b) (j : Fin h) :
    (reserveClasses C B f j).card ≤ max (3*L) b := by
  by_cases hj : ∃ i, f i=j
  · obtain ⟨i,rfl⟩ := hj
    rw [reserveClasses_at C B f hf]
    exact (hB i).trans (le_max_right _ _)
  · rw [reserveClasses_other C B f j hj]
    exact (C.card_le j).trans (le_max_left _ _)

theorem reserveClasses_support_card_le (B : I → Finset E) (f : I → Fin h)
    (hf : Function.Injective f) {b : ℕ} (hB : ∀ i, (B i).card ≤ b) (j : Fin h) :
    (G.edgeSupport (reserveClasses C B f j)).card ≤ 2*max (3*L) b :=
  (G.edgeSupport_card_le _).trans
    (Nat.mul_le_mul_left 2 (reserveClasses_card_le C B f hf hB j))

/-- Passing to the joining part loses no cut copy of a union of label fibers. -/
theorem cutOn_inter_joining (A : Finset E) (S : Finset K) :
    G.cutOn (A ∩ joiningCopies G label) (labelShore label S) =
      G.cutOn A (labelShore label S) := by
  ext e
  simp only [Multigraph.mem_cutOn,mem_inter]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · rintro ⟨he,hcut⟩
    refine ⟨⟨he,?_⟩,hcut⟩
    apply (mem_joiningCopies G label e).mpr
    intro heq
    exact hcut (propext (by simp only [mem_labelShore,heq]))

/-- Every assigned-fiber cut is unchanged exactly, not merely modulo two. -/
theorem reserveClasses_cut_eq (B : I → Finset E) (f : I → Fin h)
    (hf : Function.Injective f)
    (htrace : ∀ i, B i ∩ joiningCopies G label = C.classes (f i))
    (j : Fin h) (S : Finset K) :
    G.cutOn (reserveClasses C B f j) (labelShore label S) =
      G.cutOn (C.classes j) (labelShore label S) := by
  calc
    _ = G.cutOn (reserveClasses C B f j ∩ joiningCopies G label) (labelShore label S) :=
      (cutOn_inter_joining (G := G) (label := label) _ S).symm
    _ = _ := congrArg (fun A => G.cutOn A (labelShore label S))
      (reserveClasses_joining C B f hf htrace j)

theorem reserveClasses_cut_parity (B : I → Finset E) (f : I → Fin h)
    (hf : Function.Injective f)
    (htrace : ∀ i, B i ∩ joiningCopies G label = C.classes (f i))
    (j : Fin h) (i : K) :
    (G.cutOn (reserveClasses C B f j) (labelShore label {i})).card % 2 = p i := by
  rw [reserveClasses_cut_eq C B f hf htrace]
  exact C.cut_parity j i

variable [Fintype I]

/-- Exact whole-family coverage includes every joining copy and precisely the
selected reserve copies. Parallel copies are never identified. -/
theorem reserveClasses_cover (B : I → Finset E) (f : I → Fin h)
    (hf : Function.Injective f)
    (htrace : ∀ i, B i ∩ joiningCopies G label = C.classes (f i)) :
    univ.biUnion (reserveClasses C B f) = joiningCopies G label ∪ univ.biUnion B := by
  ext e
  constructor
  · intro he
    obtain ⟨j,_,hej⟩ := mem_biUnion.mp he
    by_cases hj : ∃ i, f i=j
    · obtain ⟨i,rfl⟩ := hj
      rw [reserveClasses_at C B f hf] at hej
      exact mem_union_right _ (mem_biUnion.mpr ⟨i,mem_univ _,hej⟩)
    · rw [reserveClasses_other C B f j hj] at hej
      exact mem_union_left _ (joiningPalette_class_subset C j hej)
  · intro he
    rcases mem_union.mp he with heJ | heB
    · rw [← C.cover] at heJ
      obtain ⟨j,_,hej⟩ := mem_biUnion.mp heJ
      exact mem_biUnion.mpr ⟨j,mem_univ _,reserveClasses_contains_original C B f hf htrace j hej⟩
    · obtain ⟨i,_,hei⟩ := mem_biUnion.mp heB
      apply mem_biUnion.mpr
      refine ⟨f i,mem_univ _,?_⟩
      rwa [reserveClasses_at C B f hf]

/-- The newly colored copy set is exactly the internal part of the selected
reserve; it is disjoint from every original joining copy. -/
theorem reserveClasses_added_copies (B : I → Finset E) (f : I → Fin h)
    (hf : Function.Injective f)
    (htrace : ∀ i, B i ∩ joiningCopies G label = C.classes (f i)) :
    (univ.biUnion (reserveClasses C B f)) \ joiningCopies G label =
      (univ.biUnion B) \ joiningCopies G label := by
  rw [reserveClasses_cover C B f hf htrace]
  ext e
  simp only [mem_sdiff,mem_union]
  tauto


/-- A matching family has exactly one used color per colored incidence.
Thus the extension's load is controlled by its actual original copies. -/
theorem reserveClasses_vertex_load_eq (B : I → Finset E) (f : I → Fin h)
    (hf : Function.Injective f) (hBm : ∀ i, G.IsMatching (B i))
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (htrace : ∀ i, B i ∩ joiningCopies G label = C.classes (f i)) (v : V) :
    (univ.filter (fun j => v ∈ G.edgeSupport (reserveClasses C B f j))).card =
      G.degreeOn (joiningCopies G label ∪ univ.biUnion B) v := by
  have hdisj := reserveClasses_disjoint C B f hf hBd htrace
  have heq := removed_degreeOn G (reserveClasses C B f) univ
    (fun i _ j _ hij => hdisj hij) v
  change G.degreeOn (univ.biUnion (reserveClasses C B f)) v = _ at heq
  rw [reserveClasses_cover C B f hf htrace] at heq
  have hdegree (j : Fin h) : G.degreeOn (reserveClasses C B f j) v =
      if v ∈ G.edgeSupport (reserveClasses C B f j) then 1 else 0 := by
    split_ifs with hv
    · have hlo := (G.degreeOn_pos_iff _ v).mpr hv
      have hhi := (G.isMatching_iff_incident_card_le_one _).mp
        (reserveClasses_matching C B f hf hBm j) v
      change G.degreeOn _ v ≤ 1 at hhi
      omega
    · exact G.degreeOn_eq_zero_of_not_mem hv
  simp_rw [hdegree] at heq
  simpa only [sum_boole] using heq.symm

/-- The extra vertex load is bounded by the actual added reserve incidences,
so no multiplication by the number of colors or boundary size is needed. -/
theorem reserveClasses_vertex_load_le (B : I → Finset E) (f : I → Fin h)
    (hf : Function.Injective f) (hBm : ∀ i, G.IsMatching (B i))
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (htrace : ∀ i, B i ∩ joiningCopies G label = C.classes (f i)) (v : V) :
    (univ.filter (fun j => v ∈ G.edgeSupport (reserveClasses C B f j))).card ≤
      D + G.degreeOn ((univ.biUnion B) \ joiningCopies G label) v := by
  rw [reserveClasses_vertex_load_eq C B f hf hBm hBd htrace]
  have hsplit : G.degreeOn (joiningCopies G label ∪ univ.biUnion B) v =
      G.degreeOn (joiningCopies G label) v +
        G.degreeOn ((univ.biUnion B) \ joiningCopies G label) v := by
    unfold Multigraph.degreeOn
    have hs : (joiningCopies G label ∪ univ.biUnion B).filter (fun e => v ∈ G.edge e) =
        (joiningCopies G label).filter (fun e => v ∈ G.edge e) ∪
          ((univ.biUnion B) \ joiningCopies G label).filter (fun e => v ∈ G.edge e) := by
      ext e
      simp only [mem_filter,mem_union,mem_sdiff]
      tauto
    rw [hs,card_union_of_disjoint]
    exact (disjoint_sdiff_self_right : Disjoint (joiningCopies G label)
      ((univ.biUnion B) \ joiningCopies G label)).mono (filter_subset _ _) (filter_subset _ _)
  rw [hsplit]
  apply Nat.add_le_add_right
  have heq := removed_degreeOn G C.classes univ (fun i _ j _ hij => C.disjoint hij) v
  change G.degreeOn (univ.biUnion C.classes) v = _ at heq
  rw [C.cover] at heq
  have hdegree (j : Fin h) : G.degreeOn (C.classes j) v =
      if v ∈ G.edgeSupport (C.classes j) then 1 else 0 := by
    split_ifs with hv
    · have hlo := (G.degreeOn_pos_iff _ v).mpr hv
      have hhi := (G.isMatching_iff_incident_card_le_one _).mp (C.matching j) v
      change G.degreeOn _ v ≤ 1 at hhi
      omega
    · exact G.degreeOn_eq_zero_of_not_mem hv
  simp_rw [hdegree] at heq
  rw [heq]
  simpa only [sum_boole] using C.vertex_load_le v

end Overfull.NativeReserve
