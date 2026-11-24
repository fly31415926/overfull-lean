# Next-run API plan: eliminate a tight shore on at most two labels

**Status: unverified implementation planning.** This file introduces no Lean
declaration and changes no assertion count. It was prepared while the current
run's frozen full verification was executing. Successful focused compilation
of supporting modules is not a claim that the full audit has completed.

The current supporting modules include:

- `FourDegreeTwoSupport.lean`: a compatible circuit partition whenever the
  actual selected support has at most three vertices.
- `FourDegreeTwoReassembly.lean`: exact selected-copy graph transport and
  disjoint union of compatible circuit partitions.
- `FourDegreeTwoSuppression.lean` and `FourDegreeTwoLift.lean`: exact path
  suppression and restoration for a degree-two label.
- `FourGlobalCoarsening.lean`: global admissibility under the constructed
  local tight-class coarsenings, and transport of compatibility/partitions
  back to the original classes. General strict nonlocal-bound transfer is
  still an implementation obligation.
- `FourTriangleSelection.lean`: the elementary actual-copy triangle-bundle
  selector and its monochromatic-corner obstruction. The general graph
  support classification, tight-shore lifts, and final four-label induction
  remain open.

The earlier research notes describe the mathematical argument. This plan
fixes concrete representations and interfaces for the next implementation.
All names below labeled proposed are new names to implement, not existing APIs.

## 1. Original-host endpoint

Proposed endpoint, with the original definitions of admissibility and circuit
partition unchanged:

```lean
theorem exists_compatibleCircuitPartition_of_tight_shore_of_card_le_two
    (Q : Multigraph (Fin 4) E) (classOf : Fin 4 → E → K)
    (C : Finset E) (X : Finset (Fin 4)) (w : Fin 4) (p : K)
    (hX : X.Nonempty) (hXsize : X.card ≤ 2) (hw : w ∉ X)
    (hadmissible : Q.AdmissibleOn classOf C)
    (heven : ∀ v, Even (Q.degreeOn C v))
    (htight : 2 * (Q.classCutOn classOf C w p X).card =
      (Q.cutOn C X).card) :
    Nonempty (Q.CompatibleCircuitPartition classOf C)
```

There is no supplied selector, path family, auxiliary partition, regularity
assumption, bound on a class size, or positive cut-size assumption. Include
the zero-cut case; the construction then reduces to independent inside and
outside partitions. The edge type `E` need not itself be finite: every
construction uses the given finite selected set `C`.

## 2. Fixed finite-copy geometry

Proposed raw sets, all consisting of original copies:

```text
boundary := Q.cutOn C X
A := Q.classCutOn classOf C w p X
B := boundary \ A
insideCopies := {e in C | some endpoint of e belongs to X}
outsideCopies := C \ insideCopies
```

Prove these identities once before defining either auxiliary graph:

- `A subset boundary`, `Disjoint A B`, `A union B = boundary`.
- `A.card = B.card`, derived from `htight` by the exact disjoint sum.
- `insideCopies` and `outsideCopies` partition `C`.
- A boundary copy has unique inside and outside endpoints. Define
  `insideEnd e` and `outsideEnd e` by testing `Q.firstEnd e ∈ X` and
  prove `Q.edge e = s(insideEnd e, outsideEnd e)` for boundary members.
- For `e ∈ A`, `outsideEnd e = w` and `classOf w e = p`.
- For `e ∈ B` with `outsideEnd e = w`, `classOf w e ≠ p`.

Do not choose representatives of parallel bundles. The endpoint helpers are
functions on actual copies; different copies remain different.

## 3. First graph: same labels, same edge type

Recommended representation: retain vertex type `Fin 4` and edge type `E`.
Use the newly available support-size theorem instead of changing to an
`Option X` vertex type. This avoids two layers of subtype transport.

Let `collapse x := if x ∈ X then x else w`. Define proposed
`innerGraph Q X w hw : Multigraph (Fin 4) E` by:

- If an original edge meets `X`, replace its endpoints by their images
  under `collapse`.
- If it does not meet `X`, leave its original edge unchanged. Such copies
  are not selected in this graph; retaining their original endpoints makes
  global looplessness straightforward without arbitrary default edges.

The selected set is exactly `insideCopies`. Its selected support lies in
`insert w X`, of cardinality at most three. Prove looplessness for selected
rewritten copies by splitting on which original endpoints belong to `X`.
Global injectivity of `collapse` is false and must not be assumed.

Use classes of type `K ⊕ Bool`:

```text
innerClass x e :=
  if x = w then Sum.inr (decide (e ∈ A))
  else Sum.inl (classOf x e)
```

At the apex, true means `A` and false means `B`; at the original interior
labels all original classes are retained. Values at unused incidences are
irrelevant. This construction needs no inhabitant of `K` beyond the supplied
original map and the fixed class `p`.

### Required inner graph lemmas

For every `Y subset X`, establish exact set identities before cardinality
consequences:

1. `innerGraph.cutOn insideCopies Y = Q.cutOn C Y`.
2. The original-class cut at an interior label `x ∈ X`, with class
   `Sum.inl k`, is `Q.classCutOn classOf C x k Y`.
3. The apex true class on that cut is the portion of `A` with inside
   endpoint in `Y`; the apex false class is the analogous portion of `B`.
4. Interior degrees equal `Q.degreeOn C x`; the apex degree is
   `boundary.card`; every other selected degree is zero.
5. Normalize an arbitrary tested shore `T`: if `w ∉ T`, its selected cut
   is the cut at `T ∩ X`; if `w ∈ T`, first take its complement. Apply
   the same normalization to class cuts, which filter the same copy set.

For the apex false-class bound, write `Z=X\Y`. Let `s` count edges between
`Y` and `Z`, and let `aY,bY,aZ,bZ` be the four boundary portions. Prove:

```text
cut(C,Y).card = s + aY + bY
cut(C,Z).card = s + aZ + bZ
aY + aZ = bY + bZ
```

Original admissibility at `(w,p,Z)` gives `2*aZ <= s+aZ+bZ`; the identities
yield `2*bY <= s+aY+bY`. This is the only new apex inequality. All other
classes either use an original inequality or have zero count.

Now construct `P1` internally with the existing
`exists_compatibleCircuitPartition_of_support_card_le_three`. Apex parity
comes from `even_cutOn_of_even_degrees`; no arbitrary pairing is needed.

## 4. Extract actual pieces from the first partition

Use the finite index subtype `{D // D ∈ P1.parts}`. Split it into parts whose
selected support contains `w` and parts that avoid `w`.

For a part through `w`, the circuit degree at `w` is two. Compatibility with
the two apex classes implies that it contains exactly one copy of `A` and
exactly one copy of `B`. Obtain actual chosen copies from singleton finite
sets, together with their uniqueness proofs:

```text
aCopy i : E, with i.copies intersect A = {aCopy i}
bCopy i : E, with i.copies intersect B = {bCopy i}
endPoint i := outsideEnd (bCopy i)
```

Proposed record `TightShorePiece` should contain the actual finite set of
copies and these derived facts; it need not contain a graph-theoretic `Walk`:

- `copies subset insideCopies` and `copies.Nonempty`.
- The unique `aCopy` and `bCopy` identities above.
- `endPoint ∉ X`; the outside endpoint of `aCopy` is `w`.
- Original compatibility of the entire finite set `copies`.
- For `x ∈ X`, its original degree in `copies` equals the first graph's
  degree there, so that degree is even.
- For `x ∉ X`, its original degree is exactly
  `(if x=w then 1 else 0) + (if x=endPoint then 1 else 0)`.
- The outside incidence at `w` has original class `p`; when the endpoint
  differs from `w`, the outside incidence there inherits the original
  class of `bCopy`.

Original compatibility at the interior labels follows from injectivity of
`Sum.inl`. If `endPoint=w`, the two original incidences there have different
classes, since `bCopy ∈ B`. Other outside incidences occur singly.

Prove that `bCopy` is injective on the through-apex part index and that its
range is exactly `B`. These follow from the original partition's disjointness
and coverage, and its one-B-copy property. This actual-copy bijection is
needed for every later count; a count of abstract paths alone is insufficient.
The analogous `aCopy` bijection to `A` is useful for the apex degree identity.

Split through-apex indices into:

- `Near`: `endPoint = w`, already closed original pieces.
- `Far`: `endPoint ≠ w`, to become virtual copies.

Parts avoiding the apex are wholly inside `X`. Those parts and `Near` are
the saved pieces. Each is an original compatible even-degree copy set.

## 5. Second graph: original copies plus indexed virtual pieces

Define proposed edge type `E ⊕ Far`, keeping vertex type `Fin 4`.

```text
outerGraph.edge (Sum.inl e) := Q.edge e
outerGraph.edge (Sum.inr i) := s(w, endPoint i)
```

The `Far` subtype supplies the required endpoint inequality. Its finite
selected set is:

```text
outsideCopies.map Sum.inlEmbedding union
  univ.map Sum.inrEmbedding
```

Use the original class type `K`:

```text
outerClass x (Sum.inl e) := classOf x e
outerClass x (Sum.inr i) :=
  if x=w then p else classOf x (bCopy i)
```

**The virtual class at `w` is the original value `p`.** It must conflict
with existing original incidences in class `p`. The existing
`pairAugmentationClass` uses a fresh class and therefore cannot be reused
unchanged for this construction. Its `toLeft`/`toRight` accounting proofs
are useful templates only.

Selected support is contained in `Xᶜ`. Its cardinality is at most three
because `X.Nonempty`. Retain `E` on the left even if it is infinite; only
`outsideCopies` is selected there, while `Far` is a finite subtype.

### Required outer cut and class identities

Normalize to `T subset Xᶜ` with `w ∉ T`. Put
`d = (Q.cutOn outsideCopies T).card`, and let `b` count members of `B`
whose outside endpoint belongs to `T`. Establish:

- The outer cut's `toLeft` is exactly `Q.cutOn outsideCopies T`.
- Its `toRight` is the finite set of `Far` indices with endpoint in `T`.
- Mapping that `toRight` through the `bCopy` embedding gives exactly the
  corresponding original `B` copies. Thus the outer cut size is `d+b`.
- The original cut at `T` is the disjoint union of that old cut and the
  same `B` copies, so it also has size `d+b`.
- For every outside label `x≠w` and class `k`, the outer class-cut count
  equals the original count on `C,T`.
- For `x=w` and `k≠p`, the same equality holds; virtual copies contribute
  no such class.
- For `(w,p)`, the outer class-cut count is `c+b`, where
  `c=(Q.classCutOn classOf outsideCopies w p T).card`.

Use subtraction-free identities for the enlarged original shore:

```text
cut(C, X union T).card + b = d + 2*A.card
classCut(C,w,p,X union T).card = c + A.card
```

Original admissibility on `X union T` then gives `2*(c+b)<=d+b`. This proves
the remaining outer inequality without truncation issues from natural
subtraction. All inside labels have zero outer incidence.

### Required outer degree identities

- At an outside label other than `w`, the degree is the original degree.
- At `w`, prove
  `outerDegree(w) + 2*Near.card = Q.degreeOn C w`.
- At a label in `X`, the selected degree is zero.

Derive these from the `aCopy` and `bCopy` bijections and the partition of
through-apex indices into `Near` and `Far`. They prove all outer degrees
even. Construct `P2` by the existing support-at-most-three theorem.

## 6. Expansion without a new connectivity theorem

For every outer part `D`, define its original expansion:

```text
expand D := D.toLeft union
  D.toRight.biUnion (fun i => (piece i).copies)
```

Compatibility at `w` bounds `D.toRight.card` by one, because every virtual
incidence has class `p`. Prove the bound using the existing
`Compatible.classCutOn_card_le_one` on the singleton shore `{w}`.

Show that `expand D` is compatible in the original graph:

- Old-old incidences transfer through `Sum.inl`.
- Within one piece, use its original compatibility.
- Two different virtual pieces cannot occur in this outer part.
- An old outside edge cannot meet an interior label of a piece.
- At `w` or the far endpoint, the original boundary class equals the
  corresponding virtual incidence class. A conflict would contradict
  outer compatibility between `Sum.inl e` and `Sum.inr i`.

Show its degrees are even. Outside `X`, expansion preserves the degrees of
the outer part exactly. Inside `X`, it contributes either zero or the even
interior degree of its unique piece. Old outside copies contribute zero.

Then use the already proved
`Q.exists_compatibleCircuitPartition_of_compatible classOf (expand D)`.
This avoids proving directly that the expansion is connected or building
a new path/circuit constructor. The same method partitions each saved
original compatible even-degree piece. This is exactly the successful
strategy used by `FourDegreeTwoLift.lean`.

## 7. Exact finite reassembly

Index all final blocks by the disjoint sum of saved first-part indices and
outer-part indices. Their original finite copy sets must be pairwise disjoint:

- Saved/saved follows from `P1.disjoint`.
- Saved/expanded: outside old copies avoid `insideCopies`; far pieces and
  saved pieces are different parts of `P1`.
- Expanded/expanded: original outside copies and virtual indices are
  disjoint by `P2.disjoint`; distinct far pieces are disjoint by `P1.disjoint`.

Their exact union is `C`, by `P1.cover`, `P2.cover`, the `toLeft`/`toRight`
identities, and `insideCopies union outsideCopies = C`. Prove the union as
an actual finite-set equality, not just equality of cardinalities.

A useful proposed generic helper is a finite disjoint-family version of
`CompatibleCircuitPartition.union`. Implement it by finite-set induction,
starting with `CompatibleCircuitPartition.empty`, and supply the derived
disjointness at each insertion. The final theorem constructs both auxiliary
partitions and every block partition internally, then invokes this helper.

## 8. Suggested nonoverlapping work packages

Agree on definitions in one small geometry module before parallel editing.

| Owner | Proposed files | Responsibility and dependency |
| --- | --- | --- |
| A | `FourTightShore/Geometry.lean`, `InnerGraph.lean`, `InnerCuts.lean` | Own raw sets, endpoint selectors, first graph and exact cut/degree/class identities; finish its admissibility certificate. |
| B | `FourTightShore/Pieces.lean` | From the fixed first graph and a constructed first partition, derive the unique A/B copies, endpoint records, original compatibility, degrees and copy bijections. |
| C | `FourTightShore/OuterGraph.lean`, `OuterCuts.lean` | Own the sum copy type and second graph; prove its exact cuts, original-class accounting, parity and support bound from the piece certificate. |
| Root | `FourTightShore/Expansion.lean`, `Reassembly.lean`, `Theorem.lean` | Prove expansion compatibility/evenness and generic finite reassembly, then compose the fully proved constructors into the original endpoint. |

After the shared raw definitions are stable, B can work against the explicit
first-graph certificate while A proves its constructor. C and the root can
similarly work against the exact piece record while B proves extraction.
These intermediate records are proof interfaces, not extra assumptions of
the final original-host theorem. Do not edit the same module from two owners.

Use focused recorded strict builds for each actual dependency stage. Before
promotion, check that the final theorem assumes only the original inputs in
Section 1 and perform the unchanged complete project gate, axiom audit, source
mapping and preservation checks. An elaborate proof of the intermediate
record alone does not complete tight-shore elimination.

## 9. Consequences and remaining independent work

Once compiled and fully audited, this endpoint will handle the general
four-label branch with a tight nonlocal singleton or two-versus-two cut.
It does not alone prove the unrestricted four-label theorem. The strict
nonlocal case still needs graph-level support/blocker classification and the
final induction using the existing exact small-circuit deletion criterion.

For the remaining uniform-C4 branch, there is a similar simplification:
choose one actual copy from each equal bundle, prove that the four-copy layer
is compatible and has degree two at each label, and invoke
`exists_compatibleCircuitPartition_of_compatible` on that layer. Reassemble
the disjoint layers with the partition-union helper. No new connected-C4
constructor is necessary. This is an unverified implementation suggestion.

There is also a shorter verified-by-reasoning argument for the K4 blocker
permutation's two-transposition case. If the singled-neighbor permutation
swaps `a,b` and swaps `c,d`, the blocked corner at `a` is the whole union of
bundles `ac,ad`, and the blocked corner at `b` is `bc,bd`. On the same shore
`{c,d}`, write `A=m_ac+m_ad` and `B=m_bc+m_bd`. The first blocker class has
exactly `A` crossing copies and the second exactly `B`; the whole cut has
`A+B` copies. The two admissibility inequalities give `A<=B` and `B<=A`,
respectively. Hence both class-cut inequalities are tight, contradicting
strict nonlocality on this positive cut. This subcase needs neither a
monochromatic choice for bundle `ab` nor the local dominance inequalities.
That simplification has not yet been implemented in Lean.

## 10. Implementation hazards already encountered

- Do not equate global graph support with selected support. Auxiliary graphs
  retain unused original copies to stay loopless on the whole edge type.
- Do not use a fresh second-graph class for the virtual copies at `w`.
- Do not identify two virtual copies with the same endpoint pair: the `Far`
  index must remain part of their edge-copy identity.
- Do not assume the first partition chooses a particular A-to-B pairing.
  All outer inequalities depend only on the exact `bCopy` bijection, so any
  partition returned by the three-label theorem is valid.
- Include zero selected cuts, empty families, and near-only families.
- Keep natural-number accounting subtraction-free wherever possible.
- Lean's selected-degree filters can use proof-irrelevant but syntactically
  different decision instances. For a failed apparent reflexive cardinality
  equality, prove the underlying finite sets equal by extensionality rather
  than changing the mathematical statement. In `simp only` proofs involving
  `Finset.mem_erase`, explicitly normalizing `ne_eq` was needed in this run.

