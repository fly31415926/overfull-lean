# Compatible circuits on at most three labels

This is a mathematical proof for subsequent formalization. It has not yet
been checked by Lean. The existing checked module
`Overfull/CompatibleCircuits/ThreeVertexDeletion.lean` supplies the exact
safe-deletion criterion used below.

## Statement

Let Q be a finite loopless multigraph on at most three vertices. At each
vertex partition its incident edge copies into arbitrary classes. Suppose
that every vertex has even degree and that, for every incidence class I
and every edge cut T,

    2 |I ∩ T| ≤ |T|.

Then the original edge copies partition into compatible circuits: each
part is either a pair of parallel copies or a triangle, and at each vertex
its two incidences belong to different prescribed classes.

The proof establishes the stronger inductive step: if the graph is
nonempty, it contains a compatible circuit whose deletion preserves all
the displayed inequalities.

Isolated vertices may be added, so use exactly three labels A, B, C.
Write AB, AC, BC for their sets of actual parallel copies and x, y, z for
the corresponding cardinalities. A nonempty edge set has at least one
positive bundle. Even degrees imply that x, y, z have the same parity.

Every nontrivial cut equals one of the three singleton cuts or its
complement. At A, the cut inequalities are precisely

    2 |I| ≤ x+y,
    2 |I ∩ AB| ≤ x+z,
    2 |I ∩ AC| ≤ y+z.

Call the first inequality local and the other two nonlocal. A class-cut
inequality is tight if equality holds. Classes have only incidences at
their own vertex; the intersection with a nonincident bundle is empty.

## 1. Two elementary selection facts

### Two-coordinate grid lemma

Let S be a nonempty finite set, with two coordinate functions f and g. If
neither function is constant on S, there are distinct e,h in S for which
f(e) differs from f(h) and g(e) differs from g(h).

Indeed, if no such pair exists, choose e0. If every element has its first
coordinate equal to f(e0), the first coordinate is constant. Otherwise
choose e1 with f(e1) different from f(e0); then g(e1)=g(e0). If some e2 has
g(e2) different from g(e0), comparison with e0 forces f(e2)=f(e0), but
comparison of e1 and e2 differs in both coordinates, a contradiction.
Thus the second coordinate is constant.

### Coarsening the local tight classes

At a positive-degree vertex v, if there is a local tight class J, replace
the class map by the two classes J and its complement among incidences.
If there is no local tight class, retain the original map. Denote this
coarse class map by gamma_v.

It has three properties:

1. Distinct coarse classes imply distinct original classes.
2. Every coarse class has at most d(v)/2 incidences. In the binary case
   both have exactly d(v)/2.
3. Any two incidences with distinct coarse classes meet every original
   local tight class at v.

For the last assertion, they meet the chosen J. Any other local tight
class J' is disjoint from J and has the same size d(v)/2, so J' is exactly
the complement of J. Thus the pair also meets J'. At an isolated vertex
no selected circuit has an incidence, so no construction is needed there.

## 2. Unequal bundle sizes

Relabel the three vertices so that

    x = |AB| ≥ y = |AC| ≥ z = |BC|.

Assume x>z. We construct a safely removable parallel pair in AB.

The locally coarsened map gamma_B is not constant on AB: each of its
classes has at most (x+z)/2 incidences in the whole graph, whereas
(x+z)/2<x=|AB|.

### 2a. A nonlocal tight class at A for the cut at B exists

Choose such a class I. Put I_AB=I ∩ AB and O=AB minus I_AB. Then

    |I_AB| = (x+z)/2,     |O| = (x-z)/2.

Both sets are nonempty. On AB use the binary coordinate indicating
membership in I_AB, and the coordinate gamma_B. Neither is constant, so
the grid lemma gives a pair e,h with e in I_AB, h in O, and distinct
gamma_B values. The pair is compatible in the original classes at both
ends and meets every local tight class at B.

It also meets all required tight classes at A:

- If J is another nonlocal tight class at A for the cut at B, and J is
  different from I, then J ∩ AB is contained in O and has size (x+z)/2.
  Because |O|=(x-z)/2, this forces z=0 and J ∩ AB=O. Thus h lies in J.
- If J is a local tight class at A different from I, its nonlocal cut
  bound at C gives

      2 |J ∩ AB| = x+y-2 |J ∩ AC| ≥ x-z = 2 |O|.

  Since J ∩ AB is contained in O, it equals O. Again h lies in J. If
  J=I, e already lies in it.

### 2b. There is no such nonlocal tight class at A

Use gamma_A and gamma_B on AB. It remains to show that gamma_A is not
constant there.

If there is no local tight class at A, gamma_A is the original map. An
original class cannot contain all x copies of AB, because its nonlocal
cut bound at B would give 2x≤x+z, contrary to x>z.

If a local tight class J was used for the binary coarsening, constancy
on AB has two possibilities. If AB is contained in J, the same cut bound
at B gives a contradiction. If J has no AB incidence, J is contained in
AC, and its local equality and nonlocal bound at C give

    x+y = 2 |J| = 2 |J ∩ AC| ≤ y+z,

again contradicting x>z. Thus both coordinates are nonconstant; the grid
lemma gives a compatible parallel pair meeting all local tight classes
at A and B. There is no nonlocal tight class at A for the cut at B by the
assumption of this case.

### 2c. Check every other tight constraint for the selected pair

The pair crosses only the singleton cuts at A and B.

- A nonlocal tight class J at B for the cut at A has
  2|J∩AB|=x+y. Its local bound gives x+y≤x+z, so y=z. Then its AB
  incidences already have size (x+z)/2, and J has no BC incidences.
  Consequently J is itself local tight at B, and has been met.
- A nonlocal tight class at C for the cut at A would satisfy
  2|J∩AC|=x+y. The local bound at C gives x+y≤y+z, contradicting x>z.
- A nonlocal tight class at C for the cut at B would satisfy
  2|J∩BC|=x+z. Since |J∩BC|≤z, this gives x≤z, also impossible.

The cut at C is not crossed, and no other nontrivial cuts exist. Thus the
pair meets every tight class on each cut it crosses. The exact
three-label deletion criterion proves that the residual is admissible.

## 3. All three bundles have the same size

Now x=y=z=s. Nonemptiness implies s>0, and every vertex has degree 2s.
The coarse maps gamma_A, gamma_B, gamma_C have all class sizes at most s.

Every nonlocal tight class at a vertex is exactly one complete incident
bundle: for example, a class I at A tight for the cut at B satisfies
|I∩AB|=s, and its local bound |I|≤s forces I=AB. Therefore **every
triangle meets every original nonlocal tight class**.

### 3a. Some original nonlocal tight class exists

Relabel so that it is I=AB at A. The bundle AB is monochromatic under
gamma_A, while no AC incidence has that coarse color. To see this, I is
local tight; if I was chosen for the coarsening this is immediate. If a
different local tight class was chosen, it is exactly the complement of
I and hence exactly AC.

Choose any actual copy g in BC. Some e in AB has gamma_B(e) different
from gamma_B(g): otherwise a coarse class at B would contain all s AB
copies and the additional copy g, contradicting its size bound s.
Similarly, some h in AC has gamma_C(h) different from gamma_C(g).

The triangle {e,h,g} is compatible under all coarse maps: the inequality
at A holds for every AB/AC pair, and the inequalities at B and C hold by
selection. It is therefore compatible originally and meets all local
tight classes. Every triangle meets all nonlocal tight classes, as noted
above. Hence it is safely removable.

### 3b. No original nonlocal tight class exists

The coarse maps at both A and B are nonconstant on AB.

For A, if no local tight class was coarsened, a monochromatic AB would
itself be an original nonlocal tight class. If a local tight class J was
coarsened, AB contained in J would imply J=AB and make J nonlocal tight
for the cut at B. If AB is in its complement, then J is entirely in AC
and has size s, so J=AC and is nonlocal tight for the cut at C. Each
possibility contradicts the assumption. The proof at B is identical.

The grid lemma now produces a compatible parallel pair in AB, meeting
all local tight classes. No nonlocal tight constraints exist, so this pair
is safely removable.

## 4. Induction and exact copy accounting

Every selected pair or triangle is nonempty and has even degrees at
each label. Deleting its actual copies preserves degree parity and, by
the checked tight-cut criterion, admissibility. The number of copies
strictly decreases. Induct until no copies remain. Reinserting the
selected circuit at each induction step yields pairwise disjoint finite
sets covering exactly the original copies, each a compatible connected
2-regular subgraph.

No assumptions on the number of original incidence classes, multiplicity,
connectivity, or positive lower degree are needed.

## Independent computational check

`three_label_selector_check.py` directly implements the selector and checks
original compatibility and all residual class-cut inequalities. It passed:

- all 1,025 admissible incidence-class assignments for every nonempty
  even-degree graph with three bundle sizes at most two (eight graphs);
- 167,867 admissible randomized assignments from 300,000 generated
  instances, with each bundle size at most eleven.

These computations support the mathematical case analysis. They do not
replace a Lean proof, and no numbered assertion has been added.

## Suggested formalization interfaces

1. `exists_pair_distinct_both_coordinates`: arbitrary finite nonempty
   edge set and two nonconstant coordinate functions.
2. `LocalCoarsening`: a finite-incidence class map with refinement,
   half-degree bounds, and the property of meeting every locally tight
   class whenever two incidences have different coarse values.
3. `ThreeLabelBundles`: three disjoint actual-copy bundles, their exact
   incidence and cut identities, and permutation of the three labels.
4. `exists_safe_parallel_pair_of_unequal_bundles`: the full unequal case,
   with sorted x≥y≥z and x>z.
5. `exists_safe_circuit_of_equal_bundles`: the full equal case s>0.
6. `exists_threeLabel_safe_circuit`: combine the two cases and express
   the output using `IsCircuit`, `Compatible`, and `AdmissibleOn`.
7. `exists_threeLabel_compatibleCircuitPartition`: strong induction on
   the actual edge-copy cardinality, with exact union/disjointness.
