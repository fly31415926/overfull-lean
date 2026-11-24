# Independent source review: suppression and triangle selection

Reviewer: `/root/four_degree_two`.

I read the complete current source of the two modules below. They were authored
by `/root/assess_next_proofs`, not by me. I authored the supporting degree-two
support, parallel, reassembly, lifting and final modules, so this note does not
claim an independent review of that authored chain. No source was changed as
part of this review.

## Exact reviewed sources

| Source | SHA-256 |
| --- | --- |
| `Overfull/CompatibleCircuits/FourDegreeTwoSuppression.lean` | `5a28587bee8faf2880767b361bcabba0e83af7b86a7907818ca9d447639936c8` |
| `Overfull/CompatibleCircuits/FourTriangleSelection.lean` | `bd621c4e2e86c6a16001e60e34e9d61d643c4f9050d8ce1a77db2e16057086c7` |

## Degree-two suppression

The construction retains the original edge type. It replaces the endpoints of
copy `e` from `a-v` to `a-b`, selects `C.erase f`, and changes only the incidence
class at `(b,e)` to the original class at `(b,f)`. The hypotheses require
pairwise distinct `a,v,b`, distinct selected copies `e,f`, their stated original
endpoints, and that every selected incidence at `v` belongs to those two copies.
Thus the final admissibility theorem concerns the complete selected degree-two
star. It does not justify suppressing an arbitrary pair at a larger-degree
vertex.

The proof checks every finite shore and every class, not merely singleton cuts:

1. Placing `v` on `b`'s side gives literal equality between the suppressed cut
   and an original cut. For a class vertex different from `v,b`, it also gives
   literal equality of the corresponding class-cut sets.
2. For the class at `b`, placing `v` on `a`'s side instead gives an exact
   bijection using the swap of the two actual copies `e,f`. Both the whole cut
   and its tested class-cut use this same swap. The inherited class at `(b,e)`
   is precisely what makes the class-cut identity valid.
3. The suppressed label `v` has degree zero, so every class-cut there is empty.

These cases exhaust the class vertex and prove `suppressionGraph_admissibleOn`
from the original `AdmissibleOn` predicate. The degree theorem preserves every
other selected degree using singleton-cut identities. Both degree conclusions
are structural: they assume neither even degrees nor an existing partition.
The code is generic in the ambient vertex, copy and class types; only the
selected copies and tested shores are finite.

The suppression module supplies cut, class-cut and degree transport. It does
not itself assert the existence of a circuit partition or an unrestricted
partwise lifting theorem. Distinct classes at the restored vertex are a
separate lifting obligation, correctly absent from the suppression statement.

## Finite triangle selection

`monochromatic_coordinate_of_no_pair` correctly derives that a nonempty bundle
is constant in at least one endpoint coordinate when no two of its copies
differ in both coordinates. The two inequalities in the forbidden-pair
predicate already imply distinct copies; no distinctness hypothesis is lost.

The main selection theorem assumes three nonempty finite bundles, one constant
endpoint coordinate for each bundle, and the absence of a common class on each
whole corner union. Its eight endpoint-orientation cases reduce to the cyclic
and transitive helper theorems. In the cyclic case each required nonconstant
choice can be made independently of the other two. In the transitive case the
two constant classes at the common corner must differ, while the remaining
corner choices are provided by nonemptiness and the absence of a common class.
The three returned inequalities concern exactly the three shared corners.
They also imply pairwise distinctness of the three selected copies, even
though disjointness of the input finite sets is not assumed.

The contrapositive theorem consequently identifies a genuinely constant
class on an entire corner union, not just failure of a particular previously
chosen triple. No finiteness assumption on the class type or bound on the
number of class values is introduced.

The formal conclusion is a triple of actual members with the three class
inequalities. To apply it to a graph, a caller still has to identify the three
sets with the appropriate endpoint bundles. This module does not prove safe
deletion of the selected triangle, the required critical-cut witnesses, or a
general four-label compatible-circuit partition.

## Verification evidence and conclusion

The current source hashes equal those recorded in the successful focused
attempts `development/d2-suppression-03` and
`development/four-triangle-selection-01`. Each ran its exact module with
`lake build --wfail`, returned exit zero, and recorded no input changes during
the command. The respective output hashes are
`1b291fd191d72ee1bc866b945db4b3bb3ad2c081a15f0a489745e4f1e6ceec29`
and `02a36dafd6948efb6ae8091e3f0e0fe7f8907a3f426ce2643cb6096ebd3a99d1`.
Earlier failed or interrupted attempts are not substituted for these receipts.

I found no mismatch between these statements and their documented scope, and
no missing mathematical hypothesis in the reviewed constructions. This source
review and the focused checks do not replace the complete frozen build,
unchanged axiom audit, baseline preservation checks or publication readback.
Neither reviewed module promotes a numbered manuscript assertion.
