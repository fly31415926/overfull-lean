# Independent source review: degree-two reduction and bounded joining stages

Reviewer: `/root/verification_infrastructure`.

The reviewer read the six-module degree-two construction and the two bounded
wrappers below. The mathematical code was authored by other agents. This
review made no mathematical source changes. The source hashes below identify
the reviewed versions and were compared directly with the successful focused
attempts before the full input freeze.

## Exact reviewed sources

| Source under `Overfull/CompatibleCircuits/` | SHA-256 |
| --- | --- |
| `FourDegreeTwoSupport.lean` | `c3415a549357a4edfd5722f0ab56017296d7e2ee7940aa334dd7f231ece788fd` |
| `FourDegreeTwoParallel.lean` | `fc25edfd1f9de81b62ed5aca3dca51a467cdb582308ba6e5fa15e25a8c595d0f` |
| `FourDegreeTwoSuppression.lean` | `5a28587bee8faf2880767b361bcabba0e83af7b86a7907818ca9d447639936c8` |
| `FourDegreeTwoReassembly.lean` | `dab7faa627b57f918f4097f0de308aa0f2000cad991a91301779791186cd1231` |
| `FourDegreeTwoLift.lean` | `ae1e1cdad4c1058b1d269b274a97f1f1c37f09ec9d0b237db0f2cb69f83dee91` |
| `FourDegreeTwo.lean` | `e6b69828aa63be32f4bc38ef3d7029de499e1f2c6bed2e23694a99ce976fa61a` |
| `FourBounded.lean` | `d88388b19185af7e92fa10c9c1479bbc75d74ceea769d98ba77df792246599fc` |
| `FourBoundedJoining.lean` | `ccefcf06474efc8459c35a3a3aa96992db23d79c1f696d1313a5677b92406964` |

## The complete low-degree construction

The public low-degree theorem assumes exactly an admissible selected-copy
instance on `Fin 4`, even selected degree at every label, and an existing
label of degree at most two. Parity reduces its degree to zero or two. The
degrees at the other labels are unrestricted. The conclusion is a genuine
compatible circuit partition of the original finite copy set; the statement
does not take a partition, a safe deletion, or a lifting certificate as an
additional premise.

For degree zero, `selectedSupportGraph` restricts vertices to the actual
selected edge support and copies to the subtype of selected copies. Its
cut, class-cut and degree identities transport the original admissibility
and parity. The unused fourth label bounds this support by three, allowing
the previously proved complete three-label theorem. Mapping the result back
retains all original selected copies and their original incidences.

For degree two, the incidence-set cardinality gives two distinct actual
copies and proves that these exhaust the entire selected star. The split
between parallel copies and a two-edge path is exhaustive because the
multigraph has distinct endpoints for every edge copy.

In the parallel branch, moving the degree-two label onto its neighbor's
side identifies every residual cut with an original cut. The same literal
set identity also identifies each tested class-cut, proving the residual
half-cut inequality for every shore and every class. Original admissibility
on the singleton shore at the removed label rules out equal classes for the
two copies at either incident endpoint. Thus they are a compatible
two-circuit. Removing both leaves that label isolated and preserves even
degrees; the three-label partition and the removed circuit then give exact
coverage of the original selected set.

In the path branch, suppression retains the original copy type. It changes
copy `e` from `a-v` to `a-b`, erases copy `f` from the selected set, and sets
the class of the changed copy at `b` equal to the original class of `f` at
`b`. The three labels are pairwise distinct, and the hypotheses establish
the complete selected star at `v`. For every tested shore, placing `v` on
`b`'s side gives the ordinary cut identity. The class at `b` uses the other
placement and a bijection swapping `e,f`; the same bijection transports the
whole cut and its class-cut. The class at `v` is empty after suppression.
These cases establish all admissibility inequalities, not only local
singleton bounds. The remaining selected degrees are unchanged and `v`
has degree zero, so the complete three-label construction applies again.

Lifting expands only the part containing `e` by reinserting `f`. The original
degree-two admissibility bound proves that the restored classes at `v`
differ. Away from `v`, the endpoint and inherited-class identities transfer
compatibility. The expanded set is even and compatible. The existing complete
decomposition theorem for an already compatible even selected set on four
labels supplies circuits within it; the proof does not assume that expansion
itself preserves connectedness. All other parts transport unchanged because
they omit both modified copies. The reassembly lemmas prove disjointness and
exact union of selected copies, so the final construction neither loses nor
duplicates copies.

## Bounded degree and copy count

`FourBounded.lean` first proves the handshake identity over the whole finite
vertex type by extending the existing support sum with zero degrees. A
four-label even-degree instance with all degrees at most four either has a
label of degree at most two, or every degree is exactly four. Those cases use
the new construction and the previously complete four-regular construction,
respectively. No connectedness hypothesis is introduced.

For at most eight selected copies, the handshake sum is at most sixteen.
If no degree is at most two, evenness gives four lower bounds of four; the
sum therefore forces every degree to be exactly four. This proves the
eight-copy statement without an unnecessary maximum-degree premise: the
low-degree branch permits other degrees greater than four. The contrapositive
statement consequently gives only necessary conditions for an unresolved
instance: every degree is at least four, some degree is at least six, and
there are at least nine selected copies. It does not assert that such a
counterexample exists.

The wrappers on an arbitrary finite vertex type of cardinality at most four
use an injective embedding into `Fin 4`. Added labels are isolated. The old
embedding theorems preserve admissibility, parity, original copies and the
partition on return. The low-degree wrapper explicitly assumes an existing
small-degree vertex; the bounded-degree and eight-copy wrappers also cover
empty ambient vertex types through the embedding argument.

## Original-host joining constructions

`FourBoundedJoining.lean` uses the actual joining-copy subtype and original
endpoint classes. For at most four even fibers, the regular original host
and its no-overfull-set hypothesis provide the existing quotient
admissibility and parity theorems. Either one fiber boundary of size at most
two, or bounds of four on every fiber boundary, then invokes the proved
quotient existence theorem. The final structure provides nonempty original
matching pieces, each of size at most four, pairwise disjoint and covering
exactly the original joining copies. A circuit's selected degree is zero or
two at every quotient label; the exact degree/cut identity gives the same
zero-or-two intersection with each original fiber cut.

For two odd fibers `a,b`, the original parity assumption names precisely those
two fibers, with `a ≠ b`. The augmented quotient adds `h` virtual copies
between them. A small boundary is required at an explicitly even fiber
different from both; its degree remains at most two after augmentation,
regardless of the virtual multiplicity. Admissibility and evenness of the
whole augmented instance are established by existing original-host results,
and the new low-degree theorem constructs the needed partition.

The output separates pieces containing a virtual copy from pieces without
one. Existing exact transport theorems give exactly `h` distinct primary
pieces, disjointness of both families and their original copies, nonempty
matching pieces, and exact coverage of all joining copies. Compatibility
allows at most one virtual copy in each circuit. Removing that copy leaves
at most three original copies; surplus circuits have at most four. A primary
piece crosses each odd fiber exactly once, with odd cut size precisely at
`a,b`; surplus cut sizes are even. These conclusions are valid also when
`h = 0`, with an empty primary family. The theorem proves the circuit stage
under its stated boundary condition, not the unrestricted terminal
factorization proposition.

## Focused evidence and final scope

The exact live hashes above match these successful genuine attempts:

| Attempt | Checked endpoint module | Reported jobs | Child exit | Input changes |
| --- | --- | ---: | ---: | --- |
| `d2-final-02` | `FourDegreeTwo` and its six-module dependency chain | 3,124 | 0 | None |
| `four-bounded-02` | `FourBounded` | 3,131 | 0 | None |
| `four-joining-02` | `FourBoundedJoining` | 3,174 | 0 | None |

Each actual command used `lake build --wfail`. The preserved output hashes are
`c09ae725b0c56e812803447ab7b54cdda184c6c34eda8b388376aa8c248aff6b`,
`70654f94b0c4f85bb01667a3451d6be0c5b5609507272a1d884bfab3e92f63d7`, and
`4d868c3ab1cb338c16143fd6aad3ae323a806ea96e1a899cebfb3be9b54f1fbc`,
respectively. They were compared with the actual retained logs. Earlier
failed or interrupted attempts remain separate evidence.

No mathematical hypothesis or documented-scope mismatch was found. The
constructions retain the original admissibility definition and exact-copy
partition meaning, and make no unrestricted four-label existence claim.
They do not complete another numbered manuscript assertion. The complete
frozen build, kernel axiom audit and independent baseline preservation gate
remain required after this review; focused successes alone do not certify
the whole project.
